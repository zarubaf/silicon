// SPDX-License-Identifier: Apache-2.0
//! The hardware aggregate in the evaluator, as Lean `Eval.normalize`, `Agg.plan`, `Agg.bindAt`,
//! and `Agg.set` give it (design sections 5.1, 5.4, and 7.3): the normal form of a part, the
//! selection of a part, the typed use, the binding by leaf, and the place update with its
//! rebind. A selection on a stored aggregate refers to the part by the numbers of its path, so
//! it copies nothing. Each walk keeps its own stack, and each charge comes before the work that
//! it pays for.

use super::place::{Index, PartInfo};
use super::{Code, Evaluator, Let, Names, Out, Res, at, fail};
use crate::agg::{Agg, Base, Node};
use crate::hw::{Seen, Val};
use crate::int::Int;
use crate::limit;
use crate::names::{PathId, Step, Sym};
use crate::ops;
use crate::types::{PartNames, Ty, TyId};
use crate::value::Value;
use parse::ast::{Ident, Nat, Pos};

/// A step of the typed use that converts: convert a part at a type, or make a node of the
/// last `n` results.
enum Convert {
    Visit(TyId, Agg),
    Build(TyId, usize),
}

/// A step of the binding: bind a part at a path, or make a node of the last `n` results.
enum Bind {
    Visit(Agg, PathId),
    Build(TyId, usize),
}

/// A container of a reference that the binding enters: its base, its path, its type, the number
/// of its next part, and the number of its parts.
struct Level {
    base: Base,
    path: PathId,
    ty: TyId,
    next: u64,
    len: u64,
}

/// A node on the path of a place update: its type, its parts without the part on the path, and
/// the number of that part.
struct Above {
    ty: TyId,
    parts: Vec<Agg>,
    k: usize,
}

impl Evaluator<'_> {
    /// The part of the type `t` of the base `base` in its normal form (section 5.1), with no
    /// charge. A part without a hardware leaf is the static zero of its type, for example a part
    /// of the type `[Unit; 4]`. A part of a scalar type is a hardware value. Another part is a
    /// reference.
    pub(super) fn part_of(&mut self, pos: Pos, base: Base, t: TyId) -> Res<Agg> {
        if self.tys.meta(t).leaves.is_zero() {
            match self.tys.zero(t) {
                Some(v) => Ok(Agg::Static(v)),
                None => fail(Code::S010, pos, format!("{} has no zero", self.tys.text(t))),
            }
        } else if matches!(self.tys.get(t), Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) {
            let ty = self.tys.get(t).clone();
            Ok(Agg::Hw(self.graph.mk(pos, ty, base.op(), Vec::new())))
        } else {
            Ok(Agg::Ref(base, t))
        }
    }

    /// A read at `pos` of the name `base` of the type `t`: a port, a register, a wire, or a
    /// child output (section 5.5). The read makes a value of the depth of a zero of `t`, so it
    /// checks this depth first, as `T()` does. A read of a leaf in a container adds the `above`
    /// nodes over the leaf to this depth (section 5.4). Then it gives the reference in its
    /// normal form.
    pub(super) fn read_agg(&mut self, pos: Pos, base: Base, t: TyId, above: u64) -> Res<Agg> {
        self.bounded(pos, above.saturating_add(self.tys.zero_depth(t)))?;
        self.normal(pos, Agg::Ref(base, t))
    }

    /// `read_agg` as a value, with no node above.
    pub(super) fn read_ref(&mut self, pos: Pos, base: Base, t: TyId) -> Res<Val> {
        Ok(self.read_agg(pos, base, t, 0)?.into_val())
    }

    /// The normal form of the aggregate `a` at `pos` as a value (`normal`).
    pub(super) fn normalize(&mut self, pos: Pos, a: Agg) -> Res<Val> {
        Ok(self.normal(pos, a)?.into_val())
    }

    /// The normal form of the aggregate `a` at `pos`. A reference without a hardware leaf is a
    /// static value, for example a part of the type `[Unit; 4]`. It charges the zero size of its
    /// type from the metadata before the zero exists (section 5.4), so a huge empty part fails
    /// before any work. A reference of a scalar type is a hardware value. Another reference
    /// stays lazy: it neither expands nor charges.
    pub(super) fn normal(&mut self, pos: Pos, a: Agg) -> Res<Agg> {
        match a {
            Agg::Ref(base, t) => {
                if self.tys.meta(t).leaves.is_zero() {
                    limit::zero(&self.tys.meta(t).zero_size).map_err(at(pos))?;
                    self.fuel
                        .pay_int(&self.tys.meta(t).zero_size)
                        .map_err(at(pos))?;
                }
                self.part_of(pos, base, t)
            }
            a => Ok(a),
        }
    }

    /// The result for the part `v` of an aggregate. A part of a reference that has no hardware
    /// leaf is a new static value, so it does not refer (section 5.4). Another part refers.
    fn part_out(from_ref: bool, v: Val) -> Out {
        if from_ref && matches!(v, Val::Static(_)) {
            Out::Made(v)
        } else {
            Out::Named(v)
        }
    }

    /// The part `k` of the aggregate that `out` is, at `pos`. A reference makes a reference to
    /// the part of type `ft`, with the leaf field `step`, in constant work. A part of a
    /// reference without a hardware leaf charges its zero size from the metadata first
    /// (`normalize`). A node that a reference to a local names gives a reference to the part by
    /// its number, so the node is not copied. A new node gives its part in its normal form, and
    /// moves it out.
    fn agg_part(&mut self, pos: Pos, out: Out, k: usize, step: Step, ft: Option<TyId>) -> Res<Out> {
        let kept = out.kept();
        let part = self.agg_part_of(pos, out, k, step, ft)?;
        // A part of a copy that still holds its local holds it too.
        Ok(match (kept, part) {
            (Some(root), Out::Made(v) | Out::Named(v)) => Out::Kept(v, root),
            (_, part) => part,
        })
    }

    /// `agg_part`, with no regard for the local that `out` holds.
    fn agg_part_of(
        &mut self,
        pos: Pos,
        out: Out,
        k: usize,
        step: Step,
        ft: Option<TyId>,
    ) -> Res<Out> {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Selected, 1);
        let lazy = match self.store.seen(&out) {
            Seen::Agg(Agg::Ref(base, parent)) => {
                let Some(ft) = ft else {
                    return fail(Code::S010, pos, "the part has no type".to_owned());
                };
                let offset = self.tys.offset(*parent, k as u64);
                Some((base.sub(&mut self.paths, step, offset), ft))
            }
            _ => None,
        };
        if let Some((sub, ft)) = lazy {
            let v = self.normalize(pos, Agg::Ref(sub, ft))?;
            return Ok(Self::part_out(true, v));
        }
        match out {
            Out::Ref(mut r) => {
                r.path.push(k);
                // A part that is a reference of a scalar type or with no hardware leaf is not in
                // its normal form, so it is read as a new reference.
                let abnormal = match self.store.at(&r) {
                    Seen::Agg(Agg::Ref(b, t))
                        if self.tys.meta(*t).leaves.is_zero()
                            || matches!(self.tys.get(*t), Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) =>
                    {
                        Some((b.clone(), *t))
                    }
                    _ => None,
                };
                match abnormal {
                    Some((base, t)) => {
                        let v = self.normalize(pos, Agg::Ref(base, t))?;
                        Ok(Self::part_out(true, v))
                    }
                    None => Ok(Out::Ref(r)),
                }
            }
            o => {
                let Val::Agg(a) = self.store.take(o) else {
                    return fail(
                        Code::S010,
                        pos,
                        "a hardware aggregate is expected".to_owned(),
                    );
                };
                let (Agg::Array(_, mut p)
                | Agg::Tuple(_, mut p)
                | Agg::Record(_, mut p)
                | Agg::List(_, mut p)) = *a
                else {
                    return fail(Code::S010, pos, "the part does not exist".to_owned());
                };
                let part =
                    p.0.get_mut(k)
                        .map(|x| std::mem::replace(x, Agg::Static(Value::Unit)));
                let Some(part) = part else {
                    return fail(Code::S010, pos, "the part does not exist".to_owned());
                };
                Ok(Out::Named(self.normalize(pos, part)?))
            }
        }
    }

    /// The number of the element that the static index `index` at `ipos` picks from `len`
    /// elements. The index is a `usize` or beyond it, so a wide index is out of range.
    pub(super) fn within(ipos: Pos, len: u64, index: &Index) -> Res<usize> {
        let range = |num: &str| {
            fail(
                Code::S013,
                ipos,
                format!("the index {num} is out of range for {len} element(s)"),
            )
        };
        match index {
            Index::Number(num) if (*num as u64) < len => Ok(*num),
            Index::Number(num) => range(&num.to_string()),
            Index::Wide(num) => range(num),
            Index::Bad(msg) => fail(Code::S010, ipos, msg.clone()),
        }
    }

    /// The number of the parts that an index of the aggregate `a` picks from: a node holds its
    /// parts, and a reference to an array or a tuple reads its type.
    pub(super) fn index_len(&self, a: &Agg) -> Option<u64> {
        match a {
            Agg::Array(_, parts) | Agg::Tuple(_, parts) | Agg::List(_, parts) => {
                Some(parts.0.len() as u64)
            }
            Agg::Ref(_, ty) => match self.tys.get(*ty) {
                Ty::Array(_, count) => Some(count.to_u64().unwrap_or(u64::MAX)),
                Ty::Tuple(parts) => Some(parts.len() as u64),
                _ => None,
            },
            _ => None,
        }
    }

    /// The number of the parts that a selector `.N` of the aggregate `a` picks from. Only a
    /// tuple has one.
    pub(super) fn select_len(&self, a: &Agg) -> Option<usize> {
        match a {
            Agg::Tuple(_, parts) => Some(parts.0.len()),
            Agg::Ref(_, ty) => match self.tys.get(*ty) {
                Ty::Tuple(parts) => Some(parts.len()),
                _ => None,
            },
            _ => None,
        }
    }

    /// The index `index` at `ipos` of the aggregate `out`, a result of the index at `pos`. A
    /// reference to an array or a tuple gives a reference to the element `<k>e`, and its type
    /// gives the length, so a huge array takes no more work.
    pub(super) fn agg_index(&mut self, pos: Pos, ipos: Pos, out: Out, index: &Index) -> Res<Out> {
        let Seen::Agg(agg) = self.store.seen(&out) else {
            return fail(
                Code::S010,
                pos,
                "a hardware aggregate is expected".to_owned(),
            );
        };
        let Some(len) = self.index_len(agg) else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "an index needs an array, a list, or a tuple, not {}",
                    self.text(Seen::Agg(agg))
                ),
            );
        };
        let num = Self::within(ipos, len, index)?;
        let part_ty = match agg {
            Agg::Ref(_, ty) => self.tys.part(*ty, num),
            _ => None,
        };
        self.agg_part(pos, out, num, Step::Elem(num as u64), part_ty)
    }

    /// The selector `.index` with its literal at `lit` of the aggregate `out`, a result of the
    /// selector at `pos`. Only a tuple has one.
    pub(super) fn agg_select(&mut self, pos: Pos, lit: Pos, index: &Nat, out: Out) -> Res<Out> {
        let Seen::Agg(agg) = self.store.seen(&out) else {
            return fail(
                Code::S010,
                pos,
                "a hardware aggregate is expected".to_owned(),
            );
        };
        self.no_enum_field(pos, index.as_str(), Seen::Agg(agg))?;
        let Some(len) = self.select_len(agg) else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "the selector `.{}` needs a tuple, not {}",
                    index.as_str(),
                    self.text(Seen::Agg(agg))
                ),
            );
        };
        let num = match index.as_str().parse::<usize>() {
            Ok(num) if num < len => num,
            _ => {
                return fail(
                    Code::S013,
                    lit,
                    format!(
                        "the selector {} is out of range for {}",
                        index.as_str(),
                        self.text(Seen::Agg(agg))
                    ),
                );
            }
        };
        let part_ty = match agg {
            Agg::Ref(_, ty) => self.tys.part(*ty, num),
            _ => None,
        };
        self.agg_part(pos, out, num, Step::Elem(num as u64), part_ty)
    }

    /// The symbol of the field name `f`. The top expression has no symbols for its fields, so a
    /// search by name finds it, as `field_number` does.
    pub(super) fn field_sym(&self, f: &Ident) -> Option<Sym> {
        match self.names {
            Names::File => self.syms.fields.get(&f.id).copied(),
            Names::Top => self.syms.find(&f.name),
        }
    }

    /// The struct type of the aggregate `a`, if it is a record or a reference to one.
    pub(super) fn record_ty(&self, a: &Agg) -> Option<TyId> {
        match a {
            Agg::Record(n, _) => Some(n.ty),
            Agg::Ref(_, t) if matches!(self.tys.get(*t), Ty::Struct(_)) => Some(*t),
            _ => None,
        }
    }

    /// The number of the field with the symbol `y` and the name `name` of the aggregate `a` and
    /// its type, if `a` is a record or a reference to one with that field.
    pub(super) fn agg_field_at_by(
        &self,
        a: &Agg,
        y: Option<Sym>,
        name: &str,
    ) -> Option<(usize, TyId)> {
        let parts = self.tys.parts(self.record_ty(a)?)?;
        let k = self.field_number_by(parts.item()?, y, name)?;
        Some((k, parts.types.get(k).copied()?))
    }

    /// The number of the field `f` of the aggregate `a` and its type (`agg_field_at_by`), by the
    /// symbol of its name.
    pub(super) fn agg_field_at(&self, a: &Agg, f: &Ident) -> Option<(usize, TyId)> {
        self.agg_field_at_by(a, self.port_sym(f), &f.name)
    }

    /// The field `f` of the aggregate `out`, a result of the field at `pos`. A reference to a
    /// record gives a reference to the part with the leaf field `f`. The record type holds the
    /// number of its specialization, and the symbol of `f` finds the number of the field, so
    /// the selection compares no name.
    pub(super) fn agg_field(&mut self, pos: Pos, f: &Ident, out: Out) -> Res<Out> {
        let sym = self.field_sym(f);
        self.agg_field_by((pos, pos), (self.port_sym(f), &f.name, sym), out)
    }

    /// The field with the symbol `y` and the name `name` of the aggregate `out`, a result of the
    /// field at `pos`. The look-up and its errors are at `kp`. A reference to a record gives a
    /// reference to the part with the leaf field, named by the symbol `leaf`.
    pub(super) fn agg_field_by(
        &mut self,
        (pos, kp): (Pos, Pos),
        (y, name, leaf): (Option<Sym>, &str, Option<Sym>),
        out: Out,
    ) -> Res<Out> {
        let Seen::Agg(agg) = self.store.seen(&out) else {
            return fail(
                Code::S010,
                kp,
                "a hardware aggregate is expected".to_owned(),
            );
        };
        self.no_enum_field(kp, name, Seen::Agg(agg))?;
        let Some((k, ft)) = self.agg_field_at_by(agg, y, name) else {
            return fail(
                Code::S010,
                kp,
                format!("{} has no field `{name}`", self.text(Seen::Agg(agg))),
            );
        };
        let step = match agg {
            Agg::Ref(..) => match leaf {
                Some(sym) => Step::User(sym),
                None => {
                    return fail(Code::S010, kp, format!("the field `{name}` has no symbol"));
                }
            },
            _ => Step::Elem(0),
        };
        self.agg_part(pos, out, k, step, Some(ft))
    }

    /// `len` of the aggregate `o` at the call `pos`. A node of an array holds its parts, and a
    /// reference to an array reads its type, so a huge array charges nothing.
    pub(super) fn agg_len(&self, pos: Pos, o: &Out) -> Res<Option<Out>> {
        let Seen::Agg(a) = self.store.seen(o) else {
            return fail(
                Code::S010,
                pos,
                "a hardware aggregate is expected".to_owned(),
            );
        };
        let n = match a {
            Agg::Array(_, p) | Agg::List(_, p) => Some(Int::from_u64(p.0.len() as u64)),
            Agg::Ref(_, t) => match self.tys.get(*t) {
                Ty::Array(_, n) => Some(n.clone()),
                _ => None,
            },
            _ => None,
        };
        match n {
            Some(n) => Ok(Some(Out::Made(Val::Static(Value::Int(n))))),
            None => fail(
                Code::S010,
                pos,
                format!(
                    "`len` takes an array, a list, or a string, not {}",
                    self.text(Seen::Agg(a))
                ),
            ),
        }
    }

    /// A typed use of the aggregate that `out` is, at the type `t` at `pos` (section 5.4). An
    /// aggregate of the type `t` charges nothing. Another one checks each part first
    /// (`plan_agg`), then charges its size plus the size of the result, then converts its
    /// static parts. A reference copies only after its charge, and the result checks its depth
    /// (`S015`).
    pub(super) fn typed_agg(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Agg> {
        let Seen::Agg(a) = self.store.seen(&out) else {
            return fail(
                Code::S010,
                pos,
                "a hardware aggregate is expected".to_owned(),
            );
        };
        if a.stored_ty() == Some(t) {
            return self.agg_of(pos, out);
        }
        let size = a.size(&self.graph, &self.tys);
        let planned = self.plan_agg(pos, t, a)?;
        self.charge(pos, u128::from(size) + u128::from(planned))?;
        let a = self.agg_of(pos, out)?;
        let r = self.convert_agg(pos, t, a)?;
        self.bounded(pos, r.depth(&self.tys))?;
        Ok(r)
    }

    /// The typed use of the part `a` at `t` at `pos`, for a part that no result holds. The
    /// charge is that of `typed_agg`, and the copy comes after it. A part of the type `t`
    /// is the caller's to keep.
    pub(super) fn typed_part(&mut self, pos: Pos, t: TyId, a: &Agg) -> Res<Agg> {
        let size = a.size(&self.graph, &self.tys);
        let planned = self.plan_agg(pos, t, a)?;
        self.charge(pos, u128::from(size) + u128::from(planned))?;
        let r = self.convert_agg(pos, t, a.clone())?;
        self.bounded(pos, r.depth(&self.tys))?;
        Ok(r)
    }

    /// The aggregate that the result `out` is. A reference to a stored one copies it, and the
    /// caller paid the copy.
    fn agg_of(&self, pos: Pos, out: Out) -> Res<Agg> {
        match self.store.take(out) {
            Val::Agg(a) => Ok(*a),
            _ => fail(
                Code::S010,
                pos,
                "a hardware aggregate is expected".to_owned(),
            ),
        }
    }

    /// The error of a part of the wrong type: `S010` at `pos`.
    fn wrong_part<T>(&self, pos: Pos, t: TyId, a: &Agg) -> Res<T> {
        fail(
            Code::S010,
            pos,
            format!(
                "expected {}, but the value is {}",
                self.tys.text(t),
                self.text(a.seen())
            ),
        )
    }

    /// The size of the converted aggregate, and the check of every part at its type, in the walk
    /// order and before any charge. A hardware leaf and a reference need the type of their
    /// position (`S010`), a static part its type and its sign (`S010`, `S012`), and a record
    /// its own struct type. The walk keeps its own stack.
    fn plan_agg(&self, pos: Pos, want: TyId, root: &Agg) -> Res<u64> {
        let mut size = 0u64;
        let mut work = vec![(want, root)];
        while let Some((want, part)) = work.pop() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Typed, 1);
            // A handle type needs a handle of exactly this type (Lean `Agg.handleAt`).
            if self.tys.get(want).is_handle() || matches!(part, Agg::Handle(_)) {
                match part {
                    Agg::Handle(h) if self.handle_fits(h, want) => {
                        size = size.saturating_add(1);
                        continue;
                    }
                    _ => return self.handle_mismatch(pos, want, part.seen()),
                }
            }
            match (part, self.tys.get(want)) {
                (Agg::Ref(_, has), _) if *has == want => {}
                (Agg::Hw(leaf), ty) if self.graph.ty(*leaf) == *ty => {}
                (Agg::Record(node, _) | Agg::List(node, _), _) if node.ty == want => {}
                (Agg::Static(value), _) => {
                    size = size
                        .saturating_add(ops::plan_value(want, value, &self.tys).map_err(at(pos))?);
                    continue;
                }
                (Agg::Array(_, parts), Ty::Array(elem, len))
                    if len.cmp_u64(parts.0.len() as u64).is_eq() =>
                {
                    size = size.saturating_add(1);
                    work.extend(parts.0.iter().rev().map(|x| (*elem, x)));
                    continue;
                }
                (Agg::Tuple(_, parts), Ty::Tuple(types)) if types.len() == parts.0.len() => {
                    size = size.saturating_add(1);
                    work.extend(types.iter().copied().zip(&parts.0).rev());
                    continue;
                }
                (Agg::List(_, parts), Ty::List(elem)) => {
                    size = size.saturating_add(1);
                    work.extend(parts.0.iter().rev().map(|x| (*elem, x)));
                    continue;
                }
                _ => return self.wrong_part(pos, want, part),
            }
            size = size.saturating_add(part.size(&self.graph, &self.tys));
        }
        Ok(size)
    }

    /// The conversion of the aggregate `a` to the type `t` after its checks: the static parts
    /// convert and check their fit (`S012`), and a node with no hardware leaf left is a static
    /// value. The walk keeps its own stack.
    fn convert_agg(&mut self, pos: Pos, t: TyId, a: Agg) -> Res<Agg> {
        let mut done: Vec<Agg> = Vec::new();
        let mut work = vec![Convert::Visit(t, a)];
        while let Some(step) = work.pop() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Typed, 1);
            match step {
                Convert::Visit(t, Agg::Static(v)) => {
                    let v = ops::run_value(t, &v, &self.tys).map_err(at(pos))?;
                    done.push(Agg::typed(&mut self.tys, t, v));
                }
                Convert::Visit(t, Agg::Record(n, p) | Agg::List(n, p)) if n.ty == t => {
                    done.push(match self.tys.get(t) {
                        Ty::List(_) => Agg::List(n, p),
                        _ => Agg::Record(n, p),
                    });
                }
                Convert::Visit(
                    t,
                    Agg::Array(_, mut p) | Agg::Tuple(_, mut p) | Agg::List(_, mut p),
                ) => {
                    let parts = std::mem::take(&mut p.0);
                    work.push(Convert::Build(t, parts.len()));
                    let tys: Vec<TyId> = match self.tys.get(t) {
                        Ty::Array(e, _) | Ty::List(e) => vec![*e; parts.len()],
                        Ty::Tuple(ts) => ts.clone(),
                        _ => Vec::new(),
                    };
                    for (x, ty) in parts.into_iter().zip(tys).rev() {
                        work.push(Convert::Visit(ty, x));
                    }
                }
                Convert::Visit(_, a) => done.push(a),
                Convert::Build(t, n) => {
                    let xs = done.split_off(done.len().saturating_sub(n));
                    let Some(node) = Agg::node(&self.graph, &self.tys, t, xs) else {
                        return fail(Code::S010, pos, "the part has the wrong shape".to_owned());
                    };
                    done.push(node);
                }
            }
        }
        match done.pop() {
            Some(a) => Ok(a),
            None => fail(Code::S010, pos, "the aggregate has no value".to_owned()),
        }
    }

    /// The step of the named part number `k` of the type `t`: a user field, with the symbol of
    /// its name. An enum has the parts `tag` and `payload`.
    fn field_step(&self, t: TyId, k: usize, pos: Pos) -> Res<Step> {
        let sym = self.tys.parts(t).and_then(|parts| match parts.names {
            PartNames::Struct(item) => self.syms.field_order.get(item)?.get(k).copied(),
            PartNames::Enum => [self.syms.tag, self.syms.payload].get(k).copied(),
        });
        match sym {
            Some(sym) => Ok(Step::User(sym)),
            None => fail(
                Code::S010,
                pos,
                format!("{} has no field {k}", self.tys.text(t)),
            ),
        }
    }

    /// The type, the leaf field, and the bit offset in a word of the part `k` of the container
    /// type `t`. The table stores the offsets, so the work is constant.
    pub(super) fn child_of(&self, pos: Pos, t: TyId, k: u64) -> Res<(TyId, Step, u64)> {
        let idx = usize::try_from(k).unwrap_or(usize::MAX);
        let (part, step) = match self.tys.get(t) {
            Ty::Array(e, _) => (*e, Step::Elem(k)),
            Ty::Tuple(ts) => match ts.get(idx) {
                Some(u) => (*u, Step::Elem(k)),
                None => return fail(Code::S010, pos, "the part does not exist".to_owned()),
            },
            Ty::Struct(_) | Ty::Enum(_) => match self.tys.parts(t).and_then(|p| p.types.get(idx)) {
                Some(u) => (*u, self.field_step(t, idx, pos)?),
                None => return fail(Code::S010, pos, "the part does not exist".to_owned()),
            },
            _ => return fail(Code::S010, pos, "the type has no parts".to_owned()),
        };
        Ok((part, step, self.tys.offset(t, k)))
    }

    /// The core `let` statements of the leaves of the reference to `base` of type `t`, at the
    /// name `path` with the leaf fields (section 7.3), in packing order. The caller paid for
    /// the leaves with the copy. A part without a hardware leaf makes none, and the walk keeps
    /// its own stack.
    fn leaf_lets(&mut self, pos: Pos, base: Base, path: PathId, t: TyId) -> Res<()> {
        let mut stack: Vec<Level> = Vec::new();
        let mut visit = Some((base, path, t));
        loop {
            if let Some((base, path, t)) = visit.take()
                && !self.tys.meta(t).leaves.is_zero()
            {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Bound, 1);
                match self.tys.get(t) {
                    Ty::Bool | Ty::UInt(_) | Ty::SInt(_) => {
                        let ty = self.tys.get(t).clone();
                        let value = self.graph.mk(pos, ty, base.op(), Vec::new());
                        self.naming.lets.push(Let { path, value, pos });
                    }
                    Ty::Array(_, n) => stack.push(Level {
                        base,
                        path,
                        ty: t,
                        next: 0,
                        len: n.to_u64().unwrap_or(u64::MAX),
                    }),
                    Ty::Tuple(ts) => {
                        let len = ts.len() as u64;
                        stack.push(Level {
                            base,
                            path,
                            ty: t,
                            next: 0,
                            len,
                        });
                    }
                    Ty::Struct(_) | Ty::Enum(_) => {
                        let len = self.tys.parts(t).map_or(0, |p| p.types.len() as u64);
                        stack.push(Level {
                            base,
                            path,
                            ty: t,
                            next: 0,
                            len,
                        });
                    }
                    _ => {}
                }
            }
            let Some(top) = stack.last_mut() else {
                return Ok(());
            };
            if top.next >= top.len {
                stack.pop();
                continue;
            }
            let k = top.next;
            top.next += 1;
            let (ty, base_ty, path) = (top.ty, top.base.clone(), top.path);
            let (child, step, offset) = self.child_of(pos, ty, k)?;
            let sub = base_ty.sub(&mut self.paths, step.clone(), offset);
            visit = Some((sub, self.paths.push(path, step), child));
        }
    }

    /// The binding of the aggregate `a` to the core name `path` (section 7.3). Each hardware
    /// leaf gets one core `let` at `path` with its leaf fields, and a reference expands into
    /// its leaves. The result refers to the names: a hardware leaf becomes a name, a reference
    /// becomes a reference to `path`, and a static part keeps its value. The copy paid for
    /// each leaf before. The walk keeps its own stack.
    pub(super) fn bind_agg(&mut self, pos: Pos, path: PathId, a: Agg) -> Res<Agg> {
        let mut done: Vec<Agg> = Vec::new();
        let mut work = vec![Bind::Visit(a, path)];
        while let Some(step) = work.pop() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Bound, 1);
            match step {
                Bind::Visit(Agg::Static(v), _) => done.push(Agg::Static(v)),
                // A handle and a list node hold no hardware leaf, so they keep their form.
                Bind::Visit(a @ (Agg::Handle(_) | Agg::List(..)), _) => done.push(a),
                Bind::Visit(Agg::Hw(h), path) => {
                    let ty = self.graph.ty(h);
                    self.naming.lets.push(Let {
                        path,
                        value: h,
                        pos,
                    });
                    done.push(Agg::Hw(self.graph.mk(
                        pos,
                        ty,
                        crate::hw::Op::Ref(path),
                        Vec::new(),
                    )));
                }
                Bind::Visit(Agg::Ref(base, t), path) => {
                    self.leaf_lets(pos, base, path, t)?;
                    done.push(Agg::Ref(Base::Name(path), t));
                }
                Bind::Visit(a, path) => {
                    let (Agg::Array(n, mut p) | Agg::Tuple(n, mut p) | Agg::Record(n, mut p)) = a
                    else {
                        return fail(Code::S010, pos, "the part has no shape".to_owned());
                    };
                    let parts = std::mem::take(&mut p.0);
                    work.push(Bind::Build(n.ty, parts.len()));
                    let mut children = Vec::with_capacity(parts.len());
                    for (k, x) in parts.into_iter().enumerate() {
                        let (_, step, _) = self.child_of(pos, n.ty, k as u64)?;
                        children.push(Bind::Visit(x, self.paths.push(path, step)));
                    }
                    work.extend(children.into_iter().rev());
                }
                Bind::Build(t, n) => {
                    let xs = done.split_off(done.len().saturating_sub(n));
                    let Some(node) = Agg::node(&self.graph, &self.tys, t, xs) else {
                        return fail(Code::S010, pos, "the part has the wrong shape".to_owned());
                    };
                    done.push(node);
                }
            }
        }
        match done.pop() {
            Some(a) => Ok(a),
            None => fail(Code::S010, pos, "the aggregate has no value".to_owned()),
        }
    }

    /// The reference to `base` of type `t`, expanded one level into its parts in their normal
    /// form. The caller paid for the parts.
    fn expand(&mut self, pos: Pos, base: &Base, t: TyId) -> Res<Agg> {
        let count = match self.tys.get(t) {
            Ty::Array(_, n) => n.to_u64().unwrap_or(u64::MAX),
            Ty::Tuple(ts) => ts.len() as u64,
            Ty::Struct(_) | Ty::Enum(_) => self.tys.parts(t).map_or(0, |p| p.types.len() as u64),
            _ => return fail(Code::S010, pos, "the type has no parts".to_owned()),
        };
        let mut parts = Vec::new();
        for k in 0..count {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Expanded, 1);
            let (ty, step, offset) = self.child_of(pos, t, k)?;
            let sub = base.sub(&mut self.paths, step, offset);
            parts.push(self.part_of(pos, sub, ty)?);
        }
        match Agg::node(&self.graph, &self.tys, t, parts) {
            Some(node) => Ok(node),
            None => fail(Code::S010, pos, "the type has no parts".to_owned()),
        }
    }

    /// The sum of the zero sizes of the empty parts that a reference on the path `keys` of `a`
    /// makes when it expands (Lean `Agg.emptySize`). Each reference expands one level, and the
    /// metadata gives each zero size, so the sum makes no part. The walk follows the path once.
    fn empty_size(&self, a: &Agg, keys: &[usize]) -> Int {
        let mut cur = a;
        let mut keys = keys;
        while let Some((&k, rest)) = keys.split_first() {
            match cur {
                Agg::Ref(_, t) => return self.empty_size_in(*t, keys),
                Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) | Agg::List(_, p) => {
                    match p.0.get(k) {
                        Some(x) => cur = x,
                        None => break,
                    }
                }
                _ => break,
            }
            keys = rest;
        }
        Int::zero()
    }

    /// The same for the type `t` of a reference, along the path `keys` (Lean `Ty.emptySize`).
    fn empty_size_in(&self, mut t: TyId, mut keys: &[usize]) -> Int {
        let mut total = Int::zero();
        let empty = |this: &Self, p: TyId| {
            let m = this.tys.meta(p);
            if m.leaves.is_zero() {
                m.zero_size.clone()
            } else {
                Int::zero()
            }
        };
        while let Some((&k, rest)) = keys.split_first() {
            let part = match self.tys.get(t) {
                Ty::Array(e, n) => {
                    total.add_assign(&n.mul(&empty(self, *e)));
                    Some(*e)
                }
                Ty::Tuple(ts) => {
                    for &p in ts {
                        total.add_assign(&empty(self, p));
                    }
                    ts.get(k).copied()
                }
                Ty::Struct(_) | Ty::Enum(_) => {
                    let fs = self.tys.parts(t).map_or(&[][..], |p| p.types);
                    for &p in fs {
                        total.add_assign(&empty(self, p));
                    }
                    fs.get(k).copied()
                }
                _ => None,
            };
            let Some(p) = part else { break };
            if self.tys.meta(p).leaves.is_zero()
                || matches!(self.tys.get(p), Ty::Bool | Ty::UInt(_) | Ty::SInt(_))
            {
                break;
            }
            t = p;
            keys = rest;
        }
        total
    }

    /// The walk down the numbers `keys` from `root`. Each node on the path gives up its part, and
    /// a reference on the path expands one level. A static container on the path opens one level
    /// when `open` (Lean `Agg.opened`): its elements become static parts. The result is the
    /// nodes above the path, the part where the walk ended, and the number of keys used. A
    /// static part with keys left ends the walk early, and the rest of the path lies inside its
    /// value. The caller paid for the expansion and the opening. The walk keeps its own stack.
    fn descend(
        &mut self,
        pos: Pos,
        root: Agg,
        keys: &[usize],
        open: bool,
    ) -> Res<(Vec<Above>, Agg, usize)> {
        let wrong = || {
            fail(
                Code::S010,
                pos,
                "the place has no part for its value".to_owned(),
            )
        };
        let mut above: Vec<Above> = Vec::new();
        let mut cur = root;
        // The type of the static part `cur`, once a step opened a static container: the type of
        // the part below comes from it, so the walk finds the type of a value only at the first
        // static container, and not at each level of a nested one.
        let mut opened: Option<TyId> = None;
        for (i, &k) in keys.iter().enumerate() {
            if let Agg::Ref(base, t) = &cur {
                cur = self.expand(pos, base, *t)?;
            }
            let (ty, mut parts) = match cur {
                Agg::Array(n, mut p)
                | Agg::Tuple(n, mut p)
                | Agg::Record(n, mut p)
                | Agg::List(n, mut p) => (n.ty, std::mem::take(&mut p.0)),
                Agg::Static(mut v) if open => {
                    let ty = match opened {
                        Some(ty) => ty,
                        None => v.ty(&mut self.tys),
                    };
                    let (Value::Array(_, xs) | Value::Tuple(_, xs) | Value::Record(_, xs)) = &mut v
                    else {
                        return wrong();
                    };
                    let parts = std::mem::take(xs).into_iter().map(Agg::Static).collect();
                    (ty, parts)
                }
                Agg::Static(_) => return Ok((above, cur, i)),
                _ => return wrong(),
            };
            let Some(part) = parts
                .get_mut(k)
                .map(|x| std::mem::replace(x, Agg::Static(Value::Unit)))
            else {
                return wrong();
            };
            opened = match part {
                Agg::Static(_) => self.part_ty(ty, k),
                _ => None,
            };
            above.push(Above { ty, parts, k });
            cur = part;
        }
        Ok((above, cur, keys.len()))
    }

    /// The nodes `above` a path with the part `cur` back in place, each in its normal form. A
    /// node takes the stored numbers of the part below it from the node just built, so a static
    /// part on the path is never walked again, and the siblings are read once.
    fn rebuild(&self, pos: Pos, mut above: Vec<Above>, mut cur: Agg) -> Res<Agg> {
        let mut below: Option<(u64, u64, u64)> = None;
        while let Some(mut level) = above.pop() {
            let k = level.k;
            if let Some(slot) = level.parts.get_mut(k) {
                *slot = cur;
            }
            let numbers = level.parts.iter().enumerate().map(|(i, x)| match below {
                Some(n) if i == k => n,
                _ => (
                    x.size(&self.graph, &self.tys),
                    x.depth(&self.tys),
                    x.leaves(&self.tys),
                ),
            });
            let Some(node) = Agg::shape_from(&self.tys, level.ty, level.parts.len(), numbers)
            else {
                return fail(
                    Code::S010,
                    pos,
                    "the place has no part for its value".to_owned(),
                );
            };
            below = Some((node.size, node.depth, node.leaves));
            cur = Agg::finish(&self.tys, node, level.parts);
        }
        Ok(cur)
    }

    /// The aggregate `root` with the part at the numbers `keys` replaced by `y`. Each step
    /// copies only the node on the path, and a reference on the path expands one level. A static
    /// part on the path opens one level when `y` has a hardware leaf, else the rest of the path
    /// updates inside it. Each node keeps its normal form. The caller paid for the copy and the
    /// expansion.
    fn set_at(&mut self, pos: Pos, root: Agg, y: Agg, keys: &[usize]) -> Res<Agg> {
        let open = !matches!(y, Agg::Static(_));
        let (above, mut cur, used) = self.descend(pos, root, keys, open)?;
        if used < keys.len() {
            let (Agg::Static(v), Agg::Static(w)) = (&mut cur, y) else {
                return fail(
                    Code::S010,
                    pos,
                    "the place has no part for its value".to_owned(),
                );
            };
            let Some(part) = keys.get(used..).and_then(|rest| part_in(v, rest)) else {
                return fail(
                    Code::S010,
                    pos,
                    "the place has no part for its value".to_owned(),
                );
            };
            *part = w;
        } else {
            cur = y;
        }
        self.rebuild(pos, above, cur)
    }

    /// Applies `f` to the list of the aggregate `root` at the numbers `keys`, in place: the nodes
    /// on the path copy, and the list itself does not. A list node builds again from its
    /// elements, which the charge of the root paid for. The caller paid for the change.
    fn edit_at<R>(
        &mut self,
        pos: Pos,
        root: Agg,
        keys: &[usize],
        f: impl FnOnce(ListMut<'_>) -> R,
    ) -> Res<(Agg, Option<R>)> {
        let wrong = || {
            fail(
                Code::S010,
                pos,
                "the place has no static part to change".to_owned(),
            )
        };
        let (above, mut cur, used) = self.descend(pos, root, keys, false)?;
        let r = match &mut cur {
            Agg::Static(v) => keys
                .get(used..)
                .and_then(|rest| part_in(v, rest))
                .and_then(ListMut::of_value)
                .map(f),
            Agg::List(_, p) if used == keys.len() => Some(f(ListMut::Node(&mut p.0))),
            _ => None,
        };
        if r.is_none() {
            return wrong();
        }
        if let Agg::List(n, mut p) = cur {
            let xs = std::mem::take(&mut p.0);
            cur = match Agg::node(&self.graph, &self.tys, n.ty, xs) {
                Some(rebuilt) => rebuilt,
                None => return wrong(),
            };
        }
        Ok((self.rebuild(pos, above, cur)?, r))
    }

    /// Applies `f` to the list of `root` at the numbers `keys`, with one refresh of each node on
    /// the path from the stored numbers (Lean `Agg.change`): the size changes by `delta`, and a
    /// growing depth becomes at least `depth` plus the steps from the node to the end of the
    /// path. A list node at the end of the path refreshes by the delta too, and no element is
    /// read. No sibling is read, and the walk keeps no stack.
    fn change_at<R>(
        pos: Pos,
        root: &mut Agg,
        keys: &[usize],
        delta: Delta,
        f: impl FnOnce(ListMut<'_>) -> R,
    ) -> Res<Option<R>> {
        let wrong = || {
            fail(
                Code::S010,
                pos,
                "the place has no static part to change".to_owned(),
            )
        };
        let mut cur = root;
        for (i, &k) in keys.iter().enumerate() {
            match cur {
                Agg::Array(n, p) | Agg::Tuple(n, p) | Agg::Record(n, p) | Agg::List(n, p) => {
                    delta.refresh(n, (keys.len() - i) as u64);
                    cur = match p.0.get_mut(k) {
                        Some(x) => x,
                        None => return wrong(),
                    };
                }
                Agg::Static(v) => {
                    let part = keys
                        .get(i..)
                        .and_then(|rest| part_in(v, rest))
                        .and_then(ListMut::of_value);
                    return Ok(part.map(f));
                }
                _ => return wrong(),
            }
        }
        match cur {
            Agg::Static(v) => Ok(ListMut::of_value(v).map(f)),
            Agg::List(n, p) => {
                delta.refresh(n, 0);
                Ok(Some(f(ListMut::Node(&mut p.0))))
            }
            _ => wrong(),
        }
    }

    /// The charge of the refresh that `push` and `pop` cause in an aggregate root: the part
    /// count of each container node on the path (Lean `Agg.pathWidth`). It comes after the
    /// charge of the element and before the charge of a held root. A static root has none.
    pub(super) fn charge_refresh(&mut self, pos: Pos, place: &super::place::Place) -> Res<()> {
        let Val::Agg(a) = self.store.root(&place.root) else {
            return Ok(());
        };
        let width = a.path_width(&place.keys);
        self.charge(pos, u128::from(width))
    }

    /// The size of an aggregate root, charged before the change that rebuilds each node on the
    /// path (Lean `changeAt` with no depth). A static root has none.
    pub(super) fn charge_root(&mut self, pos: Pos, place: &super::place::Place) -> Res<()> {
        let Val::Agg(a) = self.store.root(&place.root) else {
            return Ok(());
        };
        let size = a.size(&self.graph, &self.tys);
        self.charge(pos, u128::from(size))
    }

    /// Applies `f` to the list at the place of an aggregate root, in place, for `push` and `pop`.
    /// The stored numbers of the nodes above the list refresh by `delta` in the walk down the
    /// path. Without a `delta` the change can lower a depth, and each node rebuilds from its
    /// parts. The caller charged that refresh (`charge_refresh`), and it logs the change. `None`
    /// if the part is no list.
    pub(super) fn edit_list<R>(
        &mut self,
        pos: Pos,
        place: &super::place::Place,
        delta: Option<Delta>,
        f: impl FnOnce(ListMut<'_>) -> R,
    ) -> Res<Option<R>> {
        let Some(root) = self.store.take_agg(place.root, &place.keys) else {
            return fail(Code::S010, pos, "the root is not an aggregate".to_owned());
        };
        let (root, r) = match delta {
            Some(delta) => {
                let mut root = *root;
                let r = Self::change_at(pos, &mut root, &place.keys, delta, f)?;
                (root, r)
            }
            None => self.edit_at(pos, *root, &place.keys, f)?,
        };
        self.store.put_back(place.root, Val::Agg(Box::new(root)));
        Ok(r)
    }

    /// The place update of an aggregate root, or of a static root that takes a hardware leaf
    /// (section 5.4). The part `x` replaces the old part, which has `old_size` and
    /// `old_leaves`. The new root has a hardware leaf unless the update replaces each one. Then
    /// the rebind charges the size of the new root from the stored sizes: the old size, minus
    /// the size of the old part, plus the size of `x`. This charge comes before the copy of the
    /// path and before a reference on the path expands.
    /// Then the held root charges, the path copies, and each hardware leaf of the new root binds
    /// at the next version of the root. A new root without a hardware leaf and without the handle
    /// flag is a static value.
    pub(super) fn rebind(&mut self, pos: Pos, place: &super::place::Place, x: Agg) -> Res<()> {
        let (size, leaves) = match self.store.root(&place.root) {
            Val::Agg(a) => (a.size(&self.graph, &self.tys), a.leaves(&self.tys)),
            Val::Static(v) => (v.size(), 0),
            _ => return fail(Code::S010, pos, "the root is not an aggregate".to_owned()),
        };
        let old = match place.part {
            Some(old) => old,
            None => PartInfo {
                size: u64::try_from(self.seen_size(self.store.current(place.root, &place.keys)))
                    .unwrap_or(u64::MAX),
                leaves: 0,
            },
        };
        let hardware = leaves
            .saturating_sub(old.leaves)
            .saturating_add(x.leaves(&self.tys))
            != 0;
        if let Val::Agg(a) = self.store.root(&place.root)
            && let Some(t) = first_ref(a, &place.keys)
        {
            limit::zero(&self.tys.meta(t).zero_size).map_err(at(pos))?;
        }
        // A root of a type with the handle flag rebuilds its node, so it pays the new size too.
        let handles = matches!(
            self.store.root(&place.root),
            Val::Agg(a) if a.stored_ty().is_some_and(TyId::holds_handles)
        );
        if hardware || handles {
            let new = u128::from(size.saturating_sub(old.size))
                + u128::from(x.size(&self.graph, &self.tys));
            self.charge(pos, new)?;
        } else if let Val::Agg(a) = self.store.root(&place.root) {
            let empty = self.empty_size(a, &place.keys);
            self.fuel.pay_int(&empty).map_err(at(pos))?;
        }
        self.charge_held(pos, place.root)?;
        // A read that waits at the root keeps the root as it is now. The new root is built from
        // a copy of the rest of the old one, which the charge above paid for, so the old root
        // moves into the log with the part that the write replaces.
        let root = self.store.take_for_rebind(place.root, &place.keys);
        let root = match root {
            Val::Agg(root) => *root,
            Val::Static(v) => Agg::Static(v),
            _ => return fail(Code::S010, pos, "the root is not an aggregate".to_owned()),
        };
        let r = self.set_at(pos, root, x, &place.keys)?;
        let v = if hardware {
            let path = self.fresh(place.id);
            Val::Agg(Box::new(self.bind_agg(pos, path, r)?))
        } else {
            r.into_val()
        };
        self.store.put_back(place.root, v);
        Ok(())
    }
}

/// The type of the first reference on the path `keys` of `a`. The write expands it and each
/// reference in it, so its zero size bounds the parts that the expansion makes (Lean
/// `Agg.firstRef`).
fn first_ref(a: &Agg, keys: &[usize]) -> Option<TyId> {
    let mut cur = a;
    for &k in keys {
        match cur {
            Agg::Ref(_, t) => return Some(*t),
            Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) | Agg::List(_, p) => {
                cur = p.0.get(k)?;
            }
            _ => return None,
        }
    }
    None
}

/// The change of the stored numbers of a node above a list that `push` or `pop` changes (Lean
/// `Agg.change`): `size` is the size of the element, and `depth` is the depth that the list can
/// reach. A pop of an element not deeper than the element type keeps each depth.
#[derive(Clone, Copy)]
pub(super) enum Delta {
    Grow { size: u64, depth: u64 },
    Shrink { size: u64 },
}

impl Delta {
    /// The refreshed numbers of the node `n`, which has `rest` steps to the end of the path.
    fn refresh(self, n: &mut Node, rest: u64) {
        n.size = match self {
            Delta::Grow { size, .. } => n.size.saturating_add(size),
            Delta::Shrink { size } => n.size.saturating_sub(size),
        };
        if let Delta::Grow { depth, .. } = self {
            n.depth = n.depth.max(rest.saturating_add(depth));
        }
    }
}

/// The list that a `push` or a `pop` changes: a static list, or the elements of a list node.
pub(super) enum ListMut<'a> {
    Static(&'a mut Vec<Value>),
    Node(&'a mut Vec<Agg>),
}

impl<'a> ListMut<'a> {
    /// The list that the static value `v` is, if it is one.
    fn of_value(v: &'a mut Value) -> Option<ListMut<'a>> {
        match v {
            Value::List(_, ys) => Some(ListMut::Static(ys)),
            _ => None,
        }
    }
}

/// The static part of `v` at the numbers `keys`, for a change in place.
fn part_in<'a>(v: &'a mut Value, keys: &[usize]) -> Option<&'a mut Value> {
    let mut cur = v;
    for &k in keys {
        cur = match cur {
            Value::Array(_, xs)
            | Value::Tuple(_, xs)
            | Value::Record(_, xs)
            | Value::List(_, xs) => xs.get_mut(k)?,
            _ => return None,
        };
    }
    Some(cur)
}
