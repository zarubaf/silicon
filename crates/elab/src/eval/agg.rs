// SPDX-License-Identifier: Apache-2.0
//! The normal form of a hardware aggregate, as Lean `Eval.normalize` gives it (design section
//! 5.1).

// TODO(#181): remove this allowance when the evaluator reads aggregates.
#![allow(dead_code)]

use super::place::Index;
use super::{Code, Evaluator, Names, Out, Res, at, fail};
use crate::agg::Agg;
use crate::hw::{Seen, Val};
use crate::int::Int;
use crate::names::{Step, Sym};
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Ident, Nat, Pos};

impl Evaluator<'_> {
    /// The normal form of the aggregate `a` at `pos`. A reference without a hardware leaf is a
    /// static value, for example a part of the type `[Unit; 4]`. It charges the zero size of its
    /// type from the metadata before the zero exists (section 5.4), so a huge empty part fails
    /// before any work. A reference of a scalar type is a hardware value. Another reference
    /// stays lazy: it neither expands nor charges.
    pub(super) fn normalize(&mut self, pos: Pos, a: Agg) -> Res<Val> {
        match a {
            Agg::Static(v) => Ok(Val::Static(v)),
            Agg::Hw(h) => Ok(Val::Hw(h)),
            Agg::Ref(base, t) => {
                if self.tys.meta(t).leaves.is_zero() {
                    self.fuel
                        .pay_int(&self.tys.meta(t).zero_size)
                        .map_err(at(pos))?;
                    match self.tys.zero(t) {
                        Some(v) => Ok(Val::Static(v)),
                        None => fail(Code::S010, pos, format!("{} has no zero", self.tys.text(t))),
                    }
                } else if matches!(self.tys.get(t), Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) {
                    let ty = self.tys.get(t).clone();
                    Ok(Val::Hw(self.graph.mk(pos, ty, base.op(), Vec::new())))
                } else {
                    Ok(Val::Agg(Box::new(Agg::Ref(base, t))))
                }
            }
            a => Ok(Val::Agg(Box::new(a))),
        }
    }

    /// The aggregate that the result `b` is. Only a result that is an aggregate comes here, and
    /// a reference into a stored aggregate does not exist before a local can hold one.
    fn agg_of(&self, pos: Pos, b: Out) -> Res<Agg> {
        match self.store.take(b) {
            Val::Agg(a) => Ok(*a),
            _ => fail(
                Code::S010,
                pos,
                "a hardware aggregate is expected".to_owned(),
            ),
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

    /// The part `k` of the aggregate `a` at `pos`. A container node gives its part in its
    /// normal form, and moves it out: the aggregate is a new value. A reference gives a
    /// reference to the part of type `ft`, with the leaf field `step`, in constant work. A part
    /// of a reference without a hardware leaf charges its zero size from the metadata first
    /// (`normalize`).
    fn agg_part(&mut self, pos: Pos, a: Agg, k: usize, step: Step, ft: Option<TyId>) -> Res<Out> {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Selected, 1);
        match a {
            Agg::Array(_, mut p) | Agg::Tuple(_, mut p) | Agg::Record(_, mut p) => {
                let part =
                    p.0.get_mut(k)
                        .map(|x| std::mem::replace(x, Agg::Static(Value::Unit)));
                let Some(part) = part else {
                    return fail(Code::S010, pos, "the part does not exist".to_owned());
                };
                Ok(Out::Named(self.normalize(pos, part)?))
            }
            Agg::Ref(base, _) => {
                let Some(ft) = ft else {
                    return fail(Code::S010, pos, "the part has no type".to_owned());
                };
                let sub = base.sub(&mut self.paths, &self.syms.texts, step);
                let v = self.normalize(pos, Agg::Ref(sub, ft))?;
                Ok(Self::part_out(true, v))
            }
            Agg::Static(_) | Agg::Hw(_) => fail(Code::S010, pos, "a leaf has no part".to_owned()),
        }
    }

    /// The number of the element that the static index `index` at `ipos` picks from `len`
    /// elements. The index is a `usize` or beyond it, so a wide index is out of range.
    fn within(ipos: Pos, len: u64, index: &Index) -> Res<usize> {
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

    /// The index `index` at `ipos` of the aggregate `out`, a result of the index at `pos`. A
    /// reference to an array or a tuple gives a reference to the element `<k>e`, and its type
    /// gives the length, so a huge array takes no more work.
    pub(super) fn agg_index(&mut self, pos: Pos, ipos: Pos, out: Out, index: &Index) -> Res<Out> {
        let agg = self.agg_of(pos, out)?;
        let len = match &agg {
            Agg::Array(_, parts) | Agg::Tuple(_, parts) => Some(parts.0.len() as u64),
            Agg::Ref(_, ty) => match self.tys.get(*ty) {
                Ty::Array(_, count) => Some(count.to_u64().unwrap_or(u64::MAX)),
                Ty::Tuple(parts) => Some(parts.len() as u64),
                _ => None,
            },
            _ => None,
        };
        let Some(len) = len else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "an index needs an array, a list, or a tuple, not {}",
                    self.text(Seen::Agg(&agg))
                ),
            );
        };
        let num = Self::within(ipos, len, index)?;
        let part_ty = match &agg {
            Agg::Ref(_, ty) => self.tys.part(*ty, num),
            _ => None,
        };
        self.agg_part(pos, agg, num, Step::Elem(num as u64), part_ty)
    }

    /// The selector `.index` with its literal at `lit` of the aggregate `out`, a result of the
    /// selector at `pos`. Only a tuple has one.
    pub(super) fn agg_select(&mut self, pos: Pos, lit: Pos, index: &Nat, out: Out) -> Res<Out> {
        let agg = self.agg_of(pos, out)?;
        let len = match &agg {
            Agg::Tuple(_, parts) => Some(parts.0.len()),
            Agg::Ref(_, ty) => match self.tys.get(*ty) {
                Ty::Tuple(parts) => Some(parts.len()),
                _ => None,
            },
            _ => None,
        };
        let Some(len) = len else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "the selector `.{}` needs a tuple, not {}",
                    index.as_str(),
                    self.text(Seen::Agg(&agg))
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
                        self.text(Seen::Agg(&agg))
                    ),
                );
            }
        };
        let part_ty = match &agg {
            Agg::Ref(_, ty) => self.tys.part(*ty, num),
            _ => None,
        };
        self.agg_part(pos, agg, num, Step::Elem(num as u64), part_ty)
    }

    /// The symbol of the field name `f`. The top expression has no symbols for its fields, so a
    /// search by name finds it, as `field_number` does.
    fn field_sym(&self, f: &Ident) -> Option<Sym> {
        match self.names {
            Names::File => self.syms.fields.get(&f.id).copied(),
            Names::Top => self.syms.texts.iter().position(|t| *t == f.name),
        }
    }

    /// The field `f` of the aggregate `b`, a result of the field at `pos`. A reference to a
    /// record gives a reference to the part with the leaf field `f`. The record type holds the
    /// number of its specialization, and the symbol of `f` finds the number of the field, so
    /// the selection compares no name.
    pub(super) fn agg_field(&mut self, pos: Pos, f: &Ident, b: Out) -> Res<Out> {
        let a = self.agg_of(pos, b)?;
        let record = match &a {
            Agg::Record(n, _) => Some(n.ty),
            Agg::Ref(_, t) if matches!(self.tys.get(*t), Ty::Struct(_)) => Some(*t),
            _ => None,
        };
        let found = record.and_then(|t| {
            let (item, fts) = self.tys.fields(t)?;
            let k = self.field_number(item, f)?;
            Some((k, fts.get(k).copied()?))
        });
        let Some((k, ft)) = found else {
            return fail(
                Code::S010,
                pos,
                format!("{} has no field `{}`", self.text(Seen::Agg(&a)), f.name),
            );
        };
        let step = match &a {
            Agg::Ref(..) => match self.field_sym(f) {
                Some(sym) => Step::User(sym),
                None => {
                    return fail(
                        Code::S010,
                        pos,
                        format!("the field `{}` has no symbol", f.name),
                    );
                }
            },
            _ => Step::Elem(0),
        };
        self.agg_part(pos, a, k, step, Some(ft))
    }

    /// `len` of the aggregate `o` at the call `pos`. A node of an array holds its parts, and a
    /// reference to an array reads its type, so a huge array charges nothing.
    pub(super) fn agg_len(&mut self, pos: Pos, o: Out) -> Res<Option<Out>> {
        let a = self.agg_of(pos, o)?;
        let n = match &a {
            Agg::Array(_, p) => Some(Int::from_u64(p.0.len() as u64)),
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
                    self.text(Seen::Agg(&a))
                ),
            ),
        }
    }
}
