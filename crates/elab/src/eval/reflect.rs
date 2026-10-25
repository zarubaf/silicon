// SPDX-License-Identifier: Apache-2.0
//! The builtin `@TypeOf(x)` of Lean `Source.Eval.Reflect` and `Eval.queryWalk` (design sections
//! 5.4, 6.2, and 9.3). The operand `x` is a place. The query gives the type of the part, and it
//! makes no hardware node and reads nothing.
//!
//! The walk goes once from the root outward. A step charges 1 at its node, and the key of an
//! index evaluates in a structural context of the kind `Query`. The checks of a step charge
//! nothing, so the walk keeps the evaluated steps (`pending`) and applies them in one pass along
//! the part (`settle_walk`), as a read does. A failed check comes before a charge or an error of a
//! later step, so `settle_walk` also runs before an error returns. Only a field of an `Instance`
//! handle changes the order of the charges: an index after it charges first (section 6.2,
//! **Selection order**). The walk therefore applies the pending steps before such a field, unless
//! the type of the part rules out an `Instance` handle (`Known`).
//!
//! A static value, a container node, and a handle keep their place in the store. A reference, a
//! hardware value, and a handle of a register, a wire, an own output, or a child input keep only
//! their data type, and every later step selects in the type.

use super::field::{At, InstInfo, Pick, base_error};
use super::place::{Index, Key, Named, Sel, chain, selector_text};
use super::record::FieldName;
use super::{Evaluator, GuardKind, Res, at, fail, need};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Handle, Kind as Resource, Port, Ref, Root, Seen, Val};
use crate::ops::Fuel;
use crate::types::{Ty, TyId, Types};
use crate::value::Value;
use parse::ast::{Builtin, Expr, Ident, Nat, Pos};
use resolve::{Kind, Target};

/// The part of a query operand after the steps so far.
enum Part {
    /// A part of a local or a constant in the store, and its declared type, if it has one.
    Held(Ref, Option<TyId>),
    /// A handle that the walk made or that the root is. It has no parts.
    Handle(Handle),
    /// Only a data type.
    Type(TyId),
}

/// What the walk knows of the part after its pending steps, to tell if it is an `Instance`
/// handle.
#[derive(Clone, Copy)]
enum Known {
    /// No `Instance` handle: a static value, a hardware value, another handle, or a type.
    Not,
    /// The type of a container or of a part of one.
    Ty(TyId),
    /// An `Instance` handle, after the pending steps ran.
    Inst(InstInfo),
    Unknown,
}

/// The walk of a query operand: the part after the steps that ran, and the steps that wait.
struct Walk<'a> {
    part: Part,
    pending: Vec<Key<'a>>,
    known: Known,
}

/// What a part of a query keeps when a step selects in its type only.
enum Only {
    Id(TyId),
    Hw(Ty),
}

/// How the walk ended, for the result of the query.
enum Ending {
    Ty(TyId),
    Handle(Handle),
    /// A literal that waits for its type has none.
    Pending,
}

/// The `S010` "Query without a type" of section 6.2 at `pos`, for the part `about`.
fn no_type<T>(pos: Pos, about: &str) -> Res<T> {
    fail(
        Code::S010,
        pos,
        format!(
            "`@TypeOf` takes a part with a type, not {about}; pass a value, a port, or a resource"
        ),
    )
}

impl Known {
    /// The knowledge about the part reached from a part that has `self`, by the step `key`.
    fn after(self, ev: &Evaluator<'_>, key: &Key<'_>) -> Known {
        match self {
            Known::Not => Known::Not,
            Known::Ty(t) => ev.key_ty(t, key).map_or(Known::Unknown, Known::Ty),
            Known::Inst(_) | Known::Unknown => Known::Unknown,
        }
    }
}

impl<'a> Walk<'a> {
    fn new(part: Part, known: Known) -> Walk<'a> {
        Walk {
            part,
            pending: Vec::new(),
            known,
        }
    }
}

impl Evaluator<'_> {
    /// The query `@TypeOf(x)` at `pos`: the node charged 1. The result is the type as a new value.
    pub(super) fn type_of_builtin(&mut self, pos: Pos, args: &[Expr]) -> Res<Option<super::Out>> {
        // The parser gives `@TypeOf` its one operand.
        let Some(operand) = args.first() else {
            return Ok(None);
        };
        let ty = self.type_of_part(pos, operand)?;
        Ok(Some(super::Out::Made(Val::Static(Value::Type(ty)))))
    }

    /// The type of the place `x` of `@TypeOf` at `pos`. The root resolves with no charge. Its
    /// steps then run once from the root outward (`query_walk`). A root that names no binding
    /// evaluates the whole operand as an expression (`query_whole`).
    fn type_of_part(&mut self, pos: Pos, operand: &Expr) -> Res<TyId> {
        let Some((
            Expr::Name {
                pos: rp,
                id,
                name: root,
            },
            steps,
        )) = chain(operand)
        else {
            return self.query_whole(pos, operand);
        };
        let Some(Target::Decl(decl)) = self.target(*id) else {
            return self.query_whole(pos, operand);
        };
        let start = match self.decl_ref(decl).kind {
            Kind::Family { .. } => {
                return self.query_family(pos, (*rp, root.as_str(), decl), &steps);
            }
            Kind::Const if self.items.contains_key(&decl) => {
                let super::Out::Ref(r) = self.constant(*rp, root, decl)? else {
                    return self.query_whole(pos, operand);
                };
                let declared = self.store.root_ty(&r.root);
                self.held(r, declared)
            }
            Kind::Const | Kind::Fn | Kind::Module | Kind::Struct | Kind::Enum => {
                return self.query_whole(pos, operand);
            }
            Kind::Alias if self.items.contains_key(&decl) => {
                return self.query_whole(pos, operand);
            }
            Kind::Domain => {
                self.keep_domain(decl, root);
                Walk::new(Part::Handle(Handle::Domain(decl)), Known::Not)
            }
            _ => {
                let Some(slot) = self.store.slot(decl) else {
                    let out = self.name(*rp, *id, root)?;
                    return self.query_out(pos, &out);
                };
                let declared = self.declared_ty(decl, slot);
                let r = Ref {
                    root: Root::Local(self.store.frame_index(), decl),
                    path: Vec::new(),
                };
                self.held(r, declared)
            }
        };
        let mut walk = self.query_walk(start, &steps)?;
        self.settle_walk(&mut walk)?;
        self.query_ty(pos, walk.part)
    }

    /// The type that the slot of the local `decl` declares: the annotation of a `let`, the type
    /// of a parameter or of a port, else none. The handle of a register or a wire gives its
    /// handle type from the value.
    fn declared_ty(&self, decl: resolve::DeclId, slot: &super::Slot) -> Option<TyId> {
        if self.untyped.contains(&decl)
            || matches!(
                &slot.value,
                Val::Handle(Handle::Res {
                    kind: Resource::Reg | Resource::Wire,
                    ..
                })
            )
        {
            return None;
        }
        slot.ty
    }

    /// The walk that starts at the part `r` with the declared type `declared`.
    fn held(&self, r: Ref, declared: Option<TyId>) -> Walk<'static> {
        let known = Self::known_of(self.store.at(&r));
        Walk::new(Part::Held(r, declared), known)
    }

    /// The root that names no binding: the whole operand evaluates as an ordinary expression in
    /// a structural context of the kind `Query`. It has no declared type.
    fn query_whole(&mut self, pos: Pos, x: &Expr) -> Res<TyId> {
        let o = self.guarded(GuardKind::Query(Builtin::TypeOf), |ev| {
            let o = ev.eval(x)?;
            need(x, o)
        })?;
        self.query_out(pos, &o)
    }

    /// The type of the result `o` of a root that names no binding.
    fn query_out(&mut self, pos: Pos, o: &super::Out) -> Res<TyId> {
        let ending = Self::ending(
            &self.graph,
            &mut self.tys,
            &mut self.fuel,
            pos,
            self.store.seen(o),
        )?;
        self.ended(pos, ending)
    }

    /// The query of an entry `req[k]` of the own family `x` with the binder `family`, at `pos`
    /// (section 6.2). The index node charged 1 at `q`, the name node at `rp` charges 1, and the
    /// key evaluates in a structural context of the kind `Query`. A family without a key is
    /// "Family as a value".
    fn query_family(
        &mut self,
        pos: Pos,
        (rp, family_name, family): (Pos, &str, resolve::DeclId),
        steps: &[Sel<'_>],
    ) -> Res<TyId> {
        let Some(&Sel::Index(index_pos, keys)) = steps.first() else {
            return super::family_value(rp, family_name);
        };
        self.charge(index_pos, 1)?;
        let [key] = keys else {
            return fail(
                Code::S010,
                index_pos,
                "an index of a value has one argument".to_owned(),
            );
        };
        self.charge(rp, 1)?;
        let out = self.guarded(GuardKind::Query(Builtin::TypeOf), |ev| {
            let out = ev.eval(key)?;
            need(key, out)
        })?;
        let number = self.selection_key(rp, key.pos(), family_name, &out)?;
        let entry = self.entry_val(key.pos(), family_name, family, number)?;
        let start = self.part_of_val(pos, entry)?;
        let mut walk = self.query_walk(start, steps.get(1..).unwrap_or_default())?;
        self.settle_walk(&mut walk)?;
        self.query_ty(pos, walk.part)
    }

    /// The walk that starts at the value `entry` of an entry of a family. A hardware value and a
    /// reference keep only their type.
    fn part_of_val(&mut self, pos: Pos, entry: Val) -> Res<Walk<'static>> {
        let part = match entry {
            Val::Hw(h) => Part::Type(self.tys.mk(self.graph.ty(h))),
            Val::Agg(a) => match *a {
                Agg::Ref(_, t) => Part::Type(t),
                node => return no_type(pos, &self.about(Seen::Agg(&node))),
            },
            Val::Handle(h) => Part::Handle(h),
            other => return no_type(pos, &self.about(other.seen())),
        };
        Ok(Walk::new(part, Known::Not))
    }

    /// What a part that the store holds now tells about an `Instance` handle. It is exact.
    fn known_of(seen: Seen<'_>) -> Known {
        match seen {
            Seen::Handle(Handle::Inst { id, path, inst, ty }) => Known::Inst(InstInfo {
                id: *id,
                path: *path,
                inst: *inst,
                ty: *ty,
            }),
            Seen::Agg(a) => a.stored_ty().map_or(Known::Unknown, Known::Ty),
            _ => Known::Not,
        }
    }

    /// Whether the part with `known` can be an `Instance` handle.
    fn maybe_instance(&self, known: Known) -> bool {
        match known {
            Known::Not => false,
            Known::Ty(t) => matches!(self.tys.get(t), Ty::Instance(_)),
            Known::Inst(_) | Known::Unknown => true,
        }
    }

    /// The steps `steps` of a `@TypeOf` operand from the part of `w`, once from the root outward
    /// (section 6.2, **`@TypeOf` order**). A step charges 1 at its node, then the key of an index
    /// evaluates, and the step waits for the pass of `settle_walk`. An error first applies the steps
    /// that wait, so a failed check wins over a later error.
    fn query_walk<'a>(&mut self, mut walk: Walk<'a>, steps: &[Sel<'a>]) -> Res<Walk<'a>> {
        let mut at = 0;
        while at < steps.len() {
            if let Err(err) = self.query_step(&mut walk, steps, &mut at) {
                self.settle_walk(&mut walk)?;
                return Err(err);
            }
        }
        Ok(walk)
    }

    /// The step `steps[*at]`, and the step after it when both make one selection. `at` moves
    /// past the steps taken.
    fn query_step<'a>(
        &mut self,
        walk: &mut Walk<'a>,
        steps: &[Sel<'a>],
        at: &mut usize,
    ) -> Res<()> {
        let Some(&step) = steps.get(*at) else {
            return Ok(());
        };
        match step {
            Sel::Index(pos, args) => {
                self.charge(pos, 1)?;
                let [key] = args else {
                    return fail(
                        Code::S010,
                        pos,
                        "an index of a value has one argument".to_owned(),
                    );
                };
                let index = self.query_key(key)?;
                self.wait(walk, Key::Index(pos, key.pos(), index));
                *at += 1;
            }
            Sel::Select(pos, lit, number) => {
                self.charge(pos, 1)?;
                self.wait(walk, Key::Select(pos, lit, number));
                *at += 1;
            }
            Sel::Key(pos, base, key) => {
                self.charge(pos, 1)?;
                let key = self.named_key(pos, base, key, true)?;
                // The part is known after the step only when its name is paid: the look-up of a
                // name reads it after its charge. A later `.f` then tells from the type that the
                // part is no `Instance` handle, and the pass along the part does not run again.
                let before = walk.known;
                walk.pending.push(key);
                *at += 1;
                self.pay_waiting(walk)?;
                if let Some(key) = walk.pending.last() {
                    walk.known = before.after(self, key);
                }
            }
            Sel::Field(pos, field) => {
                let Some(info) = self.instance_of(walk)? else {
                    self.charge(pos, 1)?;
                    self.wait(walk, Key::Field(pos, field));
                    *at += 1;
                    return Ok(());
                };
                if let Some(&Sel::Index(index_pos, args)) = steps.get(*at + 1) {
                    self.instance_pair(walk, info, (pos, field), (index_pos, args))?;
                    *at += 2;
                } else {
                    self.charge(pos, 1)?;
                    let port = self.port_find(pos, info, field)?;
                    *walk = Self::port_walk(info, port);
                    *at += 1;
                }
            }
        }
        Ok(())
    }

    /// The step `key` waits at the part of `walk`.
    fn wait<'a>(&self, walk: &mut Walk<'a>, key: Key<'a>) {
        walk.known = walk.known.after(self, &key);
        walk.pending.push(key);
    }

    /// The `Instance` handle that the part of `walk` is, if it is one. A part whose type rules it
    /// out answers at once. Else the pending steps run first.
    fn instance_of(&mut self, walk: &mut Walk<'_>) -> Res<Option<InstInfo>> {
        match walk.known {
            Known::Inst(info) if walk.pending.is_empty() => return Ok(Some(info)),
            known if !self.maybe_instance(known) => return Ok(None),
            _ => {}
        }
        self.settle_walk(walk)?;
        Ok(match walk.known {
            Known::Inst(info) => Some(info),
            _ => None,
        })
    }

    /// The selection `u.f[k]` of an `Instance` handle: the index node at `index_pos` charges 1
    /// before the field node at `pos`. A field that names a family of the child takes the index
    /// as its key, which evaluates in a structural context of the kind `Query` and gets the
    /// checks of a selection key (`selection_key`). Another field selects its port, and the index
    /// then takes its key as a step of the part.
    fn instance_pair<'a>(
        &mut self,
        walk: &mut Walk<'a>,
        info: InstInfo,
        (pos, field): (Pos, &'a Ident),
        (index_pos, args): (Pos, &'a [Expr]),
    ) -> Res<()> {
        self.charge(index_pos, 1)?;
        let [key] = args else {
            return fail(
                Code::S010,
                index_pos,
                "an index of a value has one argument".to_owned(),
            );
        };
        self.charge(pos, 1)?;
        let family = self
            .port_sym(field)
            .filter(|sym| self.has_family(info.inst, *sym));
        if let Some(sym) = family {
            let out = self.guarded(GuardKind::Query(Builtin::TypeOf), |ev| {
                let out = ev.eval(key)?;
                need(key, out)
            })?;
            let number = self.selection_key(pos, key.pos(), &field.name, &out)?;
            let Some(port) = self.elab.port(info.inst, (sym, Some(number))) else {
                let child = self.tys.text(info.ty);
                return super::inst::child_key(key.pos(), &child, &field.name, number);
            };
            *walk = Self::port_walk(info, port);
        } else {
            let port = self.port_find(pos, info, field)?;
            *walk = Self::port_walk(info, port);
            let index = self.query_key(key)?;
            self.wait(walk, Key::Index(index_pos, key.pos(), index));
        }
        Ok(())
    }

    /// The scalar port of the child `info` with the field `field` at `pos`. A family of the child
    /// without a key is "Family as a value", and a name that the child does not declare is "No
    /// public port".
    fn port_find(&self, pos: Pos, info: InstInfo, field: &Ident) -> Res<Port> {
        self.port_named(
            pos,
            (info.inst, info.ty),
            (self.port_sym(field), &field.name),
            None,
        )
    }

    /// The walk from a port of a child: an input gives its handle, and an output its type, with
    /// no read.
    fn port_walk(child: InstInfo, port: Port) -> Walk<'static> {
        let start = if port.input {
            Part::Handle(Handle::Input {
                inst: child.id,
                path: child.path,
                port,
            })
        } else {
            Part::Type(port.ty)
        };
        Walk::new(start, Known::Not)
    }

    /// The key `key` of an index step of a `@TypeOf` operand (section 6.2, **`@TypeOf` order**).
    /// It evaluates in a structural context of the kind `Query` (`S016`). Then it is static
    /// (`S011`): a handle gives "Handle at a static position", and another hardware value gives
    /// "Value not static".
    fn query_key(&mut self, key: &Expr) -> Res<Index> {
        let out = self.guarded(GuardKind::Query(Builtin::TypeOf), |ev| {
            let out = ev.eval(key)?;
            need(key, out)
        })?;
        self.static_position(key.pos(), "a key of `@TypeOf`", &out)?;
        self.check_static(key.pos(), &out)?;
        Ok(self.index_of(&out))
    }

    /// Applies the pending steps of `walk` to its part, in one pass along the part. A part that
    /// keeps only its type selects in the type from there. The answer about an `Instance` handle
    /// is exact afterwards. An `@field` step that selects a port of a child ends the pass at its
    /// part, and the pass goes on at the port with the steps after it.
    fn settle_walk(&mut self, walk: &mut Walk<'_>) -> Res<()> {
        let pending = std::mem::take(&mut walk.pending);
        let mut from = 0;
        while let Some(next) = self.settle_from(walk, &pending, from)? {
            from = next;
        }
        Ok(())
    }

    /// The pass of `settle_walk` over the steps of `pending` from the step `from`. The result is
    /// the step after a port switch of an `@field`, else `None`.
    fn settle_from(
        &mut self,
        walk: &mut Walk<'_>,
        pending: &[Key<'_>],
        from: usize,
    ) -> Res<Option<usize>> {
        let keys = pending.get(from..).unwrap_or_default();
        let ty = match &mut walk.part {
            Part::Type(ty) => *ty,
            Part::Handle(handle) => {
                let Some(key) = keys.first() else {
                    walk.known = Self::known_of(Seen::Handle(handle));
                    return Ok(None);
                };
                let Some(only) = Self::only_of(&self.graph, Seen::Handle(handle)) else {
                    if let Key::Named(n) = key {
                        let stepped = self.named_on_handle(n, handle)?;
                        *walk = Self::port_walk(stepped.0, stepped.1);
                        return Ok(Some(from + 1));
                    }
                    self.step_value(key, Seen::Handle(handle))?;
                    return no_type(
                        super::place::key_pos(key),
                        &self.about(Seen::Handle(handle)),
                    );
                };
                self.only_id(only)
            }
            Part::Held(r, declared) => {
                let mut seen = self.store.at(r);
                let mut done = 0;
                let mut only = None;
                let mut switch = None;
                for key in keys {
                    only = Self::only_of(&self.graph, seen);
                    if only.is_some() {
                        break;
                    }
                    #[cfg(test)]
                    crate::counters::add(crate::counters::Count::Queried, 1);
                    let (number, field) = if let Key::Named(n) = key {
                        let at = At::Seen(seen);
                        let plan = self.named_plan(n, at, self.store.value(&n.key))?;
                        if !n.paid
                            && let Some(name) = plan.name()
                        {
                            Self::pay_name(&mut self.fuel, n.kp, name)?;
                        }
                        match self.named_finish(n, seen, &plan)? {
                            Pick::Field(number, ft, _) => (number, Some(ft)),
                            Pick::Index(i) => self.step_value(&Key::Index(n.pos, n.kp, i), seen)?,
                            Pick::Port(info, port) => {
                                switch = Some((info, port));
                                done += 1;
                                break;
                            }
                        }
                    } else {
                        self.step_value(key, seen)?
                    };
                    *declared = field.or_else(|| match declared {
                        Some(ty) => self.tys.part(*ty, number),
                        None => self.stored_part(seen, number),
                    });
                    r.path.push(number);
                    seen = self.store.step(seen, number);
                    done += 1;
                }
                if let Some((info, port)) = switch {
                    *walk = Self::port_walk(info, port);
                    return Ok(Some(from + done));
                }
                let Some(only) = only else {
                    walk.known = Self::known_of(seen);
                    return Ok(None);
                };
                let ty = self.only_id(only);
                self.settle_type(walk, ty, keys.get(done..).unwrap_or_default())?;
                return Ok(None);
            }
        };
        self.settle_type(walk, ty, keys)?;
        Ok(None)
    }

    /// The part of `walk` is the type `ty`, and the steps `keys` select in it.
    fn settle_type(&mut self, walk: &mut Walk<'_>, mut ty: TyId, keys: &[Key<'_>]) -> Res<()> {
        for key in keys {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Queried, 1);
            ty = match key {
                Key::Named(n) => self.named_ty(n, ty)?,
                key => self.ty_step(ty, key)?,
            };
        }
        walk.part = Part::Type(ty);
        walk.known = Known::Not;
        Ok(())
    }

    /// The id of the type of a part that keeps only its type.
    fn only_id(&mut self, only: Only) -> TyId {
        match only {
            Only::Id(t) => t,
            Only::Hw(ty) => self.tys.mk(ty),
        }
    }

    /// The data type of a part that a step selects in as a type (`Val.typeOnly?`): a hardware
    /// value, a reference, and a handle of a register, a wire, an own output, or a child input.
    fn only_of(graph: &crate::hw::Graph, seen: Seen<'_>) -> Option<Only> {
        match seen {
            Seen::Hw(h) => Some(Only::Hw(graph.ty(h))),
            Seen::Agg(Agg::Ref(_, t)) => Some(Only::Id(*t)),
            Seen::Handle(Handle::Res { ty, .. }) => Some(Only::Id(*ty)),
            Seen::Handle(Handle::Input { port, .. }) => Some(Only::Id(port.ty)),
            _ => None,
        }
    }

    /// The type that the container `seen` stores for its part `k`, with no walk. A static tuple
    /// stores none.
    fn stored_part(&self, seen: Seen<'_>, k: usize) -> Option<TyId> {
        match seen {
            Seen::Static(Value::Array(e, _) | Value::List(e, _)) => Some(*e),
            Seen::Agg(a) => a.stored_ty().and_then(|t| self.tys.part(t, k)),
            _ => None,
        }
    }

    /// The step `key` on the part `seen` that holds its parts (section 9.3). The result is the
    /// number of the part and the field type of a field. A static value selects with no charge,
    /// and another value fails there, for example a memory. An index of a string is "String index
    /// in a query", because the walk selects in types and a `String` has no element type.
    fn step_value(&self, key: &Key<'_>, seen: Seen<'_>) -> Res<(usize, Option<TyId>)> {
        match key {
            Key::Index(pos, _, _) if matches!(seen, Seen::Static(Value::Str(_))) => fail(
                Code::S010,
                *pos,
                "a query cannot index a string; an index of a string has the type `String`, so \
                 write `String` instead of the query"
                    .to_owned(),
            ),
            Key::Field(pos, field) => {
                self.no_enum_field(*pos, &field.name, seen)?;
                let (found, record) = match seen {
                    Seen::Static(Value::Record(ty, _)) => {
                        (self.struct_field(*ty, field), Some(*ty))
                    }
                    Seen::Agg(agg) => (self.agg_field_at(agg, field), self.record_ty(agg)),
                    _ => (None, None),
                };
                if let Some((number, field_ty)) = found {
                    return Ok((number, Some(field_ty)));
                }
                self.missing_field(*pos, self.field_name(field), record, seen)
            }
            key => self.step_at(key, seen),
        }
    }

    /// The number and the type of the field `field` of the struct type `ty`.
    fn struct_field(&self, ty: TyId, field: &Ident) -> Option<(usize, TyId)> {
        self.struct_field_by(ty, self.field_name(field))
    }

    /// The number and the type of the field `f` of the struct type `ty`. A name from a key
    /// without a symbol is no field of the file, so it needs no search by name.
    fn struct_field_by(&self, ty: TyId, f: FieldName<'_>) -> Option<(usize, TyId)> {
        if f.keyed && f.sym.is_none() {
            return None;
        }
        let parts = self.tys.parts(ty)?;
        let number = self.field_number_by(parts.item()?, f.sym, f.name)?;
        Some((number, parts.types.get(number).copied()?))
    }

    /// The step `key` on a part of the data type `ty` (section 9.3). A field selects the field
    /// type of a struct, a selector the element type of a tuple, and an index the element type of
    /// an array or a tuple, with the range of the type. The text of an error names the part as a
    /// reference of `ty` does.
    fn ty_step(&self, ty: TyId, key: &Key<'_>) -> Res<TyId> {
        match key {
            Key::Field(pos, field) => self.field_ty(ty, *pos, field),
            Key::Select(pos, lit, number) => self.select_ty(ty, (*pos, *lit), number),
            // The step of an `@field` has its own walk (`named_ty`).
            Key::Named(n) => Self::named_placeholder(n.pos),
            Key::Index(pos, key_pos, index) => {
                let part = match self.tys.get(ty) {
                    Ty::Array(elem, count) => {
                        Self::within(*key_pos, count.to_u64().unwrap_or(u64::MAX), index)?;
                        Some(*elem)
                    }
                    Ty::Tuple(parts) => {
                        let at = Self::within(*key_pos, parts.len() as u64, index)?;
                        parts.get(at).copied()
                    }
                    _ => None,
                };
                part.map_or_else(
                    || {
                        fail(
                            Code::S010,
                            *pos,
                            format!(
                                "an index needs an array, a list, or a tuple, not {}",
                                self.query_part_text(ty)
                            ),
                        )
                    },
                    Ok,
                )
            }
        }
    }

    /// The field `field` at `pos` of a part of the data type `ty`.
    fn field_ty(&self, ty: TyId, pos: Pos, field: &Ident) -> Res<TyId> {
        self.field_ty_by(ty, pos, self.field_name(field))
    }

    /// The field `f` at `pos` of a part of the data type `ty`.
    fn field_ty_by(&self, ty: TyId, pos: Pos, f: FieldName<'_>) -> Res<TyId> {
        match self.tys.get(ty) {
            Ty::Enum(_) => self.enum_field_error(pos, &f.shown(), ty),
            Ty::Struct(_) => match self.struct_field_by(ty, f) {
                Some((_, field_ty)) => Ok(field_ty),
                None => super::record::no_field(pos, &self.tys.text(ty), &f.shown()),
            },
            _ => fail(
                Code::S010,
                pos,
                format!("{} has no field `{}`", self.query_part_text(ty), f.shown()),
            ),
        }
    }

    /// The `@field` step `n` of a query operand on the part of the data type `ty` (Lean
    /// `queryField`). The checks of its key charge the size of a name that the step did not pay
    /// yet, and the selection is the step of a field or an index in the type.
    fn named_ty(&mut self, n: &Named<'_>, ty: TyId) -> Res<TyId> {
        let key = self.store.value(&n.key);
        let plan = self.named_plan(n, At::Ty(ty), key)?;
        if !n.paid
            && let Some(name) = plan.name()
        {
            Self::pay_name(&mut self.fuel, n.kp, name)?;
        }
        match plan {
            super::field::Plan::Name(name) => {
                let f = FieldName {
                    sym: self.syms.find(name),
                    name,
                    keyed: true,
                };
                self.field_ty_by(ty, n.kp, f)
            }
            super::field::Plan::Index => {
                self.ty_step(ty, &Key::Index(n.pos, n.kp, self.index_of(&n.key)))
            }
            // A data type is no `Instance` handle.
            super::field::Plan::Port(..) => {
                base_error(n.base.pos(), &format!("a value of `{}`", self.tys.text(ty)))
            }
        }
    }

    /// The `@field` step `n` on the handle `handle` that keeps its value in the query: an
    /// `Instance` handle selects the port of its child.
    fn named_on_handle(&mut self, n: &Named<'_>, handle: &Handle) -> Res<(InstInfo, Port)> {
        let seen = Seen::Handle(handle);
        let key = self.store.value(&n.key);
        let plan = self.named_plan(n, At::Seen(seen), key)?;
        if !n.paid
            && let Some(name) = plan.name()
        {
            Self::pay_name(&mut self.fuel, n.kp, name)?;
        }
        match self.named_finish(n, seen, &plan)? {
            Pick::Port(info, port) => Ok((info, port)),
            // Only an `Instance` handle is a base of `@field`, and it selects a port.
            _ => base_error(n.base.pos(), &self.about(seen)),
        }
    }

    /// Pays the size of the name of the key that the walk just made wait. A query pays it at its
    /// step, as Lean charges it at its step, and the pass checks the kind of the key later. An
    /// error of that check wins over a failed payment, because the walk applies the steps that
    /// wait before it returns an error.
    fn pay_waiting(&mut self, walk: &mut Walk<'_>) -> Res<()> {
        let Some(Key::Named(n)) = walk.pending.last_mut() else {
            return Ok(());
        };
        if let Some(name) = self.key_name(self.store.value(&n.key)) {
            Self::pay_name(&mut self.fuel, n.kp, name)?;
            n.paid = true;
        }
        Ok(())
    }

    /// The selector `.number` at `pos`, with its literal at `lit`, of a part of the data type
    /// `ty`.
    fn select_ty(&self, ty: TyId, (pos, lit): (Pos, Pos), number: &Nat) -> Res<TyId> {
        match self.tys.get(ty) {
            Ty::Enum(_) => self.enum_field_error(pos, &selector_text(number), ty),
            Ty::Tuple(parts) => {
                match number
                    .as_str()
                    .parse::<usize>()
                    .ok()
                    .and_then(|at| parts.get(at))
                {
                    Some(part) => Ok(*part),
                    None => fail(
                        Code::S013,
                        lit,
                        format!(
                            "the selector {} is out of range for {}",
                            selector_text(number),
                            self.query_part_text(ty)
                        ),
                    ),
                }
            }
            _ => fail(
                Code::S010,
                pos,
                format!(
                    "the selector `.{}` needs a tuple, not {}",
                    selector_text(number),
                    self.query_part_text(ty)
                ),
            ),
        }
    }

    /// The text of a part of the data type `ty` in a message: the type, or hardware of the type
    /// if it has a hardware leaf.
    fn query_part_text(&self, ty: TyId) -> String {
        if self.tys.meta(ty).leaves.is_zero() {
            self.tys.text(ty)
        } else {
            format!("hardware {}", self.tys.text(ty))
        }
    }

    /// The type of the part at the end of the walk (section 9.3). A declared type is the result.
    /// A part in the store gives its type (`ending`).
    fn query_ty(&mut self, pos: Pos, part: Part) -> Res<TyId> {
        let ending = match part {
            Part::Type(t) | Part::Held(_, Some(t)) => return Ok(t),
            Part::Held(r, None) => Self::ending(
                &self.graph,
                &mut self.tys,
                &mut self.fuel,
                pos,
                self.store.at(&r),
            )?,
            Part::Handle(h) => Ending::Handle(h),
        };
        self.ended(pos, ending)
    }

    /// The type of the end of the walk. A handle gives its handle type, except an own output,
    /// which gives its data type. A domain has no type.
    fn ended(&mut self, pos: Pos, ending: Ending) -> Res<TyId> {
        match ending {
            Ending::Ty(t) => Ok(t),
            Ending::Pending => no_type(pos, "`[]`"),
            Ending::Handle(h) => match &h {
                Handle::Res {
                    kind: Resource::Output,
                    ty,
                    ..
                } => Ok(*ty),
                h => match self.handle_ty(h) {
                    Some(t) => Ok(t),
                    None => no_type(pos, &self.about(Seen::Handle(h))),
                },
            },
        }
    }

    /// The end of the walk at the part `seen` without a declared type. A static tuple stores no
    /// type, so the walk builds it (`built_ty`). Another part refers to its type.
    fn ending(
        g: &crate::hw::Graph,
        tys: &mut Types,
        fuel: &mut Fuel,
        pos: Pos,
        seen: Seen<'_>,
    ) -> Res<Ending> {
        Ok(match seen {
            Seen::Static(v @ Value::Tuple(..)) => Ending::Ty(Self::built_ty(tys, fuel, pos, v)?),
            Seen::Static(v) => Ending::Ty(v.ty(tys)),
            Seen::Hw(h) => Ending::Ty(tys.mk(g.ty(h))),
            Seen::Agg(a) => Ending::Ty(a.ty(g, tys)),
            Seen::Handle(h) => Ending::Handle(h.clone()),
            Seen::Pending(..) => Ending::Pending,
        })
    }

    /// The type of the static tuple `v` at the node `pos` of `@TypeOf` (section 5.4). A tuple
    /// stores no type. Each tuple node charges 1 before the walk visits its elements, then the
    /// size of the type term charges. Only then the result exists. The walk keeps its own stack.
    fn built_ty(tys: &mut Types, fuel: &mut Fuel, pos: Pos, v: &Value) -> Res<TyId> {
        enum Step<'v> {
            Visit(&'v Value),
            Join(usize),
        }
        let mut work = vec![Step::Visit(v)];
        let mut done: Vec<TyId> = Vec::new();
        while let Some(step) = work.pop() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Queried, 1);
            match step {
                Step::Visit(Value::Tuple(_, xs)) => {
                    fuel.pay(1).map_err(at(pos))?;
                    work.push(Step::Join(xs.len()));
                    work.extend(xs.iter().rev().map(Step::Visit));
                }
                Step::Visit(x) => done.push(x.ty(tys)),
                Step::Join(n) => {
                    let parts = done.split_off(done.len().saturating_sub(n));
                    done.push(tys.tuple(parts));
                }
            }
        }
        let t = done.pop().unwrap_or_else(|| tys.mk(Ty::Unit));
        fuel.pay(u128::from(t.size())).map_err(at(pos))?;
        Ok(t)
    }
}
