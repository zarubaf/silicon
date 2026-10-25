// SPDX-License-Identifier: Apache-2.0
//! The typed use of Lean `Eval.typedUse` (design section 5.4). One function, `typed_use`,
//! charges the copy and then gives the value its typed use by the kind of its position. The
//! kind is a `Site`, and its `Used` is the form that the caller stores, as the index of the Lean
//! `Site` is. A caller that pays its copy before passes `copies: false`.

use super::container::Piece;
use super::list::Typed;
use super::{Evaluator, Opnd, Out, Res, at, fail, no_type};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Seen, Val};
use crate::ops;
use crate::types::TyId;
use crate::value::Value;
use parse::ast::Pos;

/// The position of a typed use, and the form of its result.
pub(super) trait Site {
    type Used;

    /// The typed use of `out` at `t` at `pos`, after its copy charged.
    fn site_use(
        self,
        ev: &mut Evaluator<'_>,
        pos: Pos,
        t: TyId,
        copies: bool,
        out: Out,
    ) -> Res<Self::Used>;
}

/// The whole value of a typed `let`, an assignment to a `let mut` local, an argument, a `return`,
/// or the value of a `:=`. A handle type keeps the handle (`handle_use`), and another type reads
/// it. A read of an aggregate gives a reference, and its binding expands the reference into its
/// leaves. Thus a copy also charges the size of the reference before the typed use (`read_use`).
pub(super) struct Whole;

/// A field of a constructor, with its argument at the node `0`, in a data context
/// (section 9.2).
pub(super) struct Field(pub(super) Pos);

/// A `push` element at the node `0`. A list holds static values and handles, and no hardware leaf.
pub(super) struct Element(pub(super) Pos);

impl Site for Whole {
    type Used = Val;

    fn site_use(
        self,
        ev: &mut Evaluator<'_>,
        pos: Pos,
        t: TyId,
        copies: bool,
        out: Out,
    ) -> Res<Val> {
        if ev.tys.get(t).is_handle() {
            ev.handle_use(pos, t, &out)
        } else {
            ev.read_use(pos, t, copies, out)
        }
    }
}

impl Site for Field {
    type Used = Piece<'static>;

    fn site_use(
        self,
        ev: &mut Evaluator<'_>,
        pos: Pos,
        t: TyId,
        _copies: bool,
        out: Out,
    ) -> Res<Piece<'static>> {
        if ev.tys.get(t).is_handle() {
            return Ok(Piece::New(Agg::Handle(ev.handle_leaf(pos, t, &out)?)));
        }
        let out = ev.settle(pos, t, out)?;
        let d = ev.data_at(self.0, t, out)?;
        ev.arg_hw_opnd(self.0, &d)?;
        let out = d.into_out();
        if ev.is_handle(&out) {
            return ev.handle_wrong(pos, t, ev.store.seen(&out));
        }
        ev.conform_piece(pos, t, Piece::Out(out))
    }
}

impl Site for Element {
    type Used = Typed;

    fn site_use(
        self,
        ev: &mut Evaluator<'_>,
        pos: Pos,
        t: TyId,
        _copies: bool,
        out: Out,
    ) -> Res<Typed> {
        ev.typed_element(pos, self.0, t, out)
    }
}

impl Evaluator<'_> {
    /// The copy of `out` when `copies`, then its typed use at `t` at `pos` by the position
    /// `site`. The copy charges the size of the result, and a handle has the size 1.
    pub(super) fn typed_use<S: Site>(
        &mut self,
        pos: Pos,
        t: TyId,
        copies: bool,
        out: Out,
        site: S,
    ) -> Res<S::Used> {
        if copies {
            self.charge(pos, self.size(&out))?;
        }
        site.site_use(self, pos, t, copies, out)
    }

    /// The check of a static position, before the value is taken. A literal that waits for
    /// its type is `S010` at its first `[]`.
    pub(super) fn check_static(&self, pos: Pos, out: &Out) -> Res<()> {
        match self.store.seen(out) {
            Seen::Static(_) => Ok(()),
            Seen::Pending(q, _) => no_type(q),
            s => fail(Code::S011, pos, self.not_static(s)),
        }
    }

    /// The text of a value `{a}` at a static position (section 6.2, "Value not static").
    pub(super) fn not_static(&self, s: Seen<'_>) -> String {
        format!(
            "a static position needs a static value, not {}; compute the value from static \
             values, for example from constants and `comptime` parameters",
            self.about(s)
        )
    }

    /// The value of a static position at the node `pos`. Another value there is `S011`.
    pub(super) fn static_value(&self, pos: Pos, out: Out) -> Res<Value> {
        self.check_static(pos, &out)?;
        match self.store.take(out) {
            Val::Static(v) => Ok(v),
            v => fail(Code::S011, pos, self.not_static(v.seen())),
        }
    }

    /// A typed use of a static result at the type `t`. Another value is `S011`.
    pub(super) fn conform(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Value> {
        self.check_static(pos, &out)?;
        let converted =
            ops::convert(t, self.store.value(&out), &mut self.fuel, &self.tys).map_err(at(pos))?;
        match converted {
            Some(v) => Ok(v),
            None => self.static_value(pos, out),
        }
    }

    /// The typed use of the data `d` at the type `t`.
    pub(super) fn conform_data(&mut self, pos: Pos, t: TyId, d: Opnd) -> Res<Val> {
        match d {
            Opnd::Static(o) if self.is_handle(&o) => self.handle_wrong(pos, t, self.store.seen(&o)),
            Opnd::Static(o) if self.is_agg(&o) => Ok(self.typed_agg(pos, t, o)?.into_val()),
            Opnd::Static(o) => {
                let v = self.conform(pos, t, o)?;
                Ok(Agg::typed(&mut self.tys, t, v).into_val())
            }
            Opnd::Hw(h) => {
                let ty = self.graph.ty(h);
                if ty == *self.tys.get(t) {
                    Ok(Val::Hw(h))
                } else {
                    fail(
                        Code::S010,
                        pos,
                        format!(
                            "expected {}, but the value is {}",
                            self.tys.text(t),
                            self.tys.text_of(&ty)
                        ),
                    )
                }
            }
        }
    }

    /// The typed use of `out` at `t` after its copy charged. A read of a handle that gives an
    /// aggregate charges the size of the reference when `copies`.
    pub(super) fn read_use(&mut self, pos: Pos, t: TyId, copies: bool, out: Out) -> Res<Val> {
        let out = self.settle(pos, t, out)?;
        let handle = self.is_handle(&out);
        let d = self.data_at(pos, t, out)?;
        self.arg_hw_opnd(pos, &d)?;
        if copies
            && handle
            && let Opnd::Static(o) = &d
            && self.is_agg(o)
        {
            self.charge(pos, self.size(o))?;
        }
        self.conform_data(pos, t, d)
    }
}
