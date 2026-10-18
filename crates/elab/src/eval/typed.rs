// SPDX-License-Identifier: Apache-2.0
//! The typed use of Lean `Eval.typedUse` (design section 5.4). One function, `typed_use`,
//! charges the copy and then gives the value its typed use by the kind of its position. The
//! kind is a `Site`, and its `Used` is the form that the caller stores, as the index of the Lean
//! `Site` is. A caller that pays its copy before passes `copies: false`.

use super::container::Piece;
use super::list::Typed;
use super::{Evaluator, Out, Res};
use crate::agg::Agg;
use crate::hw::Val;
use crate::types::TyId;
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

/// A typed `let` or an assignment to a `let mut` local. A handle type keeps the handle.
pub(super) struct Binding;

/// An argument, a `return`, or the value of a `:=`.
pub(super) struct Passed;

/// A field of a constructor, with its argument at the node `0`, in a data context
/// (section 9.2).
pub(super) struct Field(pub(super) Pos);

/// A `push` element at the node `0`. A list holds only static values.
pub(super) struct Element(pub(super) Pos);

impl Site for Binding {
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
            Passed.site_use(ev, pos, t, copies, out)
        }
    }
}

impl Site for Passed {
    type Used = Val;

    fn site_use(
        self,
        ev: &mut Evaluator<'_>,
        pos: Pos,
        t: TyId,
        copies: bool,
        out: Out,
    ) -> Res<Val> {
        ev.later_handle(pos, t)?;
        ev.read_use(pos, t, copies, out)
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
        let out = ev.data_at(self.0, t, out)?.into_out();
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
        ev.later_handle(pos, t)?;
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
}
