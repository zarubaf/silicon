// SPDX-License-Identifier: Apache-2.0
//! The handle typing of a result and the `S010` texts of a handle that does not fit (design
//! section 5.1). A handle has no `Ty`, so a handle type is a node with the ids of its parts, and
//! a handle leaf fits a type only by the exact form.

use super::{Evaluator, Out, Res, fail};
use crate::Code;
use crate::hw::{Handle, Kind as Resource, Seen, Val};
use crate::int::Int;
use crate::ops::str_text;
use crate::types::{Ty, TyId};
use parse::ast::Pos;

/// A handle has no `Ty`, so an assignment keeps its form.
pub(super) fn same_form(a: Seen<'_>, b: Seen<'_>) -> bool {
    match (a, b) {
        (
            Seen::Handle(Handle::Res { kind, ty, .. }),
            Seen::Handle(Handle::Res {
                kind: k2, ty: t2, ..
            }),
        ) => kind == k2 && ty == t2,
        _ => false,
    }
}

impl Evaluator<'_> {
    /// The handle type of the handle `h` (section 5.1), built from the stored ids with no
    /// interning: `Reg[T]`, `Wire[T]`, `Input[T]`, `Mem[T, N]`, or the stored instance type. An
    /// own output and a domain have none.
    pub(super) fn handle_form(&self, h: &Handle) -> Option<Ty> {
        match h {
            Handle::Res {
                kind: Resource::Reg,
                ty,
                ..
            } => Some(Ty::Reg(*ty)),
            Handle::Res {
                kind: Resource::Wire,
                ty,
                ..
            } => Some(Ty::Wire(*ty)),
            Handle::Res {
                kind: Resource::Output,
                ..
            }
            | Handle::Domain(_) => None,
            Handle::Mem(id) => {
                let m = self.mem(*id)?;
                Some(Ty::Mem(m.word, Int::from_u64(m.depth)))
            }
            Handle::Inst { ty, .. } => Some(self.tys.get(*ty).clone()),
            Handle::Input { port, .. } => Some(Ty::Input(port.ty)),
        }
    }

    /// Whether the result is a handle: a local, or a leaf of a container of handles. The type of
    /// the root tells if a path can end at a handle, so a reference into a root without the
    /// handle flag walks no path.
    pub(super) fn is_handle(&self, out: &Out) -> bool {
        match out {
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => matches!(v, Val::Handle(_)),
            Out::Ref(r) => match self.store.root(&r.root) {
                Val::Handle(_) => r.path.is_empty(),
                Val::Agg(a)
                    if !r.path.is_empty() && a.stored_ty().is_some_and(TyId::holds_handles) =>
                {
                    matches!(self.store.at(r), Seen::Handle(_))
                }
                _ => false,
            },
        }
    }

    /// The typed use at `pos` of `out` at the handle type `t` (section 5.4, Lean `handleUse`).
    /// The handle type of the value equals `t`, else `S010`. The compare is an id compare, it has
    /// no charge, and nothing reads the value. An own output has no handle type, so its text
    /// names the fix: use it as data.
    pub(super) fn handle_use(&mut self, pos: Pos, t: TyId, out: &Out) -> Res<Val> {
        Ok(Val::Handle(self.handle_leaf(pos, t, out)?))
    }

    /// The handle of `out` at the handle type `t`: the same check as `handle_use`, for a caller
    /// that stores the handle as a leaf of a container.
    pub(super) fn handle_leaf(&mut self, pos: Pos, t: TyId, out: &Out) -> Res<Handle> {
        if let Seen::Handle(h) = self.store.seen(out)
            && self.handle_is(h, t)
        {
            return Ok(h.clone());
        }
        self.handle_wrong(pos, t, self.store.seen(out))
    }

    /// The error at `pos` of a typed use of `v` at the type `t` with the handle flag (Lean
    /// `handleWrong`): `S010` with the text of `handle_use_text`. An own output has no handle
    /// type, so its text names the fix: use it as data.
    pub(super) fn handle_wrong<T>(&self, pos: Pos, t: TyId, v: Seen<'_>) -> Res<T> {
        if let Seen::Handle(Handle::Res {
            kind: Resource::Output,
            path,
            ..
        }) = v
        {
            let r = str_text(&self.paths.source(*path, &self.syms.texts));
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{r}` is an output, and an output has no handle type; use `{r}` directly as data"
                ),
            );
        }
        fail(Code::S010, pos, self.handle_use_text(t, &self.about(v)))
    }

    /// The text of a wrong value or leaf `a` at the type `t` with the handle flag (section 6.2,
    /// Lean `handleUseText`). A handle type gives "Typed use at a handle type". Another type, such
    /// as `[Reg[UInt[8]]; 1]`, gives "Typed use at a container of handles".
    pub(super) fn handle_use_text(&self, t: TyId, a: &str) -> String {
        let ty = self.tys.text(t);
        if self.tys.get(t).is_handle() {
            format!(
                "expected `{ty}`, but the value is {a}; a handle type takes only a handle of \
                 exactly this type, so give such a handle or change the type"
            )
        } else {
            format!(
                "expected `{ty}`, but the value is {a}; a value of `{ty}` takes only handles of \
                 exactly its handle types, so give such a value or change the type"
            )
        }
    }

    /// The text "Handle at a data leaf" of section 6.2 (Lean `dataLeafText`): it names the data
    /// type `t` of the position in a container and the handle leaf `a` at it.
    pub(super) fn data_leaf_text(&self, t: TyId, a: &str) -> String {
        format!(
            "expected `{}`, but the value is {a}; a literal element keeps its handle, so read it in \
             the literal, for example `(r, read(r))`",
            self.tys.text(t)
        )
    }

    /// The type of what a result is (Lean `Val.ty?`). A handle has its handle type, and a literal
    /// that waits has none.
    pub(super) fn out_ty(&mut self, out: &Out) -> Option<TyId> {
        if let Seen::Handle(h) = self.store.seen(out) {
            let h = h.clone();
            return self.handle_ty(&h);
        }
        self.store.seen(out).ty(&self.graph, &mut self.tys)
    }

    /// Whether the handle type of `h` is the type `t` (Lean `Handle.ty?` and `Ty.same`). The type
    /// `t` is in the table, so the compare looks up the handle type and makes none.
    pub(super) fn handle_is(&self, h: &Handle, t: TyId) -> bool {
        match h {
            Handle::Inst { ty, .. } => *ty == t,
            _ => self
                .handle_form(h)
                .is_some_and(|form| self.tys.id_of(&form) == Some(t)),
        }
    }

    /// The handle type of `h` as an id (Lean `Handle.ty?`). It reads the stored ids and charges
    /// nothing.
    pub(super) fn handle_ty(&mut self, h: &Handle) -> Option<TyId> {
        let form = self.handle_form(h)?;
        Some(match h {
            Handle::Inst { ty, .. } => *ty,
            _ => self.tys.mk(form),
        })
    }

    /// Whether the handle `h` fits the type `t`: a handle type needs a handle of exactly this
    /// type. It is the one rule of the typed use of a handle leaf, also for the plan of an
    /// aggregate.
    pub(super) fn handle_fits(&self, h: &Handle, t: TyId) -> bool {
        self.tys.get(t).is_handle() && self.handle_is(h, t)
    }

    /// The `S010` at `pos` for the `leaf` that does not fit the type `t`, when `t` is a handle
    /// type or the leaf is a handle. A type with the handle flag is a container of handles, and
    /// a data type is a data leaf, each with its own text. It is the one choice of the text,
    /// also for the plan of an aggregate.
    pub(super) fn handle_mismatch<T>(&self, pos: Pos, t: TyId, leaf: Seen<'_>) -> Res<T> {
        let a = self.about(leaf);
        let text = if t.holds_handles() {
            self.handle_use_text(t, &a)
        } else {
            self.data_leaf_text(t, &a)
        };
        fail(Code::S010, pos, text)
    }
}
