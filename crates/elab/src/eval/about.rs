// SPDX-License-Identifier: Apache-2.0
//! The text of a result in a message (Lean `Val.about`): the bounded text of a static value, the
//! type of a hardware node, and the form of a handle.

use super::{Evaluator, Opnd};
use crate::hw::{Handle, Kind as Resource, Part, Seen};
use crate::ops::str_text;

impl Evaluator<'_> {
    pub(super) fn part_text(&self, p: &Part) -> String {
        match p {
            Part::Value(a) => self.text(a.seen()),
            Part::Empty(_) => "`[]`".to_owned(),
            Part::Array(..) => "an array literal with `[]`".to_owned(),
            Part::Tuple(..) => "a tuple literal with `[]`".to_owned(),
        }
    }

    pub(super) fn text(&self, s: Seen<'_>) -> String {
        match s {
            Seen::Pending(_, p) => format!("{} without a type", self.part_text(p)),
            s => s.text(&self.graph, &self.tys).unwrap_or_default(),
        }
    }

    /// The value `{a}` of a message (section 6.2, Lean `Val.about`). A handle names its handle
    /// type, an own output its source name, and a domain its name. A literal that waits is `[]`.
    /// Another value names its type, so the text reads no value in full and each type text is
    /// bounded.
    pub(super) fn about(&self, s: Seen<'_>) -> String {
        match s {
            Seen::Handle(Handle::Res {
                kind: Resource::Output,
                path,
                ..
            }) => format!(
                "the output `{}`",
                str_text(&self.paths.source(*path, &self.syms.texts))
            ),
            Seen::Handle(Handle::Domain(d)) => format!("the domain `{}`", self.domain_name(*d)),
            Seen::Handle(h) => match self.handle_form(h) {
                Some(t) => format!("a handle of `{}`", self.tys.text_of(&t)),
                None => self.text(s),
            },
            Seen::Pending(..) => "`[]`".to_owned(),
            Seen::Static(v) => format!("a value of `{}`", v.type_text(&self.tys)),
            Seen::Hw(h) => format!("a value of `{}`", self.tys.text_of(&self.graph.ty(h))),
            Seen::Agg(a) => match a.stored_ty() {
                Some(t) => format!("a value of `{}`", self.tys.text(t)),
                None => self.text(s),
            },
        }
    }

    /// What the operand is, for a message: a hardware aggregate prints as `hardware T`.
    pub(super) fn opnd_text(&self, o: &Opnd) -> String {
        match o {
            Opnd::Hw(h) => format!("hardware {}", self.tys.text_of(&self.graph.ty(*h))),
            Opnd::Static(out) => self.text(self.store.seen(out)),
        }
    }

    /// The type of the operand, for a message: a hardware aggregate names its type, and a
    /// static value is what it is.
    pub(super) fn type_text(&self, o: &Opnd) -> String {
        match o {
            Opnd::Static(out) => match self.store.seen(out) {
                Seen::Agg(a) => a.stored_ty().map(|t| self.tys.text(t)).unwrap_or_default(),
                seen => self.text(seen),
            },
            Opnd::Hw(h) => self.tys.text_of(&self.graph.ty(*h)),
        }
    }
}
