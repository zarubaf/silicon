// SPDX-License-Identifier: Apache-2.0
//! The source form of a type or a value in a message. The walk keeps its own stack and stops
//! after `TEXT_LIMIT` bytes, so no message grows with the size of a type or a value.

use crate::types::{Ty, TyId, Types};
use crate::value::Value;
use std::fmt::Write;

/// The longest text of a type or a value in a message, before `...`.
pub(crate) const TEXT_LIMIT: usize = 1024;

/// A piece of the source form of a value or a type.
pub(crate) enum Piece<'a> {
    Value(&'a Value),
    Ty(TyId),
    Text(&'static str),
    Owned(String),
}

/// The source form of a type or of the type of a value, for a message. The walk keeps its
/// own stack and stops after `TEXT_LIMIT` bytes.
#[derive(Default)]
pub(crate) struct Text<'a> {
    pub(crate) out: String,
    pub(crate) work: Vec<Piece<'a>>,
}

impl<'a> Text<'a> {
    /// The node `ty`. Its parts wait on the stack.
    pub(crate) fn ty_node(&mut self, ty: &Ty) {
        match ty {
            Ty::Bool => self.out.push_str("Bool"),
            Ty::Nat => self.out.push_str("Nat"),
            Ty::Int => self.out.push_str("Int"),
            Ty::Unit => self.out.push_str("Unit"),
            Ty::UInt(w) => write!(self.out, "UInt[{w}]").unwrap_or_default(),
            Ty::SInt(w) => write!(self.out, "SInt[{w}]").unwrap_or_default(),
            Ty::Array(elem, len) => {
                self.out.push('[');
                self.work
                    .push(Piece::Owned(format!("; {}]", crate::ops::int_text(len))));
                self.work.push(Piece::Ty(*elem));
            }
            Ty::Tuple(parts) => {
                self.out.push('(');
                self.work
                    .push(Piece::Text(if parts.len() == 1 { ",)" } else { ")" }));
                for (k, part) in parts.iter().enumerate().rev() {
                    self.work.push(Piece::Ty(*part));
                    if k > 0 {
                        self.work.push(Piece::Text(", "));
                    }
                }
            }
        }
    }

    /// The type of the value `v`, which has one. Its elements wait on the stack.
    pub(crate) fn value(&mut self, v: &'a Value) {
        match v {
            Value::Int(_) => self.out.push_str("Int"),
            Value::Bool(_) => self.out.push_str("Bool"),
            Value::UInt(x) => write!(self.out, "UInt[{}]", x.width()).unwrap_or_default(),
            Value::SInt(x) => write!(self.out, "SInt[{}]", x.width()).unwrap_or_default(),
            Value::Unit => self.out.push_str("Unit"),
            Value::Array(elem, xs) => {
                self.out.push('[');
                self.work.push(Piece::Owned(format!("; {}]", xs.len())));
                self.work.push(Piece::Ty(*elem));
            }
            Value::Tuple(xs) => {
                self.out.push('(');
                self.work
                    .push(Piece::Text(if xs.len() == 1 { ",)" } else { ")" }));
                for (k, x) in xs.iter().enumerate().rev() {
                    self.work.push(Piece::Value(x));
                    if k > 0 {
                        self.work.push(Piece::Text(", "));
                    }
                }
            }
            Value::Str(_) | Value::Type(_) => {}
        }
    }

    /// The text after the walk of each piece on the stack, or its first `TEXT_LIMIT` bytes.
    /// A length prints at most 256 bits, so each piece is short and the walk stops soon after
    /// the limit.
    pub(crate) fn finish(mut self, tys: &Types) -> String {
        while self.out.len() <= TEXT_LIMIT
            && let Some(piece) = self.work.pop()
        {
            match piece {
                Piece::Value(v) => self.value(v),
                Piece::Ty(t) => self.ty_node(tys.get(t)),
                Piece::Text(text) => self.out.push_str(text),
                Piece::Owned(text) => self.out.push_str(&text),
            }
        }
        if self.out.len() > TEXT_LIMIT {
            let mut cut = TEXT_LIMIT;
            while !self.out.is_char_boundary(cut) {
                cut -= 1;
            }
            self.out.truncate(cut);
            self.out.push_str("...");
        }
        self.out
    }
}
