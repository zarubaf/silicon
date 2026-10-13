// SPDX-License-Identifier: Apache-2.0
//! The source form of a type or a value in a message. The walk keeps its own stack and stops
//! after `TEXT_LIMIT` bytes, so no message grows with the size of a type or a value.

use crate::int::Int;
use crate::ops::int_text;
use crate::types::{Ty, TyId, TyParam, Types};
use crate::value::Value;
use std::fmt::Write;

/// The longest text of a type or a value in a message, before `...`.
pub(crate) const TEXT_LIMIT: usize = 1024;

/// A piece of the source form of a value or a type.
pub(crate) enum Piece<'a> {
    /// The type of a value, which has one.
    Value(&'a Value),
    /// The literal form of a static argument.
    Lit(&'a Value),
    Ty(TyId),
    /// A parameter type of a function type, with `mut ` before it if it has the mark.
    Param(TyParam),
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
    /// Pushes `items` so that they come off the stack in order with `sep` between.
    fn push_list(
        &mut self,
        items: &'a [Value],
        sep: &'static str,
        piece: fn(&'a Value) -> Piece<'a>,
    ) {
        for (k, x) in items.iter().enumerate().rev() {
            self.work.push(piece(x));
            if k > 0 {
                self.work.push(Piece::Text(sep));
            }
        }
    }

    /// The node `ty`. Its parts wait on the stack.
    pub(crate) fn ty_node(&mut self, tys: &'a Types, ty: &Ty) {
        match ty {
            Ty::Bool => self.out.push_str("Bool"),
            Ty::Nat => self.out.push_str("Nat"),
            Ty::Int => self.out.push_str("Int"),
            Ty::Unit => self.out.push_str("Unit"),
            Ty::Type => self.out.push_str("Type"),
            Ty::String => self.out.push_str("String"),
            Ty::UInt(w) => write!(self.out, "UInt[{w}]").unwrap_or_default(),
            Ty::SInt(w) => write!(self.out, "SInt[{w}]").unwrap_or_default(),
            Ty::Array(elem, len) => {
                self.out.push('[');
                self.work
                    .push(Piece::Owned(format!("; {}]", int_text(len))));
                self.work.push(Piece::Ty(*elem));
            }
            Ty::List(elem) => {
                self.out.push_str("List[");
                self.work.push(Piece::Text("]"));
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
            Ty::Fn(params, ret) => {
                self.out.push_str("fn (");
                self.work.push(Piece::Ty(*ret));
                self.work.push(Piece::Text(") -> "));
                for (k, p) in params.iter().enumerate().rev() {
                    self.work.push(Piece::Param(*p));
                    if k > 0 {
                        self.work.push(Piece::Text(", "));
                    }
                }
            }
            Ty::Struct(s) => {
                let spec = tys.spec(*s);
                self.out.push_str(spec.name());
                if !spec.args().is_empty() {
                    self.out.push('[');
                    self.work.push(Piece::Text("]"));
                    self.push_list(spec.args(), ", ", Piece::Lit);
                }
            }
        }
    }

    /// The type of the value `v`. Its elements wait on the stack.
    pub(crate) fn value(&mut self, v: &'a Value) {
        match v {
            Value::Int(_) => self.out.push_str("Int"),
            Value::Bool(_) => self.out.push_str("Bool"),
            Value::UInt(x) => write!(self.out, "UInt[{}]", x.width()).unwrap_or_default(),
            Value::SInt(x) => write!(self.out, "SInt[{}]", x.width()).unwrap_or_default(),
            Value::Unit => self.out.push_str("Unit"),
            Value::Type(_) => self.out.push_str("Type"),
            Value::Array(elem, xs) => {
                self.out.push('[');
                self.work.push(Piece::Owned(format!("; {}]", xs.len())));
                self.work.push(Piece::Ty(*elem));
            }
            Value::Record(t, _) | Value::Function(_, t) => self.work.push(Piece::Ty(*t)),
            Value::List(elem, _) => {
                self.out.push_str("List[");
                self.work.push(Piece::Text("]"));
                self.work.push(Piece::Ty(*elem));
            }
            Value::Tuple(_, xs) => {
                self.out.push('(');
                self.work
                    .push(Piece::Text(if xs.len() == 1 { ",)" } else { ")" }));
                self.push_list(xs, ", ", Piece::Value);
            }
            Value::Str(_) => self.out.push_str("String"),
        }
    }

    /// The literal form of the static argument `v`, as Lean `Value.literal` prints it.
    fn lit(&mut self, tys: &Types, v: &'a Value) {
        match v {
            Value::Int(n) => self.out.push_str(&int_text(n)),
            Value::Bool(b) => write!(self.out, "{b}").unwrap_or_default(),
            Value::Str(s) => {
                let head: String = s.chars().take(TEXT_LIMIT + 1).collect();
                parse::quote(&head, &mut self.out);
            }
            Value::UInt(x) => self.out.push_str(&int_text(&Int::from_unsigned(x))),
            Value::SInt(x) => self
                .out
                .push_str(&int_text(&Int::from_signed(x, x.width()))),
            Value::Type(t) => self.work.push(Piece::Ty(*t)),
            Value::Unit => self.out.push_str("()"),
            Value::Function(item, _) => self.out.push_str(tys.fn_name(*item)),
            Value::List(t, xs) if xs.is_empty() => {
                self.out.push_str("list(");
                self.work.push(Piece::Text(")"));
                self.work.push(Piece::Ty(*t));
            }
            Value::Array(_, xs) | Value::List(_, xs) => {
                self.out.push('[');
                self.work.push(Piece::Text("]"));
                self.push_list(xs, ", ", Piece::Lit);
            }
            Value::Tuple(_, xs) => {
                self.out.push('(');
                self.work
                    .push(Piece::Text(if xs.len() == 1 { ",)" } else { ")" }));
                self.push_list(xs, ", ", Piece::Lit);
            }
            Value::Record(t, xs) => {
                self.work.push(Piece::Text(")"));
                self.push_list(xs, ", ", Piece::Lit);
                self.work.push(Piece::Text("("));
                self.work.push(Piece::Ty(*t));
            }
        }
    }

    /// The text after the walk of each piece on the stack, or its first `TEXT_LIMIT` bytes.
    /// A length prints at most 256 bits, so each piece is short and the walk stops soon after
    /// the limit.
    pub(crate) fn finish(mut self, tys: &'a Types) -> String {
        while self.out.len() <= TEXT_LIMIT
            && let Some(piece) = self.work.pop()
        {
            match piece {
                Piece::Value(v) => self.value(v),
                Piece::Lit(v) => self.lit(tys, v),
                Piece::Ty(t) => self.ty_node(tys, tys.get(t)),
                Piece::Param(p) => {
                    if p.mutable {
                        self.out.push_str("mut ");
                    }
                    self.work.push(Piece::Ty(p.ty));
                }
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
