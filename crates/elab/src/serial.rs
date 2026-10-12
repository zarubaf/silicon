// SPDX-License-Identifier: Apache-2.0
//! The canonical serialization of section 7.1 for values and types, as Lean `Value.serialize`
//! and `Ty.serialize` define it. One walk writes both, and the walk keeps its own stack, so a
//! value or a type of any depth is safe on any thread.
//!
//! A sink takes the text, or only its length in bytes. The length of a whole type comes from
//! the table, so the length of a value costs no walk of its types.

use crate::int::Int;
use crate::types::{Ty, TyId, Types};
use crate::value::Value;
use std::fmt::Write;

/// Where a serialization goes: the text itself, or only its length in bytes.
pub(crate) trait Sink: Write {
    /// Writes the whole type `t` if the sink can do so from the table. The walk expands `t`
    /// when this is `false`.
    fn whole_type(&mut self, tys: &Types, t: TyId) -> bool;

    /// Writes a string with the escapes of the grammar.
    fn quoted(&mut self, s: &str);
}

impl Sink for String {
    fn whole_type(&mut self, _: &Types, _: TyId) -> bool {
        false
    }

    fn quoted(&mut self, s: &str) {
        parse::quote(s, self);
    }
}

/// The length in bytes of a serialization.
#[derive(Default)]
pub(crate) struct Len(pub(crate) u64);

impl Write for Len {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0 = self.0.saturating_add(s.len() as u64);
        Ok(())
    }
}

impl Sink for Len {
    fn whole_type(&mut self, tys: &Types, t: TyId) -> bool {
        self.0 = self.0.saturating_add(tys.text_len(t));
        true
    }

    fn quoted(&mut self, s: &str) {
        let mut text = String::new();
        parse::quote(s, &mut text);
        self.0 = self.0.saturating_add(text.len() as u64);
    }
}

/// A piece of the serialization that waits on the stack of the walk.
pub(crate) enum Item<'a> {
    Value(&'a Value),
    /// A type of the table. The sink can write it whole.
    Ty(TyId),
    /// The node of a type, with its parts as pieces. The table makes a new entry from it.
    Node(&'a Ty),
    Text(&'static str),
    Name(&'a str),
    Int(&'a Int),
}

/// Pushes `items` so that they come off the stack in order with `sep` between.
fn push_list<'a>(work: &mut Vec<Item<'a>>, items: impl DoubleEndedIterator<Item = Item<'a>>) {
    let mut items = items.rev().peekable();
    while let Some(item) = items.next() {
        work.push(item);
        if items.peek().is_some() {
            work.push(Item::Text(" "));
        }
    }
}

/// Writes `first` into `out`.
pub(crate) fn write<S: Sink>(tys: &Types, first: Item<'_>, out: &mut S) {
    let mut work = vec![first];
    while let Some(item) = work.pop() {
        match item {
            Item::Text(s) | Item::Name(s) => out.write_str(s).unwrap_or_default(),
            Item::Int(n) => write!(out, "{n}").unwrap_or_default(),
            Item::Ty(t) => {
                if !out.whole_type(tys, t) {
                    work.push(Item::Node(tys.get(t)));
                }
            }
            Item::Node(ty) => type_node(tys, ty, out, &mut work),
            Item::Value(v) => value_node(v, out, &mut work),
        }
    }
}

/// The node of a type. Its parts wait on the stack.
fn type_node<'a, S: Sink>(tys: &'a Types, ty: &'a Ty, out: &mut S, work: &mut Vec<Item<'a>>) {
    match ty {
        Ty::Bool => out.write_str("bool").unwrap_or_default(),
        Ty::Nat => out.write_str("nat").unwrap_or_default(),
        Ty::Int => out.write_str("int").unwrap_or_default(),
        Ty::Unit => out.write_str("unit").unwrap_or_default(),
        Ty::Type => out.write_str("type").unwrap_or_default(),
        Ty::UInt(w) => write!(out, "(uint {w})").unwrap_or_default(),
        Ty::SInt(w) => write!(out, "(sint {w})").unwrap_or_default(),
        Ty::Array(elem, len) => {
            out.write_str("(array ").unwrap_or_default();
            work.push(Item::Text(")"));
            work.push(Item::Int(len));
            work.push(Item::Text(" "));
            work.push(Item::Ty(*elem));
        }
        Ty::Tuple(parts) => {
            out.write_str("(tuple (").unwrap_or_default();
            work.push(Item::Text("))"));
            push_list(work, parts.iter().map(|part| Item::Ty(*part)));
        }
        Ty::Struct(s) => {
            let spec = tys.spec(*s);
            out.write_str("(struct root ").unwrap_or_default();
            work.push(Item::Text("))"));
            push_list(work, spec.args().iter().map(Item::Value));
            work.push(Item::Text(" ("));
            work.push(Item::Name(spec.name()));
        }
    }
}

/// The node of a value. Its parts wait on the stack.
fn value_node<'a, S: Sink>(v: &'a Value, out: &mut S, work: &mut Vec<Item<'a>>) {
    match v {
        Value::Int(n) => write!(out, "(int {n})").unwrap_or_default(),
        Value::Bool(b) => write!(out, "(bool {b})").unwrap_or_default(),
        Value::Str(s) => {
            out.write_str("(string ").unwrap_or_default();
            out.quoted(s);
            out.write_str(")").unwrap_or_default();
        }
        Value::UInt(x) => {
            write!(out, "(uint {} {})", x.width(), Int::from_unsigned(x)).unwrap_or_default();
        }
        Value::SInt(x) => write!(
            out,
            "(sint {} {})",
            x.width(),
            Int::from_signed(x, x.width())
        )
        .unwrap_or_default(),
        Value::Unit => out.write_str("(unit)").unwrap_or_default(),
        Value::Type(t) => {
            out.write_str("(type ").unwrap_or_default();
            work.push(Item::Text(")"));
            work.push(Item::Ty(*t));
        }
        Value::Array(t, xs) => container(out, work, "(array ", Some(*t), xs),
        Value::Record(t, xs) => container(out, work, "(record ", Some(*t), xs),
        Value::Tuple(xs) => container(out, work, "(tuple ", None, xs),
    }
}

/// `(<form> [<type> ](<elements>))`.
fn container<'a, S: Sink>(
    out: &mut S,
    work: &mut Vec<Item<'a>>,
    form: &'static str,
    ty: Option<TyId>,
    xs: &'a [Value],
) {
    out.write_str(form).unwrap_or_default();
    work.push(Item::Text("))"));
    push_list(work, xs.iter().map(Item::Value));
    match ty {
        Some(t) => {
            work.push(Item::Text(" ("));
            work.push(Item::Ty(t));
        }
        None => work.push(Item::Text("(")),
    }
}
