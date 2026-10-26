// SPDX-License-Identifier: Apache-2.0
//! The canonical serialization of section 7.1 for values and types, as Lean `Value.serialize`
//! and `Ty.serialize` define it. One walk writes both, and the walk keeps its own stack, so a
//! value or a type of any depth is safe on any thread.
//!
//! A sink takes the text, or only its length in bytes. The length of a whole type comes from
//! the table once `Types::measure` measured it, so the length of a value costs no walk of its
//! types.

use crate::int::{Int, Pow10};
use crate::types::{Generated, Ty, TyId, TyParam, Types};
use crate::value::Value;
use core_ir::Bits;
use std::collections::BTreeMap;
use std::fmt::Write;

/// Where a serialization goes: the text itself, or only its length in bytes.
pub(crate) trait Sink: Write {
    /// Writes the whole type `t` if the sink can do so from the table. The walk expands `t`
    /// when this is `false`.
    fn whole_type(&mut self, tys: &Types, t: TyId) -> bool;

    /// Writes a string with the escapes of the grammar.
    fn quoted(&mut self, s: &str);

    /// Writes the decimal form of an integer.
    fn int(&mut self, n: &Int);
}

impl Sink for String {
    fn whole_type(&mut self, _: &Types, _: TyId) -> bool {
        false
    }

    fn quoted(&mut self, s: &str) {
        parse::quote(s, self);
    }

    fn int(&mut self, n: &Int) {
        write!(self, "{n}").unwrap_or_default();
    }
}

/// What a length measure keeps between texts: the length of each type it measured, and the
/// powers of ten that the digit counts of integers built. Both stay true for the whole run.
#[derive(Default)]
pub(crate) struct Cache {
    types: BTreeMap<TyId, u64>,
    pow10: Pow10,
}

/// The length in bytes of a serialization.
#[derive(Default)]
pub(crate) struct Len(pub(crate) u64, pub(crate) Cache);

impl Len {
    /// A measure that starts with `cache`.
    pub(crate) fn with(cache: Cache) -> Len {
        Len(0, cache)
    }

    /// The length of the text of the type `t`. A part that the cache holds is a lookup, and
    /// a new type takes the lengths of its parts first, with a stack of its own, so each
    /// type in the table measures once and no text unfolds a type.
    pub(crate) fn type_len(&mut self, tys: &Types, t: TyId) -> u64 {
        let mut work = vec![t];
        while let Some(&t) = work.last() {
            if self.1.types.contains_key(&t) {
                work.pop();
                continue;
            }
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::TypeNodes, 1);
            let mut parts = Vec::new();
            match tys.get(t) {
                Ty::Array(elem, _)
                | Ty::List(elem)
                | Ty::Reg(elem)
                | Ty::Wire(elem)
                | Ty::Input(elem)
                | Ty::Mem(elem, _) => parts.push(*elem),
                Ty::Tuple(ts) => parts.extend(ts.iter().copied()),
                Ty::Fn(ps, ret) => {
                    parts.extend(ps.iter().map(|p| p.ty));
                    parts.push(*ret);
                }
                Ty::Struct(s) => {
                    let spec = tys.spec(*s);
                    for arg in spec.args() {
                        held_types(arg, &mut parts);
                    }
                    if spec.generated().is_some() {
                        parts.extend(spec.field_types().iter().copied());
                    }
                }
                Ty::Instance(i) => {
                    for arg in tys.inst(*i).args() {
                        held_types(arg, &mut parts);
                    }
                }
                _ => {}
            }
            let waiting = work.len();
            work.extend(parts.into_iter().filter(|p| !self.1.types.contains_key(p)));
            if work.len() == waiting {
                let mut node = Len::with(std::mem::take(&mut self.1));
                write(tys, Item::Node(tys.get(t)), &mut node);
                self.1 = node.1;
                self.1.types.insert(t, node.0);
                work.pop();
            }
        }
        self.1.types.get(&t).copied().unwrap_or_default()
    }
}

/// Pushes onto `out` each type that `v` holds as a part: a type value and the type of an array
/// or a record, at any depth of `v`.
fn held_types(v: &Value, out: &mut Vec<TyId>) {
    let mut work = vec![v];
    while let Some(v) = work.pop() {
        match v {
            Value::Type(t) | Value::Enum(t, ..) => out.push(*t),
            Value::Array(t, xs) | Value::Record(t, xs) | Value::List(t, xs) => {
                out.push(*t);
                work.extend(xs);
            }
            Value::Tuple(_, xs) => work.extend(xs),
            _ => {}
        }
    }
}

impl Write for Len {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0 = self.0.saturating_add(s.len() as u64);
        Ok(())
    }
}

impl Sink for Len {
    fn whole_type(&mut self, tys: &Types, t: TyId) -> bool {
        let len = self.type_len(tys, t);
        self.0 = self.0.saturating_add(len);
        true
    }

    fn int(&mut self, n: &Int) {
        self.0 = self.0.saturating_add(n.decimal_len_with(&mut self.1.pow10));
    }

    fn quoted(&mut self, s: &str) {
        // The two quotes, and two bytes for each escape of `parse::quote`.
        let escaped = s
            .chars()
            .map(|c| match c {
                '"' | '\\' | '\n' | '\r' | '\t' => 2,
                c => c.len_utf8() as u64,
            })
            .sum::<u64>();
        self.0 = self.0.saturating_add(escaped + 2);
    }
}

/// A piece of the serialization that waits on the stack of the walk.
pub(crate) enum Item<'a> {
    Value(&'a Value),
    /// A type of the table. The sink can write it whole.
    Ty(TyId),
    /// The node of a type, with its parts as pieces. The table makes a new entry from it.
    Node(&'a Ty),
    /// A parameter type of a function type: `(mut <type>)` with the mark, else the type.
    Param(TyParam),
    Text(&'static str),
    Name(&'a str),
    /// A name as a string with the escapes of the grammar.
    Quoted(&'a str),
    Int(&'a Int),
    /// The tag and the payload of an enum value after its type, and the closing parenthesis.
    EnumRest(&'a Bits, Option<&'a Bits>),
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
            Item::Quoted(s) => out.quoted(s),
            Item::Int(n) => out.int(n),
            Item::EnumRest(tag, payload) => {
                out.write_str(" ").unwrap_or_default();
                out.int(&Int::from_unsigned(tag));
                if let Some(p) = payload {
                    write!(out, " (uint {} ", p.width()).unwrap_or_default();
                    out.int(&Int::from_unsigned(p));
                    out.write_str(")").unwrap_or_default();
                }
                out.write_str(")").unwrap_or_default();
            }
            Item::Ty(t) => {
                if !out.whole_type(tys, t) {
                    #[cfg(test)]
                    crate::counters::add(crate::counters::Count::Unfolded, 1);
                    work.push(Item::Node(tys.get(t)));
                }
            }
            Item::Param(p) if p.mutable => {
                out.write_str("(mut ").unwrap_or_default();
                work.push(Item::Text(")"));
                work.push(Item::Ty(p.ty));
            }
            Item::Param(p) => work.push(Item::Ty(p.ty)),
            Item::Node(ty) => type_node(tys, ty, out, &mut work),
            Item::Value(v) => value_node(tys, v, out, &mut work),
        }
    }
}

/// The node of a type. Its parts wait on the stack.
fn type_node<'a, S: Sink>(tys: &'a Types, ty: &'a Ty, out: &mut S, work: &mut Vec<Item<'a>>) {
    #[cfg(test)]
    crate::counters::add(crate::counters::Count::TypeNodes, 1);
    match ty {
        Ty::Bool => out.write_str("bool").unwrap_or_default(),
        Ty::Nat => out.write_str("nat").unwrap_or_default(),
        Ty::Int => out.write_str("int").unwrap_or_default(),
        Ty::Unit => out.write_str("unit").unwrap_or_default(),
        Ty::Type => out.write_str("type").unwrap_or_default(),
        Ty::String => out.write_str("string").unwrap_or_default(),
        Ty::UInt(w) => write!(out, "(uint {w})").unwrap_or_default(),
        Ty::SInt(w) => write!(out, "(sint {w})").unwrap_or_default(),
        Ty::Array(elem, len) => {
            out.write_str("(array ").unwrap_or_default();
            work.push(Item::Text(")"));
            work.push(Item::Int(len));
            work.push(Item::Text(" "));
            work.push(Item::Ty(*elem));
        }
        Ty::List(elem) => {
            out.write_str("(list ").unwrap_or_default();
            work.push(Item::Text(")"));
            work.push(Item::Ty(*elem));
        }
        Ty::Tuple(parts) => {
            out.write_str("(tuple (").unwrap_or_default();
            work.push(Item::Text("))"));
            push_list(work, parts.iter().map(|part| Item::Ty(*part)));
        }
        Ty::Fn(params, ret) => {
            out.write_str("(fn (").unwrap_or_default();
            work.push(Item::Text(")"));
            work.push(Item::Ty(*ret));
            work.push(Item::Text(") "));
            push_list(work, params.iter().map(|p| Item::Param(*p)));
        }
        Ty::Reg(t) => handle(out, work, "(reg ", *t),
        Ty::Wire(t) => handle(out, work, "(wire ", *t),
        Ty::Input(t) => handle(out, work, "(input ", *t),
        Ty::Mem(t, depth) => {
            out.write_str("(mem ").unwrap_or_default();
            work.push(Item::Text(")"));
            work.push(Item::Int(depth));
            work.push(Item::Text(" "));
            work.push(Item::Ty(*t));
        }
        Ty::Instance(i) => {
            let inst = tys.inst(*i);
            out.write_str("(instance root ").unwrap_or_default();
            work.push(Item::Text("))"));
            push_list(work, inst.args().iter().map(Item::Value));
            work.push(Item::Text(" ("));
            work.push(Item::Name(inst.name()));
        }
        Ty::Enum(e) => {
            out.write_str("(enum root ").unwrap_or_default();
            out.write_str(tys.enum_name(*e)).unwrap_or_default();
            out.write_str(" ())").unwrap_or_default();
        }
        Ty::Struct(s) if tys.spec(*s).generated().is_some() => {
            let spec = tys.spec(*s);
            out.write_str("(gstruct (").unwrap_or_default();
            work.push(Item::Text("))"));
            let names = spec.generated().map_or(&[][..], Generated::names);
            let fields = names.iter().zip(spec.field_types());
            let mut items = Vec::new();
            for (k, (name, t)) in fields.enumerate() {
                if k > 0 {
                    items.push(Item::Text(" "));
                }
                items.extend([
                    Item::Text("("),
                    Item::Quoted(name),
                    Item::Text(" "),
                    Item::Ty(*t),
                    Item::Text(")"),
                ]);
            }
            work.extend(items.into_iter().rev());
        }
        Ty::Struct(s) => {
            let spec = tys.spec(*s);
            out.write_str("(struct ").unwrap_or_default();
            out.write_str(spec.origin().token()).unwrap_or_default();
            out.write_str(" ").unwrap_or_default();
            work.push(Item::Text("))"));
            push_list(work, spec.args().iter().map(Item::Value));
            work.push(Item::Text(" ("));
            work.push(Item::Name(spec.name()));
        }
    }
}

/// `(<form> <type>)` of a handle type with one part.
fn handle<S: Sink>(out: &mut S, work: &mut Vec<Item<'_>>, form: &'static str, t: TyId) {
    out.write_str(form).unwrap_or_default();
    work.push(Item::Text(")"));
    work.push(Item::Ty(t));
}

/// The node of a value. Its parts wait on the stack.
fn value_node<'a, S: Sink>(tys: &Types, v: &'a Value, out: &mut S, work: &mut Vec<Item<'a>>) {
    match v {
        Value::Int(n) => {
            out.write_str("(int ").unwrap_or_default();
            out.int(n);
            out.write_str(")").unwrap_or_default();
        }
        Value::Bool(b) => write!(out, "(bool {b})").unwrap_or_default(),
        Value::Str(s) => {
            out.write_str("(string ").unwrap_or_default();
            out.quoted(s);
            out.write_str(")").unwrap_or_default();
        }
        Value::UInt(x) => {
            write!(out, "(uint {} ", x.width()).unwrap_or_default();
            out.int(&Int::from_unsigned(x));
            out.write_str(")").unwrap_or_default();
        }
        Value::SInt(x) => {
            write!(out, "(sint {} ", x.width()).unwrap_or_default();
            out.int(&Int::from_signed(x, x.width()));
            out.write_str(")").unwrap_or_default();
        }
        Value::Unit => out.write_str("(unit)").unwrap_or_default(),
        Value::Type(t) => {
            out.write_str("(type ").unwrap_or_default();
            work.push(Item::Text(")"));
            work.push(Item::Ty(*t));
        }
        Value::Array(t, xs) => container(out, work, "(array ", Some(*t), xs),
        Value::Record(t, xs) => container(out, work, "(record ", Some(*t), xs),
        Value::List(t, xs) => container(out, work, "(list ", Some(*t), xs),
        Value::Tuple(_, xs) => container(out, work, "(tuple ", None, xs),
        Value::Function(item, _) => {
            write!(out, "(function root {})", tys.fn_name(*item)).unwrap_or_default();
        }
        Value::Enum(t, tag, payload) => {
            out.write_str("(enum ").unwrap_or_default();
            work.push(Item::EnumRest(tag, payload.as_ref()));
            work.push(Item::Ty(*t));
        }
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
