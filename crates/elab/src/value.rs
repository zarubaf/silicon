// SPDX-License-Identifier: Apache-2.0
//! The static values of slice 1 and the static containers of slice 2, their canonical
//! serialization, their recursive size, and their depth, as Lean `Source.Value` defines them.
//! Section 7.1 of the front-end spec uses the serialization in an `InstantiationId`, section
//! 5.4 uses the size in the cost model, and section 5.5 bounds the depth.
//!
//! A container nests as deep as the nesting depth allows, and that limit is a budget. Thus no
//! walk over a value or a type recurses: each one keeps its own stack, so it runs on any
//! thread, also after the evaluator ends.

use crate::int::Int;
use crate::text::Text;
use crate::types::{Ty, TyId, Types};
use core_ir::Bits;
use std::fmt::Write;

/// A static value of slice 1, or a static container of slice 2. A finite value holds the bit
/// vector of the core semantics with the width of its type. An array keeps its element type,
/// so an empty array has a type. A tuple has at least one element: `()` is `Unit`.
#[derive(Debug)]
pub enum Value {
    Int(Int),
    Bool(bool),
    Str(String),
    UInt(Bits),
    SInt(Bits),
    Type(TyId),
    Unit,
    Array(TyId, Vec<Value>),
    Tuple(Vec<Value>),
}

impl Value {
    fn take_children(&mut self, work: &mut Vec<Value>) {
        match self {
            Value::Array(_, elems) | Value::Tuple(elems) => work.append(elems),
            Value::Int(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::UInt(_)
            | Value::SInt(_)
            | Value::Type(_)
            | Value::Unit => {}
        }
    }
}

impl Drop for Value {
    fn drop(&mut self) {
        let mut work = Vec::new();
        self.take_children(&mut work);
        while let Some(mut v) = work.pop() {
            v.take_children(&mut work);
        }
    }
}

/// A step of a walk that builds a container after its elements: visit a value, or make a
/// container of the last `n` results.
enum Build<'a> {
    Visit(&'a Value),
    Array(TyId, usize),
    Tuple(usize),
}

/// The last `n` results of a walk that builds containers.
fn last<T>(done: &mut Vec<T>, n: usize) -> Vec<T> {
    done.split_off(done.len().saturating_sub(n))
}

impl Clone for Value {
    fn clone(&self) -> Value {
        let mut done = Vec::new();
        let mut work = vec![Build::Visit(self)];
        while let Some(step) = work.pop() {
            match step {
                Build::Visit(Value::Array(t, xs)) => {
                    work.push(Build::Array(*t, xs.len()));
                    work.extend(xs.iter().rev().map(Build::Visit));
                }
                Build::Visit(Value::Tuple(xs)) => {
                    work.push(Build::Tuple(xs.len()));
                    work.extend(xs.iter().rev().map(Build::Visit));
                }
                Build::Visit(v) => done.push(v.clone_scalar()),
                Build::Array(t, n) => {
                    let xs = last(&mut done, n);
                    done.push(Value::Array(t, xs));
                }
                Build::Tuple(n) => {
                    let xs = last(&mut done, n);
                    done.push(Value::Tuple(xs));
                }
            }
        }
        done.pop().unwrap_or(Value::Unit)
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        let mut work = vec![(self, other)];
        while let Some(pair) = work.pop() {
            let same = match pair {
                (Value::Array(s, xs), Value::Array(t, ys)) => {
                    work.extend(xs.iter().zip(ys));
                    s == t && xs.len() == ys.len()
                }
                (Value::Tuple(xs), Value::Tuple(ys)) => {
                    work.extend(xs.iter().zip(ys));
                    xs.len() == ys.len()
                }
                (Value::Int(a), Value::Int(b)) => a == b,
                (Value::Bool(a), Value::Bool(b)) => a == b,
                (Value::Str(a), Value::Str(b)) => a == b,
                (Value::UInt(a), Value::UInt(b)) | (Value::SInt(a), Value::SInt(b)) => a == b,
                (Value::Type(a), Value::Type(b)) => a == b,
                (Value::Unit, Value::Unit) => true,
                _ => false,
            };
            if !same {
                return false;
            }
        }
        true
    }
}

impl Eq for Value {}

/// The size of an integer: 1 for each 64-bit word of its magnitude, and at least 1.
#[must_use]
pub fn int_size(n: &Int) -> u64 {
    n.log2() / 64 + 1
}

/// The size of a finite value: 1 for each 64-bit word of its width, and at least 1.
#[must_use]
pub fn width_size(width: u32) -> u64 {
    u64::from(width).div_ceil(64).max(1)
}

pub(crate) fn width_int(width: u32) -> Int {
    Int::from_u64(u64::from(width))
}

/// Where a serialization goes: the text itself, or only its length in bytes. The length of a
/// type comes from the table, so it costs no walk of the type.
pub(crate) trait Sink: Write {
    fn ty(&mut self, tys: &Types, t: TyId);
    fn quoted(&mut self, s: &str);
}

impl Sink for String {
    fn ty(&mut self, tys: &Types, t: TyId) {
        tys.write(t, self);
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
    fn ty(&mut self, tys: &Types, t: TyId) {
        self.0 = self.0.saturating_add(tys.text_len(t));
    }

    fn quoted(&mut self, s: &str) {
        let mut text = String::new();
        parse::quote(s, &mut text);
        self.0 = self.0.saturating_add(text.len() as u64);
    }
}

/// `(<form> <field> ...)`: the fields come from `fields`, which writes each one.
pub(crate) fn node<S: Sink>(out: &mut S, form: &str, fields: impl FnOnce(&mut S)) {
    out.write_str("(").unwrap_or_default();
    out.write_str(form).unwrap_or_default();
    fields(out);
    out.write_str(")").unwrap_or_default();
}

/// `(<item> <item> ...)`.
pub(crate) fn list<S: Sink, T>(out: &mut S, items: &[T], mut each: impl FnMut(&T, &mut S)) {
    out.write_str("(").unwrap_or_default();
    for (k, item) in items.iter().enumerate() {
        if k > 0 {
            out.write_str(" ").unwrap_or_default();
        }
        each(item, out);
    }
    out.write_str(")").unwrap_or_default();
}

impl Value {
    /// The type of a value. A string, a type, and a tuple that holds them have no type.
    pub fn ty(&self, tys: &mut Types) -> Option<TyId> {
        #[cfg(test)]
        {
            tys.work += self.typing_nodes();
        }
        if !self.has_type() {
            return None;
        }
        let mut done = Vec::new();
        let mut work = vec![Build::Visit(self)];
        while let Some(step) = work.pop() {
            match step {
                Build::Visit(Value::Tuple(xs)) => {
                    work.push(Build::Tuple(xs.len()));
                    work.extend(xs.iter().rev().map(Build::Visit));
                }
                Build::Visit(v) => done.push(v.node_ty(tys)?),
                Build::Tuple(n) | Build::Array(_, n) => {
                    let parts = last(&mut done, n);
                    done.push(tys.tuple(parts));
                }
            }
        }
        done.pop()
    }

    /// Whether the value has a type: no string and no type is an element of it, also of a
    /// tuple in it. An array has the type of its elements, so the walk does not enter it.
    fn has_type(&self) -> bool {
        let mut work = vec![self];
        while let Some(v) = work.pop() {
            match v {
                Value::Str(_) | Value::Type(_) => return false,
                Value::Tuple(xs) => work.extend(xs),
                _ => {}
            }
        }
        true
    }

    /// The nodes that `has_type` visits, for the test of the work of a type.
    #[cfg(test)]
    fn typing_nodes(&self) -> u64 {
        let mut nodes = 0;
        let mut work = vec![self];
        while let Some(v) = work.pop() {
            nodes += 1;
            match v {
                Value::Str(_) | Value::Type(_) => return nodes,
                Value::Tuple(xs) => work.extend(xs),
                _ => {}
            }
        }
        nodes
    }

    /// The type of a value that is not a tuple.
    fn node_ty(&self, tys: &mut Types) -> Option<TyId> {
        match self {
            Value::Int(_) => Some(tys.mk(Ty::Int)),
            Value::Bool(_) => Some(tys.mk(Ty::Bool)),
            Value::UInt(x) => Some(tys.mk(Ty::UInt(x.width()))),
            Value::SInt(x) => Some(tys.mk(Ty::SInt(x.width()))),
            Value::Unit => Some(tys.mk(Ty::Unit)),
            Value::Array(elem, xs) => Some(tys.array(*elem, Int::from_u64(xs.len() as u64))),
            Value::Str(_) | Value::Type(_) | Value::Tuple(_) => None,
        }
    }

    /// A copy of a value that is not a container.
    fn clone_scalar(&self) -> Value {
        match self {
            Value::Int(n) => Value::Int(n.clone()),
            Value::Bool(b) => Value::Bool(*b),
            Value::Str(s) => Value::Str(s.clone()),
            Value::UInt(x) => Value::UInt(x.clone()),
            Value::SInt(x) => Value::SInt(x.clone()),
            Value::Type(t) => Value::Type(*t),
            Value::Unit | Value::Array(..) | Value::Tuple(_) => Value::Unit,
        }
    }

    /// The type of a scalar or `()`, as a node with no part.
    #[must_use]
    pub fn scalar_ty(&self) -> Option<Ty> {
        match self {
            Value::Int(_) => Some(Ty::Int),
            Value::Bool(_) => Some(Ty::Bool),
            Value::Unit => Some(Ty::Unit),
            _ => self.finite_ty(),
        }
    }

    /// The type of a finite value.
    #[must_use]
    pub fn finite_ty(&self) -> Option<Ty> {
        match self {
            Value::UInt(x) => Some(Ty::UInt(x.width())),
            Value::SInt(x) => Some(Ty::SInt(x.width())),
            _ => None,
        }
    }

    /// What the value is, for a message. Only a tuple has neither a type nor its own text.
    /// The text of a type stops after `TEXT_LIMIT` bytes.
    #[must_use]
    pub fn text(&self, tys: &Types) -> String {
        match self {
            Value::Str(_) => "a string".to_owned(),
            Value::Type(_) => "a type".to_owned(),
            v if !v.has_type() => "a tuple".to_owned(),
            v => {
                let mut out = Text::default();
                out.value(v);
                out.finish(tys)
            }
        }
    }

    /// The canonical serialization of section 7.1.
    #[must_use]
    pub fn serialize(&self, tys: &Types) -> String {
        let mut out = String::new();
        self.write(tys, &mut out);
        out
    }

    /// The length in bytes of `serialize`, without the text. The element type of an array
    /// and a type take their length from the table, so the walk is in the size of the value.
    #[must_use]
    pub fn serialized_len(&self, tys: &Types) -> u64 {
        let mut len = Len::default();
        self.write(tys, &mut len);
        len.0
    }

    /// The serialization into `out`. An element waits on the stack of the walk, so the walk
    /// does not recurse.
    fn write<S: Sink>(&self, tys: &Types, out: &mut S) {
        // `None` on the stack closes the innermost open container. `Some(v)` writes `v`, with
        // a space before it if it is not the first element of its container.
        let mut work = vec![Some(self)];
        let mut first = true;
        while let Some(item) = work.pop() {
            let Some(v) = item else {
                out.write_str("))").unwrap_or_default();
                first = false;
                continue;
            };
            if !first {
                out.write_str(" ").unwrap_or_default();
            }
            first = false;
            match v {
                Value::Array(elem, xs) => {
                    out.write_str("(array ").unwrap_or_default();
                    out.ty(tys, *elem);
                    out.write_str(" (").unwrap_or_default();
                    work.push(None);
                    work.extend(xs.iter().rev().map(Some));
                    first = true;
                }
                Value::Tuple(xs) => {
                    out.write_str("(tuple (").unwrap_or_default();
                    work.push(None);
                    work.extend(xs.iter().rev().map(Some));
                    first = true;
                }
                v => v.write_scalar(tys, out),
            }
        }
    }

    /// The serialization of a value that is not a container.
    fn write_scalar<S: Sink>(&self, tys: &Types, out: &mut S) {
        match self {
            Value::Int(n) => write!(out, "(int {n})").unwrap_or_default(),
            Value::Bool(b) => write!(out, "(bool {b})").unwrap_or_default(),
            Value::Str(s) => node(out, "string", |out| {
                out.write_str(" ").unwrap_or_default();
                out.quoted(s);
            }),
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
            Value::Type(t) => node(out, "type", |out| {
                out.write_str(" ").unwrap_or_default();
                out.ty(tys, *t);
            }),
            Value::Unit | Value::Array(..) | Value::Tuple(_) => {
                out.write_str("(unit)").unwrap_or_default();
            }
        }
    }

    /// The recursive size of section 5.4. A string counts characters, not bytes. A container
    /// has the size 1 plus the sizes of its elements, without the element type of an array.
    #[must_use]
    pub fn size(&self) -> u64 {
        let mut sum = 0u64;
        let mut work = vec![self];
        while let Some(v) = work.pop() {
            let own = match v {
                Value::Int(n) => int_size(n),
                Value::Bool(_) | Value::Unit => 1,
                Value::Str(s) => 1 + s.chars().count() as u64,
                Value::UInt(x) | Value::SInt(x) => width_size(x.width()),
                Value::Type(t) => t.size(),
                Value::Array(_, xs) | Value::Tuple(xs) => {
                    work.extend(xs);
                    1
                }
            };
            sum = sum.saturating_add(own);
        }
        sum
    }

    /// The depth of section 5.5: 1 for a scalar value, and 1 more than its deepest part. An
    /// array counts its element type, and a type is as deep as its term.
    #[must_use]
    pub fn depth(&self) -> u64 {
        let mut deepest = 0;
        let mut work = vec![(self, 0u64)];
        while let Some((v, above)) = work.pop() {
            let own = match v {
                Value::Type(t) => t.depth(),
                Value::Array(elem, xs) => {
                    work.extend(xs.iter().map(|x| (x, above + 1)));
                    1 + elem.depth()
                }
                Value::Tuple(xs) => {
                    work.extend(xs.iter().map(|x| (x, above + 1)));
                    1
                }
                _ => 1,
            };
            deepest = deepest.max(above + own);
        }
        deepest
    }

    /// The charge of the walk that measures the serialization, before the charge of its bytes
    /// (section 5.4). Each container charges 1. An integer and a finite value charge the
    /// square of their size, because a naive decimal conversion takes this time.
    #[must_use]
    pub fn measure_charge(&self) -> u128 {
        let mut sum = 0u128;
        let mut work = vec![self];
        while let Some(v) = work.pop() {
            sum += match v {
                Value::Int(_) | Value::UInt(_) | Value::SInt(_) => {
                    u128::from(v.size()) * u128::from(v.size())
                }
                Value::Array(_, xs) | Value::Tuple(xs) => {
                    work.extend(xs);
                    1
                }
                _ => 0,
            };
        }
        sum
    }
}

/// A static value with the table of the types that it names. Only together do they have a
/// serialization.
pub struct Evaluated {
    pub value: Value,
    pub types: Types,
    /// The steps of the walks along paths into values, for a test of their work.
    #[cfg(test)]
    pub(crate) steps: u64,
}

impl Evaluated {
    /// The canonical serialization of section 7.1.
    #[must_use]
    pub fn serialize(&self) -> String {
        self.value.serialize(&self.types)
    }

    /// The length in bytes of `serialize`, without the text.
    #[must_use]
    pub fn serialized_len(&self) -> u64 {
        self.value.serialized_len(&self.types)
    }
}

/// An `InstantiationId`: a module and its static arguments in order. Up to slice 5, the
/// package of each module is the root package `root`.
pub struct InstantiationId {
    pub module: String,
    pub args: Vec<Value>,
}

impl InstantiationId {
    /// The serialization from the serializations of the arguments.
    #[must_use]
    pub fn render(module: &str, args: &[String]) -> String {
        format!("(instantiation root {module} ({}))", args.join(" "))
    }

    /// The byte length of `render(module, args)` from the byte lengths `lens` of the
    /// arguments, known before the text exists.
    #[must_use]
    pub fn render_size(module: &str, lens: &[u64]) -> u64 {
        let mut bytes = 24 + module.len() as u64;
        for len in lens {
            bytes = bytes.saturating_add(*len);
        }
        bytes.saturating_add((lens.len() as u64).saturating_sub(1))
    }

    #[must_use]
    pub fn serialize(&self, tys: &Types) -> String {
        let args: Vec<String> = self.args.iter().map(|a| a.serialize(tys)).collect();
        InstantiationId::render(&self.module, &args)
    }
}

#[cfg(test)]
mod tests {
    //! The cases of `Silicon.Source.Test.Value` in Lean.

    use super::*;

    fn int(digits: &str) -> Value {
        let (neg, digits) = match digits.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, digits),
        };
        let n = Int::from_decimal(digits).unwrap();
        Value::Int(if neg { n.neg() } else { n })
    }

    fn uint(w: u32, v: u64) -> Value {
        Value::UInt(crate::int::finite(w, v).unwrap())
    }

    fn sint(w: u32, v: u64) -> Value {
        Value::SInt(crate::int::finite(w, v).unwrap())
    }

    fn id(module: &str, args: Vec<Value>) -> InstantiationId {
        InstantiationId {
            module: module.to_owned(),
            args,
        }
    }

    fn array_ty(tys: &mut Types, elem: TyId, len: u64) -> TyId {
        tys.array(elem, Int::from_u64(len))
    }

    #[test]
    fn serialization() {
        let tys = Types::default();
        assert_eq!(int("-5").serialize(&tys), "(int -5)");
        assert_eq!(int("0").serialize(&tys), "(int 0)");
        assert_eq!(
            int("18446744073709551616").serialize(&tys),
            "(int 18446744073709551616)"
        );
        assert_eq!(Value::Bool(true).serialize(&tys), "(bool true)");
        assert_eq!(Value::Bool(false).serialize(&tys), "(bool false)");
        assert_eq!(
            Value::Str("a\"b".to_owned()).serialize(&tys),
            "(string \"a\\\"b\")"
        );
        assert_eq!(
            Value::Str("\\\n\r\t".to_owned()).serialize(&tys),
            "(string \"\\\\\\n\\r\\t\")"
        );
        assert_eq!(Value::Str(String::new()).serialize(&tys), "(string \"\")");
        assert_eq!(
            id("Counter", vec![int("8")]).serialize(&tys),
            "(instantiation root Counter ((int 8)))"
        );
        assert_eq!(
            id("Fifo", vec![int("16"), Value::Bool(true)]).serialize(&tys),
            "(instantiation root Fifo ((int 16) (bool true)))"
        );
        assert_eq!(
            id("Top", vec![]).serialize(&tys),
            "(instantiation root Top ())"
        );
        for (module, args) in [
            ("Top", vec![]),
            ("Fifo", vec![int("16"), Value::Bool(true)]),
        ] {
            let parts: Vec<String> = args.iter().map(|a| a.serialize(&tys)).collect();
            let lens: Vec<u64> = args.iter().map(|a| a.serialized_len(&tys)).collect();
            let text = InstantiationId::render(module, &parts);
            assert_eq!(
                InstantiationId::render_size(module, &lens),
                text.len() as u64
            );
        }
    }

    #[test]
    fn finite_values_and_types() {
        let mut tys = Types::default();
        assert_eq!(uint(8, 255).serialize(&tys), "(uint 8 255)");
        assert_eq!(sint(8, 255).serialize(&tys), "(sint 8 -1)");
        assert_eq!(sint(8, 127).serialize(&tys), "(sint 8 127)");
        for (t, text) in [
            (Ty::Bool, "(type bool)"),
            (Ty::Nat, "(type nat)"),
            (Ty::Int, "(type int)"),
            (Ty::UInt(8), "(type (uint 8))"),
            (Ty::SInt(16), "(type (sint 16))"),
        ] {
            let t = tys.mk(t);
            assert_eq!(Value::Type(t).serialize(&tys), text);
        }
    }

    #[test]
    fn sizes_at_the_word_limits() {
        let mut tys = Types::default();
        assert_eq!(int("0").size(), 1);
        assert_eq!(int("1").size(), 1);
        assert_eq!(int("18446744073709551615").size(), 1);
        assert_eq!(int("18446744073709551616").size(), 2);
        assert_eq!(int("-18446744073709551615").size(), 1);
        assert_eq!(int("-18446744073709551616").size(), 2);
        assert_eq!(int("340282366920938463463374607431768211455").size(), 2);
        assert_eq!(int("340282366920938463463374607431768211456").size(), 3);
        assert_eq!(Value::Bool(true).size(), 1);
        assert_eq!(Value::Str(String::new()).size(), 1);
        assert_eq!(Value::Str("abc".to_owned()).size(), 4);
        assert_eq!(Value::Str("\u{e4}".to_owned()).size(), 2);
        assert_eq!(uint(64, 0).size(), 1);
        assert_eq!(sint(65, 0).size(), 2);
        let (b, u8t) = (tys.mk(Ty::Bool), tys.mk(Ty::UInt(8)));
        assert_eq!(Value::Type(b).size(), 1);
        assert_eq!(Value::Type(u8t).size(), 2);
        assert_eq!(int("18446744073709551616").measure_charge(), 4);
        assert_eq!(Value::Str("abc".to_owned()).measure_charge(), 0);
    }

    #[test]
    fn container_serialization() {
        let mut tys = Types::default();
        let (b, u8t) = (tys.mk(Ty::Bool), tys.mk(Ty::UInt(8)));
        let ser = |tys: &Types, v: &Value| v.serialize(tys);
        assert_eq!(ser(&tys, &Value::Unit), "(unit)");
        assert_eq!(
            ser(&tys, &Value::Array(u8t, vec![uint(8, 1), uint(8, 2)])),
            "(array (uint 8) ((uint 8 1) (uint 8 2)))"
        );
        assert_eq!(ser(&tys, &Value::Array(b, vec![])), "(array bool ())");
        assert_eq!(
            ser(&tys, &Value::Tuple(vec![int("1"), Value::Bool(true)])),
            "(tuple ((int 1) (bool true)))"
        );
        assert_eq!(
            ser(&tys, &Value::Tuple(vec![Value::Unit])),
            "(tuple ((unit)))"
        );
        let arr = array_ty(&mut tys, u8t, 4);
        assert_eq!(ser(&tys, &Value::Type(arr)), "(type (array (uint 8) 4))");
        let tup = tys.tuple(vec![b, u8t]);
        assert_eq!(
            ser(&tys, &Value::Type(tup)),
            "(type (tuple (bool (uint 8))))"
        );
        let unit = tys.mk(Ty::Unit);
        assert_eq!(ser(&tys, &Value::Type(unit)), "(type unit)");
        let bool2 = array_ty(&mut tys, b, 2);
        assert_eq!(
            ser(
                &tys,
                &Value::Array(
                    bool2,
                    vec![Value::Array(b, vec![Value::Bool(true), Value::Bool(false)])]
                )
            ),
            "(array (array bool 2) ((array bool ((bool true) (bool false)))))"
        );
        assert_eq!(
            id("Top", vec![Value::Tuple(vec![int("1")]), Value::Unit]).serialize(&tys),
            "(instantiation root Top ((tuple ((int 1))) (unit)))"
        );
    }

    #[test]
    fn the_length_of_a_serialization_needs_no_text() {
        let mut tys = Types::default();
        let (b, i) = (tys.mk(Ty::Bool), tys.mk(Ty::Int));
        let wide = tys.tuple(vec![i; 40]);
        let arr = array_ty(&mut tys, wide, 0);
        let vs = [
            Value::Array(
                arr,
                vec![Value::Array(wide, vec![]), Value::Array(wide, vec![])],
            ),
            Value::Type(arr),
            Value::Tuple(vec![
                Value::Str("a\"".to_owned()),
                int("-12"),
                Value::Array(b, vec![]),
            ]),
            uint(70, 5),
        ];
        for v in &vs {
            assert_eq!(v.serialized_len(&tys), v.serialize(&tys).len() as u64);
        }
    }

    #[test]
    fn container_texts_and_types() {
        let mut tys = Types::default();
        let (b, i, u8t) = (tys.mk(Ty::Bool), tys.mk(Ty::Int), tys.mk(Ty::UInt(8)));
        let unit = tys.mk(Ty::Unit);
        assert_eq!(tys.text(unit), "Unit");
        let arr = array_ty(&mut tys, u8t, 4);
        assert_eq!(tys.text(arr), "[UInt[8]; 4]");
        let one = tys.tuple(vec![b]);
        assert_eq!(tys.text(one), "(Bool,)");
        let int2 = array_ty(&mut tys, i, 2);
        let two = tys.tuple(vec![b, int2]);
        assert_eq!(tys.text(two), "(Bool, [Int; 2])");
        let pair = Value::Tuple(vec![int("1"), Value::Bool(true)]);
        let pair_ty = tys.tuple(vec![i, b]);
        assert_eq!(pair.ty(&mut tys), Some(pair_ty));
        let empty = Value::Array(b, vec![]);
        let empty_ty = array_ty(&mut tys, b, 0);
        assert_eq!(empty.ty(&mut tys), Some(empty_ty));
        let strings = Value::Tuple(vec![Value::Str("a".to_owned())]);
        assert_eq!(strings.ty(&mut tys), None);
        assert_eq!(strings.text(&tys), "a tuple");
        assert_eq!(pair.text(&tys), "(Int, Bool)");
    }

    #[test]
    fn container_equality_is_structural() {
        let mut tys = Types::default();
        let (b, i) = (tys.mk(Ty::Bool), tys.mk(Ty::Int));
        assert_ne!(Value::Array(b, vec![]), Value::Array(i, vec![]));
        assert_ne!(
            Value::Tuple(vec![int("1")]),
            Value::Array(i, vec![int("1")])
        );
        assert_eq!(
            Value::Tuple(vec![uint(8, 1)]),
            Value::Tuple(vec![uint(8, 1)])
        );
        assert_ne!(uint(8, 1), uint(16, 1));
        let tup = tys.tuple(vec![b]);
        let arr = array_ty(&mut tys, b, 1);
        assert_ne!(tup, arr);
    }

    #[test]
    fn equal_types_have_one_id() {
        let mut tys = Types::default();
        let (b, u8t) = (tys.mk(Ty::Bool), tys.mk(Ty::UInt(8)));
        let first = tys.tuple(vec![b, u8t]);
        let again = tys.tuple(vec![b, u8t]);
        assert_eq!(first, again);
        assert_ne!(first, tys.tuple(vec![u8t, b]));
        let a = array_ty(&mut tys, first, 3);
        assert_eq!(a, array_ty(&mut tys, again, 3));
        assert_ne!(a, array_ty(&mut tys, first, 4));
    }

    #[test]
    fn container_sizes() {
        let mut tys = Types::default();
        let (b, i, u8t) = (tys.mk(Ty::Bool), tys.mk(Ty::Int), tys.mk(Ty::UInt(8)));
        let unit = tys.mk(Ty::Unit);
        let _ = i;
        assert_eq!(Value::Unit.size(), 1);
        assert_eq!(Value::Type(unit).size(), 1);
        assert_eq!(Value::Array(b, vec![]).size(), 1);
        assert_eq!(Value::Array(u8t, vec![uint(8, 1), uint(8, 2)]).size(), 3);
        assert_eq!(
            Value::Tuple(vec![int("1"), Value::Str("ab".to_owned())]).size(),
            5
        );
        let arr = array_ty(&mut tys, u8t, 4);
        assert_eq!(Value::Type(arr).size(), 4);
        let tup = tys.tuple(vec![b, u8t]);
        assert_eq!(Value::Type(tup).size(), 4);
        let long = Int::from_decimal("18446744073709551616").unwrap();
        let big = tys.array(b, long);
        assert_eq!(Value::Type(big).size(), 4);
    }

    /// The nested doubling of section 5.5: `a_k = [a_(k-1), a_(k-1)]`.
    fn doubling(tys: &mut Types, k: u32) -> Value {
        if k == 0 {
            let b = tys.mk(Ty::Bool);
            return Value::Array(b, vec![Value::Bool(true), Value::Bool(false)]);
        }
        let below = doubling(tys, k - 1);
        let elem = below.ty(tys).unwrap();
        Value::Array(elem, vec![below.clone(), below])
    }

    #[test]
    fn nested_doubling_size_and_depth() {
        let mut tys = Types::default();
        for k in 0..8 {
            let v = doubling(&mut tys, k);
            assert_eq!(v.size(), (1 << (k + 2)) - 1);
            assert_eq!(v.depth(), u64::from(k) + 2);
        }
    }

    #[test]
    fn depths() {
        let mut tys = Types::default();
        let (b, i, u8t) = (tys.mk(Ty::Bool), tys.mk(Ty::Int), tys.mk(Ty::UInt(8)));
        assert_eq!(int("5").depth(), 1);
        assert_eq!(Value::Unit.depth(), 1);
        assert_eq!(Value::Type(u8t).depth(), 1);
        let inner = array_ty(&mut tys, b, 2);
        let outer = array_ty(&mut tys, inner, 3);
        assert_eq!(Value::Type(outer).depth(), 3);
        let tup_int = tys.tuple(vec![i]);
        let tup = tys.tuple(vec![b, tup_int]);
        assert_eq!(Value::Type(tup).depth(), 3);
        assert_eq!(
            Value::Tuple(vec![Value::Tuple(vec![int("1")]), Value::Bool(true)]).depth(),
            3
        );
        assert_eq!(Value::Array(b, vec![]).depth(), 2);
        let zero = array_ty(&mut tys, b, 0);
        assert_eq!(Value::Array(zero, vec![]).depth(), 3);
    }

    #[test]
    fn measure_charges() {
        let mut tys = Types::default();
        let (b, u8t) = (tys.mk(Ty::Bool), tys.mk(Ty::UInt(8)));
        assert_eq!(int("5").measure_charge(), 1);
        assert_eq!(sint(65, 0).measure_charge(), 4);
        assert_eq!(Value::Bool(true).measure_charge(), 0);
        let arr = array_ty(&mut tys, u8t, 4);
        assert_eq!(Value::Type(arr).measure_charge(), 0);
        assert_eq!(Value::Unit.measure_charge(), 0);
        assert_eq!(Value::Array(b, vec![]).measure_charge(), 1);
        assert_eq!(
            Value::Array(u8t, vec![uint(8, 1), uint(8, 2)]).measure_charge(),
            3
        );
        assert_eq!(
            Value::Tuple(vec![
                int("18446744073709551616"),
                Value::Tuple(vec![Value::Bool(true)])
            ])
            .measure_charge(),
            6
        );
    }

    /// A value as deep as a long loop can make it drops without a deep recursion, and a deep
    /// type has depth and size with no walk.
    #[test]
    fn a_deep_value_drops_without_recursion() {
        let mut tys = Types::default();
        let mut v = Value::Unit;
        let mut t = tys.mk(Ty::Unit);
        for _ in 0..1_000_000 {
            v = Value::Tuple(vec![v]);
            t = tys.tuple(vec![t]);
        }
        assert_eq!(t.depth(), 1_000_001);
        drop(v);
    }
}
