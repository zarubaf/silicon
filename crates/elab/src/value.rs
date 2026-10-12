// SPDX-License-Identifier: Apache-2.0
//! The static values of slice 1 and the static containers of slice 2, their canonical
//! serialization, their recursive size, and their depth, as Lean `Source.Value` defines them.
//! Section 7.1 of the front-end spec uses the serialization in an `InstantiationId`, section
//! 5.4 uses the size in the cost model, and section 5.5 bounds the depth.
//!
//! A container nests as deep as the nesting depth allows, and that limit is a budget. Thus a
//! value drops without recursion, and no walk here recurses deeper than the value is deep.

use crate::int::Int;
use core_ir::Bits;
use std::fmt::Write;

/// A type as a static value: the scalar types of slice 1 with a width from 1 to 65536, `()`,
/// and the container types. A tuple type has at least one element type: `()` is `Unit`. The
/// length of an array type is any natural number, as the type does not hold the elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Nat,
    Int,
    UInt(u32),
    SInt(u32),
    Unit,
    Array(Box<Ty>, Int),
    Tuple(Vec<Ty>),
}

/// A static value of slice 1, or a static container of slice 2. A finite value holds the bit
/// vector of the core semantics with the width of its type. An array keeps its element type,
/// so an empty array has a type. A tuple has at least one element: `()` is `Unit`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(Int),
    Bool(bool),
    Str(String),
    UInt(Bits),
    SInt(Bits),
    Type(Ty),
    Unit,
    Array(Box<Ty>, Vec<Value>),
    Tuple(Vec<Value>),
}

impl Ty {
    fn take_children(&mut self, work: &mut Vec<Ty>) {
        match self {
            Ty::Array(elem, _) => work.push(std::mem::replace(&mut **elem, Ty::Bool)),
            Ty::Tuple(elems) => work.append(elems),
            Ty::Bool | Ty::Nat | Ty::Int | Ty::UInt(_) | Ty::SInt(_) | Ty::Unit => {}
        }
    }
}

impl Drop for Ty {
    fn drop(&mut self) {
        let mut work = Vec::new();
        self.take_children(&mut work);
        while let Some(mut t) = work.pop() {
            t.take_children(&mut work);
        }
    }
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

fn width_int(width: u32) -> Int {
    Int::from_u64(u64::from(width))
}

/// `(<form> <field> ...)`: the fields come from `fields`, which writes each one.
fn node(out: &mut String, form: &str, fields: impl FnOnce(&mut String)) {
    out.push('(');
    out.push_str(form);
    fields(out);
    out.push(')');
}

/// `(<item> <item> ...)`.
fn list<T>(out: &mut String, items: &[T], mut each: impl FnMut(&T, &mut String)) {
    out.push('(');
    for (k, item) in items.iter().enumerate() {
        if k > 0 {
            out.push(' ');
        }
        each(item, out);
    }
    out.push(')');
}

impl Ty {
    /// `UInt[W]` or `SInt[W]`.
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Ty::UInt(_) | Ty::SInt(_))
    }

    #[must_use]
    pub fn serialize(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out
    }

    fn write(&self, out: &mut String) {
        match self {
            Ty::Bool => out.push_str("bool"),
            Ty::Nat => out.push_str("nat"),
            Ty::Int => out.push_str("int"),
            Ty::Unit => out.push_str("unit"),
            Ty::UInt(w) => write!(out, "(uint {w})").unwrap_or_default(),
            Ty::SInt(w) => write!(out, "(sint {w})").unwrap_or_default(),
            Ty::Array(elem, len) => node(out, "array", |out| {
                out.push(' ');
                elem.write(out);
                write!(out, " {len}").unwrap_or_default();
            }),
            Ty::Tuple(elems) => node(out, "tuple", |out| {
                out.push(' ');
                list(out, elems, Ty::write);
            }),
        }
    }

    /// The number of nodes of the type term, plus the size of each integer in it.
    #[must_use]
    pub fn size(&self) -> u64 {
        match self {
            Ty::Bool | Ty::Nat | Ty::Int | Ty::Unit => 1,
            Ty::UInt(w) | Ty::SInt(w) => 1 + int_size(&width_int(*w)),
            Ty::Array(elem, len) => 1 + elem.size() + int_size(len),
            Ty::Tuple(elems) => 1 + elems.iter().map(Ty::size).sum::<u64>(),
        }
    }

    /// The depth of section 5.5: 1 for a scalar type, and 1 more than its deepest part.
    #[must_use]
    pub fn depth(&self) -> u64 {
        match self {
            Ty::Array(elem, _) => 1 + elem.depth(),
            Ty::Tuple(elems) => 1 + elems.iter().map(Ty::depth).max().unwrap_or(0),
            _ => 1,
        }
    }

    /// The source form, for a message.
    #[must_use]
    pub fn text(&self) -> String {
        match self {
            Ty::Bool => "Bool".to_owned(),
            Ty::Nat => "Nat".to_owned(),
            Ty::Int => "Int".to_owned(),
            Ty::Unit => "Unit".to_owned(),
            Ty::UInt(w) => format!("UInt[{w}]"),
            Ty::SInt(w) => format!("SInt[{w}]"),
            Ty::Array(elem, len) => format!("[{}; {len}]", elem.text()),
            Ty::Tuple(elems) if elems.len() == 1 => {
                let first = elems.first().map(Ty::text).unwrap_or_default();
                format!("({first},)")
            }
            Ty::Tuple(elems) => {
                let parts: Vec<String> = elems.iter().map(Ty::text).collect();
                format!("({})", parts.join(", "))
            }
        }
    }
}

impl Value {
    /// The type of a value. A string, a type, and a tuple that holds them have no `Ty`.
    #[must_use]
    pub fn ty(&self) -> Option<Ty> {
        match self {
            Value::Int(_) => Some(Ty::Int),
            Value::Bool(_) => Some(Ty::Bool),
            Value::UInt(x) => Some(Ty::UInt(x.width())),
            Value::SInt(x) => Some(Ty::SInt(x.width())),
            Value::Unit => Some(Ty::Unit),
            Value::Array(elem, xs) => Some(Ty::Array(elem.clone(), Int::from_u64(xs.len() as u64))),
            Value::Tuple(xs) => xs
                .iter()
                .map(Value::ty)
                .collect::<Option<Vec<Ty>>>()
                .map(Ty::Tuple),
            Value::Str(_) | Value::Type(_) => None,
        }
    }

    /// The type of a finite value.
    #[must_use]
    pub fn finite_ty(&self) -> Option<Ty> {
        match self {
            Value::UInt(_) | Value::SInt(_) => self.ty(),
            _ => None,
        }
    }

    /// What the value is, for a message. Only a tuple has neither a `Ty` nor its own text.
    #[must_use]
    pub fn text(&self) -> String {
        match self {
            Value::Str(_) => "a string".to_owned(),
            Value::Type(_) => "a type".to_owned(),
            v => v.ty().map_or_else(|| "a tuple".to_owned(), |t| t.text()),
        }
    }

    /// The canonical serialization of section 7.1.
    #[must_use]
    pub fn serialize(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out
    }

    pub(crate) fn write(&self, out: &mut String) {
        match self {
            Value::Int(n) => write!(out, "(int {n})").unwrap_or_default(),
            Value::Bool(b) => write!(out, "(bool {b})").unwrap_or_default(),
            Value::Str(s) => node(out, "string", |out| {
                out.push(' ');
                parse::quote(s, out);
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
                out.push(' ');
                t.write(out);
            }),
            Value::Unit => out.push_str("(unit)"),
            Value::Array(elem, xs) => node(out, "array", |out| {
                out.push(' ');
                elem.write(out);
                out.push(' ');
                list(out, xs, Value::write);
            }),
            Value::Tuple(xs) => node(out, "tuple", |out| {
                out.push(' ');
                list(out, xs, Value::write);
            }),
        }
    }

    /// The recursive size of section 5.4. A string counts characters, not bytes. A container
    /// has the size 1 plus the sizes of its elements, without the element type of an array.
    #[must_use]
    pub fn size(&self) -> u64 {
        match self {
            Value::Int(n) => int_size(n),
            Value::Bool(_) | Value::Unit => 1,
            Value::Str(s) => 1 + s.chars().count() as u64,
            Value::UInt(x) | Value::SInt(x) => width_size(x.width()),
            Value::Type(t) => t.size(),
            Value::Array(_, xs) | Value::Tuple(xs) => 1 + xs.iter().map(Value::size).sum::<u64>(),
        }
    }

    /// The depth of section 5.5: 1 for a scalar value, and 1 more than its deepest part. An
    /// array counts its element type, and a type is as deep as its term.
    #[must_use]
    pub fn depth(&self) -> u64 {
        match self {
            Value::Type(t) => t.depth(),
            Value::Array(elem, xs) => 1 + xs.iter().map(Value::depth).fold(elem.depth(), u64::max),
            Value::Tuple(xs) => 1 + xs.iter().map(Value::depth).max().unwrap_or(0),
            _ => 1,
        }
    }

    /// The charge of the walk that measures the serialization, before the charge of its bytes
    /// (section 5.4). Each container charges 1. An integer and a finite value charge the
    /// square of their size, because a naive decimal conversion takes this time.
    #[must_use]
    pub fn measure_charge(&self) -> u128 {
        match self {
            Value::Int(_) | Value::UInt(_) | Value::SInt(_) => {
                u128::from(self.size()) * u128::from(self.size())
            }
            Value::Array(_, xs) | Value::Tuple(xs) => {
                1 + xs.iter().map(Value::measure_charge).sum::<u128>()
            }
            _ => 0,
        }
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

    /// The byte length of `render(module, args)`, known before the text exists.
    #[must_use]
    pub fn render_size(module: &str, args: &[String]) -> u64 {
        let mut bytes = 24 + module.len() as u64;
        for arg in args {
            bytes += arg.len() as u64;
        }
        bytes + (args.len() as u64).saturating_sub(1)
    }

    #[must_use]
    pub fn serialize(&self) -> String {
        let args: Vec<String> = self.args.iter().map(Value::serialize).collect();
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

    #[test]
    fn serialization() {
        assert_eq!(int("-5").serialize(), "(int -5)");
        assert_eq!(int("0").serialize(), "(int 0)");
        assert_eq!(
            int("18446744073709551616").serialize(),
            "(int 18446744073709551616)"
        );
        assert_eq!(Value::Bool(true).serialize(), "(bool true)");
        assert_eq!(Value::Bool(false).serialize(), "(bool false)");
        assert_eq!(
            Value::Str("a\"b".to_owned()).serialize(),
            "(string \"a\\\"b\")"
        );
        assert_eq!(
            Value::Str("\\\n\r\t".to_owned()).serialize(),
            "(string \"\\\\\\n\\r\\t\")"
        );
        assert_eq!(Value::Str(String::new()).serialize(), "(string \"\")");
        assert_eq!(
            id("Counter", vec![int("8")]).serialize(),
            "(instantiation root Counter ((int 8)))"
        );
        assert_eq!(
            id("Fifo", vec![int("16"), Value::Bool(true)]).serialize(),
            "(instantiation root Fifo ((int 16) (bool true)))"
        );
        assert_eq!(id("Top", vec![]).serialize(), "(instantiation root Top ())");
        for (module, args) in [
            ("Top", vec![]),
            ("Fifo", vec![int("16"), Value::Bool(true)]),
        ] {
            let parts: Vec<String> = args.iter().map(Value::serialize).collect();
            let text = InstantiationId::render(module, &parts);
            assert_eq!(
                InstantiationId::render_size(module, &parts),
                text.len() as u64
            );
        }
    }

    #[test]
    fn finite_values_and_types() {
        assert_eq!(uint(8, 255).serialize(), "(uint 8 255)");
        assert_eq!(sint(8, 255).serialize(), "(sint 8 -1)");
        assert_eq!(sint(8, 127).serialize(), "(sint 8 127)");
        assert_eq!(Value::Type(Ty::Bool).serialize(), "(type bool)");
        assert_eq!(Value::Type(Ty::Nat).serialize(), "(type nat)");
        assert_eq!(Value::Type(Ty::Int).serialize(), "(type int)");
        assert_eq!(Value::Type(Ty::UInt(8)).serialize(), "(type (uint 8))");
        assert_eq!(Value::Type(Ty::SInt(16)).serialize(), "(type (sint 16))");
    }

    #[test]
    fn sizes_at_the_word_limits() {
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
        assert_eq!(Value::Str("ä".to_owned()).size(), 2);
        assert_eq!(uint(64, 0).size(), 1);
        assert_eq!(sint(65, 0).size(), 2);
        assert_eq!(Value::Type(Ty::Bool).size(), 1);
        assert_eq!(Value::Type(Ty::UInt(8)).size(), 2);
        assert_eq!(int("18446744073709551616").measure_charge(), 4);
        assert_eq!(Value::Str("abc".to_owned()).measure_charge(), 0);
    }

    fn array(elem: Ty, xs: Vec<Value>) -> Value {
        Value::Array(Box::new(elem), xs)
    }

    fn array_ty(elem: Ty, len: u64) -> Ty {
        Ty::Array(Box::new(elem), Int::from_u64(len))
    }

    #[test]
    fn container_serialization() {
        assert_eq!(Value::Unit.serialize(), "(unit)");
        assert_eq!(
            array(Ty::UInt(8), vec![uint(8, 1), uint(8, 2)]).serialize(),
            "(array (uint 8) ((uint 8 1) (uint 8 2)))"
        );
        assert_eq!(array(Ty::Bool, vec![]).serialize(), "(array bool ())");
        assert_eq!(
            Value::Tuple(vec![int("1"), Value::Bool(true)]).serialize(),
            "(tuple ((int 1) (bool true)))"
        );
        assert_eq!(
            Value::Tuple(vec![Value::Unit]).serialize(),
            "(tuple ((unit)))"
        );
        assert_eq!(
            Value::Type(array_ty(Ty::UInt(8), 4)).serialize(),
            "(type (array (uint 8) 4))"
        );
        assert_eq!(
            Value::Type(Ty::Tuple(vec![Ty::Bool, Ty::UInt(8)])).serialize(),
            "(type (tuple (bool (uint 8))))"
        );
        assert_eq!(Value::Type(Ty::Unit).serialize(), "(type unit)");
        assert_eq!(
            array(
                array_ty(Ty::Bool, 2),
                vec![array(Ty::Bool, vec![Value::Bool(true), Value::Bool(false)])]
            )
            .serialize(),
            "(array (array bool 2) ((array bool ((bool true) (bool false)))))"
        );
        assert_eq!(
            id("Top", vec![Value::Tuple(vec![int("1")]), Value::Unit]).serialize(),
            "(instantiation root Top ((tuple ((int 1))) (unit)))"
        );
    }

    #[test]
    fn container_texts_and_types() {
        assert_eq!(Ty::Unit.text(), "Unit");
        assert_eq!(array_ty(Ty::UInt(8), 4).text(), "[UInt[8]; 4]");
        assert_eq!(Ty::Tuple(vec![Ty::Bool]).text(), "(Bool,)");
        assert_eq!(
            Ty::Tuple(vec![Ty::Bool, array_ty(Ty::Int, 2)]).text(),
            "(Bool, [Int; 2])"
        );
        assert_eq!(
            Value::Tuple(vec![int("1"), Value::Bool(true)]).ty(),
            Some(Ty::Tuple(vec![Ty::Int, Ty::Bool]))
        );
        assert_eq!(array(Ty::Bool, vec![]).ty(), Some(array_ty(Ty::Bool, 0)));
        let strings = Value::Tuple(vec![Value::Str("a".to_owned())]);
        assert_eq!(strings.ty(), None);
        assert_eq!(strings.text(), "a tuple");
    }

    #[test]
    fn container_equality_is_structural() {
        assert_ne!(array(Ty::Bool, vec![]), array(Ty::Int, vec![]));
        assert_ne!(Value::Tuple(vec![int("1")]), array(Ty::Int, vec![int("1")]));
        assert_eq!(
            Value::Tuple(vec![uint(8, 1)]),
            Value::Tuple(vec![uint(8, 1)])
        );
        assert_ne!(uint(8, 1), uint(16, 1));
        assert_ne!(Ty::Tuple(vec![Ty::Bool]), array_ty(Ty::Bool, 1));
    }

    #[test]
    fn container_sizes() {
        assert_eq!(Value::Unit.size(), 1);
        assert_eq!(Value::Type(Ty::Unit).size(), 1);
        assert_eq!(array(Ty::Bool, vec![]).size(), 1);
        assert_eq!(array(Ty::UInt(8), vec![uint(8, 1), uint(8, 2)]).size(), 3);
        assert_eq!(
            Value::Tuple(vec![int("1"), Value::Str("ab".to_owned())]).size(),
            5
        );
        assert_eq!(Value::Type(array_ty(Ty::UInt(8), 4)).size(), 4);
        assert_eq!(
            Value::Type(Ty::Tuple(vec![Ty::Bool, Ty::UInt(8)])).size(),
            4
        );
        let long = Int::from_decimal("18446744073709551616").unwrap();
        assert_eq!(Value::Type(Ty::Array(Box::new(Ty::Bool), long)).size(), 4);
    }

    /// The nested doubling of section 5.5: `a_k = [a_(k-1), a_(k-1)]`.
    fn doubling(k: u32) -> Value {
        if k == 0 {
            return array(Ty::Bool, vec![Value::Bool(true), Value::Bool(false)]);
        }
        let below = doubling(k - 1);
        let elem = below.ty().unwrap();
        array(elem, vec![below.clone(), below])
    }

    #[test]
    fn nested_doubling_size_and_depth() {
        for k in 0..8 {
            assert_eq!(doubling(k).size(), (1 << (k + 2)) - 1);
            assert_eq!(doubling(k).depth(), u64::from(k) + 2);
        }
    }

    #[test]
    fn depths() {
        assert_eq!(int("5").depth(), 1);
        assert_eq!(Value::Unit.depth(), 1);
        assert_eq!(Value::Type(Ty::UInt(8)).depth(), 1);
        assert_eq!(Value::Type(array_ty(array_ty(Ty::Bool, 2), 3)).depth(), 3);
        assert_eq!(
            Value::Type(Ty::Tuple(vec![Ty::Bool, Ty::Tuple(vec![Ty::Int])])).depth(),
            3
        );
        assert_eq!(
            Value::Tuple(vec![Value::Tuple(vec![int("1")]), Value::Bool(true)]).depth(),
            3
        );
        assert_eq!(array(Ty::Bool, vec![]).depth(), 2);
        assert_eq!(array(array_ty(Ty::Bool, 0), vec![]).depth(), 3);
    }

    #[test]
    fn measure_charges() {
        assert_eq!(int("5").measure_charge(), 1);
        assert_eq!(sint(65, 0).measure_charge(), 4);
        assert_eq!(Value::Bool(true).measure_charge(), 0);
        assert_eq!(Value::Type(array_ty(Ty::UInt(8), 4)).measure_charge(), 0);
        assert_eq!(Value::Unit.measure_charge(), 0);
        assert_eq!(array(Ty::Bool, vec![]).measure_charge(), 1);
        assert_eq!(
            array(Ty::UInt(8), vec![uint(8, 1), uint(8, 2)]).measure_charge(),
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

    /// A value as deep as a long loop can make it drops without a deep recursion, and so does
    /// a deep type.
    #[test]
    fn a_deep_value_drops_without_recursion() {
        let mut v = Value::Unit;
        let mut t = Ty::Unit;
        for _ in 0..1_000_000 {
            v = Value::Tuple(vec![v]);
            t = Ty::Tuple(vec![t]);
        }
        drop(v);
        drop(t);
    }
}
