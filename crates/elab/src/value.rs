// SPDX-License-Identifier: Apache-2.0
//! The static values of slice 1 and the static containers, types, records, strings, and lists of slice 2,
//! their canonical serialization, their recursive size, and their depth, as Lean
//! `Source.Value` defines them. Section 7.1 of the front-end spec uses the serialization in an
//! `InstantiationId`, section 5.4 uses the size in the cost model, and section 5.5 bounds the
//! depth.
//!
//! A container nests as deep as the nesting depth allows, and that limit is a budget. Thus no
//! walk over a value or a type recurses: each one keeps its own stack, so it runs on any
//! thread, also after the evaluator ends.

use crate::int::Int;
use crate::serial::{self, Item, Len};
use crate::text::Text;
use crate::types::{Ty, TyId, Types};
use core_ir::Bits;
use std::fmt;
use std::hash::Hasher;

/// A static value of slice 1, or a static container of slice 2. A finite value holds the bit
/// vector of the core semantics with the width of its type. An array keeps its element type,
/// so an empty array has a type, and a record keeps its struct type for the same reason. A
/// list keeps its element type too. A tuple has at least one element: `()` is `Unit`. A
/// function value is the item that the name refers to and the id of its signature, which is
/// its type. The table `Types` keeps the name of the item, so a copy of the value is constant
/// work. A tuple keeps the function flag of its type, which it reads from its elements once,
/// at its construction (`Value::tuple`). A write to an element keeps the type of the element,
/// so it keeps the flag.
pub enum Value {
    Int(Int),
    Bool(bool),
    Str(String),
    UInt(Bits),
    SInt(Bits),
    Type(TyId),
    Unit,
    Array(TyId, Vec<Value>),
    Tuple(bool, Vec<Value>),
    Record(TyId, Vec<Value>),
    List(TyId, Vec<Value>),
    Function(usize, TyId),
}

impl Value {
    /// The tuple of `elems`, with the function flag of its type. Each element answers in
    /// constant work, so the cost of the flag is in the construction, which already visits
    /// each element.
    #[must_use]
    pub fn tuple(elems: Vec<Value>) -> Value {
        Value::Tuple(elems.iter().any(Value::holds_fn), elems)
    }

    fn take_children(&mut self, work: &mut Vec<Value>) {
        match self {
            Value::Array(_, elems)
            | Value::Tuple(_, elems)
            | Value::Record(_, elems)
            | Value::List(_, elems) => {
                work.append(elems);
            }
            Value::Int(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::UInt(_)
            | Value::SInt(_)
            | Value::Type(_)
            | Value::Function(..)
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

/// The derived `Debug` would recurse over a deep value, and a failed assertion prints one. This
/// one keeps its own stack and prints a type by its index in the table.
impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[derive(Clone, Copy)]
        enum Piece<'a> {
            Value(&'a Value),
            Text(&'static str),
        }
        let mut work = vec![Piece::Value(self)];
        while let Some(piece) = work.pop() {
            let Piece::Value(v) = piece else {
                if let Piece::Text(text) = piece {
                    f.write_str(text)?;
                }
                continue;
            };
            match v {
                Value::Int(n) => write!(f, "Int({n})")?,
                Value::Bool(b) => write!(f, "Bool({b})")?,
                Value::Str(s) => write!(f, "Str({s:?})")?,
                Value::UInt(x) => write!(f, "UInt({x:?})")?,
                Value::SInt(x) => write!(f, "SInt({x:?})")?,
                Value::Type(t) => write!(f, "Type({t:?})")?,
                Value::Unit => f.write_str("Unit")?,
                Value::Function(i, t) => write!(f, "Function({i}, {t:?})")?,
                Value::Array(t, xs) | Value::Record(t, xs) | Value::List(t, xs) => {
                    let form = match v {
                        Value::Array(..) => "Array",
                        Value::Record(..) => "Record",
                        _ => "List",
                    };
                    write!(f, "{form}({t:?}, [")?;
                    work.push(Piece::Text("])"));
                    push_each(&mut work, xs, Piece::Value, Piece::Text(", "));
                }
                Value::Tuple(_, xs) => {
                    f.write_str("Tuple([")?;
                    work.push(Piece::Text("])"));
                    push_each(&mut work, xs, Piece::Value, Piece::Text(", "));
                }
            }
        }
        Ok(())
    }
}

/// Pushes the pieces of `xs` so that they come off the stack in order with `sep` between.
fn push_each<'a, P>(work: &mut Vec<P>, xs: &'a [Value], piece: fn(&'a Value) -> P, sep: P)
where
    P: Clone,
{
    for (k, x) in xs.iter().enumerate().rev() {
        work.push(piece(x));
        if k > 0 {
            work.push(sep.clone());
        }
    }
}

/// A step of a walk that builds a container after its elements: visit a value, or make a
/// container of the last `n` results.
enum Build<'a> {
    Visit(&'a Value),
    Array(TyId, usize),
    Tuple(usize),
    Record(TyId, usize),
    List(TyId, usize),
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
                Build::Visit(Value::Tuple(_, xs)) => {
                    work.push(Build::Tuple(xs.len()));
                    work.extend(xs.iter().rev().map(Build::Visit));
                }
                Build::Visit(Value::Record(t, xs)) => {
                    work.push(Build::Record(*t, xs.len()));
                    work.extend(xs.iter().rev().map(Build::Visit));
                }
                Build::Visit(Value::List(t, xs)) => {
                    work.push(Build::List(*t, xs.len()));
                    work.extend(xs.iter().rev().map(Build::Visit));
                }
                Build::Visit(v) => done.push(v.clone_scalar()),
                Build::Array(t, n) => {
                    let xs = last(&mut done, n);
                    done.push(Value::Array(t, xs));
                }
                Build::Tuple(n) => {
                    let xs = last(&mut done, n);
                    done.push(Value::tuple(xs));
                }
                Build::Record(t, n) => {
                    let xs = last(&mut done, n);
                    done.push(Value::Record(t, xs));
                }
                Build::List(t, n) => {
                    let xs = last(&mut done, n);
                    done.push(Value::List(t, xs));
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
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Compared, 1);
            let same = match pair {
                (Value::Array(s, xs), Value::Array(t, ys))
                | (Value::Record(s, xs), Value::Record(t, ys))
                | (Value::List(s, xs), Value::List(t, ys)) => {
                    work.extend(xs.iter().zip(ys));
                    s == t && xs.len() == ys.len()
                }
                (Value::Tuple(_, xs), Value::Tuple(_, ys)) => {
                    work.extend(xs.iter().zip(ys));
                    xs.len() == ys.len()
                }
                (Value::Int(a), Value::Int(b)) => a == b,
                (Value::Bool(a), Value::Bool(b)) => a == b,
                (Value::Str(a), Value::Str(b)) => a == b,
                (Value::UInt(a), Value::UInt(b)) | (Value::SInt(a), Value::SInt(b)) => a == b,
                (Value::Type(a), Value::Type(b)) => a == b,
                (Value::Function(i, s), Value::Function(j, t)) => i == j && s == t,
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

impl Value {
    /// The type of a value. An array and a list have the type of their elements, and a record
    /// its struct type, so the walk enters only the tuples.
    pub fn ty(&self, tys: &mut Types) -> TyId {
        let mut done = Vec::new();
        let mut work = vec![Build::Visit(self)];
        while let Some(step) = work.pop() {
            match step {
                Build::Visit(Value::Tuple(_, xs)) => {
                    #[cfg(test)]
                    tys.tick(1);
                    work.push(Build::Tuple(xs.len()));
                    work.extend(xs.iter().rev().map(Build::Visit));
                }
                Build::Visit(v) => {
                    #[cfg(test)]
                    tys.tick(1);
                    done.push(v.node_ty(tys));
                }
                Build::Tuple(n) | Build::Array(_, n) | Build::Record(_, n) | Build::List(_, n) => {
                    let parts = last(&mut done, n);
                    done.push(tys.tuple(parts));
                }
            }
        }
        done.pop().unwrap_or_else(|| tys.mk(Ty::Unit))
    }

    /// The type of a value that is not a tuple.
    fn node_ty(&self, tys: &mut Types) -> TyId {
        match self {
            Value::Int(_) => tys.mk(Ty::Int),
            Value::Bool(_) => tys.mk(Ty::Bool),
            Value::UInt(x) => tys.mk(Ty::UInt(x.width())),
            Value::SInt(x) => tys.mk(Ty::SInt(x.width())),
            Value::Type(_) => tys.mk(Ty::Type),
            Value::Str(_) => tys.mk(Ty::String),
            Value::Array(elem, xs) => tys.array(*elem, Int::from_u64(xs.len() as u64)),
            Value::List(elem, _) => tys.list(*elem),
            Value::Record(t, _) | Value::Function(_, t) => *t,
            Value::Unit | Value::Tuple(..) => tys.mk(Ty::Unit),
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
            Value::Function(i, t) => Value::Function(*i, *t),
            Value::Unit
            | Value::Array(..)
            | Value::Tuple(..)
            | Value::Record(..)
            | Value::List(..) => Value::Unit,
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

    /// What the value is, for a message: a string and a type have their own text, and another
    /// value its type. The text of a type stops after `TEXT_LIMIT` bytes.
    #[must_use]
    pub fn text(&self, tys: &Types) -> String {
        match self {
            Value::Str(_) => "a string".to_owned(),
            Value::Type(_) => "a type".to_owned(),
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
        serial::write(tys, Item::Value(self), &mut out);
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Serialized, out.len() as u64);
        out
    }

    /// The length in bytes of `serialize`, without the text. The element type of an array
    /// and a type take their length from the table, so the walk is in the size of the value.
    #[must_use]
    pub fn serialized_len(&self, tys: &Types) -> u64 {
        let mut len = Len::default();
        serial::write(tys, Item::Value(self), &mut len);
        len.0
    }

    /// The recursive size of section 5.4. A string counts characters, not bytes. A container
    /// has the size 1 plus the sizes of its elements, without the type of an array or of a
    /// record.
    #[must_use]
    pub fn size(&self) -> u64 {
        let mut sum = 0u64;
        let mut work = vec![self];
        while let Some(v) = work.pop() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Walked, 1);
            let own = match v {
                Value::Int(n) => int_size(n),
                Value::Bool(_) | Value::Unit | Value::Function(..) => 1,
                Value::Str(s) => 1 + s.chars().count() as u64,
                Value::UInt(x) | Value::SInt(x) => width_size(x.width()),
                Value::Type(t) => t.size(),
                Value::Array(_, xs)
                | Value::Tuple(_, xs)
                | Value::Record(_, xs)
                | Value::List(_, xs) => {
                    work.extend(xs);
                    1
                }
            };
            sum = sum.saturating_add(own);
        }
        sum
    }

    /// The depth of section 5.5: 1 for a scalar value, and 1 more than its deepest part. An
    /// array counts its element type and a record its struct type, and a type is as deep as
    /// its term.
    #[must_use]
    pub fn depth(&self) -> u64 {
        let mut deepest = 0;
        let mut work = vec![(self, 0u64)];
        while let Some((v, above)) = work.pop() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Walked, 1);
            let own = match v {
                Value::Type(t) => t.depth(),
                Value::Array(t, xs) | Value::Record(t, xs) | Value::List(t, xs) => {
                    work.extend(xs.iter().map(|x| (x, above + 1)));
                    1 + t.depth()
                }
                Value::Tuple(_, xs) => {
                    work.extend(xs.iter().map(|x| (x, above + 1)));
                    1
                }
                _ => 1,
            };
            deepest = deepest.max(above + own);
        }
        deepest
    }

    /// Whether the type of the value holds a function type (the function flag of section 5.4).
    /// It reads the flag of the type id or of the tuple, with no walk over the value.
    #[must_use]
    pub fn holds_fn(&self) -> bool {
        match self {
            Value::Function(..) => true,
            Value::Array(t, _) | Value::Record(t, _) | Value::List(t, _) => t.holds_fn(),
            Value::Tuple(flag, _) => *flag,
            _ => false,
        }
    }

    /// The charge of the walk that measures the serialization, before the charge of its bytes
    /// (section 5.4). Each container charges 1. An integer and a finite value charge the
    /// square of their size, because a naive decimal conversion takes this time. A type
    /// charges nothing: an integer in a type gets no charge for its decimal form.
    #[must_use]
    pub fn measure_charge(&self) -> u128 {
        let mut sum = 0u128;
        let mut work = vec![self];
        while let Some(v) = work.pop() {
            sum += match v {
                Value::Int(_) | Value::UInt(_) | Value::SInt(_) => {
                    u128::from(v.size()) * u128::from(v.size())
                }
                Value::Array(_, xs)
                | Value::Tuple(_, xs)
                | Value::Record(_, xs)
                | Value::List(_, xs) => {
                    work.extend(xs);
                    1
                }
                _ => 0,
            };
        }
        sum
    }

    /// Feeds the structure of the value to `h`, for the fingerprint of a specialization. Two
    /// equal values feed the same.
    pub fn hash_into(&self, h: &mut impl Hasher) {
        let mut work = vec![self];
        while let Some(v) = work.pop() {
            match v {
                Value::Int(n) => {
                    h.write_u8(0);
                    n.hash_into(h);
                }
                Value::Bool(b) => h.write_u8(1 + u8::from(*b)),
                Value::Str(s) => {
                    h.write_u8(3);
                    h.write(s.as_bytes());
                }
                Value::UInt(x) => {
                    h.write_u8(4);
                    h.write_u32(x.width());
                    Int::from_unsigned(x).hash_into(h);
                }
                Value::SInt(x) => {
                    h.write_u8(5);
                    h.write_u32(x.width());
                    Int::from_unsigned(x).hash_into(h);
                }
                Value::Type(t) => {
                    h.write_u8(6);
                    t.hash_into(h);
                }
                Value::Unit => h.write_u8(7),
                Value::Function(i, t) => {
                    h.write_u8(12);
                    h.write_usize(*i);
                    t.hash_into(h);
                }
                Value::Array(t, xs) | Value::Record(t, xs) | Value::List(t, xs) => {
                    h.write_u8(match v {
                        Value::Array(..) => 8,
                        Value::Record(..) => 9,
                        _ => 11,
                    });
                    t.hash_into(h);
                    h.write_usize(xs.len());
                    work.extend(xs.iter().rev());
                }
                Value::Tuple(_, xs) => {
                    h.write_u8(10);
                    h.write_usize(xs.len());
                    work.extend(xs.iter().rev());
                }
            }
        }
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
    pub fn serialized_len(&mut self) -> u64 {
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
            ser(&tys, &Value::tuple(vec![int("1"), Value::Bool(true)])),
            "(tuple ((int 1) (bool true)))"
        );
        assert_eq!(
            ser(&tys, &Value::tuple(vec![Value::Unit])),
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
            id("Top", vec![Value::tuple(vec![int("1")]), Value::Unit]).serialize(&tys),
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
            Value::tuple(vec![
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
        let pair = Value::tuple(vec![int("1"), Value::Bool(true)]);
        let pair_ty = tys.tuple(vec![i, b]);
        assert_eq!(pair.ty(&mut tys), pair_ty);
        let empty = Value::Array(b, vec![]);
        let empty_ty = array_ty(&mut tys, b, 0);
        assert_eq!(empty.ty(&mut tys), empty_ty);
        let strings = Value::tuple(vec![Value::Str("a".to_owned())]);
        let string = tys.mk(Ty::String);
        let strings_ty = tys.tuple(vec![string]);
        assert_eq!(strings.ty(&mut tys), strings_ty);
        assert_eq!(strings.text(&tys), "(String,)");
        assert_eq!(pair.text(&tys), "(Int, Bool)");
    }

    #[test]
    fn container_equality_is_structural() {
        let mut tys = Types::default();
        let (b, i) = (tys.mk(Ty::Bool), tys.mk(Ty::Int));
        assert_ne!(Value::Array(b, vec![]), Value::Array(i, vec![]));
        assert_ne!(
            Value::tuple(vec![int("1")]),
            Value::Array(i, vec![int("1")])
        );
        assert_eq!(
            Value::tuple(vec![uint(8, 1)]),
            Value::tuple(vec![uint(8, 1)])
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
            Value::tuple(vec![int("1"), Value::Str("ab".to_owned())]).size(),
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
        let elem = below.ty(tys);
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
            Value::tuple(vec![Value::tuple(vec![int("1")]), Value::Bool(true)]).depth(),
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
            Value::tuple(vec![
                int("18446744073709551616"),
                Value::tuple(vec![Value::Bool(true)])
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
            v = Value::tuple(vec![v]);
            t = tys.tuple(vec![t]);
        }
        assert_eq!(t.depth(), 1_000_001);
        drop(v);
    }

    /// `struct Packet(comptime W: Nat) { a: UInt[W], b: Bool }`.
    fn packet(tys: &mut Types, w: u32) -> TyId {
        let s = tys.begin_spec("Packet", 0, vec![int(&w.to_string())], false);
        let fields = vec![tys.mk(Ty::UInt(w)), tys.mk(Ty::Bool)];
        let (meta, depth) = tys.struct_meta(s, &fields);
        tys.finish_spec(s, fields, meta, depth)
    }

    /// `struct Empty {}`.
    fn empty(tys: &mut Types) -> TyId {
        let s = tys.begin_spec("Empty", 1, Vec::new(), false);
        let (meta, depth) = tys.struct_meta(s, &[]);
        tys.finish_spec(s, Vec::new(), meta, depth)
    }

    /// `struct Wrap(comptime T: Type) {}` at `T = [[Bool; 1]; 1]`.
    fn wrap(tys: &mut Types) -> TyId {
        let b = tys.mk(Ty::Bool);
        let inner = array_ty(tys, b, 1);
        let outer = array_ty(tys, inner, 1);
        let s = tys.begin_spec("Wrap", 2, vec![Value::Type(outer)], false);
        let (meta, depth) = tys.struct_meta(s, &[]);
        tys.finish_spec(s, Vec::new(), meta, depth)
    }

    #[test]
    fn the_forms_of_types_and_records() {
        let mut tys = Types::default();
        let ty = tys.mk(Ty::Type);
        assert_eq!(Value::Type(ty).serialize(&tys), "(type type)");
        let p8 = packet(&mut tys, 8);
        assert_eq!(
            Value::Type(p8).serialize(&tys),
            "(type (struct root Packet ((int 8))))"
        );
        let r = Value::Record(p8, vec![uint(8, 3), Value::Bool(false)]);
        assert_eq!(
            r.serialize(&tys),
            "(record (struct root Packet ((int 8))) ((uint 8 3) (bool false)))"
        );
        let e = empty(&mut tys);
        assert_eq!(
            Value::Record(e, vec![]).serialize(&tys),
            "(record (struct root Empty ()) ())"
        );
        let w = wrap(&mut tys);
        assert_eq!(
            tys.serialize(w),
            "(struct root Wrap ((type (array (array bool 1) 1))))"
        );
        let two = array_ty(&mut tys, e, 2);
        let tup = tys.tuple(vec![ty, two]);
        assert_eq!(
            Value::Type(tup).serialize(&tys),
            "(type (tuple (type (array (struct root Empty ()) 2))))"
        );
    }

    #[test]
    fn the_length_of_a_record_needs_no_text() {
        let mut tys = Types::default();
        let p8 = packet(&mut tys, 8);
        let w = wrap(&mut tys);
        let vs = [
            Value::Record(p8, vec![uint(8, 3), Value::Bool(false)]),
            Value::Type(p8),
            Value::Type(w),
            Value::Array(p8, vec![]),
        ];
        for v in &vs {
            assert_eq!(v.serialized_len(&tys), v.serialize(&tys).len() as u64);
        }
        assert_eq!(tys.text_len(w), Some(tys.serialize(w).len() as u64));
    }

    #[test]
    fn the_text_of_a_struct_type_names_its_arguments() {
        let mut tys = Types::default();
        let ty = tys.mk(Ty::Type);
        assert_eq!(tys.text(ty), "Type");
        let p8 = packet(&mut tys, 8);
        assert_eq!(tys.text(p8), "Packet[8]");
        let e = empty(&mut tys);
        assert_eq!(tys.text(e), "Empty");
        let w = wrap(&mut tys);
        assert_eq!(tys.text(w), "Wrap[[[Bool; 1]; 1]]");
        let r = Value::Record(p8, vec![uint(8, 3), Value::Bool(false)]);
        assert_eq!(r.text(&tys), "Packet[8]");
        assert_eq!(r.ty(&mut tys), p8);
        let pair = Value::tuple(vec![Value::Type(p8), Value::Unit]);
        assert_eq!(pair.text(&tys), "(Type, Unit)");
        let lit = tys.begin_spec(
            "Lit",
            3,
            vec![r.clone(), Value::Str("a\"".to_owned())],
            false,
        );
        let (meta, depth) = tys.struct_meta(lit, &[]);
        let lit = tys.finish_spec(lit, Vec::new(), meta, depth);
        assert_eq!(tys.text(lit), "Lit[Packet[8](3, false), \"a\\\"\"]");
    }

    #[test]
    fn struct_types_are_equal_by_item_and_arguments() {
        let mut tys = Types::default();
        let (a, b) = (packet(&mut tys, 8), packet(&mut tys, 16));
        assert_ne!(a, b);
        assert_eq!(Value::Type(a), Value::Type(a));
        let e = empty(&mut tys);
        assert_ne!(Value::Record(e, vec![]), Value::tuple(vec![]));
        assert_ne!(
            Value::Record(a, vec![uint(8, 1), Value::Bool(true)]),
            Value::Record(a, vec![uint(8, 2), Value::Bool(true)])
        );
        let key = [int("8")];
        let found = tys.find_spec(0, &key.iter().collect::<Vec<_>>());
        assert_eq!(found.and_then(|(_, t)| t), Some(a));
        assert!(tys.find_spec(1, &[&key[0]]).is_none());
        assert!(tys.find_spec(0, &[]).is_none());
    }

    #[test]
    fn struct_sizes_and_depths() {
        let mut tys = Types::default();
        let (ty, p8, e, w) = (
            tys.mk(Ty::Type),
            packet(&mut tys, 8),
            empty(&mut tys),
            wrap(&mut tys),
        );
        assert_eq!((ty.size(), p8.size(), e.size(), w.size()), (1, 2, 1, 6));
        assert_eq!((ty.depth(), p8.depth(), e.depth(), w.depth()), (1, 2, 1, 4));
        let r = Value::Record(p8, vec![uint(8, 3), Value::Bool(false)]);
        assert_eq!(r.size(), 3);
        assert_eq!(Value::Record(e, vec![]).size(), 1);
        assert_eq!(Value::Type(w).depth(), 4);
        assert_eq!(r.depth(), 3);
        assert_eq!(Value::Record(w, vec![]).depth(), 5);
        assert_eq!(array_ty(&mut tys, p8, 2).depth(), 3);
        assert_eq!(r.measure_charge(), 2);
        assert_eq!(Value::Type(p8).measure_charge(), 0);
    }

    fn meta(tys: &Types, t: TyId) -> (String, String, String, u64, bool) {
        let m = tys.meta(t);
        (
            m.width.to_string(),
            m.leaves.to_string(),
            m.zero_size.to_string(),
            t.depth(),
            m.data,
        )
    }

    fn expect(m: (&str, &str, &str, u64, bool)) -> (String, String, String, u64, bool) {
        (m.0.to_owned(), m.1.to_owned(), m.2.to_owned(), m.3, m.4)
    }

    #[test]
    fn the_metadata_of_scalars_tuples_and_structs() {
        let mut tys = Types::default();
        let (b, i, ty, u65) = (
            tys.mk(Ty::Bool),
            tys.mk(Ty::Int),
            tys.mk(Ty::Type),
            tys.mk(Ty::UInt(65)),
        );
        let unit = tys.mk(Ty::Unit);
        assert_eq!(meta(&tys, b), expect(("1", "1", "1", 1, true)));
        assert_eq!(meta(&tys, u65), expect(("65", "1", "2", 1, true)));
        assert_eq!(meta(&tys, unit), expect(("0", "0", "1", 1, true)));
        assert_eq!(meta(&tys, ty), expect(("0", "0", "0", 1, false)));
        let tup = tys.tuple(vec![b, i]);
        assert_eq!(meta(&tys, tup), expect(("1", "1", "2", 2, false)));
        let (p8, e, w) = (packet(&mut tys, 8), empty(&mut tys), wrap(&mut tys));
        assert_eq!(meta(&tys, p8), expect(("9", "2", "3", 2, true)));
        assert_eq!(meta(&tys, e), expect(("0", "0", "1", 1, true)));
        assert_eq!(meta(&tys, w), expect(("0", "0", "1", 4, true)));
        assert_eq!(tys.meta(p8).int_charge(2), 4);
    }

    #[test]
    fn an_array_type_multiplies_the_metadata_and_charges_its_sizes() {
        let mut tys = Types::default();
        let (b, u8t, p8) = (tys.mk(Ty::Bool), tys.mk(Ty::UInt(8)), packet(&mut tys, 8));
        let four = array_ty(&mut tys, p8, 4);
        assert_eq!(meta(&tys, four), expect(("36", "8", "13", 3, true)));
        let none = array_ty(&mut tys, b, 0);
        assert_eq!(meta(&tys, none), expect(("0", "0", "1", 2, true)));
        assert_eq!(tys.meta(p8).array_charge(&Int::from_u64(4)), 3);
        let big = Int::from_decimal("18446744073709551616").unwrap();
        assert_eq!(tys.meta(u8t).array_charge(&big), 6);
        let wide = tys.array(u8t, big);
        assert_eq!(tys.meta(wide).width.to_string(), "147573952589676412928");
    }

    /// `S(k+1) { a: S(k), b: S(k) }` doubles the width at each step, and each struct stores its
    /// numbers.
    #[test]
    fn a_doubling_chain_of_structs_stores_its_metadata() {
        let mut tys = Types::default();
        let b = tys.mk(Ty::Bool);
        let mut t = {
            let s = tys.begin_spec("S0", 0, Vec::new(), false);
            let (meta, depth) = tys.struct_meta(s, &[b]);
            tys.finish_spec(s, vec![b], meta, depth)
        };
        for k in 1..=200usize {
            let s = tys.begin_spec(&format!("S{k}"), k, Vec::new(), false);
            let (meta, depth) = tys.struct_meta(s, &[t, t]);
            t = tys.finish_spec(s, vec![t, t], meta, depth);
        }
        let pow = Int::from_u64(1).shl(200);
        let m = tys.meta(t);
        assert_eq!(m.width, pow);
        assert_eq!(m.leaves, pow);
        assert_eq!(
            m.zero_size,
            Int::from_u64(3).mul(&pow).sub(&Int::from_u64(1))
        );
        assert_eq!((t.size(), t.depth()), (1, 202));
        assert_eq!(
            Value::Type(t).serialize(&tys),
            "(type (struct root S200 ()))"
        );
    }

    #[test]
    fn the_zero_of_a_data_type() {
        let mut tys = Types::default();
        let (b, u8t, p8) = (tys.mk(Ty::Bool), tys.mk(Ty::UInt(8)), packet(&mut tys, 8));
        let arr = array_ty(&mut tys, p8, 2);
        let tup = tys.tuple(vec![b, arr]);
        let zero = tys.zero(tup).unwrap();
        assert_eq!(zero.size(), tys.meta(tup).zero_size.to_u64().unwrap());
        assert_eq!(zero.depth(), tys.zero_depth(tup));
        assert_eq!(
            zero.serialize(&tys),
            "(tuple ((bool false) (array (struct root Packet ((int 8))) \
             ((record (struct root Packet ((int 8))) ((uint 8 0) (bool false))) \
             (record (struct root Packet ((int 8))) ((uint 8 0) (bool false)))))))"
        );
        let none = array_ty(&mut tys, u8t, 0);
        assert_eq!(tys.zero(none).map(|z| z.size()), Some(1));
        assert_eq!(tys.zero_depth(none), 2);
        let nat = tys.mk(Ty::Nat);
        assert!(tys.zero(nat).is_none());
    }

    /// The forms of section 7.1 for strings and lists, and their types and texts, as the cases
    /// of `Silicon.Source.Test.Value` in Lean.
    #[test]
    fn strings_and_lists() {
        let mut tys = Types::default();
        let (i, s, u8t) = (tys.mk(Ty::Int), tys.mk(Ty::String), tys.mk(Ty::UInt(8)));
        let list = |tys: &mut Types, e: TyId, xs: Vec<Value>| {
            let _ = tys.list(e);
            Value::List(e, xs)
        };
        let two = list(&mut tys, i, vec![int("1"), int("2")]);
        assert_eq!(two.serialize(&tys), "(list int ((int 1) (int 2)))");
        let none = list(&mut tys, i, vec![]);
        assert_eq!(none.serialize(&tys), "(list int ())");
        let list_int = tys.list(i);
        assert_eq!(Value::Type(list_int).serialize(&tys), "(type (list int))");
        assert_eq!(Value::Type(s).serialize(&tys), "(type string)");
        let strings = list(&mut tys, s, vec![Value::Str("a".to_owned())]);
        assert_eq!(strings.serialize(&tys), "(list string ((string \"a\")))");
        let list_u8 = tys.list(u8t);
        let nested = tys.list(list_u8);
        assert_eq!(
            Value::Type(nested).serialize(&tys),
            "(type (list (list (uint 8))))"
        );
        assert_eq!(Value::Str("a".to_owned()).ty(&mut tys), s);
        assert_eq!(none.ty(&mut tys), list_int);
        assert_eq!(tys.text(list_u8), "List[UInt[8]]");
        assert_eq!(tys.text(s), "String");
        assert_eq!(none.text(&tys), "List[Int]");
        let mut text = Text::default();
        text.value(&none);
        assert_eq!(text.finish(&tys), "List[Int]");
        assert_eq!(Value::Type(list_int).size(), 2);
        assert_eq!(list_u8.size(), 3);
        assert_eq!((list_int.size(), list_int.depth()), (2, 2));
        assert_eq!((s.size(), s.depth()), (1, 1));
        assert_eq!((nested.size(), nested.depth()), (4, 3));
        assert_eq!(none.size(), 1);
        assert_eq!(strings.size(), 3);
        assert_eq!(
            list(&mut tys, i, vec![int("1"), int("18446744073709551616")]).size(),
            4
        );
        assert_eq!(none.depth(), 2);
        let inner = list(&mut tys, i, vec![]);
        let outer = list(&mut tys, list_int, vec![inner]);
        assert_eq!(outer.depth(), 3);
        assert_eq!(none.measure_charge(), 1);
        assert_eq!(two.measure_charge(), 3);
        assert_eq!(Value::Str("abc".to_owned()).measure_charge(), 0);
        assert!(!tys.meta(s).data && !tys.meta(list_int).data);
        assert!(tys.zero(s).is_none() && tys.zero(list_int).is_none());
    }

    #[test]
    fn a_list_equals_by_its_type_and_elements() {
        let mut tys = Types::default();
        let (b, i) = (tys.mk(Ty::Bool), tys.mk(Ty::Int));
        assert_ne!(Value::List(i, vec![]), Value::List(b, vec![]));
        assert_ne!(Value::List(i, vec![]), Value::Array(i, vec![]));
        assert_eq!(
            Value::List(i, vec![int("1")]),
            Value::List(i, vec![int("1")])
        );
        assert_ne!(
            Value::List(i, vec![int("1")]),
            Value::List(i, vec![int("1"), int("1")])
        );
        let (l, m) = (tys.list(i), tys.list(b));
        assert_ne!(l, m);
        assert_eq!(l, tys.list(i));
    }

    /// A list of lists as deep as a long loop can make it keeps every walk off the stack. A
    /// list prints its element type in full, so the text of a deep list grows with the square
    /// of its depth: the walks that print run at a smaller depth.
    #[test]
    fn the_walks_over_a_deep_list_do_not_recurse() {
        fn nest(tys: &mut Types, depth: usize) -> Value {
            let mut t = tys.mk(Ty::Int);
            let mut v = Value::List(t, vec![int("1")]);
            for _ in 0..depth {
                v = Value::List(tys.list(t), vec![v]);
                t = tys.list(t);
            }
            v
        }
        std::thread::scope(|scope| {
            let worker = std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, || {
                    const DEPTH: usize = 100_000;
                    let mut tys = Types::default();
                    let v = nest(&mut tys, DEPTH);
                    assert_eq!(v.size(), DEPTH as u64 + 2);
                    assert_eq!(v.measure_charge(), DEPTH as u128 + 2);
                    assert_eq!(v.depth(), DEPTH as u64 + 2);
                    assert!(v.text(&tys).len() < 1100);
                    let w = v.clone();
                    let same = v == w;
                    assert!(same);
                    let mut hash = std::hash::DefaultHasher::new();
                    v.hash_into(&mut hash);
                    assert!(format!("{v:?}").len() > DEPTH);
                    drop(w);
                    drop(v);
                });
            assert!(worker.is_ok_and(|w| w.join().is_ok()));
            let worker = std::thread::Builder::new()
                .stack_size(48 * 1024)
                .spawn_scoped(scope, || {
                    const DEPTH: usize = 2_000;
                    let mut tys = Types::default();
                    let v = nest(&mut tys, DEPTH);
                    let text = v.serialize(&tys);
                    assert_eq!(text.len() as u64, v.serialized_len(&tys));
                    let _ = v.ty(&mut tys);
                });
            assert!(worker.is_ok_and(|w| w.join().is_ok()));
        });
    }

    /// The `Debug` of a value keeps its own stack, so a failed assertion about a deep value
    /// does not overflow.
    #[test]
    fn the_debug_of_a_deep_value_does_not_recurse() {
        std::thread::scope(|scope| {
            let worker = std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, || {
                    let mut tys = Types::default();
                    let e = empty(&mut tys);
                    let mut v = Value::Record(e, vec![]);
                    for _ in 0..100_000 {
                        v = Value::tuple(vec![v, Value::Int(Int::from_u64(1))]);
                    }
                    let text = format!("{v:?}");
                    assert!(text.starts_with("Tuple([Tuple([Tuple(["));
                    assert!(text.ends_with("Int(1)])"));
                });
            assert!(worker.is_ok_and(|w| w.join().is_ok()));
        });
    }
}
