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
use std::collections::BTreeMap;
use std::fmt::Write;

/// A type as a static value: the scalar types of slice 1 with a width from 1 to 65536, `()`,
/// and the container types. A tuple type has at least one element type: `()` is `Unit`. The
/// length of an array type is any natural number, as the type does not hold the elements.
///
/// This is one node of the table `Types`. The parts of a container type are ids, so a type
/// is never copied by its parts. The hardware values hold only scalar types of this form.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ty {
    Bool,
    Nat,
    Int,
    UInt(u32),
    SInt(u32),
    Unit,
    Array(TyId, Int),
    Tuple(Vec<TyId>),
}

/// A type in the table `Types`. Two ids of one table are equal exactly if their types are
/// structurally equal. The id carries the recursive size and the depth of its type, as the
/// type metadata of design section 5.4, so a copy of an id is constant work.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyId {
    index: usize,
    size: u64,
    depth: u64,
}

impl TyId {
    /// The number of nodes of the type term, plus the size of each integer in it.
    #[must_use]
    pub fn size(self) -> u64 {
        self.size
    }

    /// The depth of section 5.5: 1 for a scalar type, and 1 more than its deepest part.
    #[must_use]
    pub fn depth(self) -> u64 {
        self.depth
    }
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
struct Len(u64);

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
fn node<S: Sink>(out: &mut S, form: &str, fields: impl FnOnce(&mut S)) {
    out.write_str("(").unwrap_or_default();
    out.write_str(form).unwrap_or_default();
    fields(out);
    out.write_str(")").unwrap_or_default();
}

/// `(<item> <item> ...)`.
fn list<S: Sink, T>(out: &mut S, items: &[T], mut each: impl FnMut(&T, &mut S)) {
    out.write_str("(").unwrap_or_default();
    for (k, item) in items.iter().enumerate() {
        if k > 0 {
            out.write_str(" ").unwrap_or_default();
        }
        each(item, out);
    }
    out.write_str(")").unwrap_or_default();
}

/// One type of the table with its metadata.
struct Entry {
    ty: Ty,
    text_len: u64,
}

/// The table of the static types of one elaboration. A structurally equal type has one id, so
/// a copy of a type and an equality of two types are constant work. A container type holds
/// the ids of its parts, so a new type costs work in its own arity only. The table grows only
/// with charged work: each new type pays its recursive size at its constructor.
#[derive(Default)]
pub struct Types {
    entries: Vec<Entry>,
    index: BTreeMap<Ty, TyId>,
    /// The work of the lookups: 1 for each type and 1 for each part of a container type.
    #[cfg(test)]
    pub(crate) work: u64,
}

/// The type that an absent id names. The table makes each id, so no id finds it.
static ABSENT: Ty = Ty::Unit;

impl Types {
    /// The id of `ty`. A new type gets its metadata from the ids of its parts.
    pub fn mk(&mut self, ty: Ty) -> TyId {
        #[cfg(test)]
        {
            self.work += 1 + match &ty {
                Ty::Tuple(parts) => parts.len() as u64,
                _ => 0,
            };
        }
        if let Some(id) = self.index.get(&ty) {
            return *id;
        }
        let (size, depth) = Types::metadata(&ty);
        let id = TyId {
            index: self.entries.len(),
            size,
            depth,
        };
        let mut len = Len::default();
        self.write_node(&ty, &mut len);
        self.entries.push(Entry {
            ty: ty.clone(),
            text_len: len.0,
        });
        self.index.insert(ty, id);
        id
    }

    /// The recursive size and the depth of a new type.
    fn metadata(ty: &Ty) -> (u64, u64) {
        match ty {
            Ty::Bool | Ty::Nat | Ty::Int | Ty::Unit => (1, 1),
            Ty::UInt(w) | Ty::SInt(w) => (1 + int_size(&width_int(*w)), 1),
            Ty::Array(elem, len) => (
                1u64.saturating_add(elem.size).saturating_add(int_size(len)),
                1 + elem.depth,
            ),
            Ty::Tuple(parts) => (
                parts
                    .iter()
                    .fold(1u64, |sum, part| sum.saturating_add(part.size)),
                1 + parts.iter().map(|part| part.depth).max().unwrap_or(0),
            ),
        }
    }

    #[must_use]
    pub fn array(&mut self, elem: TyId, len: Int) -> TyId {
        self.mk(Ty::Array(elem, len))
    }

    #[must_use]
    pub fn tuple(&mut self, parts: Vec<TyId>) -> TyId {
        self.mk(Ty::Tuple(parts))
    }

    /// The type with the id `t`.
    #[must_use]
    pub fn get(&self, t: TyId) -> &Ty {
        self.entries.get(t.index).map_or(&ABSENT, |e| &e.ty)
    }

    /// The id of the part `k` of the container type `t`: the element type of an array, or
    /// the type of the element `k` of a tuple.
    #[must_use]
    pub fn part(&self, t: TyId, k: usize) -> Option<TyId> {
        match self.get(t) {
            Ty::Array(elem, _) => Some(*elem),
            Ty::Tuple(parts) => parts.get(k).copied(),
            _ => None,
        }
    }

    /// The length in bytes of the serialization of `t`.
    fn text_len(&self, t: TyId) -> u64 {
        self.entries.get(t.index).map_or(0, |e| e.text_len)
    }

    #[must_use]
    pub fn serialize(&self, t: TyId) -> String {
        let mut out = String::new();
        self.write(t, &mut out);
        out
    }

    fn write(&self, t: TyId, out: &mut String) {
        self.write_node(self.get(t), out);
    }

    fn write_node<S: Sink>(&self, ty: &Ty, out: &mut S) {
        match ty {
            Ty::Bool => out.write_str("bool").unwrap_or_default(),
            Ty::Nat => out.write_str("nat").unwrap_or_default(),
            Ty::Int => out.write_str("int").unwrap_or_default(),
            Ty::Unit => out.write_str("unit").unwrap_or_default(),
            Ty::UInt(w) => write!(out, "(uint {w})").unwrap_or_default(),
            Ty::SInt(w) => write!(out, "(sint {w})").unwrap_or_default(),
            Ty::Array(elem, len) => node(out, "array", |out| {
                out.write_str(" ").unwrap_or_default();
                out.ty(self, *elem);
                write!(out, " {len}").unwrap_or_default();
            }),
            Ty::Tuple(parts) => node(out, "tuple", |out| {
                out.write_str(" ").unwrap_or_default();
                list(out, parts, |part, out| out.ty(self, *part));
            }),
        }
    }

    /// The source form, for a message.
    #[must_use]
    pub fn text(&self, t: TyId) -> String {
        self.text_of(self.get(t))
    }

    /// The source form of the node `ty`, for a message.
    #[must_use]
    pub fn text_of(&self, ty: &Ty) -> String {
        match ty {
            Ty::Bool => "Bool".to_owned(),
            Ty::Nat => "Nat".to_owned(),
            Ty::Int => "Int".to_owned(),
            Ty::Unit => "Unit".to_owned(),
            Ty::UInt(w) => format!("UInt[{w}]"),
            Ty::SInt(w) => format!("SInt[{w}]"),
            Ty::Array(elem, len) => format!("[{}; {len}]", self.text(*elem)),
            Ty::Tuple(parts) => {
                tuple_text(&parts.iter().map(|p| self.text(*p)).collect::<Vec<String>>())
            }
        }
    }
}

/// `(A, B)`, or `(A,)` for one part.
fn tuple_text(parts: &[String]) -> String {
    match parts {
        [one] => format!("({one},)"),
        _ => format!("({})", parts.join(", ")),
    }
}

impl Ty {
    /// `UInt[W]` or `SInt[W]`.
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Ty::UInt(_) | Ty::SInt(_))
    }
}

impl Value {
    /// The type of a value. A string, a type, and a tuple that holds them have no type.
    pub fn ty(&self, tys: &mut Types) -> Option<TyId> {
        match self {
            Value::Int(_) => Some(tys.mk(Ty::Int)),
            Value::Bool(_) => Some(tys.mk(Ty::Bool)),
            Value::UInt(x) => Some(tys.mk(Ty::UInt(x.width()))),
            Value::SInt(x) => Some(tys.mk(Ty::SInt(x.width()))),
            Value::Unit => Some(tys.mk(Ty::Unit)),
            Value::Array(elem, xs) => Some(tys.array(*elem, Int::from_u64(xs.len() as u64))),
            Value::Tuple(xs) => {
                let parts = xs
                    .iter()
                    .map(|x| x.ty(tys))
                    .collect::<Option<Vec<TyId>>>()?;
                Some(tys.tuple(parts))
            }
            Value::Str(_) | Value::Type(_) => None,
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

    /// The source form of the type of a value, if it has one, without a new type in the
    /// table.
    fn type_text(&self, tys: &Types) -> Option<String> {
        Some(match self {
            Value::Int(_) => "Int".to_owned(),
            Value::Bool(_) => "Bool".to_owned(),
            Value::UInt(x) => format!("UInt[{}]", x.width()),
            Value::SInt(x) => format!("SInt[{}]", x.width()),
            Value::Unit => "Unit".to_owned(),
            Value::Array(elem, xs) => format!("[{}; {}]", tys.text(*elem), xs.len()),
            Value::Tuple(xs) => tuple_text(
                &xs.iter()
                    .map(|x| x.type_text(tys))
                    .collect::<Option<Vec<String>>>()?,
            ),
            Value::Str(_) | Value::Type(_) => return None,
        })
    }

    /// What the value is, for a message. Only a tuple has neither a type nor its own text.
    #[must_use]
    pub fn text(&self, tys: &Types) -> String {
        match self {
            Value::Str(_) => "a string".to_owned(),
            Value::Type(_) => "a type".to_owned(),
            v => v.type_text(tys).unwrap_or_else(|| "a tuple".to_owned()),
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

    fn write<S: Sink>(&self, tys: &Types, out: &mut S) {
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
            Value::Unit => out.write_str("(unit)").unwrap_or_default(),
            Value::Array(elem, xs) => node(out, "array", |out| {
                out.write_str(" ").unwrap_or_default();
                out.ty(tys, *elem);
                out.write_str(" ").unwrap_or_default();
                list(out, xs, |x, out| x.write(tys, out));
            }),
            Value::Tuple(xs) => node(out, "tuple", |out| {
                out.write_str(" ").unwrap_or_default();
                list(out, xs, |x, out| x.write(tys, out));
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
            Value::Array(_, xs) | Value::Tuple(xs) => {
                xs.iter().fold(1u64, |sum, x| sum.saturating_add(x.size()))
            }
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
