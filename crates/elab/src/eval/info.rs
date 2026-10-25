// SPDX-License-Identifier: Apache-2.0
//! The builtin `@typeInfo(T)` of Lean `Source.Eval.Reflect` (`typeInfo`) and `Eval.eval`
//! (design sections 6.2 and 9.3). The argument evaluates under the guard `Arg` and is a `Type`.
//! The use of `TypeInfo` then follows (the first one completes `FieldInfo` and `VariantInfo`).
//!
//! The record reads the stored parts of the type: the field types of a tuple or a struct entry,
//! and the variants of an enum entry. The counts of fields and variants come from them with no
//! walk. The call charges those counts, adds the payload counts, and charges them. Only then it
//! visits the parts once to find the depth and the recursive size of the result. The size pays
//! for each name and each type, from the fifth metadata number that the id of a type holds. The
//! record exists after that charge, so no name is copied before it, and the walk enters no field
//! type and no payload type.

use super::container::bounded;
use super::place::chain;
use super::{ArgRec, Evaluator, GuardKind, Out, Res, at, fail, need};
use crate::Code;
use crate::hw::{Handle, Seen, Val};
use crate::int::Int;
use crate::types::{Ty, TyId, Types, Variant};
use crate::value::{Value, int_size};
use core_ir::Bits;
use parse::ast::{Builtin, Expr, Item, Pos, StructField, Variant as VariantItem};
use resolve::Resolved;

/// The prelude struct that holds the record.
const TYPE_INFO: &str = "TypeInfo";

/// A number of the record: a count that fits a word, or an integer of a type.
enum Num<'v> {
    Word(u64),
    Big(&'v Int),
}

impl Num<'_> {
    /// The recursive size of the number as a value. A word is below `2^64`, so its size is 1.
    fn size(&self) -> u64 {
        match self {
            Num::Word(_) => 1,
            Num::Big(n) => int_size(n),
        }
    }

    fn value(&self) -> Value {
        Value::Int(match self {
            Num::Word(n) => Int::from_u64(*n),
            Num::Big(n) => (*n).clone(),
        })
    }
}

/// The names of the fields of a type: the positions of a tuple, or the declared names of a
/// struct. `info_of` checks that a struct has one name for each field type.
#[derive(Clone, Copy)]
enum Names<'v> {
    Index,
    Declared(&'v [StructField]),
}

impl<'v> Names<'v> {
    /// The names in the order of the field types.
    fn iter(self) -> NameIter<'v> {
        match self {
            Names::Index => NameIter::Index(0),
            Names::Declared(fs) => NameIter::Declared(fs.iter()),
        }
    }
}

enum NameIter<'v> {
    Index(usize),
    Declared(std::slice::Iter<'v, StructField>),
}

impl<'v> Iterator for NameIter<'v> {
    type Item = FieldName<'v>;

    fn next(&mut self) -> Option<FieldName<'v>> {
        match self {
            NameIter::Index(k) => {
                *k += 1;
                Some(FieldName::Index(*k - 1))
            }
            NameIter::Declared(fs) => fs.next().map(|f| FieldName::Declared(&f.name.name)),
        }
    }
}

/// The name of one field. A name is an identifier, so its length in bytes is its length in
/// characters.
enum FieldName<'v> {
    Index(usize),
    Declared(&'v str),
}

impl FieldName<'_> {
    fn len(&self) -> u64 {
        match self {
            FieldName::Index(k) => k.checked_ilog10().map_or(1, |d| u64::from(d) + 1),
            FieldName::Declared(n) => n.len() as u64,
        }
    }

    fn text(&self) -> String {
        match self {
            FieldName::Index(k) => k.to_string(),
            FieldName::Declared(n) => (*n).to_owned(),
        }
    }
}

/// The ids of the types that the shape of the record needs: `TypeInfo`, `FieldInfo`,
/// `VariantInfo`, and `Type`.
#[derive(Clone, Copy)]
struct Ids {
    info: TyId,
    field: TyId,
    variant: TyId,
    ty: TyId,
}

/// The parts of `@typeInfo(t)` as the type stores them (Lean `Info`). A part that the kind does
/// not use keeps its default. Reading them takes constant work: the slices belong to the entry
/// of the type.
struct Info<'v> {
    kind: &'static str,
    element: TyId,
    length: Num<'v>,
    width: Num<'v>,
    names: Names<'v>,
    fields: &'v [TyId],
    names_of_variants: &'v [VariantItem],
    variants: &'v [Variant],
}

/// The kind tag of the type `t` (Lean `kindTag`). Each struct type is a `record`.
fn kind_tag(t: &Ty) -> &'static str {
    match t {
        Ty::Bool => "bool",
        Ty::UInt(_) => "uint",
        Ty::SInt(_) => "sint",
        Ty::Unit => "unit",
        Ty::Array(..) => "array",
        Ty::Tuple(_) => "tuple",
        Ty::Struct(_) => "record",
        Ty::Int => "int",
        Ty::Nat => "nat",
        Ty::String => "string",
        Ty::Type => "type",
        Ty::Fn(..) => "function",
        Ty::List(_) => "list",
        Ty::Reg(_) => "reg",
        Ty::Wire(_) => "wire",
        Ty::Mem(..) => "mem",
        Ty::Input(_) => "input",
        Ty::Instance(_) => "instance",
        Ty::Enum(_) => "enum",
    }
}

/// The size of the value of a tag, from its significant bits, with no conversion.
fn tag_size(tag: &Bits) -> u64 {
    tag.value().bits().saturating_sub(1) / 64 + 1
}

/// The `TypeInfo` of Lean `infoOf` for the type `t`: the stored parts, with `unit` as the default
/// element. A struct reads the fields of its done entry, so a struct with parameters gives the
/// field types of its specialization. An enum reads its done entry and the variant names of its
/// item.
fn info_of<'v>(
    (tys, file): (&'v Types, &'v Resolved),
    pos: Pos,
    t: TyId,
    unit: TyId,
) -> Res<Info<'v>> {
    let ty = tys.get(t);
    let mut info = Info {
        kind: kind_tag(ty),
        element: unit,
        length: Num::Word(0),
        width: Num::Word(0),
        names: Names::Index,
        fields: &[],
        names_of_variants: &[],
        variants: &[],
    };
    let missing = || fail(Code::S010, pos, format!("{} has no entry", tys.text(t)));
    match ty {
        Ty::Bool => info.width = Num::Word(1),
        Ty::UInt(w) | Ty::SInt(w) => info.width = Num::Word(u64::from(*w)),
        Ty::Array(e, n) | Ty::Mem(e, n) => {
            info.element = *e;
            info.length = Num::Big(n);
        }
        Ty::Tuple(ts) => {
            info.fields = ts;
            info.length = Num::Word(ts.len() as u64);
        }
        Ty::Struct(_) => {
            let Some(parts) = tys.parts(t) else {
                return missing();
            };
            let Some(Item::Struct { fields, .. }) = parts.item().and_then(|i| file.ast().get(i))
            else {
                return missing();
            };
            if fields.len() != parts.types.len() {
                return missing();
            }
            info.names = Names::Declared(fields);
            info.fields = parts.types;
            info.length = Num::Word(parts.types.len() as u64);
        }
        Ty::List(e) | Ty::Reg(e) | Ty::Wire(e) | Ty::Input(e) => info.element = *e,
        Ty::Enum(e) => {
            let (Some(parts), Some(variants)) = (tys.parts(t), tys.variants(t)) else {
                return missing();
            };
            let Some(Item::Enum {
                variants: items, ..
            }) = file.ast().get(e.item())
            else {
                return fail(Code::S010, pos, "the enum item is missing".to_owned());
            };
            let Some(tag) = parts.types.first() else {
                return missing();
            };
            info.element = *tag;
            info.width = Num::Big(&tys.meta(t).width);
            info.names_of_variants = items;
            info.variants = variants;
        }
        _ => {}
    }
    Ok(info)
}

impl Info<'_> {
    /// The number of payload types of all variants.
    fn payloads(&self) -> u64 {
        self.variants.iter().map(|v| v.payload.len() as u64).sum()
    }

    fn variant_name(&self, j: usize) -> &str {
        self.names_of_variants
            .get(j)
            .map_or("", |v| v.name.name.as_str())
    }

    /// The recursive size and the depth of the record (Lean `Value.size` and `Value.depth` of
    /// the value that `build` makes). It visits each field, each variant, and each payload type
    /// once, and reads the length of each name, never the name or a type.
    fn shape(&self, ids: Ids) -> (u128, u64) {
        // The record, the kind, and the two lists. The element and the two numbers follow.
        let mut size = 1 + (1 + self.kind.len() as u128) + 1 + 1;
        size += u128::from(self.element.size());
        size += u128::from(self.length.size()) + u128::from(self.width.size());
        let mut fields = ids.field.depth();
        for (name, t) in self.names.iter().zip(self.fields) {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Reflected, 1);
            size += 1 + (1 + u128::from(name.len())) + u128::from(t.size());
            fields = fields.max(1 + ids.field.depth().max(1).max(t.depth()));
        }
        let mut variants = ids.variant.depth();
        for (j, v) in self.variants.iter().enumerate() {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Reflected, 1);
            let mut payload = ids.ty.depth();
            size += 1 + (1 + self.variant_name(j).len() as u128) + u128::from(tag_size(&v.tag)) + 1;
            for p in &v.payload {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Reflected, 1);
                size += u128::from(p.size());
                payload = payload.max(p.depth());
            }
            variants = variants.max(1 + ids.variant.depth().max(1).max(1 + payload));
        }
        let depth = 1 + ids
            .info
            .depth()
            .max(1)
            .max(1 + fields)
            .max(self.element.depth())
            .max(1)
            .max(1 + variants);
        (size, depth)
    }

    /// The record `TypeInfo(kind, fields, element, length, width, variants)`.
    fn build(&self, ids: Ids) -> Value {
        let fields = self
            .fields
            .iter()
            .zip(self.names.iter())
            .map(|(t, name)| {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Reflected, 1);
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::TextBytes, name.len());
                Value::Record(ids.field, vec![Value::Str(name.text()), Value::Type(*t)])
            })
            .collect();
        let variants = self
            .variants
            .iter()
            .enumerate()
            .map(|(j, v)| {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Reflected, 1);
                #[cfg(test)]
                crate::counters::add(
                    crate::counters::Count::TextBytes,
                    self.variant_name(j).len() as u64,
                );
                let payload = v.payload.iter().map(|p| Value::Type(*p)).collect();
                Value::Record(
                    ids.variant,
                    vec![
                        Value::Str(self.variant_name(j).to_owned()),
                        Value::Int(Int::from_unsigned(&v.tag)),
                        Value::List(ids.ty, payload),
                    ],
                )
            })
            .collect();
        Value::Record(
            ids.info,
            vec![
                Value::Str(self.kind.to_owned()),
                Value::List(ids.field, fields),
                Value::Type(self.element),
                self.length.value(),
                self.width.value(),
                Value::List(ids.variant, variants),
            ],
        )
    }
}

/// Whether the value has only type leaves: a `Type`, or a tuple or a non-empty array whose
/// elements have them (Lean `typeLeaves`). The walk keeps its own stack and reads only the
/// argument, which its evaluation charged.
fn type_leaves(v: &Value) -> bool {
    let mut work = vec![v];
    while let Some(x) = work.pop() {
        match x {
            Value::Type(_) => {}
            Value::Tuple(_, xs) => work.extend(xs),
            Value::Array(_, xs) if !xs.is_empty() => work.extend(xs),
            _ => return false,
        }
    }
    true
}

impl Evaluator<'_> {
    /// `@typeInfo(arg)` at `pos`, after its node charged (section 6.2, **`@typeInfo` order**,
    /// steps 2 to 8).
    pub(super) fn type_info(&mut self, pos: Pos, arg: &Expr) -> Res<Out> {
        let rec = if chain(arg).is_some() {
            ArgRec::Place
        } else {
            ArgRec::Node
        };
        let out = self.guarded(GuardKind::Arg(Builtin::TypeInfo), |ev| {
            ev.with_arg(rec, |ev| {
                let o = ev.eval(arg)?;
                need(arg, o)
            })
        })?;
        let t = self.type_info_arg(arg.pos(), &out)?;
        let ti = self.type_info_struct(pos)?;
        Ok(Out::Made(Val::Static(self.type_info_value(pos, ti, t)?)))
    }

    /// The fix `{h}` of "`@typeInfo` of a value" for the argument `s` (Lean `typeInfoHint`).
    fn type_info_hint(s: Seen<'_>) -> &'static str {
        const BIND: &str = "bind the value with `let x = ...;` and use `@typeInfo(@TypeOf(x))`";
        match s {
            Seen::Handle(Handle::Domain(_)) => "a domain has no type, so remove the `@typeInfo`",
            Seen::Static(v @ Value::Tuple(..)) if type_leaves(v) => {
                "name the tuple type with `type T = (A, B);` and use `@typeInfo(T)`"
            }
            Seen::Static(v @ Value::Array(..)) if type_leaves(v) => {
                "name the array type with `type T = [A; N];` and use `@typeInfo(T)`"
            }
            _ => BIND,
        }
    }

    /// The type that the argument at `pos` gives (step 3). A value that is not a `Type` is
    /// `S010`, with no copy charge.
    fn type_info_arg(&self, pos: Pos, out: &Out) -> Res<TyId> {
        match self.store.seen(out) {
            Seen::Static(Value::Type(t)) => Ok(*t),
            s => fail(
                Code::S010,
                pos,
                format!(
                    "`@typeInfo` takes a type, not {}; {}",
                    self.about(s),
                    Self::type_info_hint(s)
                ),
            ),
        }
    }

    /// The use of the prelude struct `TypeInfo` at `pos` (step 4), as a struct use.
    fn type_info_struct(&mut self, pos: Pos) -> Res<TyId> {
        match self.file.prelude_struct(TYPE_INFO) {
            Some(i) => self.spec(pos, i, &[]),
            None => fail(Code::S010, pos, format!("{TYPE_INFO} has no entry")),
        }
    }

    /// The record of `@typeInfo(t)` at `pos`, after the use of `TypeInfo` gave `ti` (steps 5 to
    /// 8). The counts of fields and variants charge first, then the payload counts. The depth
    /// check and the size charge come before any part of the record exists.
    fn type_info_value(&mut self, pos: Pos, ti: TyId, t: TyId) -> Res<Value> {
        let file = self.file;
        let (field, variant) = self.info_lists(pos, ti)?;
        let ids = Ids {
            info: ti,
            field,
            variant,
            ty: self.tys.mk(Ty::Type),
        };
        let unit = self.tys.mk(Ty::Unit);
        let info = info_of((&self.tys, file), pos, t, unit)?;
        let counts = info.fields.len() as u128 + info.variants.len() as u128;
        self.fuel.pay(counts).map_err(at(pos))?;
        self.fuel
            .pay(u128::from(info.payloads()))
            .map_err(at(pos))?;
        let (size, depth) = info.shape(ids);
        bounded(self.limit, self.site, pos, depth)?;
        self.fuel.pay(size).map_err(at(pos))?;
        Ok(info.build(ids))
    }

    /// The element types of the lists `fields` and `variants` of `TypeInfo`: `FieldInfo` and
    /// `VariantInfo`.
    fn info_lists(&self, pos: Pos, ti: TyId) -> Res<(TyId, TyId)> {
        let list = |k: usize| {
            let t = self.tys.parts(ti).and_then(|p| p.types.get(k).copied())?;
            match self.tys.get(t) {
                Ty::List(e) => Some(*e),
                _ => None,
            }
        };
        match (list(1), list(5)) {
            (Some(f), Some(v)) => Ok((f, v)),
            _ => fail(
                Code::S010,
                pos,
                format!("{} has no entry", self.tys.text(ti)),
            ),
        }
    }
}
