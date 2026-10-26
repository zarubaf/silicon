// SPDX-License-Identifier: Apache-2.0
//! The records of Lean `Source.Eval.Container` and `Source.Eval` (design section 5.6): the
//! constructor of a type, the zero `T()`, the field `.f`, and `data_bits`.
//!
//! A constructor charges the sizes of its arguments before any copy, so a record copies a
//! value only after it paid for it. The zero charges its size from the metadata before it
//! exists, and `data_bits` reads the width from the metadata, so neither walks the field types.

use super::typed::Field;
use super::{Evaluator, Names, Opnd, Out, Res, at, fail, need};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Seen, Val};
use crate::int::BitBuf;
use crate::limit;
use crate::names::Sym;
use crate::ops::{int_text, str_text};
use crate::types::{PartNames, Ty, TyId};
use crate::value::{Value, int_size, width_size};
use parse::ast::{Expr, Ident, Item, Pos};

/// A field name at a selection: its symbol, if the file or the run has one, and its text. A name
/// that comes from a key has the limit of a string in a message (section 5.5), and a name of the
/// source has none.
#[derive(Clone, Copy)]
pub(super) struct FieldName<'a> {
    pub(super) sym: Option<Sym>,
    pub(super) name: &'a str,
    pub(super) keyed: bool,
}

impl FieldName<'_> {
    /// The name as a message shows it. It renders only in an error.
    pub(super) fn shown(&self) -> String {
        let text = if self.keyed {
            str_text(self.name)
        } else {
            self.name.to_owned()
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::TextBytes, text.len() as u64);
        text
    }
}

/// The `S010` "No field" of section 6.2 at `pos`, for the struct type `ty` and the field name
/// `field`. The name has the limit of a string in a message (section 5.5).
pub(super) fn no_field<T>(pos: Pos, ty: &str, field: &str) -> Res<T> {
    let err = fail(
        Code::S010,
        pos,
        format!("`{ty}` has no field `{field}`; select a field that `{ty}` declares"),
    );
    #[cfg(test)]
    if let Err(super::Stop::Error(e)) = &err {
        crate::counters::add(crate::counters::Count::TextBytes, e.message.len() as u64);
    }
    err
}

impl Evaluator<'_> {
    /// A call whose callee is not a function item or a prelude function: the callee is a type,
    /// and the call is its constructor. No argument is the zero `T()`. A struct type takes one
    /// argument for each field. Another type takes one argument, which it converts. The callee
    /// waits in the store while the arguments evaluate.
    pub(super) fn construct(&mut self, pos: Pos, callee: Out, xs: &[Expr]) -> Res<Option<Out>> {
        let Seen::Static(Value::Type(ty)) = self.store.seen(&callee) else {
            return fail(
                Code::S010,
                pos,
                format!("{} is not a function", self.text(self.store.seen(&callee))),
            );
        };
        let ty = *ty;
        if matches!(self.tys.get(ty), Ty::Fn(..)) {
            return fail(
                Code::S010,
                pos,
                format!(
                    "a constructor needs a hardware data type, not {}",
                    self.tys.text(ty)
                ),
            );
        }
        if matches!(self.tys.get(ty), Ty::Enum(_)) && !xs.is_empty() {
            let t = self.tys.text(ty);
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{t}` is an enum, so `{t}(...)` takes no arguments; construct a variant \
                     such as `{t}::V(...)`, or write `{t}()` for the zero"
                ),
            );
        }
        self.not_handle(pos, ty)?;
        let value = match xs {
            [] => Val::Static(self.zero(pos, ty)?),
            _ if matches!(self.tys.get(ty), Ty::Struct(_)) => {
                self.record(pos, ty, callee, xs)?.into_val()
            }
            [x] => {
                let at = self.store.park(callee);
                let a = self.eval(x)?;
                let a = need(x, a)?;
                self.store.resume_one(at);
                self.charge(pos, self.size(&a))?;
                Val::Static(self.conform(pos, ty, a)?)
            }
            _ => {
                return fail(
                    Code::S007,
                    pos,
                    "a constructor takes 0 or 1 argument(s)".to_owned(),
                );
            }
        };
        Ok(Some(Out::Made(value)))
    }

    /// The variant that the path node `ty` names, from the resolver.
    pub(super) fn variant_ref(&self, ty: &Ident) -> Option<resolve::VariantRef> {
        match self.names {
            Names::Top => self.top.and_then(|t| t.variant(ty.id)),
            Names::File => self.file.variant(ty.id),
        }
    }

    /// A variant path `E::V` at `pos` with the arguments `xs` of a constructor call
    /// (section 5.4). It uses the enum, then evaluates the payload values; each result waits
    /// while the later ones evaluate. A constructor makes no call frame.
    pub(super) fn variant(&mut self, pos: Pos, ty: &Ident, xs: &[Expr]) -> Res<Option<Out>> {
        let Some(found) = self.variant_ref(ty) else {
            return fail(Code::S010, pos, "the variant path has no target".to_owned());
        };
        let t = self.enum_use(pos, found.item)?;
        let outs = self.args(xs)?;
        let v = self.variant_of(pos, t, found.index, outs)?;
        Ok(Some(Out::Made(v)))
    }

    /// The variant `j` of the enum type `t` at `pos` with the payload values `outs`
    /// (section 5.4). The node, the use of the enum, and the payload values come before. Then
    /// these steps run:
    ///
    /// 1. The copies of the payload values charge, by the rule of builtins.
    /// 2. Each payload value gets its typed use at its payload type, in order (`S010`, `S012`).
    ///    A register or a wire is read, and the read of an aggregate charges its zero size.
    /// 3. The recursive size of the result charges, before the static or the hardware pack. A
    ///    hardware result reads its size from the node of its leaves. The copies paid for the
    ///    walk that collects the leaves, and the pack node has no charge, so no work is unpaid.
    /// 4. The pack makes the result. The tag is the static tag value of the variant. When each
    ///    payload value is static, the payload packs into one bit buffer, and the result is a
    ///    static enum value. Else the payload is a hardware pack of the leaves of the payload
    ///    values, and the lowering charges its core nodes (section 7.4).
    fn variant_of(&mut self, pos: Pos, t: TyId, j: usize, outs: Vec<Out>) -> Res<Val> {
        let entry = self
            .tys
            .widths(t)
            .zip(self.tys.variants(t).and_then(|vs| vs.get(j)));
        let Some((widths, variant)) = entry else {
            return fail(
                Code::S010,
                pos,
                format!("{} has no variant {j}", self.tys.text(t)),
            );
        };
        let (tag, payload) = (variant.tag.clone(), variant.payload.clone());
        if payload.len() != outs.len() {
            // Pass 4 reports each arity (`S007`), so this is a defect.
            return fail(
                Code::S010,
                pos,
                format!(
                    "{} has {} payload type(s) here, but {} value(s)",
                    self.tys.text(t),
                    payload.len(),
                    outs.len()
                ),
            );
        }
        let mut copies = 0u128;
        for o in &outs {
            copies += self.size(o);
        }
        self.charge(pos, copies)?;
        let mut vals = Vec::with_capacity(outs.len());
        for (u, o) in payload.iter().zip(outs) {
            vals.push(self.read_use(pos, *u, true, o)?);
        }
        self.enum_depth(pos, t)?;
        let result_size =
            |p: u32| 1 + width_size(widths.tag) + if p == 0 { 0 } else { width_size(p) };
        if vals.iter().all(|v| matches!(v, Val::Static(_))) {
            // The size does not read the payload bits, so the charge comes before the pack.
            self.charge(pos, u128::from(result_size(widths.payload)))?;
            let bits = (widths.payload > 0).then(|| {
                let mut buf = BitBuf::new(widths.payload);
                for v in &vals {
                    if let Val::Static(v) = v {
                        v.pack_into(&mut buf);
                    }
                }
                buf.finish(widths.payload)
            });
            return Ok(Val::Static(Value::Enum(t, tag, bits.flatten())));
        }
        if widths.payload == 0 {
            return fail(
                Code::S010,
                pos,
                format!("a payload value of {} is not data", self.tys.text(t)),
            );
        }
        let parts: Vec<(TyId, Val)> = payload.into_iter().zip(vals).collect();
        let h = self.pack_hw(pos, widths.payload, &parts)?;
        let parts = vec![Agg::Static(Value::UInt(tag)), Agg::Hw(h)];
        let Some(node) = Agg::shape(&self.graph, &self.tys, t, &parts) else {
            return fail(Code::S010, pos, "the part has the wrong shape".to_owned());
        };
        self.charge(pos, u128::from(node.size))?;
        Ok(Agg::finish(&self.tys, node, parts).into_val())
    }

    /// The zero `T()` of the type `t` at `pos` (section 5.6). A type that is not hardware data
    /// is `S010`. The zero checks its depth and charges its size from the metadata before it
    /// exists.
    fn zero(&mut self, pos: Pos, t: TyId) -> Res<Value> {
        if !self.tys.meta(t).data {
            return fail(
                Code::S010,
                pos,
                format!(
                    "a zero `T()` needs a hardware data type, not `{}`; write a full value, for \
                     example a constructor with one value for each field",
                    self.tys.text(t)
                ),
            );
        }
        self.bounded(pos, self.tys.zero_depth(t))?;
        limit::zero(&self.tys.meta(t).zero_size).map_err(at(pos))?;
        self.fuel
            .pay_int(&self.tys.meta(t).zero_size)
            .map_err(at(pos))?;
        match self.tys.zero(t) {
            Some(v) => Ok(v),
            None => fail(Code::S010, pos, format!("{} has no zero", self.tys.text(t))),
        }
    }

    /// A record constructor of the struct type `ty` at `pos`. The arguments paid their copies.
    /// Each field is a typed use in declaration order, in a data context (section 9.2): a
    /// register or a wire is read. A literal with `[]` takes the type of its field. A field can
    /// hold a hardware value or a hardware aggregate. Then the record checks its depth and
    /// charges its size.
    fn record(&mut self, pos: Pos, ty: TyId, callee: Out, xs: &[Expr]) -> Res<Agg> {
        let Some(fields) = self.tys.parts(ty).map(|p| p.types) else {
            return fail(
                Code::S010,
                pos,
                format!("{} has no specialization", self.tys.text(ty)),
            );
        };
        if fields.len() != xs.len() {
            return fail(
                Code::S007,
                pos,
                format!(
                    "a struct constructor takes 0 or {} argument(s), but it has {}; pass one \
                     value for each field, or none for the zero",
                    fields.len(),
                    xs.len()
                ),
            );
        }
        let fields = fields.to_vec();
        let at = self.store.park(callee);
        let args = self.args(xs)?;
        self.store.resume_one(at);
        let mut sizes = 0u128;
        for a in &args {
            sizes += self.size(a);
        }
        self.charge(pos, sizes)?;
        let mut pieces = Vec::with_capacity(args.len());
        for ((field, arg), x) in fields.into_iter().zip(args).zip(xs) {
            pieces.push(self.typed_use(pos, field, false, arg, Field(x.pos()))?);
        }
        self.made_pieces(pos, ty, pieces)
    }

    /// A field `.f` or a selector `.N` of an enum is `S010` (section 6.2). `f` is the field name
    /// or the number of the selector. An enum has the leaves `tag` and `payload`, but no field.
    /// Another value passes.
    pub(super) fn no_enum_field(&self, pos: Pos, f: &str, seen: Seen<'_>) -> Res<()> {
        let t = match seen {
            Seen::Static(Value::Enum(t, ..)) => *t,
            Seen::Agg(a) => match a.stored_ty() {
                Some(t) if matches!(self.tys.get(t), Ty::Enum(_)) => t,
                _ => return Ok(()),
            },
            _ => return Ok(()),
        };
        self.enum_field_error(pos, f, t)
    }

    /// The `S010` of a field or a selector `f` of the enum type `t`, with the bits of the enum
    /// as the fix.
    pub(super) fn enum_field_error<T>(&self, pos: Pos, f: &str, t: TyId) -> Res<T> {
        fail(
            Code::S010,
            pos,
            format!(
                "`{}` is an enum and has no field `{f}`; read a payload with `match`, or the bits \
                 with `reinterpret(UInt[{}], e)`",
                self.tys.text(t),
                int_text(&self.tys.meta(t).width)
            ),
        )
    }

    /// The number of the field with the symbol `y` and the name `name` among the parts `names` of
    /// a struct type. Each look-up of a field by its name reads the member map here and nowhere
    /// else. No symbol is a name that the scan did not intern, and the top expression has no
    /// symbols for its fields. It runs once, so a search by name stays within its size.
    pub(super) fn field_number_by(
        &self,
        names: PartNames,
        y: Option<Sym>,
        name: &str,
    ) -> Option<usize> {
        match (y, self.names) {
            (Some(sym), _) => names.members(&self.syms.struct_fields)?.get(&sym).copied(),
            (None, Names::File) => None,
            (None, Names::Top) => match self.file.ast().get(names.item()?)? {
                Item::Struct { fields, .. } => fields.iter().position(|d| d.name.name == name),
                _ => None,
            },
        }
    }

    /// The number of the field `f` among the parts `names` of a struct type, by the symbol of its
    /// name.
    pub(super) fn field_number(&self, names: PartNames, f: &Ident) -> Option<usize> {
        self.field_number_by(names, self.port_sym(f), &f.name)
    }

    /// The number of the field `f` of the record that `cur` finds, and its type. A field
    /// selection refers to the field, so it charges no size. A missing field is `S010`: "No
    /// field" for a struct type, else the text of the value.
    pub(super) fn field_at_by(
        &self,
        pos: Pos,
        f: FieldName<'_>,
        cur: Seen<'_>,
    ) -> Res<(usize, TyId)> {
        self.no_enum_field(pos, f.name, cur)?;
        if let Seen::Agg(a) = cur {
            return self
                .agg_field_at_by(a, f.sym, f.name)
                .ok_or(())
                .or_else(|()| self.missing_field(pos, f, self.record_ty(a), cur));
        }
        let record = match cur {
            Seen::Static(Value::Record(t, _)) => Some(*t),
            _ => None,
        };
        let found = record.and_then(|t| {
            let parts = self.tys.parts(t)?;
            let k = self.field_number_by(parts.names, f.sym, f.name)?;
            Some((k, parts.types.get(k).copied()?))
        });
        match found {
            Some(found) => Ok(found),
            None => self.missing_field(pos, f, record, cur),
        }
    }

    /// The `S010` of the field `f` that the value `cur` does not have, at `pos`. A struct type
    /// `record` gives "No field" (section 6.2). Another value gives its text.
    pub(super) fn missing_field<T>(
        &self,
        pos: Pos,
        f: FieldName<'_>,
        record: Option<TyId>,
        cur: Seen<'_>,
    ) -> Res<T> {
        match record {
            Some(ty) => no_field(pos, &self.tys.text(ty), &f.shown()),
            None => fail(
                Code::S010,
                pos,
                format!("{} has no field `{}`", self.text(cur), f.shown()),
            ),
        }
    }

    /// The number of the field `f` of the record that `cur` finds, and its type
    /// (`field_at_by`), by the symbol of its name.
    pub(super) fn field_at(&self, pos: Pos, f: &Ident, cur: Seen<'_>) -> Res<(usize, TyId)> {
        self.field_at_by(pos, self.field_name(f), cur)
    }

    /// The name of the field `f` of the source, with its symbol.
    pub(super) fn field_name<'f>(&self, f: &'f Ident) -> FieldName<'f> {
        FieldName {
            sym: self.port_sym(f),
            name: &f.name,
            keyed: false,
        }
    }

    /// The field `.f` of a record: a reference to the field.
    pub(super) fn record_field(&mut self, pos: Pos, b: Out, f: &Ident) -> Res<Out> {
        let (k, _) = self.field_at(pos, f, self.store.seen(&b))?;
        Ok(super::place::elem(Opnd::Static(b), k))
    }

    /// `data_bits(T)` at the call `pos`: the width of a hardware data type, from its metadata.
    /// It charges its node and the size of the width that it copies, so the size of the type
    /// does not count.
    pub(super) fn data_bits(&mut self, pos: Pos, g: &str, vs: &[Out]) -> Res<Option<Out>> {
        match vs {
            [v] => match self.store.seen(v) {
                Seen::Static(Value::Type(t)) => {
                    let t = *t;
                    self.not_handle(pos, t)?;
                    let meta = self.tys.meta(t);
                    if meta.data {
                        let units = u128::from(int_size(&meta.width));
                        self.charge(pos, units)?;
                        let width = self.tys.meta(t).width.clone();
                        Ok(Some(Out::Made(Val::Static(Value::Int(width)))))
                    } else {
                        fail(
                            Code::S010,
                            pos,
                            format!(
                                "`data_bits` needs a hardware data type, not `{}`; only a \
                                 fixed-width type has a bit count, for example `UInt[8]`",
                                self.tys.text(t)
                            ),
                        )
                    }
                }
                s => fail(
                    Code::S010,
                    pos,
                    format!("`{g}` needs a type, not {}", self.text(s)),
                ),
            },
            _ => fail(
                Code::S007,
                pos,
                format!("`{g}` takes 1 argument(s), but it has {}", vs.len()),
            ),
        }
    }
}
