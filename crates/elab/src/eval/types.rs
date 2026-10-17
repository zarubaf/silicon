// SPDX-License-Identifier: Apache-2.0
//! The types as values of Lean `Source.Eval.Types` and `Source.Eval`: the type expressions, the
//! type families, the tuple and array types with the charges of their metadata, and the struct
//! specializations (design sections 5.1, 5.4, 5.5, and 5.6).
//!
//! A struct specialization is one entry of the table `Types` for its item and its static
//! arguments after their typed use at the parameter types. Each argument charges its size right
//! after its typed use, and only then is it copied into the frame, so a later parameter type
//! reads it as a local. A first use then charges the size of the struct type, evaluates the
//! field types, and charges the metadata. A later use finds the entry and charges nothing more.

use super::{Evaluator, Out, ROOT, Res, Slot, Stop, at, expr_pos, fail, need, type_pos};
use crate::hw::{Ref, Root, Seen, Val};
use crate::int::Int;
use crate::limit;
use crate::ops;
use crate::types::{EnumStatus, Meta, Ty, TyId, TyParam, Types, Variant};
use crate::value::Value;
use crate::{Code, Error};
use parse::ast::{
    Expr, FnParam, Ident, Item, NodeId, Param, ParamMode, Pos, StructField, TypeExpr,
    Variant as VariantItem,
};
use resolve::{DeclId, Prelude, Target};
use std::collections::BTreeMap;

/// The most bits of the payload of an enum.
const PAYLOAD_LIMIT: u64 = 65536;

impl Evaluator<'_> {
    /// The index of the struct item that the name node `id` refers to.
    pub(super) fn struct_item(&self, id: NodeId) -> Option<usize> {
        let Some(Target::Decl(decl)) = self.target(id) else {
            return None;
        };
        let i = *self.items.get(&decl)?;
        matches!(self.file.ast().get(i), Some(Item::Struct { .. })).then_some(i)
    }

    /// The index of the item that the name node `id` refers to.
    fn item_of(&self, id: NodeId) -> Option<usize> {
        match self.target(id) {
            Some(Target::Decl(decl)) => self.items.get(&decl).copied(),
            _ => None,
        }
    }

    /// A type expression: one unit for the node, then the rules of the form.
    pub(super) fn type_expr(&mut self, t: &TypeExpr) -> Res<TyId> {
        self.charge(type_pos(t), 1)?;
        self.structural(|ev| ev.type_expr_form(t))
    }

    /// The rules of the form of a type expression, in its structural context.
    fn type_expr_form(&mut self, t: &TypeExpr) -> Res<TyId> {
        match t {
            TypeExpr::Name { pos, id, name } => {
                let o = self.name(*pos, *id, name)?;
                self.type_of(*pos, name, &o)
            }
            TypeExpr::Index { pos, base, args } => match &**base {
                TypeExpr::Name { pos: bp, id, .. } => match self.target(*id) {
                    Some(Target::Prelude(k)) if k.is_type() => {
                        self.charge(*bp, 1)?;
                        self.index(*pos, k, args)
                    }
                    _ => match self.item_of(*id) {
                        Some(i) => {
                            self.charge(*bp, 1)?;
                            self.spec(*pos, i, args)
                        }
                        None => fail(
                            Code::S007,
                            *pos,
                            "a complete type takes no more index".to_owned(),
                        ),
                    },
                },
                _ => fail(
                    Code::S007,
                    *pos,
                    "a complete type takes no more index".to_owned(),
                ),
            },
            TypeExpr::Unit { pos } => {
                let unit = self.tys.mk(Ty::Unit);
                self.charge(*pos, u128::from(unit.size()))?;
                Ok(unit)
            }
            TypeExpr::Tuple { pos, elems } => self.tuple_type(*pos, elems),
            TypeExpr::Array { pos, elem, len } => self.array_type(*pos, elem, len),
            TypeExpr::Fn { pos, params, ret } => self.fn_type(*pos, params, ret),
        }
    }

    /// The type that the name `x` at `pos` holds. Another value is `S010`.
    fn type_of(&self, pos: Pos, x: &str, o: &Out) -> Res<TyId> {
        match self.store.seen(o) {
            Seen::Static(Value::Type(t)) => Ok(*t),
            s => fail(
                Code::S010,
                pos,
                format!("`{x}` names a type, not {}", self.text(s)),
            ),
        }
    }

    /// `UInt[e]` or `SInt[e]` in a type or an expression. The base charged its node.
    pub(super) fn index(&mut self, pos: Pos, k: Prelude, xs: &[Expr]) -> Res<TyId> {
        self.structural(|ev| ev.family(pos, k, xs))
    }

    fn family(&mut self, pos: Pos, k: Prelude, xs: &[Expr]) -> Res<TyId> {
        let base = self.store.parked_len();
        for x in xs {
            let o = self.eval(x)?;
            let o = need(x, o)?;
            self.check_static(pos, &o)?;
            self.store.park(o);
        }
        let outs = self.store.resume(base);
        let views: Vec<&Value> = outs.iter().map(|o| self.store.value(o)).collect();
        let t = ops::family(k, &views, &mut self.tys).map_err(at(pos))?;
        if matches!(self.tys.get(t), Ty::List(_)) {
            self.bounded(pos, t.depth())?;
        }
        self.charge(pos, u128::from(t.size()))?;
        Ok(t)
    }

    /// The tuple type of the element types `elems` at `pos`. It checks its depth, then charges
    /// its size and the sums of its metadata, as a struct does.
    pub(super) fn tuple_type(&mut self, pos: Pos, elems: &[TypeExpr]) -> Res<TyId> {
        let mut parts = Vec::with_capacity(elems.len());
        for elem in elems {
            parts.push(self.type_expr(elem)?);
        }
        limit::metadata(limit::sum_bits(parts.iter().map(|p| self.tys.meta(*p))))
            .map_err(at(pos))?;
        let (size, depth) = Types::tuple_shape(&parts);
        self.bounded(pos, depth)?;
        self.charge(pos, u128::from(size))?;
        let meta = self.sums(pos, &parts, depth)?;
        Ok(self.tys.mk_with(Ty::Tuple(parts), meta))
    }

    /// The function type with the parameter types `params` and the result type `ret` at `pos`:
    /// the parameter types in order, then the result type, then the type.
    pub(super) fn fn_type(&mut self, pos: Pos, params: &[FnParam], ret: &TypeExpr) -> Res<TyId> {
        self.structural(|ev| ev.fn_type_of(pos, params, ret))
    }

    fn fn_type_of(&mut self, pos: Pos, params: &[FnParam], ret: &TypeExpr) -> Res<TyId> {
        let mut parts = Vec::with_capacity(params.len());
        for p in params {
            parts.push(TyParam {
                mutable: p.mutable,
                ty: self.type_expr(&p.ty)?,
            });
        }
        let ret = self.type_expr(ret)?;
        self.fn_ty(pos, parts, ret)
    }

    /// The function type of the parameters `params` and the result `ret` at `pos`. It checks
    /// its depth, then charges its size, both from the ids of its parts. It has no metadata to
    /// charge: it is not hardware data, and its numbers are 0.
    pub(super) fn fn_ty(&mut self, pos: Pos, params: Vec<TyParam>, ret: TyId) -> Res<TyId> {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Params, params.len() as u64 + 1);
        let (size, depth) = Types::fn_shape(&params, ret);
        self.bounded(pos, depth)?;
        self.charge(pos, u128::from(size))?;
        Ok(self.tys.function(params, ret))
    }

    /// The function item `i` named `name` as a value at the name `pos`. Its signature evaluates
    /// in the scope of the function, with no locals. It takes one nesting level and no call
    /// frame, and each depth check of the signature reports at the name.
    pub(super) fn fn_value(&mut self, pos: Pos, i: usize) -> Res<Out> {
        let file = self.file;
        let Some(Item::Fn {
            name, params, ret, ..
        }) = file.ast().get(i)
        else {
            return fail(Code::S010, pos, "the name is not a value".to_owned());
        };
        // A signature can name its own function in a call, so the evaluation takes a nesting
        // level, which bounds the recursion and keeps it on the stack of its group.
        let signature = self.nested(pos, |ev| {
            let saved = ev.site.replace(pos);
            let signature = ev.in_frame(None, |ev| {
                ev.in_item(i, ROOT, |ev| {
                    let mut parts = Vec::with_capacity(params.len());
                    for q in params {
                        parts.push(TyParam {
                            mutable: q.mode == ParamMode::Mut,
                            ty: ev.type_expr(&q.ty)?,
                        });
                    }
                    Ok((parts, ev.type_expr(ret)?))
                })
            });
            ev.site = saved;
            signature
        });
        let (parts, ret) = signature?;
        let sig = self.fn_ty(pos, parts, ret)?;
        self.tys.name_fn(i, &name.name);
        Ok(Out::Made(Val::Static(Value::Function(i, sig))))
    }

    /// The metadata sums of a tuple or a struct type of the depth `depth` with the parts
    /// `parts`, as Lean `sums`. The sums read the four integers of each part, so they charge
    /// their sizes first. Then they charge the sizes of the four new integers.
    fn sums(&mut self, pos: Pos, parts: &[TyId], depth: u64) -> Res<Meta> {
        self.charge(pos, self.tys.read_charge(parts))?;
        let meta = self.tys.sum(parts);
        self.charge(pos, meta.int_charge(depth))?;
        Ok(meta)
    }

    /// The array type `[elem; len]` at `pos`. The length is a static `Nat`. It checks its
    /// depth, then charges its size and the products of its metadata.
    pub(super) fn array_type(&mut self, pos: Pos, elem: &TypeExpr, len: &Expr) -> Res<TyId> {
        self.structural(|ev| ev.array_type_of(pos, elem, len))
    }

    fn array_type_of(&mut self, pos: Pos, elem: &TypeExpr, len: &Expr) -> Res<TyId> {
        let elem = self.type_expr(elem)?;
        let out = self.eval(len)?;
        let out = need(len, out)?;
        let at_len = super::expr_pos(len);
        self.check_static(at_len, &out)?;
        match self.store.value(&out) {
            Value::Int(n) if n.is_negative() => fail(
                Code::S012,
                at_len,
                format!("the length {} is not a Nat", ops::int_text(n)),
            ),
            Value::Int(n) => {
                let (size, depth) = Types::array_shape(elem, n);
                self.bounded(pos, depth)?;
                limit::metadata(limit::array_bits(self.tys.meta(elem), n)).map_err(at(pos))?;
                let units = u128::from(size) + self.tys.meta(elem).array_charge(n);
                self.fuel.pay(units).map_err(at(pos))?;
                let n = n.clone();
                Ok(self.tys.array(elem, n))
            }
            other => fail(
                Code::S010,
                at_len,
                format!(
                    "the length of an array is a static Nat, not {}",
                    other.text(&self.tys)
                ),
            ),
        }
    }

    /// A use at `pos` of the struct item `i` with the arguments `xs`. Each argument is static.
    /// Each use binds the parameters in the scope of the struct, one level deeper. A literal
    /// with `[]` takes the type of its parameter there, as a module argument does. The typed
    /// uses give the key of the table. The first use evaluates the field types there. The key
    /// exists only after the parameter types, so a use of the struct while its parameter types
    /// evaluate is a cycle (`S019`).
    pub(super) fn spec(&mut self, pos: Pos, i: usize, xs: &[Expr]) -> Res<TyId> {
        self.structural(|ev| ev.spec_use(pos, i, xs))
    }

    fn spec_use(&mut self, pos: Pos, i: usize, xs: &[Expr]) -> Res<TyId> {
        let file = self.file;
        let Some(Item::Struct {
            name,
            params,
            fields,
            ..
        }) = file.ast().get(i)
        else {
            return fail(Code::S007, pos, "a complete type takes no index".to_owned());
        };
        let base = self.store.parked_len();
        for x in xs {
            let o = self.eval(x)?;
            let o = need(x, o)?;
            if !matches!(self.store.seen(&o), Seen::Pending(..)) {
                self.check_static(pos, &o)?;
            }
            self.store.park(o);
        }
        let args = self.store.resume(base);
        self.spec_of(pos, (i, name, params, fields), args)
    }

    /// The use at `pos` of the struct item `i`, with the name, the parameters, and the fields of
    /// its item, for the arguments `args` that evaluated. The prelude struct has no source
    /// position, so each error of its work reports at `pos` (section 6.2).
    pub(super) fn spec_of(
        &mut self,
        pos: Pos,
        (i, name, params, fields): (usize, &Ident, &[Param], &[StructField]),
        args: Vec<Out>,
    ) -> Res<TyId> {
        let file = self.file;
        if params.len() != args.len() {
            return fail(
                Code::S007,
                pos,
                format!(
                    "`{}` takes {} argument(s), but it has {}",
                    name.name,
                    params.len(),
                    args.len()
                ),
            );
        }
        if self.binding.contains(&i) {
            return fail(
                Code::S019,
                pos,
                format!(
                    "the parameter types of `{}` depend on `{}`",
                    name.name, name.name
                ),
            );
        }
        let work = self.nested(pos, |ev| {
            ev.in_frame(None, |ev| {
                ev.in_item(i, ROOT, |ev| {
                    ev.specialize(pos, name, i, params, fields, args)
                })
            })
        });
        // The prelude struct has no source position, so each error of its work reports at the
        // use (section 6.2).
        if file.is_prelude_item(i) {
            work.map_err(|stop| match stop {
                Stop::Error(e) => Stop::Error(Error { pos, ..e }),
                Stop::Stack(e) => Stop::Stack(e),
            })
        } else {
            work
        }
    }

    /// The typed uses of the arguments at the parameter types, then the specialization of the
    /// struct item `i` with them. The parameters bind as locals of the frame of the struct
    /// for the types after them and for the field types.
    fn specialize(
        &mut self,
        pos: Pos,
        name: &Ident,
        i: usize,
        params: &[Param],
        fields: &[StructField],
        args: Vec<Out>,
    ) -> Res<TyId> {
        self.binding.push(i);
        let bound = self.bind_params(pos, params, args)?;
        self.binding.pop();
        let keys: Vec<Out> = bound.into_iter().map(|(_, o)| o).collect();
        self.first_or_later_use(pos, name, i, &keys, fields)
    }

    /// A use at `pos` of the enum item `i` (sections 5.4 and 5.6). A later use reads the done
    /// entry and charges nothing more. A use in progress is `S019`. The first use nests one
    /// level deeper, in the scope of the enum, and runs in a structural context, so the tag
    /// values have its guard (section 9.4).
    pub(super) fn enum_use(&mut self, pos: Pos, i: usize) -> Res<TyId> {
        self.structural(|ev| ev.enum_first_use(pos, i))
    }

    fn enum_first_use(&mut self, pos: Pos, i: usize) -> Res<TyId> {
        let file = self.file;
        let Some(Item::Enum {
            pos: keyword,
            name,
            tag,
            variants,
        }) = file.ast().get(i)
        else {
            return fail(Code::S010, pos, "the enum item is missing".to_owned());
        };
        match self.tys.enum_status(i) {
            EnumStatus::Done(t) => return Ok(t),
            EnumStatus::InProgress => {
                return fail(
                    Code::S019,
                    pos,
                    format!("the enum `{}` depends on itself", name.name),
                );
            }
            EnumStatus::Fresh => {}
        }
        self.nested(pos, |ev| {
            ev.in_frame(None, |ev| {
                ev.in_item(i, ROOT, |ev| {
                    ev.enum_checks(pos, (i, *keyword, name), (tag, variants))
                })
            })
        })
    }

    /// The checks of an enum in the order of section 5.6. It charges the size of the enum type,
    /// then:
    ///
    /// 1. The tag type is `UInt[W]` (`S010`).
    /// 2. For each variant: its tag value gets its typed use at `UInt[W]` (`S010`, `S012`).
    ///    Then the tag goes into the tag map with no charge, and a tag of an earlier variant is
    ///    `S021` at the tag value. Then each payload type is hardware data (`S010`). Then the metadata sums of the tuple
    ///    of the payload types charge, after their size-limit check.
    /// 3. The payload width `P`, the largest width of these tuples, is at most 65536 (`S012` at
    ///    the `enum` keyword). Then the metadata sums of the enum charge.
    fn enum_checks(
        &mut self,
        pos: Pos,
        (item, keyword, name): (usize, Pos, &Ident),
        (tag, variants): (&TypeExpr, &[VariantItem]),
    ) -> Res<TyId> {
        self.charge(pos, 1)?;
        self.tys.begin_enum(item, &name.name);
        let tag_ty = self.type_expr(tag)?;
        let Ty::UInt(tag_width) = *self.tys.get(tag_ty) else {
            return fail(
                Code::S010,
                type_pos(tag),
                format!(
                    "the tag type of an enum is UInt[W], not {}",
                    self.tys.text(tag_ty)
                ),
            );
        };
        let mut width = Int::zero();
        let mut done = Vec::with_capacity(variants.len());
        let mut tags: BTreeMap<Int, usize> = BTreeMap::new();
        for variant in variants {
            let tag_pos = expr_pos(&variant.tag);
            let o = self.eval(&variant.tag)?;
            let o = need(&variant.tag, o)?;
            let converted = self.conform(tag_pos, tag_ty, o)?;
            let tag = match &converted {
                Value::UInt(bits) => bits.clone(),
                other => {
                    return fail(
                        Code::S010,
                        tag_pos,
                        format!(
                            "expected UInt[{tag_width}], but the value is {}",
                            other.text(&self.tys)
                        ),
                    );
                }
            };
            // The check is one map insert, O(log v) compares: no charge (the log factor).
            let key = Int::from_unsigned(&tag);
            if let Some(&earlier) = tags.get(&key) {
                let at = variants[earlier].name.pos;
                return fail(
                    Code::S021,
                    tag_pos,
                    format!(
                        "the variant `{}` has the tag `{key}` of the variant at {}:{}; give each \
                         variant its own tag value",
                        variant.name.name, at.line, at.col
                    ),
                );
            }
            tags.insert(key, done.len());
            let mut payload = Vec::with_capacity(variant.payload.len());
            for ty_expr in &variant.payload {
                let payload_ty = self.type_expr(ty_expr)?;
                if !self.tys.meta(payload_ty).data {
                    return fail(
                        Code::S010,
                        type_pos(ty_expr),
                        format!(
                            "a payload type is hardware data, not {}",
                            self.tys.text(payload_ty)
                        ),
                    );
                }
                payload.push(payload_ty);
            }
            limit::metadata(limit::sum_bits(payload.iter().map(|p| self.tys.meta(*p))))
                .map_err(at(pos))?;
            let (_, depth) = Types::tuple_shape(&payload);
            let meta = self.sums(pos, &payload, depth)?;
            if meta.width > width {
                width = meta.width;
            }
            done.push(Variant { tag, payload });
        }
        if width > Int::from_u64(PAYLOAD_LIMIT) {
            return fail(
                Code::S012,
                keyword,
                format!(
                    "the payload of `{}` has {} bits, above {PAYLOAD_LIMIT}; use smaller payloads",
                    name.name,
                    ops::int_text(&width)
                ),
            );
        }
        let payload_width = u32::try_from(width.to_u64().unwrap_or(0)).unwrap_or(0);
        let mut parts = vec![tag_ty];
        if payload_width > 0 {
            parts.push(self.tys.mk(Ty::UInt(payload_width)));
        }
        let (_, depth) = Types::tuple_shape(&parts);
        let meta = self.sums(pos, &parts, depth)?;
        Ok(self
            .tys
            .finish_enum(item, (tag_width, payload_width), done, tags, meta, depth))
    }

    /// The typed uses at `pos` of the arguments `args` at the parameters `params`, in order,
    /// in the item scope and the frame that the caller sets. Each parameter type evaluates with
    /// the earlier parameters bound. Each argument settles, is static, and converts to its type.
    /// The size of the converted argument charges, and then the parameter binds to a copy of it
    /// in the frame, so a later parameter type reads a local. It gives each parameter type with
    /// the reference to its local.
    pub(super) fn bind_params(
        &mut self,
        pos: Pos,
        params: &[Param],
        args: Vec<Out>,
    ) -> Res<Vec<(TyId, Out)>> {
        let mut bound = Vec::with_capacity(args.len());
        for (q, o) in params.iter().zip(args) {
            let t = self.type_expr(&q.ty)?;
            let o = if matches!(self.store.seen(&o), Seen::Pending(..)) {
                self.settle(pos, t, o)?
            } else {
                o
            };
            self.check_static(pos, &o)?;
            let id = self.decl(&q.name)?;
            bound.push((t, self.bind_argument(pos, t, id, o)?));
        }
        Ok(bound)
    }

    /// The typed use of the argument `o` at the type `t`. The size of the converted value
    /// charges first, so the copy of an argument that is already of the type is paid. The
    /// parameter `id` then binds to the value.
    fn bind_argument(&mut self, pos: Pos, t: TyId, id: DeclId, o: Out) -> Res<Out> {
        let converted =
            ops::convert(t, self.store.value(&o), &mut self.fuel, &self.tys).map_err(at(pos))?;
        let size = match &converted {
            Some(v) => u128::from(v.size()),
            None => self.size(&o),
        };
        self.charge(pos, size)?;
        let value = match converted {
            Some(v) => v,
            None => self.static_value(pos, o)?,
        };
        let frame = self.store.frame_index();
        self.bind(
            id,
            Slot {
                ty: Some(t),
                mutable: false,
                value: Val::Static(value),
            },
        );
        Ok(Out::Ref(Ref {
            root: Root::Local(frame, id),
            path: Vec::new(),
        }))
    }

    /// The specialization of the struct item `i` with the arguments `keys`. `bind_params`
    /// charged the sizes of the arguments before the lookup, which hashes and compares them in
    /// full. A done entry charges nothing more. A first use charges the size of the struct type,
    /// evaluates the field types, checks the depth of the struct type, and charges its
    /// metadata.
    fn first_or_later_use(
        &mut self,
        pos: Pos,
        name: &Ident,
        i: usize,
        keys: &[Out],
        fields: &[StructField],
    ) -> Res<TyId> {
        let values: Vec<&Value> = keys.iter().map(|o| self.store.value(o)).collect();
        let sizes = values
            .iter()
            .fold(0u64, |sum, v| sum.saturating_add(v.size()));
        match self.tys.find_spec(i, &values) {
            Some((_, Some(t))) => return Ok(t),
            Some((s, None)) => {
                return fail(
                    Code::S019,
                    pos,
                    format!(
                        "the specialization {} is in progress",
                        self.tys.text_of(&Ty::Struct(s))
                    ),
                );
            }
            None => {}
        }
        self.fuel.pay(1 + u128::from(sizes)).map_err(at(pos))?;
        let args: Vec<Value> = values.into_iter().cloned().collect();
        let prelude = self.file.is_prelude_item(i);
        let s = self.tys.begin_spec(&name.name, i, args, prelude);
        let mut types = Vec::with_capacity(fields.len());
        for f in fields {
            types.push(self.type_expr(&f.ty)?);
        }
        limit::metadata(limit::sum_bits(types.iter().map(|p| self.tys.meta(*p))))
            .map_err(at(pos))?;
        let depth = self.tys.struct_depth(s, &types);
        self.bounded(pos, depth)?;
        let meta = self.sums(pos, &types, depth)?;
        Ok(self.tys.finish_spec(s, types, meta, depth))
    }
}
