// SPDX-License-Identifier: Apache-2.0
//! The records of Lean `Source.Eval.Container` and `Source.Eval` (design section 5.6): the
//! constructor of a type, the zero `T()`, the field `.f`, and `data_bits`.
//!
//! A constructor charges the sizes of its arguments before any copy, so a record copies a
//! value only after it paid for it. The zero charges its size from the metadata before it
//! exists, and `data_bits` reads the width from the metadata, so neither walks the field types.

use super::container::Piece;
use super::{Evaluator, Names, Opnd, Out, Res, at, expr_pos, fail, need};
use crate::Code;
use crate::agg::Agg;
use crate::hw::{Seen, Val};
use crate::limit;
use crate::types::{Ty, TyId};
use crate::value::{Value, int_size};
use parse::ast::{Expr, Ident, Item, Pos};

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

    /// The zero `T()` of the type `t` at `pos` (section 5.6). A type that is not hardware data
    /// is `S010`. The zero checks its depth and charges its size from the metadata before it
    /// exists.
    fn zero(&mut self, pos: Pos, t: TyId) -> Res<Value> {
        if !self.tys.meta(t).data {
            return fail(
                Code::S010,
                pos,
                format!(
                    "a zero `T()` needs a hardware data type, not {}",
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
        let Some((_, fields)) = self.tys.fields(ty) else {
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
                    "a struct constructor takes 0 or {} argument(s), but it has {}",
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
            let arg = self.settle(pos, field, arg)?;
            let arg = self.data(expr_pos(x), arg)?.into_out();
            pieces.push(self.conform_piece(pos, field, Piece::Out(arg))?);
        }
        self.made_pieces(pos, ty, pieces)
    }

    /// The number of the field `f` in the struct item `item`.
    pub(super) fn field_number(&self, item: usize, f: &Ident) -> Option<usize> {
        match self.names {
            Names::File => {
                let sym = self.syms.fields.get(&f.id)?;
                self.syms.struct_fields.get(item)?.get(sym).copied()
            }
            // The top expression has no symbols for its fields. It runs once, so a search by
            // name stays within its size.
            Names::Top => match self.file.ast().get(item)? {
                Item::Struct { fields, .. } => fields.iter().position(|d| d.name.name == f.name),
                _ => None,
            },
        }
    }

    /// The number of the field `f` of the record that `cur` finds, and its type. A field
    /// selection refers to the field, so it charges no size. A missing field is `S010`.
    pub(super) fn field_at(&self, pos: Pos, f: &Ident, cur: Seen<'_>) -> Res<(usize, TyId)> {
        let missing = || {
            fail(
                Code::S010,
                pos,
                format!("{} has no field `{}`", self.text(cur), f.name),
            )
        };
        if let Seen::Agg(a) = cur {
            return self.agg_field_at(a, f).ok_or(()).or_else(|()| missing());
        }
        let Seen::Static(Value::Record(t, _)) = cur else {
            return missing();
        };
        let Some((item, types)) = self.tys.fields(*t) else {
            return missing();
        };
        match self
            .field_number(item, f)
            .and_then(|k| types.get(k).map(|ft| (k, *ft)))
        {
            Some(found) => Ok(found),
            None => missing(),
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
                            format!("`{g}` needs a hardware data type, not {}", self.tys.text(t)),
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
