// SPDX-License-Identifier: Apache-2.0
//! The type expressions of Lean `Source.Eval`: the prelude types, the type families, the tuple
//! and array types, and the metadata of a new type.

use super::{Evaluator, Res, at, fail, need, prim, type_pos};
use crate::Code;
use crate::ops;
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Expr, Pos, TypeExpr};
use resolve::{Prelude, Target};

impl Evaluator<'_> {
    pub(super) fn type_expr(&mut self, t: &TypeExpr) -> Res<TyId> {
        self.charge(type_pos(t), 1)?;
        match t {
            TypeExpr::Name { pos, id, name } => match self.target(*id) {
                Some(Target::Prelude(k)) if k.is_type() => Ok(self.tys.mk(prim(*pos, name, k)?)),
                _ => fail(Code::S010, *pos, format!("`{name}` is not a type")),
            },
            TypeExpr::Index { pos, base, args } => match &**base {
                TypeExpr::Name { pos: bp, id, name } => {
                    self.charge(*bp, 1)?;
                    match self.target(*id) {
                        Some(Target::Prelude(k)) if k.is_type() => self.index(*pos, k, args),
                        _ => fail(Code::S010, *bp, format!("`{name}` is not a type")),
                    }
                }
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
        }
    }

    /// `UInt[e]` or `SInt[e]` in a type or an expression. The base charged its node.
    pub(super) fn index(&mut self, pos: Pos, k: Prelude, xs: &[Expr]) -> Res<TyId> {
        let mut outs = Vec::with_capacity(xs.len());
        for x in xs {
            let o = self.eval(x)?;
            let o = need(x, o)?;
            self.check_static(pos, &o)?;
            outs.push(o);
        }
        let views: Vec<&Value> = outs.iter().map(|o| self.store.value(o)).collect();
        let t = ops::family(k, &views, &mut self.tys).map_err(at(pos))?;
        self.charge(pos, u128::from(t.size()))?;
        Ok(t)
    }

    /// The tuple type of the element types `elems` at `pos`.
    pub(super) fn tuple_type(&mut self, pos: Pos, elems: &[TypeExpr]) -> Res<TyId> {
        let mut types = Vec::with_capacity(elems.len());
        for elem in elems {
            types.push(self.type_expr(elem)?);
        }
        let ty = self.tys.tuple(types);
        self.new_type(pos, ty)
    }

    /// The array type `[elem; len]` at `pos`. The length is a static `Nat`.
    pub(super) fn array_type(&mut self, pos: Pos, elem: &TypeExpr, len: &Expr) -> Res<TyId> {
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
                let ty = self.tys.array(elem, n.clone());
                self.new_type(pos, ty)
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

    /// A new container type at `pos`: its depth, then the charge of its size.
    fn new_type(&mut self, pos: Pos, ty: TyId) -> Res<TyId> {
        self.bounded(pos, ty.depth())?;
        self.charge(pos, u128::from(ty.size()))?;
        Ok(ty)
    }
}
