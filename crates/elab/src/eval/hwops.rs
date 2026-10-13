// SPDX-License-Identifier: Apache-2.0
//! The hardware operations of Lean `Source.Eval`. A hardware operation makes one node and
//! charges 1 plus the number of its operands. Its operand trees are shared, so the work is
//! constant per node. A read of a handle and a lift of a static operand only refer, so they
//! charge nothing.
//!
//! A constant node copies a Boolean or a finite value. A finite value has at most 1024 words,
//! because a width is at most 65536, so the copy stays within a constant factor of the charge.

use super::{Evaluator, Opnd, Res, at, fail};
use crate::Code;
use crate::hw::{Graph, HwId, Op, Val};
use crate::int::unsigned_size;
use crate::ops::{self, Fuel, MAX_WIDTH, binop_text, int_text, unop_text};
use crate::types::{Ty, TyId, Types};
use crate::value::{Value, int_size};
use parse::ast::{BinOp, Pos, UnOp};
use resolve::Prelude;

/// The amount of a static shift count that the lowering reads: `min k 65536`.
fn amount(k: Option<u64>) -> u32 {
    let k = k.map_or(MAX_WIDTH, |k| k.min(MAX_WIDTH));
    u32::try_from(k).unwrap_or(u32::MAX)
}

/// A static value as a constant node. Only a Boolean and a finite value have a hardware type.
fn lit_of(pos: Pos, v: Value, graph: &mut Graph, tys: &Types) -> Res<HwId> {
    match v {
        Value::Bool(_) | Value::UInt(_) | Value::SInt(_) => {
            let ty = v.scalar_ty().unwrap_or(Ty::Bool);
            Ok(graph.mk(pos, ty, Op::Lit(v), Vec::new()))
        }
        v => fail(
            Code::S010,
            pos,
            format!(
                "hardware needs a Bool or a finite value, not {}",
                v.text(tys)
            ),
        ),
    }
}

/// The static value `v` as a constant node. A value that has no hardware type fails before its
/// copy.
fn lit_value(pos: Pos, v: &Value, graph: &mut Graph, tys: &Types) -> Res<HwId> {
    if !matches!(v, Value::Bool(_) | Value::UInt(_) | Value::SInt(_)) {
        return fail(
            Code::S010,
            pos,
            format!(
                "hardware needs a Bool or a finite value, not {}",
                v.text(tys)
            ),
        );
    }
    lit_of(pos, v.clone(), graph, tys)
}

/// The static value `v` next to a hardware operand of the type `t`. An integer takes the
/// type `t`, with the charge of its conversion.
fn lit_value_at(
    pos: Pos,
    t: &Ty,
    v: &Value,
    fuel: &mut Fuel,
    graph: &mut Graph,
    tys: &mut Types,
) -> Res<HwId> {
    if matches!(v, Value::Int(_)) && t.is_finite() {
        let t = tys.mk(t.clone());
        let converted = ops::convert(t, v, fuel, tys).map_err(at(pos))?;
        let v = converted.unwrap_or_else(|| v.clone());
        return lit_of(pos, v, graph, tys);
    }
    lit_value(pos, v, graph, tys)
}

impl Evaluator<'_> {
    /// Makes a hardware node. It charges 1 plus the number of its operands.
    fn node(&mut self, pos: Pos, ty: Ty, op: Op, args: Vec<HwId>) -> Res<Val> {
        self.charge(pos, 1 + args.len() as u128)?;
        Ok(Val::Hw(self.graph.mk(pos, ty, op, args)))
    }

    /// A static value at a hardware use. Only a Boolean and a finite value have a hardware
    /// type.
    pub(super) fn lit(&mut self, pos: Pos, v: Value) -> Res<HwId> {
        lit_of(pos, v, &mut self.graph, &self.tys)
    }

    /// A static result at a hardware use. The copy of a constant is small, so a value that
    /// has no hardware type fails before its copy.
    fn lit_out(&mut self, pos: Pos, o: &super::Out) -> Res<HwId> {
        lit_value(pos, self.store.value(o), &mut self.graph, &self.tys)
    }

    /// A static operand next to a hardware operand of the type `t`. An integer takes the
    /// type `t`.
    fn lit_at(&mut self, pos: Pos, t: &Ty, o: &super::Out) -> Res<HwId> {
        let v = self.store.value(o);
        lit_value_at(pos, t, v, &mut self.fuel, &mut self.graph, &mut self.tys)
    }

    /// Two data operands as hardware. At least one of them is hardware.
    fn hw_pair(&mut self, pos: Pos, lhs: Opnd, rhs: Opnd) -> Res<(HwId, HwId)> {
        match (lhs, rhs) {
            (Opnd::Hw(left), Opnd::Hw(right)) => Ok((left, right)),
            (Opnd::Hw(left), Opnd::Static(right)) => {
                let ty = self.graph.ty(left);
                Ok((left, self.lit_at(pos, &ty, &right)?))
            }
            (Opnd::Static(left), Opnd::Hw(right)) => {
                let ty = self.graph.ty(right);
                Ok((self.lit_at(pos, &ty, &left)?, right))
            }
            (Opnd::Static(left), Opnd::Static(right)) => fail(
                Code::S010,
                pos,
                format!(
                    "expected data operands, not {} and {}",
                    self.store.value(&left).text(&self.tys),
                    self.store.value(&right).text(&self.tys)
                ),
            ),
        }
    }

    pub(super) fn hw_unary(&mut self, pos: Pos, op: UnOp, a: HwId) -> Res<Val> {
        let t = self.graph.ty(a);
        match (op, &t) {
            (UnOp::Not, Ty::Bool) => self.node(pos, Ty::Bool, Op::Un(op), vec![a]),
            (UnOp::Inv | UnOp::Neg, t) if t.is_finite() => {
                self.node(pos, t.clone(), Op::Un(op), vec![a])
            }
            _ => fail(
                Code::S010,
                pos,
                format!(
                    "`{}` does not accept {}",
                    unop_text(op),
                    self.tys.text_of(&t)
                ),
            ),
        }
    }

    /// A shift with a hardware operand. A static count becomes an `Int` constant of the
    /// node, so the lowering can use the row "Shift by a static count" of section 7.4.
    fn hw_shift(&mut self, pos: Pos, op: BinOp, a: Opnd, b: &Opnd) -> Res<Val> {
        let count = match b {
            Opnd::Static(o) => match self.store.value(o) {
                Value::Int(k) if k.is_negative() => {
                    return fail(
                        Code::S013,
                        pos,
                        format!("the shift count {} is negative", int_text(k)),
                    );
                }
                Value::Int(k) => {
                    let (amount, size) = (amount(k.to_u64()), int_size(k));
                    self.graph
                        .mk(pos, Ty::Int, Op::Count { amount, size }, Vec::new())
                }
                Value::UInt(x) => {
                    let amount = crate::int::min_unsigned(x, 65536);
                    let size = unsigned_size(x);
                    self.graph
                        .mk(pos, Ty::Int, Op::Count { amount, size }, Vec::new())
                }
                v => {
                    return fail(
                        Code::S010,
                        pos,
                        format!(
                            "a shift count is UInt or a static Int, not {}",
                            v.text(&self.tys)
                        ),
                    );
                }
            },
            Opnd::Hw(c) => {
                let ty = self.graph.ty(*c);
                if matches!(ty, Ty::UInt(_)) {
                    *c
                } else {
                    return fail(
                        Code::S010,
                        pos,
                        format!(
                            "a shift count is UInt or a static Int, not {}",
                            self.tys.text_of(&ty)
                        ),
                    );
                }
            }
        };
        let left = match a {
            Opnd::Hw(x) => x,
            Opnd::Static(o) => self.lit_at(pos, &Ty::Bool, &o)?,
        };
        let t = self.graph.ty(left);
        if t.is_finite() {
            self.node(pos, t, Op::Bin(op), vec![left, count])
        } else {
            fail(
                Code::S010,
                pos,
                format!(
                    "`{}` does not accept {}",
                    binop_text(op),
                    self.tys.text_of(&t)
                ),
            )
        }
    }

    /// A binary operator with at least one hardware operand. Both operands are data.
    pub(super) fn hw_binary(&mut self, pos: Pos, op: BinOp, lhs: Opnd, rhs: Opnd) -> Res<Val> {
        match op {
            BinOp::Shl | BinOp::Shr => return self.hw_shift(pos, op, lhs, &rhs),
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "`{}` accepts only Int and Nat; hardware has `+%`, `-%`, and `*%`",
                        binop_text(op)
                    ),
                );
            }
            _ => {}
        }
        let (left, right) = self.hw_pair(pos, lhs, rhs)?;
        let (ty, other) = (self.graph.ty(left), self.graph.ty(right));
        let accepted = ty == other
            && match op {
                BinOp::Eq | BinOp::Ne => true,
                BinOp::Land | BinOp::Lor => ty == Ty::Bool,
                _ => ty.is_finite(),
            };
        if !accepted {
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{}` does not accept {} and {}",
                    binop_text(op),
                    self.tys.text_of(&ty),
                    self.tys.text_of(&other)
                ),
            );
        }
        let result = match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Land
            | BinOp::Lor
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge => Ty::Bool,
            _ => ty,
        };
        self.node(pos, result, Op::Bin(op), vec![left, right])
    }

    /// A hardware `if` with the condition `cond`. A static arm takes the type of the other
    /// arm. Both arms have one type. Two function arms are a static pair: they charge as a
    /// static equality, and one function item gives the static value. Two different functions
    /// are `S011`.
    pub(super) fn mux(&mut self, pos: Pos, cond: HwId, yes: Opnd, no: Opnd) -> Res<Val> {
        if let (Opnd::Static(y), Opnd::Static(n)) = (&yes, &no)
            && let (v @ Value::Function(i, _), w @ Value::Function(j, _)) =
                (self.store.value(y), self.store.value(n))
        {
            let (same, kept) = (i == j, v.clone());
            self.charge(pos, u128::from(v.size()) + u128::from(w.size()))?;
            if same {
                return Ok(Val::Static(kept));
            }
            return fail(
                Code::S011,
                pos,
                "the arms of a hardware `if` are two different functions".to_owned(),
            );
        }
        let (left, right) = match (yes, no) {
            (Opnd::Static(yes), Opnd::Static(no)) => {
                let yes_ty = self.store.value(&yes).finite_ty();
                let no_ty = self.store.value(&no).finite_ty();
                match (yes_ty, no_ty) {
                    (Some(ty), _) => {
                        let left = self.lit_out(pos, &yes)?;
                        (left, self.lit_at(pos, &ty, &no)?)
                    }
                    (_, Some(ty)) => {
                        let left = self.lit_at(pos, &ty, &yes)?;
                        (left, self.lit_out(pos, &no)?)
                    }
                    _ => {
                        let left = self.lit_out(pos, &yes)?;
                        (left, self.lit_out(pos, &no)?)
                    }
                }
            }
            (yes, no) => self.hw_pair(pos, yes, no)?,
        };
        let (ty, other) = (self.graph.ty(left), self.graph.ty(right));
        if ty == other {
            self.node(pos, ty, Op::Mux, vec![cond, left, right])
        } else {
            fail(
                Code::S010,
                pos,
                format!(
                    "the arms of an `if` have one type, not {} and {}",
                    self.tys.text_of(&ty),
                    self.tys.text_of(&other)
                ),
            )
        }
    }

    /// `resize` or `reinterpret` of a hardware value.
    pub(super) fn hw_convert(&mut self, pos: Pos, f: Prelude, to: TyId, arg: HwId) -> Res<Val> {
        let from = self.graph.ty(arg);
        let to = self.tys.get(to).clone();
        let to = &to;
        match (f, to, &from) {
            (Prelude::Resize, Ty::UInt(_), Ty::UInt(_))
            | (Prelude::Resize, Ty::SInt(_), Ty::SInt(_)) => {
                self.node(pos, to.clone(), Op::Resize, vec![arg])
            }
            (
                Prelude::Reinterpret,
                Ty::UInt(width) | Ty::SInt(width),
                Ty::UInt(old) | Ty::SInt(old),
            ) if old == width => self.node(pos, to.clone(), Op::Reinterpret, vec![arg]),
            _ => fail(
                Code::S010,
                pos,
                format!(
                    "no conversion of {} to {} here",
                    self.tys.text_of(&from),
                    self.tys.text_of(to)
                ),
            ),
        }
    }
}
