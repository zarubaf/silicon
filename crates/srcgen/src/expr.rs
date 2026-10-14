// SPDX-License-Identifier: Apache-2.0
//! The source spelling of each core expression form. Every value is a
//! `UInt[w]`; `Bool` appears only in `if` conditions.

use super::lift::Unsupported;
use super::shape::Shape;
use core_ir::Pred;
use core_ir::ast::{BinOp, Expr, Module, UnOp};
use core_ir::r#gen::RESET;
use num_bigint::BigUint;
use std::collections::HashMap;

/// What the expressions of one module can name: the widths of its ports,
/// lets, and registers, and the module of each instance.
pub(super) struct Env<'a> {
    pub widths: HashMap<&'a str, u32>,
    pub insts: HashMap<&'a str, &'a Module>,
    /// A name that source spells as another text, for example the
    /// response register of a memory.
    pub alias: HashMap<&'a str, String>,
    /// The groups of each module, by module name.
    pub shapes: &'a HashMap<&'a str, Shape>,
}

impl Env<'_> {
    pub(super) fn width(&self, e: &Expr) -> Result<u32, Unsupported> {
        Ok(match e {
            Expr::Ref(n) => *self.widths.get(n.text.as_str()).ok_or_else(|| {
                // Source cannot read the reset of the domain.
                if n.text == RESET {
                    Unsupported::Reset(n.text.clone())
                } else {
                    Unsupported::Name(n.text.clone())
                }
            })?,
            Expr::InstOut { inst, port, .. } => self.inst_out(&inst.text, &port.text)?,
            Expr::Const { width, .. } | Expr::Extract { width, .. } => width.value,
            Expr::Unary { arg, .. } => self.width(arg)?,
            Expr::Binary {
                op: BinOp::Concat,
                lhs,
                rhs,
                ..
            } => self.width(lhs)? + self.width(rhs)?,
            Expr::Binary { lhs, .. } => self.width(lhs)?,
            Expr::Icmp { .. } => 1,
            Expr::Mux { then, .. } => self.width(then)?,
            Expr::Replicate { arg, count, .. } => self.width(arg)? * count.value,
            Expr::Read { mem, .. } => return Err(Unsupported::Memory(mem.text.clone())),
        })
    }

    fn inst_out(&self, inst: &str, port: &str) -> Result<u32, Unsupported> {
        let unknown = || Unsupported::Name(format!("{inst}.{port}"));
        let module = self.insts.get(inst).ok_or_else(unknown)?;
        module
            .ports
            .iter()
            .find_map(|p| match p.ty {
                core_ir::ast::Ty::Bits(n) if p.name.text == port => Some(n.value),
                _ => None,
            })
            .ok_or_else(unknown)
    }

    pub(super) fn source(&self, e: &Expr) -> Result<String, Unsupported> {
        Ok(match e {
            Expr::Ref(n) => {
                self.width(e)?;
                self.alias
                    .get(n.text.as_str())
                    .map_or_else(|| n.text.clone(), Clone::clone)
            }
            Expr::InstOut { inst, port, .. } => {
                let leaf = self
                    .insts
                    .get(inst.text.as_str())
                    .and_then(|m| self.shapes.get(m.name.text.as_str()))
                    .and_then(|shape| shape.read(&port.text))
                    .unwrap_or_else(|| port.text.clone());
                format!("{}.{leaf}", inst.text)
            }
            Expr::Const { width, value, .. } => format!("UInt[{}]({value})", width.value),
            Expr::Unary {
                op: UnOp::Not, arg, ..
            } => format!("(~{})", self.source(arg)?),
            Expr::Binary { op, lhs, rhs, .. } => self.binary(*op, lhs, rhs)?,
            Expr::Icmp { pred, lhs, rhs, .. } => {
                let w = self.width(lhs)?;
                let (a, b) = (self.source(lhs)?, self.source(rhs)?);
                let (op, signed) = compare(*pred);
                let side = |x: String| {
                    if signed {
                        format!("reinterpret(SInt[{w}], {x})")
                    } else {
                        x
                    }
                };
                format!(
                    "(if (({} {op} {})) {{ UInt[1](1) }} else {{ UInt[1](0) }})",
                    side(a),
                    side(b)
                )
            }
            Expr::Mux {
                cond, then, els, ..
            } => format!(
                "(if (({} == UInt[1](1))) {{ {} }} else {{ {} }})",
                self.source(cond)?,
                self.source(then)?,
                self.source(els)?
            ),
            Expr::Extract { arg, lo, width, .. } => {
                let a = self.source(arg)?;
                let shifted = if *lo == 0 {
                    a
                } else {
                    format!("({a} >> {lo})")
                };
                format!("resize(UInt[{}], {shifted})", width.value)
            }
            Expr::Replicate { arg, count, .. } => self.replicate(arg, count.value)?,
            Expr::Read { mem, .. } => return Err(Unsupported::Memory(mem.text.clone())),
        })
    }

    fn binary(&self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Result<String, Unsupported> {
        let (a, b) = (self.source(lhs)?, self.source(rhs)?);
        Ok(match op {
            BinOp::Add => format!("({a} +% {b})"),
            BinOp::Sub => format!("({a} -% {b})"),
            BinOp::Mul => format!("({a} *% {b})"),
            BinOp::And => format!("({a} & {b})"),
            BinOp::Or => format!("({a} | {b})"),
            BinOp::Xor => format!("({a} ^ {b})"),
            BinOp::Shl => format!("({a} << {b})"),
            BinOp::Shru => format!("({a} >> {b})"),
            BinOp::Shrs => {
                let w = self.width(lhs)?;
                format!("reinterpret(UInt[{w}], (reinterpret(SInt[{w}], {a}) >> {b}))")
            }
            BinOp::Concat => {
                let (wl, total) = (self.width(rhs)?, self.width(lhs)? + self.width(rhs)?);
                format!("((resize(UInt[{total}], {a}) << {wl}) | resize(UInt[{total}], {b}))")
            }
        })
    }

    /// `a * (1 + 2^w + ... )` places `k` copies of `a` side by side; the
    /// partial products do not overlap because `a < 2^w`, and `a` appears once.
    fn replicate(&self, arg: &Expr, k: u32) -> Result<String, Unsupported> {
        let a = self.source(arg)?;
        if k == 1 {
            return Ok(a);
        }
        let w = self.width(arg)?;
        let total = w * k;
        let ones: BigUint = (0..k).map(|i| BigUint::from(1u8) << (i * w)).sum();
        Ok(format!(
            "(resize(UInt[{total}], {a}) *% UInt[{total}]({ones}))"
        ))
    }
}

/// The source operator and whether the operands are signed.
fn compare(pred: Pred) -> (&'static str, bool) {
    match pred {
        Pred::Eq => ("==", false),
        Pred::Ne => ("!=", false),
        Pred::Ult => ("<", false),
        Pred::Ule => ("<=", false),
        Pred::Ugt => (">", false),
        Pred::Uge => (">=", false),
        Pred::Slt => ("<", true),
        Pred::Sle => ("<=", true),
        Pred::Sgt => (">", true),
        Pred::Sge => (">=", true),
    }
}
