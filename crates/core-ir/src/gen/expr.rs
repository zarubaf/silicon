// SPDX-License-Identifier: Apache-2.0
//! Random expressions, each built for its target width.

use num_bigint::BigUint;

use super::scope::{Mem, Scope, Value};
use super::{NARROW, Tape, name, num};
use crate::Pred;
use crate::ast::{BinOp, Expr, UnOp};
use crate::diag::Span;
use crate::typed::address_width;
use crate::value::mask;

const BINOPS: [BinOp; 9] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::Shru,
    BinOp::Shrs,
];

const PREDS: [Pred; 10] = [
    Pred::Eq,
    Pred::Ne,
    Pred::Ult,
    Pred::Ule,
    Pred::Ugt,
    Pred::Uge,
    Pred::Slt,
    Pred::Sle,
    Pred::Sgt,
    Pred::Sge,
];

/// The most levels of nested operations in one expression.
pub(super) const NESTING: u32 = 4;

impl Tape {
    /// An expression of width `width` with at most `nesting` levels of
    /// operations. An operation that does not fit the width gives a leaf.
    pub(super) fn expr(&mut self, scope: &Scope, width: u32, nesting: u32) -> Expr {
        if nesting == 0 {
            return self.leaf(scope, width);
        }
        let sub = |tape: &mut Tape, width| Box::new(tape.expr(scope, width, nesting - 1));
        let span = Span::default();
        match self.below(10) {
            1 => Expr::Unary {
                op: UnOp::Not,
                arg: sub(self, width),
                span,
            },
            2 => Expr::Binary {
                op: BINOPS[self.index(BINOPS.len())],
                lhs: sub(self, width),
                rhs: sub(self, width),
                span,
            },
            3 if width > 1 => {
                let high = self.between(1, width - 1);
                Expr::Binary {
                    op: BinOp::Concat,
                    lhs: sub(self, high),
                    rhs: sub(self, width - high),
                    span,
                }
            }
            4 if width == 1 => {
                let operands = self.width();
                Expr::Icmp {
                    pred: PREDS[self.index(PREDS.len())],
                    lhs: sub(self, operands),
                    rhs: sub(self, operands),
                    span,
                }
            }
            5 => Expr::Mux {
                cond: sub(self, 1),
                then: sub(self, width),
                els: sub(self, width),
                span,
            },
            6 => {
                let arg = width + self.below(NARROW);
                Expr::Extract {
                    lo: self.below(arg - width + 1),
                    arg: sub(self, arg),
                    width: num(width),
                    span,
                }
            }
            7 => {
                let counts: Vec<u32> = (1..=width).filter(|k| width.is_multiple_of(*k)).collect();
                let count = counts[self.index(counts.len())];
                Expr::Replicate {
                    arg: sub(self, width / count),
                    count: num(count),
                    span,
                }
            }
            8 => {
                let fits: Vec<&Mem> = scope.mems.iter().filter(|m| m.width == width).collect();
                match fits.get(self.index(fits.len())) {
                    Some(mem) => Expr::Read {
                        mem: name(mem.name.clone()),
                        addr: sub(self, address_width(mem.depth)),
                        span,
                    },
                    None => self.leaf(scope, width),
                }
            }
            _ => self.leaf(scope, width),
        }
    }

    /// A constant, a value of the scope, or a slice of a wider value.
    fn leaf(&mut self, scope: &Scope, width: u32) -> Expr {
        let span = Span::default();
        let wide: Vec<&Value> = scope.values.iter().filter(|v| v.width >= width).collect();
        match (self.below(3), wide.get(self.index(wide.len()))) {
            (1, Some(value)) if value.width == width => value.expr.clone(),
            (1 | 2, Some(value)) => Expr::Extract {
                arg: Box::new(value.expr.clone()),
                lo: self.below(value.width - width + 1),
                width: num(width),
                span,
            },
            _ => Expr::Const {
                width: num(width),
                value: self.constant(width),
                value_span: span,
                span,
            },
        }
    }

    /// A value below `2^width`: zero, one, all ones, or random bits.
    fn constant(&mut self, width: u32) -> BigUint {
        match self.below(4) {
            0 => BigUint::ZERO,
            1 => BigUint::from(1u8),
            2 => mask(width),
            _ => {
                let words: Vec<u32> = (0..width.div_ceil(32))
                    .map(|_| self.below(u32::MAX))
                    .collect();
                BigUint::from_slice(&words) & mask(width)
            }
        }
    }
}
