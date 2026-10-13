// SPDX-License-Identifier: Apache-2.0
//! The normal form of a hardware aggregate, as Lean `Eval.normalize` gives it (design section
//! 5.1).

// TODO(#181): remove this allowance when the evaluator reads aggregates.
#![allow(dead_code)]

use super::{Code, Evaluator, Res, at, fail};
use crate::agg::Agg;
use crate::hw::Val;
use crate::types::Ty;
use parse::ast::Pos;

impl Evaluator<'_> {
    /// The normal form of the aggregate `a` at `pos`. A reference without a hardware leaf is a
    /// static value, for example a part of the type `[Unit; 4]`. It charges the zero size of its
    /// type from the metadata before the zero exists (section 5.4), so a huge empty part fails
    /// before any work. A reference of a scalar type is a hardware value. Another reference
    /// stays lazy: it neither expands nor charges.
    pub(super) fn normalize(&mut self, pos: Pos, a: Agg) -> Res<Val> {
        match a {
            Agg::Static(v) => Ok(Val::Static(v)),
            Agg::Hw(h) => Ok(Val::Hw(h)),
            Agg::Ref(base, t) => {
                if self.tys.meta(t).leaves.is_zero() {
                    self.fuel
                        .pay_int(&self.tys.meta(t).zero_size)
                        .map_err(at(pos))?;
                    match self.tys.zero(t) {
                        Some(v) => Ok(Val::Static(v)),
                        None => fail(Code::S010, pos, format!("{} has no zero", self.tys.text(t))),
                    }
                } else if matches!(self.tys.get(t), Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) {
                    let ty = self.tys.get(t).clone();
                    Ok(Val::Hw(self.graph.mk(pos, ty, base.op(), Vec::new())))
                } else {
                    Ok(Val::Agg(Box::new(Agg::Ref(base, t))))
                }
            }
            a => Ok(Val::Agg(Box::new(a))),
        }
    }
}
