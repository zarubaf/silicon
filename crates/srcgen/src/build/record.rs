// SPDX-License-Identifier: Apache-2.0
//! Records: the `struct` items, the choice of a specialization, the
//! constructor and the zero, and `data_bits`.
//!
//! A struct of the builder has one of two flavors. A value struct has
//! `Int`, `Bool`, and small container fields, and the builder constructs
//! it. A hardware struct has `Bool`, `UInt[W]`, and `SInt[W]` fields over
//! its parameters, and the builder makes only its zero `S()` and its size
//! `data_bits(S[args])`, so no static integer converts to a finite type.

use super::stat::{Kind, Reach, int};
use super::{Builder, Built, STRUCT_FIELDS, STRUCT_PARAMS, STRUCTS};
use crate::eval::{Value, record_ty};
use crate::program::{FieldTy, Radix, RecTy, SBin, SExpr, STy, StructDef};
use num_bigint::BigInt;

impl Builder {
    /// The `struct` items `S<k>`. They come first, so a `const` can use
    /// them.
    pub(super) fn structs(&mut self) -> Built {
        for k in 0..self.tape.below(STRUCTS + 1) {
            let params: Vec<String> = (0..self.tape.below(STRUCT_PARAMS + 1))
                .map(|i| format!("W{i}"))
                .collect();
            let hardware = self.tape.flag();
            let count = self.tape.between(1, STRUCT_FIELDS);
            let fields = (0..count)
                .map(|i| (format!("m{i}"), self.field_ty(hardware, &params)))
                .collect();
            let def = StructDef {
                name: format!("S{k}"),
                params,
                fields,
            };
            self.structs.push(def);
            self.refresh()?;
        }
        Ok(())
    }

    fn field_ty(&mut self, hardware: bool, params: &[String]) -> FieldTy {
        if hardware {
            return match self.tape.below(4) {
                0 => FieldTy::Static(STy::Bool),
                1 | 2 => FieldTy::UInt(self.field_width(params)),
                _ => FieldTy::SInt(self.field_width(params)),
            };
        }
        match self.tape.below(3) {
            0 => FieldTy::Static(STy::Int),
            1 => FieldTy::Static(STy::Bool),
            _ => FieldTy::Static(self.container_ty(1)),
        }
    }

    /// A width over the parameters, in `1..=20` for the arguments in
    /// `1..=12`.
    fn field_width(&mut self, params: &[String]) -> SExpr {
        let Some(p) = params.get(self.tape.index(params.len())) else {
            return self.number(1, 16);
        };
        match self.tape.below(3) {
            0 => self.number(1, 16),
            1 => SExpr::Name(p.clone()),
            _ => {
                let k = self.number(1, 8);
                SExpr::Binary(SBin::Add, Box::new(SExpr::Name(p.clone())), Box::new(k))
            }
        }
    }

    /// A specialization of a struct at random arguments.
    pub(super) fn record_ty(&mut self) -> Option<STy> {
        let def = self.structs.get(self.tape.index(self.structs.len()))?;
        let name = def.name.clone();
        let count = def.params.len();
        let args: Vec<Value> = (0..count)
            .map(|_| Value::Int(BigInt::from(self.tape.between(1, 12))))
            .collect();
        record_ty(&name, &args, &self.scope)
            .ok()
            .map(|r| STy::Record(Box::new(r)))
    }

    /// A value of the record type `rt`: its zero, or a constructor over
    /// container values of the field types. The type arguments are
    /// literals, or expressions with the same value in each env.
    pub(super) fn record(&mut self, rt: &RecTy, depth: u32, r: Reach<'_>) -> SExpr {
        note!(self, records);
        let targs: Vec<SExpr> = rt.args.iter().map(|a| self.type_argument(a, r)).collect();
        let only_bool = rt.fields.iter().all(|(_, t)| *t == STy::Bool);
        if rt.zeroable() && (!only_bool || self.tape.flag()) {
            note!(self, zeros);
            return SExpr::Zero(rt.name.clone(), targs);
        }
        let fields = rt
            .fields
            .iter()
            .map(|(_, t)| self.container(t, depth, r))
            .collect();
        SExpr::Record(rt.name.clone(), targs, fields)
    }

    /// An expression with the value `v` in each env: a literal, or
    /// `((e * 0) + v)` over a static candidate `e` that evaluates.
    fn type_argument(&mut self, v: &Value, r: Reach<'_>) -> SExpr {
        let Value::Int(n) = v else {
            return super::stat::value_expr(v);
        };
        let literal = match u64::try_from(n) {
            Ok(k) => self.literal(k),
            Err(_) => SExpr::Int(n.clone(), Radix::Dec),
        };
        let Some(envs) = r.envs else {
            return literal;
        };
        if self.tape.below(4) != 3 {
            return literal;
        }
        note!(self, arguments);
        let e = self.sexpr(Kind::Int, 1, r);
        if self.values(&e, envs).is_none() {
            note!(self, argument_fallbacks);
            return literal;
        }
        let zero = super::stat::bin(SBin::Mul, e, int(0));
        super::stat::bin(SBin::Add, zero, literal)
    }

    /// `data_bits(S[args])` of a struct of hardware data, with arguments
    /// in `1..=12` in each env. `None` if no struct is hardware data or
    /// the position has no envs.
    pub(super) fn data_bits(&mut self, r: Reach<'_>) -> Option<SExpr> {
        let envs = r.envs?;
        let hardware: Vec<&StructDef> = self
            .structs
            .iter()
            .filter(|d| {
                d.fields.iter().all(|(_, t)| {
                    matches!(
                        t,
                        FieldTy::UInt(_) | FieldTy::SInt(_) | FieldTy::Static(STy::Bool)
                    )
                })
            })
            .collect();
        let def = *hardware.get(self.tape.index(hardware.len()))?;
        let (name, params) = (def.name.clone(), def.params.len());
        let targs: Vec<SExpr> = (0..params)
            .map(|_| self.argument(&STy::Nat, r, envs))
            .collect();
        note!(self, data_bits);
        Some(SExpr::DataBits(name, targs))
    }
}
