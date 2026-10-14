// SPDX-License-Identifier: Apache-2.0
//! The file-scope items: consts and `comptime fn`s.
//!
//! A `comptime fn` has one fixed shape: `comptime if ((x0 == 0)) { return
//! BASE; } return STEP;`, where `STEP` calls itself with `(x0 - 1)` once or
//! twice. The recursion is structural, and the body is checked on a sample
//! of arguments before a call site uses it.

use super::stat::{self, Kind, Reach, bin, int};
use super::{Builder, CONSTS, COUNT, FNS, SAMPLE_INTS};
use crate::eval::{Env, Fault, Scope, Value, eval};
use crate::program::{ComptimeFn, Item, SBin, SExpr, STy};
use num_bigint::BigInt;

impl Builder {
    pub(super) fn const_names(&self) -> Vec<(String, STy)> {
        self.consts
            .iter()
            .map(|(n, t, _)| (n.clone(), *t))
            .collect()
    }

    pub(super) fn file_items(&self) -> Vec<Item> {
        let consts = self.consts.iter().map(|(name, ty, value)| Item::Const {
            name: name.clone(),
            ty: *ty,
            value: value.clone(),
        });
        let fns = self.fns.iter().cloned().map(Item::ComptimeFn);
        consts.chain(fns).collect()
    }

    /// The scope of the consts and `comptime fn`s so far. The builder adds
    /// only consts that evaluate, so it does not fault.
    fn refresh(&mut self) -> Result<(), Fault> {
        self.scope = Scope::new(&self.file_items())?;
        Ok(())
    }

    pub(super) fn consts(&mut self) -> Result<(), Fault> {
        let envs = [Env::default()];
        for k in 0..self.tape.below(CONSTS + 1) {
            let names = self.const_names();
            let kind = if self.tape.below(3) == 2 {
                Kind::Bool
            } else {
                Kind::Int
            };
            let r = Reach {
                names: &names,
                fns: 0,
                envs: Some(&envs),
            };
            let (value, vs) = self.evaluated(kind, r, &envs);
            let ty = self.static_ty(kind, &vs);
            self.consts.push((format!("C{k}"), ty, value));
            self.refresh()?;
        }
        Ok(())
    }

    /// `Nat` for most non-negative values (a negative `Nat` is `S012`),
    /// else `Int`; or `Bool`.
    pub(super) fn static_ty(&mut self, kind: Kind, vs: &[Value]) -> STy {
        let natural = vs
            .iter()
            .all(|v| matches!(v, Value::Int(n) if *n >= BigInt::ZERO));
        match kind {
            Kind::Bool => STy::Bool,
            Kind::Int if natural && self.tape.below(4) != 0 => STy::Nat,
            Kind::Int => STy::Int,
        }
    }

    pub(super) fn fns(&mut self) -> Result<(), Fault> {
        for k in 0..self.tape.below(FNS + 1) {
            let f = self.comptime_fn(k as usize);
            self.fns.push(f);
            self.refresh()?;
        }
        Ok(())
    }

    /// `f<k>`, checked on the sample. A body that faults on the sample
    /// takes a simpler step, then a literal base.
    fn comptime_fn(&mut self, k: usize) -> ComptimeFn {
        let name = format!("f{k}");
        let mut params = vec![("x0".to_owned(), STy::Nat)];
        for i in 1..=self.tape.below(3) {
            let t = if self.tape.flag() {
                STy::Bool
            } else {
                STy::Int
            };
            params.push((format!("x{i}"), t));
        }
        let names: Vec<(String, STy)> = params.iter().cloned().chain(self.const_names()).collect();
        let r = Reach {
            names: &names,
            fns: k,
            envs: None,
        };
        let base = self.sexpr(Kind::Int, stat::DEPTH, r);
        let step = self.step(&name, &params, r);
        let fallback = bin(
            SBin::Add,
            self_call(&name, &params, |_, n| SExpr::Name(n.to_owned())),
            int(1),
        );
        let literal = self.number(0, 16);
        let mut f = ComptimeFn {
            name,
            params,
            ret: STy::Int,
            base,
            step,
        };
        let mut results = self.sample(&f);
        if results.is_none() {
            f.step = fallback;
            results = self.sample(&f);
        }
        if results.is_none() {
            f.base = literal;
            results = self.sample(&f);
        }
        if let Some(vs) = results
            && self.static_ty(Kind::Int, &vs) == STy::Nat
        {
            f.ret = STy::Nat;
        }
        f
    }

    /// One or two calls `f<k>((x0 - 1), ...)`, in an expression.
    fn step(&mut self, name: &str, params: &[(String, STy)], r: Reach<'_>) -> SExpr {
        const OPS: [SBin; 8] = [
            SBin::Add,
            SBin::Sub,
            SBin::Mul,
            SBin::And,
            SBin::Or,
            SBin::Xor,
            SBin::Div,
            SBin::Rem,
        ];
        let arg = |b: &mut Builder, t: STy| b.sexpr(stat::kind(t), 1, r);
        let first = self_call(name, params, |t, _| arg(self, t));
        let op = self.pick(&OPS);
        match self.tape.below(3) {
            0 => first,
            1 => bin(op, first, self.sexpr(Kind::Int, 1, r)),
            _ => {
                let second = self_call(name, params, |t, _| arg(self, t));
                bin(op, first, second)
            }
        }
    }

    /// The results of `f` on the sample, if none faults.
    fn sample(&self, f: &ComptimeFn) -> Option<Vec<Value>> {
        let mut items = self.file_items();
        items.push(Item::ComptimeFn(f.clone()));
        let scope = Scope::new(&items).ok()?;
        let mut rows: Vec<Vec<SExpr>> = (0..=i64::from(COUNT)).map(|n| vec![int(n)]).collect();
        for (_, t) in f.params.iter().skip(1) {
            let values: Vec<SExpr> = match t {
                STy::Bool => vec![SExpr::Bool(false), SExpr::Bool(true)],
                _ => SAMPLE_INTS.iter().map(|n| int(*n)).collect(),
            };
            rows = rows
                .into_iter()
                .flat_map(|row| {
                    values.iter().map(move |v| {
                        let mut row = row.clone();
                        row.push(v.clone());
                        row
                    })
                })
                .collect();
        }
        let mut out = Vec::new();
        for row in rows {
            let call = SExpr::Call(f.name.clone(), row);
            out.push(eval(&call, &Env::default(), &scope).ok()?);
        }
        Some(out)
    }
}

/// `f((x0 - 1), a1, ...)` with `a_i` from `arg(type, formal)`.
fn self_call(
    name: &str,
    params: &[(String, STy)],
    mut arg: impl FnMut(STy, &str) -> SExpr,
) -> SExpr {
    let first = params.first().map_or(int(0), |(x, _)| {
        bin(SBin::Sub, SExpr::Name(x.clone()), int(1))
    });
    let rest = params.iter().skip(1).map(|(n, t)| arg(*t, n));
    SExpr::Call(
        name.to_owned(),
        std::iter::once(first).chain(rest).collect(),
    )
}
