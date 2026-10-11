// SPDX-License-Identifier: Apache-2.0
//! Helpers, module signatures, and module bodies: frames and their
//! statements.

use super::hw::{DEPTH, Want};
use super::stat::{Kind, Reach, value_expr};
use super::{
    Builder, CONTEXTS, COUNT, Ctx, ENVS, HELPERS, Helper, Hw, INPUTS, INSTANCES, MODULE_STMTS,
    MODULES, Module, NESTED_STMTS, NESTING, Names, OUTPUTS, PARAMS, SAMPLE_INTS, Sig,
};
use crate::r#gen::eval::{Env, Fault, Value, concrete, eval, loop_values};
use crate::r#gen::program::{HExpr, Place, SExpr, Scalar, StaticTy, Stmt, Ty};
use num_bigint::BigInt;

/// The result of a step whose faults the checks of the builder exclude.
/// A fault reaches `build`, which the coverage test watches.
type Built<T = ()> = Result<T, Fault>;

const STATIC_TYS: [StaticTy; 3] = [StaticTy::Nat, StaticTy::Int, StaticTy::Bool];

/// One env per argument tuple in the ranges of the module arguments.
fn domain(params: &[(String, StaticTy)]) -> Vec<Env> {
    let mut envs = vec![Env::default()];
    for (name, t) in params {
        let values: Vec<Value> = if *t == StaticTy::Bool {
            vec![Value::Bool(false), Value::Bool(true)]
        } else {
            let (lo, hi) = super::stat::arg_range(*t);
            (lo..=hi).map(|n| Value::Int(BigInt::from(n))).collect()
        };
        envs = envs
            .into_iter()
            .flat_map(|env| {
                values.iter().map(move |v| {
                    let mut env = env.clone();
                    env.statics.insert(name.clone(), v.clone());
                    env
                })
            })
            .collect();
    }
    envs
}

impl Builder {
    pub(super) fn helpers(&mut self) -> Built {
        for k in 0..self.tape.below(HELPERS + 1) {
            let h = self.helper(k as usize)?;
            self.helpers.push(h);
        }
        Ok(())
    }

    /// A helper type: `Bool`, or a width that is a literal or a `Nat`
    /// const in `1..=64`.
    fn data_ty(&mut self) -> (Ty, Scalar) {
        let shape = self.tape.below(3);
        if shape == 0 {
            return (Ty::Bool, Scalar::Bool);
        }
        let widths: Vec<(String, u32)> = self
            .consts
            .iter()
            .filter(|(_, t, _)| *t == StaticTy::Nat)
            .filter_map(|(n, _, _)| {
                match eval(&SExpr::Name(n.clone()), &Env::default(), &self.scope) {
                    Ok(Value::Int(v)) => u32::try_from(v)
                        .ok()
                        .filter(|w| (1..=64).contains(w))
                        .map(|w| (n.clone(), w)),
                    _ => None,
                }
            })
            .collect();
        let named = if self.tape.flag() {
            widths.get(self.tape.index(widths.len())).cloned()
        } else {
            None
        };
        let (expr, w) = named.map_or_else(
            || {
                let w = self.tape.between(1, 16);
                (self.literal(u64::from(w)), w)
            },
            |(n, w)| (SExpr::Name(n), w),
        );
        if shape == 1 {
            (Ty::UInt(expr), Scalar::UInt(w))
        } else {
            (Ty::SInt(expr), Scalar::SInt(w))
        }
    }

    /// `h<k>`: `let`s, an optional loop over a `let mut`, and the result.
    /// It has one type for each formal, so one context fits all its calls.
    /// It calls only `h<j>`, `j < k`, so no call cycle occurs.
    fn helper(&mut self, k: usize) -> Built<Helper> {
        let mut names = Names::default();
        let mut params = Vec::new();
        for _ in 0..self.tape.between(1, 2) {
            let (t, s) = self.data_ty();
            params.push((names.fresh("x"), t, s));
        }
        let ret = self.data_ty();
        let mut ctx = Ctx {
            envs: vec![Env::default()],
            statics: self.const_names(),
            hw: params
                .iter()
                .map(|(n, t, s)| Hw {
                    expr: HExpr::Name(n.clone()),
                    ty: Some(t.clone()),
                    types: vec![*s],
                    mutable: false,
                })
                .collect(),
            helpers: k,
        };
        let mut body = Vec::new();
        for _ in 0..self.tape.below(3) {
            self.binding(&mut ctx, &mut names, &mut body, false)?;
        }
        let want = Want {
            types: vec![ret.1],
            ty: Some(ret.0.clone()),
        };
        if self.tape.flag() {
            self.accumulate(&mut ctx, &mut names, &mut body, &want)?;
        }
        let result = self.value(&ctx, &want, DEPTH);
        Ok(Helper {
            name: format!("h{k}"),
            params,
            ret,
            body,
            result,
        })
    }

    /// `let mut v = ...; comptime for j in lo..hi { v = ...; }` with bounds
    /// over consts and literals.
    fn accumulate(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        body: &mut Vec<Stmt>,
        want: &Want,
    ) -> Built {
        let v = names.fresh("v");
        let value = self.value(ctx, want, DEPTH);
        body.push(Stmt::Let {
            name: v.clone(),
            mutable: true,
            ty: want.ty.clone(),
            value,
        });
        ctx.hw.push(Hw {
            expr: HExpr::Name(v.clone()),
            ty: want.ty.clone(),
            types: want.types.clone(),
            mutable: true,
        });
        let binder = names.fresh("j");
        let consts = self.const_names();
        let r = Reach {
            names: &consts,
            fns: 0,
            envs: Some(&ctx.envs),
        };
        let (lo, hi) = self.bounds(r, &ctx.envs);
        let Some(inner) = self.iterations(ctx, &binder, &lo, &hi)? else {
            return Ok(());
        };
        // The accumulator is the last hardware name of `inner`.
        let stmts = match inner.hw.last().map(Want::of) {
            Some(w) if !inner.envs.is_empty() => {
                vec![Stmt::Assign(v, self.value(&inner, &w, DEPTH))]
            }
            _ => vec![Stmt::Error("dead".to_owned())],
        };
        body.push(Stmt::For(binder, lo, hi, stmts));
        Ok(())
    }

    /// The scope of the body of `comptime for binder in lo..hi`, or `None`
    /// when the loop would pass `ENVS` envs.
    fn iterations(&self, ctx: &Ctx, binder: &str, lo: &SExpr, hi: &SExpr) -> Built<Option<Ctx>> {
        let los = self.values(lo, &ctx.envs).ok_or(Fault::Type)?;
        let his = self.values(hi, &ctx.envs).ok_or(Fault::Type)?;
        let mut parents = Vec::new();
        let mut envs = Vec::new();
        for (i, (env, (lo, hi))) in ctx.envs.iter().zip(los.iter().zip(&his)).enumerate() {
            let (Value::Int(lo), Value::Int(hi)) = (lo, hi) else {
                return Err(Fault::Type);
            };
            for value in loop_values(lo, hi) {
                let mut env = env.clone();
                env.statics.insert(binder.to_owned(), value);
                envs.push(env);
                parents.push(i);
            }
            if envs.len() > ENVS {
                return Ok(None);
            }
        }
        let mut inner = ctx.derive(&parents, envs);
        inner.statics.push((binder.to_owned(), StaticTy::Int));
        Ok(Some(inner))
    }

    /// A random type with a width that holds in each env.
    fn decl_ty(&mut self, r: Reach<'_>, envs: &[Env]) -> Ty {
        match self.tape.below(3) {
            0 => Ty::Bool,
            1 => Ty::UInt(self.width(r, envs)),
            _ => Ty::SInt(self.width(r, envs)),
        }
    }

    /// The concrete type of `t` in each env.
    fn types(&self, t: &Ty, envs: &[Env]) -> Built<Vec<Scalar>> {
        envs.iter()
            .map(|env| concrete(t, env, &self.scope))
            .collect()
    }

    /// The type of a declaration: the type of a name in scope or a new one.
    fn decl(&mut self, ctx: &Ctx) -> Built<(Ty, Want)> {
        if self.tape.flag()
            && let Some(h) = ctx.hw.get(self.tape.index(ctx.hw.len()))
            && let Some(t) = Want::of(h).printable()
        {
            let types = h.types.clone();
            return Ok((t.clone(), Want { types, ty: Some(t) }));
        }
        let t = self.decl_ty(self.reach(ctx), &ctx.envs);
        let types = self.types(&t, &ctx.envs)?;
        Ok((t.clone(), Want { types, ty: Some(t) }))
    }

    pub(super) fn signatures(&mut self) {
        for k in 0..self.tape.between(1, MODULES) {
            let mut names = Names::default();
            let mut params = Vec::new();
            for _ in 0..self.tape.below(PARAMS + 1) {
                let t = self.pick(&STATIC_TYS);
                params.push((names.fresh("P"), t));
            }
            let clocked = if k == 0 {
                self.tape.below(4) != 0
            } else {
                self.tape.flag()
            };
            let domain = domain(&params);
            // Port widths read only `Nat` names: an `Int` parameter takes
            // negative values over the domain, so it rarely gives a width.
            let statics: Vec<(String, StaticTy)> = self
                .const_names()
                .into_iter()
                .chain(params.clone())
                .filter(|(_, t)| *t == StaticTy::Nat)
                .collect();
            // A port width holds in every context, so a call (which can be
            // costly over the whole domain) is not a candidate here.
            let r = Reach {
                names: &statics,
                fns: 0,
                envs: Some(&domain),
            };
            // Most modules have inputs, so that their outputs vary.
            let count = match self.tape.below(4 * INPUTS) {
                0 => 0,
                n => 1 + (n - 1) % INPUTS,
            };
            let mut inputs = Vec::new();
            for _ in 0..count {
                inputs.push((names.fresh("i"), self.decl_ty(r, &domain)));
            }
            let mut outputs = Vec::new();
            for _ in 0..self.tape.between(1, OUTPUTS) {
                outputs.push((names.fresh("o"), self.decl_ty(r, &domain)));
            }
            self.sigs.push(Sig {
                name: format!("M{k}"),
                params,
                clocked,
                inputs,
                outputs,
            });
        }
    }

    /// The body of module `k` in its contexts, if a parent reaches it.
    pub(super) fn body(&mut self, k: usize) -> Built {
        let sig = self.sigs.get(k).cloned().ok_or(Fault::Type)?;
        let tuples = self.contexts.get(k).cloned().ok_or(Fault::Type)?;
        if tuples.is_empty() {
            return Ok(());
        }
        let mut ctx = Ctx {
            envs: tuples.iter().map(|a| Env::of(&sig.params, a)).collect(),
            statics: self.const_names().into_iter().chain(sig.params).collect(),
            hw: Vec::new(),
            helpers: self.helpers.len(),
        };
        let mut body = Vec::new();
        for (n, t) in &sig.inputs {
            body.push(Stmt::Input(n.clone(), t.clone()));
            let types = self.types(t, &ctx.envs)?;
            ctx.hw.push(Hw {
                expr: HExpr::Name(n.clone()),
                ty: Some(t.clone()),
                types,
                mutable: false,
            });
        }
        let mut outputs = Vec::new();
        for (n, t) in &sig.outputs {
            body.push(Stmt::Output(n.clone(), t.clone()));
            let types = self.types(t, &ctx.envs)?;
            let ty = Some(t.clone());
            outputs.push((n.clone(), Want { types, ty }));
        }
        let mut m = Module {
            index: k,
            clocked: sig.clocked,
            names: Names::default(),
        };
        body.extend(self.frame(&mut ctx, &mut m, 0)?);
        // The first module that no parent reaches yet gets this one as a
        // parent, so that most signatures become modules of the tree.
        let orphan = (k + 1..self.sigs.len())
            .find(|&j| self.reachable(&m, j) && self.contexts.get(j).is_some_and(Vec::is_empty));
        if let Some(j) = orphan {
            self.instantiate(&mut ctx, &mut m, j, &mut body)?;
        }
        for (n, w) in outputs {
            body.push(Stmt::Connect(Place::Name(n), self.driver(&ctx, &w)));
        }
        *self.bodies.get_mut(k).ok_or(Fault::Type)? = Some(body);
        Ok(())
    }

    /// The statements of a frame, then the `:=` of its registers. A frame
    /// with no env never runs, so it only holds `error("dead")`.
    fn frame(&mut self, ctx: &mut Ctx, m: &mut Module, level: u32) -> Built<Vec<Stmt>> {
        if ctx.envs.is_empty() {
            return Ok(vec![Stmt::Error("dead".to_owned())]);
        }
        let max = if level == 0 {
            MODULE_STMTS
        } else {
            NESTED_STMTS
        };
        let mut out = Vec::new();
        let mut regs = Vec::new();
        let mut instances = 0;
        for _ in 0..self.tape.below(max + 1) {
            let nested = level < NESTING;
            match self.tape.below(12) {
                1 => self.static_let(ctx, &mut m.names, &mut out),
                2 => self.binding(ctx, &mut m.names, &mut out, true)?,
                3 => self.assign(ctx, &mut m.names, &mut out)?,
                4 => self.wire(ctx, &mut m.names, &mut out)?,
                5 if m.clocked => self.reg(ctx, &mut m.names, &mut out, &mut regs)?,
                6 | 7 if instances < INSTANCES => {
                    if self.instance(ctx, m, &mut out)? {
                        instances += 1;
                    }
                }
                8 | 9 if nested => self.repeat(ctx, m, &mut out, level)?,
                10 if nested => self.branch(ctx, m, &mut out, level)?,
                11 => {
                    let c = self.assertion(self.reach(ctx), &ctx.envs);
                    out.push(Stmt::Assert(c, "holds".to_owned()));
                }
                _ => self.binding(ctx, &mut m.names, &mut out, false)?,
            }
        }
        for (r, w) in regs {
            out.push(Stmt::Connect(Place::Name(r), self.driver(ctx, &w)));
        }
        Ok(out)
    }

    /// `let` or `let mut`, with or without its type.
    fn binding(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
        mutable: bool,
    ) -> Built {
        let (t, want) = self.decl(ctx)?;
        let typed = self.tape.flag();
        // An untyped `let` of a static value is a static binding, so an
        // untyped one takes a hardware value.
        let value = if typed {
            None
        } else {
            self.hw(ctx, &want, DEPTH)
        };
        // An untyped `let mut` of a wire or a register names that wire or
        // register, and `=` on it is no assignment; a typed one copies.
        let (ty, value) = match value {
            Some(v) if !(mutable && matches!(v, HExpr::Name(_) | HExpr::Field(..))) => (None, v),
            Some(v) => (Some(t), v),
            None => (Some(t), self.value(ctx, &want, DEPTH)),
        };
        let name = names.fresh(if mutable { "v" } else { "l" });
        out.push(Stmt::Let {
            name: name.clone(),
            mutable,
            ty,
            value,
        });
        ctx.hw.push(Hw {
            expr: HExpr::Name(name),
            ty: want.ty,
            types: want.types,
            mutable,
        });
        Ok(())
    }

    /// A static `let` of type `Nat`, `Int`, or `Bool`.
    fn static_let(&mut self, ctx: &mut Ctx, names: &mut Names, out: &mut Vec<Stmt>) {
        let kind = if self.tape.below(3) == 2 {
            Kind::Bool
        } else {
            Kind::Int
        };
        let (value, vs) = self.evaluated(kind, self.reach(ctx), &ctx.envs);
        let ty = self.static_ty(kind, &vs);
        let name = names.fresh("s");
        for (env, v) in ctx.envs.iter_mut().zip(vs) {
            env.statics.insert(name.clone(), v);
        }
        ctx.statics.push((name.clone(), ty));
        out.push(Stmt::StaticLet(name, ty, value));
    }

    /// `v = ...;` of a `let mut` in scope, or a new `let`.
    fn assign(&mut self, ctx: &mut Ctx, names: &mut Names, out: &mut Vec<Stmt>) -> Built {
        let targets: Vec<&Hw> = ctx.hw.iter().filter(|h| h.mutable).collect();
        let target = targets
            .get(self.tape.index(targets.len()))
            .and_then(|h| match &h.expr {
                HExpr::Name(n) => Some((n.clone(), Want::of(h))),
                _ => None,
            });
        match target {
            Some((n, w)) => {
                let value = self.value(ctx, &w, DEPTH);
                out.push(Stmt::Assign(n, value));
                Ok(())
            }
            None => self.binding(ctx, names, out, false),
        }
    }

    /// `wire w: T; w := ...;`.
    fn wire(&mut self, ctx: &mut Ctx, names: &mut Names, out: &mut Vec<Stmt>) -> Built {
        let (ty, want) = self.decl(ctx)?;
        let name = names.fresh("w");
        out.push(Stmt::Wire(name.clone(), ty));
        let value = self.driver(ctx, &want);
        out.push(Stmt::Connect(Place::Name(name.clone()), value));
        ctx.hw.push(Hw {
            expr: HExpr::Name(name),
            ty: want.ty,
            types: want.types,
            mutable: false,
        });
        Ok(())
    }

    /// `reg r: T = reset;`; its `:=` comes at the end of the frame.
    fn reg(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
        regs: &mut Vec<(String, Want)>,
    ) -> Built {
        let (ty, want) = self.decl(ctx)?;
        let reset = self.fit(&want.types, self.reach(ctx), &ctx.envs);
        let name = names.fresh("r");
        out.push(Stmt::Reg(name.clone(), ty, reset));
        ctx.hw.push(Hw {
            expr: HExpr::Name(name.clone()),
            ty: want.ty.clone(),
            types: want.types.clone(),
            mutable: false,
        });
        regs.push((name, want));
        Ok(())
    }

    /// Whether module `m` can instantiate module `j`: a later module, and a
    /// combinational parent takes only combinational children.
    fn reachable(&self, m: &Module, j: usize) -> bool {
        j > m.index && (m.clocked || self.sigs.get(j).is_some_and(|s| !s.clocked))
    }

    /// An instance of a random child, if one is reachable.
    fn instance(&mut self, ctx: &mut Ctx, m: &mut Module, out: &mut Vec<Stmt>) -> Built<bool> {
        let children: Vec<usize> = (m.index + 1..self.sigs.len())
            .filter(|&j| self.reachable(m, j))
            .collect();
        let Some(&j) = children.get(self.tape.index(children.len())) else {
            return Ok(false);
        };
        self.instantiate(ctx, m, j, out)?;
        Ok(true)
    }

    /// `instance u = M<j>(args);` and the `:=` of each child input.
    fn instantiate(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        j: usize,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let sig = self.sigs.get(j).cloned().ok_or(Fault::Type)?;
        let mut args = Vec::new();
        for (_, t) in &sig.params {
            args.push(self.argument(*t, self.reach(ctx), &ctx.envs));
        }
        let tuples = self.tuples(j, &mut args, &ctx.envs)?;
        let name = m.names.fresh("u");
        out.push(Stmt::Instance(name.clone(), sig.name.clone(), args));
        let envs: Vec<Env> = tuples.iter().map(|a| Env::of(&sig.params, a)).collect();
        for (p, t) in &sig.inputs {
            let types = self.types(t, &envs)?;
            let value = self.driver(ctx, &Want { types, ty: None });
            let place = Place::Field(name.clone(), p.clone());
            out.push(Stmt::Connect(place, value));
        }
        for (q, t) in &sig.outputs {
            let types = self.types(t, &envs)?;
            ctx.hw.push(Hw {
                expr: HExpr::Field(name.clone(), q.clone()),
                ty: None,
                types,
                mutable: false,
            });
        }
        Ok(())
    }

    /// The argument tuple of each env, recorded as contexts of module `j`.
    /// When `j` would pass `CONTEXTS` tuples, the arguments become the
    /// literals of a tuple that it has.
    fn tuples(&mut self, j: usize, args: &mut Vec<SExpr>, envs: &[Env]) -> Built<Vec<Vec<Value>>> {
        let columns: Vec<Vec<Value>> = args
            .iter()
            .map(|a| self.values(a, envs))
            .collect::<Option<_>>()
            .ok_or(Fault::Type)?;
        let mut tuples: Vec<Vec<Value>> = (0..envs.len())
            .map(|i| columns.iter().filter_map(|c| c.get(i).cloned()).collect())
            .collect();
        let known = self.contexts.get(j).ok_or(Fault::Type)?.clone();
        let mut all = known.clone();
        for t in &tuples {
            if !all.contains(t) {
                all.push(t.clone());
            }
        }
        if all.len() > CONTEXTS {
            let pick = known.first().or(tuples.first()).ok_or(Fault::Type)?.clone();
            *args = pick.iter().map(value_expr).collect();
            tuples = vec![pick.clone(); envs.len()];
            all = known;
            if !all.contains(&pick) {
                all.push(pick);
            }
        }
        *self.contexts.get_mut(j).ok_or(Fault::Type)? = all;
        Ok(tuples)
    }

    /// `comptime for`, skipped when it would pass `ENVS` envs.
    fn repeat(&mut self, ctx: &Ctx, m: &mut Module, out: &mut Vec<Stmt>, level: u32) -> Built {
        let binder = m.names.fresh("j");
        let (lo, hi) = self.bounds(self.reach(ctx), &ctx.envs);
        if let Some(mut inner) = self.iterations(ctx, &binder, &lo, &hi)? {
            let body = self.frame(&mut inner, m, level + 1)?;
            out.push(Stmt::For(binder, lo, hi, body));
        }
        Ok(())
    }

    /// `comptime if`: each branch takes the envs that select it.
    fn branch(&mut self, ctx: &Ctx, m: &mut Module, out: &mut Vec<Stmt>, level: u32) -> Built {
        let c = self.condition(self.reach(ctx), &ctx.envs);
        let vs = self.values(&c, &ctx.envs).ok_or(Fault::Type)?;
        let split = |want: bool| -> (Vec<usize>, Vec<Env>) {
            ctx.envs
                .iter()
                .zip(&vs)
                .enumerate()
                .filter(|(_, (_, v))| **v == Value::Bool(want))
                .map(|(i, (env, _))| (i, env.clone()))
                .unzip()
        };
        let (parents, envs) = split(true);
        let then = self.frame(&mut ctx.derive(&parents, envs), m, level + 1)?;
        let els = if self.tape.flag() {
            let (parents, envs) = split(false);
            Some(self.frame(&mut ctx.derive(&parents, envs), m, level + 1)?)
        } else {
            None
        };
        out.push(Stmt::If(c, then, els));
        Ok(())
    }

    /// The `eval` probe: a call at the root when a `comptime fn` exists,
    /// else an expression over the consts; `0` if it faults.
    pub(super) fn probe(&mut self) -> (SExpr, Value) {
        let envs = [Env::default()];
        let names = self.const_names();
        let e = if self.fns.is_empty() {
            let kind = if self.tape.below(4) == 3 {
                Kind::Bool
            } else {
                Kind::Int
            };
            let r = Reach {
                names: &names,
                fns: 0,
                envs: Some(&envs),
            };
            self.sexpr(kind, super::stat::DEPTH, r)
        } else {
            let i = self.tape.index(self.fns.len());
            let params = self
                .fns
                .get(i)
                .map(|f| f.params.clone())
                .unwrap_or_default();
            let mut args = Vec::new();
            for (k, (_, t)) in params.iter().enumerate() {
                args.push(match t {
                    StaticTy::Bool => SExpr::Bool(self.tape.flag()),
                    _ if k == 0 => self.number(0, COUNT),
                    _ => super::stat::int(self.pick(&SAMPLE_INTS)),
                });
            }
            SExpr::Call(format!("f{i}"), args)
        };
        match eval(&e, &Env::default(), &self.scope) {
            Ok(v) => (e, v),
            Err(_) => (super::stat::int(0), Value::Int(BigInt::ZERO)),
        }
    }
}
