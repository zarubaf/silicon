// SPDX-License-Identifier: Apache-2.0
//! Helpers, module signatures, and module bodies: frames and their
//! statements.

use super::hw::{DEPTH, Want};
use super::reflect::RTy;
use super::stat::{self, Kind, Reach};
use super::{
    Builder, Built, COUNT, Ctx, ENVS, HELPERS, Helper, Hw, HwEnum, INPUTS, INSTANCES, MODULE_STMTS,
    MODULES, Module, NESTED_STMTS, NESTING, Names, OUTPUTS, PARAMS, SAMPLE_INTS, Sig,
};
use crate::eval::{Env, Fault, Value, concrete, eval, loop_values};
use crate::program::{EnumDef, HExpr, Place, SExpr, STy, Scalar, Stmt, Ty};
use num_bigint::BigInt;
use std::collections::BTreeSet;

const STATIC_TYS: [STy; 3] = [STy::Nat, STy::Int, STy::Bool];

/// One env per argument tuple in the ranges of the module arguments.
fn domain(params: &[(String, STy)], builder: &Builder) -> Vec<Env> {
    let mut envs = vec![Env::default()];
    for (name, t) in params {
        let values: Vec<Value> = if *t == STy::Bool {
            vec![Value::Bool(false), Value::Bool(true)]
        } else if let STy::UInt(w) | STy::SInt(w) = t {
            // Only widths read the domain, and they read `Nat` names, so
            // one value stands for all.
            vec![if matches!(t, STy::UInt(_)) {
                Value::UInt(*w, BigInt::ZERO)
            } else {
                Value::SInt(*w, BigInt::ZERO)
            }]
        } else if let STy::Fn(ft) = t {
            // Only widths read the domain, and they read `Nat` names, so
            // one function stands for all.
            builder.fn_domain(ft).into_iter().take(1).collect()
        } else {
            let (lo, hi) = super::stat::arg_range(t);
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

/// The kinds of statement of a frame.
#[derive(Clone, Copy)]
enum StmtKind {
    StaticLet,
    List,
    Push,
    Pop,
    MutCall,
    HwMutCall,
    Diagnostic,
    MutBinding,
    Assign,
    Wire,
    Reg,
    Instance,
    Repeat,
    Branch,
    Assert,
    /// A `let` of a hardware value, and the fallback of a kind that does
    /// not apply.
    Binding,
}

/// The weight of each kind. They are those of the 22 draws before enums,
/// doubled, and `pop`, the calls with a `mut` formal, the instances, and
/// the diagnostics weigh a little more, so that the forms that depend on
/// them keep their coverage.
const WEIGHTS: [(StmtKind, u32); 16] = [
    (StmtKind::StaticLet, 2),
    (StmtKind::List, 2),
    (StmtKind::Push, 2),
    (StmtKind::Pop, 3),
    (StmtKind::MutCall, 3),
    (StmtKind::HwMutCall, 3),
    (StmtKind::Diagnostic, 10),
    (StmtKind::MutBinding, 2),
    (StmtKind::Binding, 2),
    (StmtKind::Assign, 2),
    (StmtKind::Wire, 2),
    (StmtKind::Reg, 2),
    (StmtKind::Instance, 8),
    (StmtKind::Repeat, 4),
    (StmtKind::Branch, 2),
    (StmtKind::Assert, 2),
];

impl Builder {
    /// A kind of statement, by the weights.
    fn statement_kind(&mut self) -> StmtKind {
        let total: u32 = WEIGHTS.iter().map(|(_, w)| w).sum();
        let mut n = self.tape.below(total);
        for (kind, w) in WEIGHTS {
            if n < w {
                return kind;
            }
            n -= w;
        }
        StmtKind::Binding
    }

    pub(super) fn helpers(&mut self) -> Built {
        for k in 0..self.tape.below(HELPERS + 1) {
            let h = self.helper(k as usize)?;
            self.helpers.push(h);
        }
        Ok(())
    }

    /// A helper type: `Bool`, or a width that is a literal or a `Nat`
    /// const in `1..=64`.
    pub(super) fn data_ty(&mut self) -> (Ty, Scalar) {
        let shape = self.tape.below(3);
        if shape == 0 {
            return (Ty::Bool, Scalar::Bool);
        }
        let widths: Vec<(String, u32)> = self
            .consts
            .iter()
            .filter(|(_, t, _)| *t == STy::Nat)
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
            lists: Vec::new(),
            counters: Vec::new(),
            enums: Vec::new(),
            pending: Vec::new(),
            hand: Vec::new(),
            local: false,
            called: BTreeSet::new(),
            looped: false,
            port: Vec::new(),
            child_reads: BTreeSet::new(),
            instances: Vec::new(),
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
            mut_first: false,
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
    pub(super) fn iterations(
        &self,
        ctx: &Ctx,
        binder: &str,
        lo: &SExpr,
        hi: &SExpr,
    ) -> Built<Option<Ctx>> {
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
        inner.statics.push((binder.to_owned(), STy::Int));
        inner.looped |= inner.envs.len() > ctx.envs.len();
        Ok(Some(inner))
    }

    /// A random type with a width that holds in each env.
    pub(super) fn decl_ty(&mut self, r: Reach<'_>, envs: &[Env]) -> Ty {
        match self.tape.below(3) {
            0 => Ty::Bool,
            1 => Ty::UInt(self.width(r, envs)),
            _ => Ty::SInt(self.width(r, envs)),
        }
    }

    /// The concrete type of `t` in each env.
    pub(super) fn types(&self, t: &Ty, envs: &[Env]) -> Built<Vec<Scalar>> {
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
                let t = STATIC_TYS[self.tape.index(STATIC_TYS.len())].clone();
                // A child, not the top, takes a function: the top arguments
                // are scalars on the command line.
                let t = match self.fn_param_ty() {
                    Some(f) if k > 0 && self.tape.below(5) == 0 => f,
                    _ if self.tape.below(if k > 0 { 3 } else { 5 }) == 0 => self.finite_param_ty(),
                    _ => t,
                };
                params.push((names.fresh("P"), t));
            }
            let clocked = if k == 0 {
                self.tape.below(4) != 0
            } else {
                self.tape.flag()
            };
            let domain = domain(&params, self);
            // Port widths read only `Nat` names: an `Int` parameter takes
            // negative values over the domain, so it rarely gives a width.
            let statics: Vec<(String, STy)> = self
                .const_names()
                .into_iter()
                .chain(params.clone())
                .filter(|(_, t)| *t == STy::Nat)
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
            let (enum_inputs, enum_outputs) = self.enum_ports();
            let plan = self.port_plan(k == 0);
            self.sigs.push(Sig {
                name: format!("M{k}"),
                params,
                clocked,
                inputs,
                outputs,
                enum_inputs,
                enum_outputs,
                plan,
                wraps: None,
            });
        }
        self.wrapper();
    }

    /// The body of module `k` in its contexts, if a parent reaches it.
    pub(super) fn body(&mut self, k: usize) -> Built {
        let sig = self.sigs.get(k).cloned().ok_or(Fault::Type)?;
        let tuples = self.contexts.get(k).cloned().ok_or(Fault::Type)?;
        if tuples.is_empty() {
            return Ok(());
        }
        if sig.wraps.is_some() {
            return self.wrapper_body(k, &sig);
        }
        let mut ctx = Ctx {
            envs: tuples.iter().map(|a| Env::of(&sig.params, a)).collect(),
            statics: self.const_names().into_iter().chain(sig.params).collect(),
            hw: Vec::new(),
            helpers: self.helpers.len(),
            lists: Vec::new(),
            counters: Vec::new(),
            enums: Vec::new(),
            pending: Vec::new(),
            hand: Vec::new(),
            local: false,
            called: BTreeSet::new(),
            looped: false,
            port: Vec::new(),
            child_reads: BTreeSet::new(),
            instances: Vec::new(),
        };
        let mut body = Vec::new();
        self.ops.clear();
        self.kids.clear();
        for (n, t) in &sig.inputs {
            body.push(Stmt::Input(n.clone(), t.clone()));
            self.add_op(n, RTy::of(t));
            let types = self.types(t, &ctx.envs)?;
            ctx.hw.push(Hw {
                expr: HExpr::Name(n.clone()),
                ty: Some(t.clone()),
                types,
                mutable: false,
            });
        }
        for (n, def) in &sig.enum_inputs {
            body.push(Stmt::Input(n.clone(), Ty::Enum(def.name.clone())));
            ctx.enums.push(HwEnum {
                expr: HExpr::Name(n.clone()),
                def: def.clone(),
                hardware: true,
            });
        }
        let mut outputs = Vec::new();
        for (n, t) in &sig.outputs {
            body.push(Stmt::Output(n.clone(), t.clone()));
            let types = self.types(t, &ctx.envs)?;
            let ty = Some(t.clone());
            outputs.push((n.clone(), Want { types, ty }));
        }
        for (n, def) in &sig.enum_outputs {
            body.push(Stmt::Output(n.clone(), Ty::Enum(def.name.clone())));
        }
        let mut m = Module {
            index: k,
            clocked: sig.clocked,
            names: Names::default(),
        };
        // The record of a finite parameter shows its converted value.
        for (n, t) in &ctx.statics {
            if matches!(t, STy::UInt(_) | STy::SInt(_)) && self.tape.flag() {
                note!(self, structured_diagnostics);
                body.push(Stmt::Diagnostic(
                    self.next_message(),
                    SExpr::Name(n.clone()),
                ));
            }
        }
        self.port_forms(&mut ctx, &mut m, &sig.plan, &mut body)?;
        let emitted = self.emitted;
        let decls = self.query_decls(&ctx, &mut m)?;
        let decls_at = body.len();
        body.extend(self.frame(&mut ctx, &mut m, 0)?);
        self.call_unused(&mut ctx, &mut m, &mut body)?;
        self.close_pending(&mut ctx, &mut body)?;
        // The first module that no parent reaches yet gets this one as a
        // parent, so that most signatures become modules of the tree.
        let orphan = (k + 1..self.sigs.len())
            .find(|&j| self.reachable(&m, j) && self.contexts.get(j).is_some_and(Vec::is_empty));
        if let Some(j) = orphan {
            self.instantiate(&mut ctx, &mut m, j, &mut body)?;
        }
        self.query_tail(&ctx, &mut m.names, &mut body);
        self.drive_outputs(&ctx, outputs, &sig.enum_outputs, &mut body);
        // The declarations of the queries stay out of a module with no query.
        if self.emitted > emitted {
            body.splice(decls_at..decls_at, decls);
        }
        *self.bodies.get_mut(k).ok_or(Fault::Type)? = Some(body);
        Ok(())
    }

    /// The `:=` of each output at the end of a module: a value of its type
    /// with the names of the other forms mixed in.
    fn drive_outputs(
        &mut self,
        ctx: &Ctx,
        outputs: Vec<(String, Want)>,
        enum_outputs: &[(String, EnumDef)],
        body: &mut Vec<Stmt>,
    ) {
        let mut values = Vec::new();
        for (n, w) in outputs {
            let value = self.driver(ctx, &w);
            let value = self.mix_hand(ctx, &w, value);
            values.push((n, w, value));
        }
        self.mix_port(ctx, &mut values);
        self.mix_query(ctx, &mut values);
        for (n, _, value) in values {
            body.push(Stmt::Connect(Place::Name(n), value));
        }
        for (n, def) in enum_outputs {
            let value = self.enum_driver(ctx, def);
            body.push(Stmt::Connect(Place::Name(n.clone()), value));
        }
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
        let (ops, kids) = (self.ops.len(), self.kids.len());
        let mut regs = Vec::new();
        let mut eregs = Vec::new();
        let mut instances = 0;
        let mut extra = self.enum_stmts();
        let mut handles = self.handle_stmts();
        for _ in 0..self.tape.below(max + 1) {
            while extra > 0 && self.side_below(3) == 0 {
                self.enum_stmt(ctx, &mut m.names, m.clocked, &mut out, &mut eregs)?;
                extra -= 1;
            }
            while handles > 0 && self.hand_below(3) == 0 {
                self.handle_stmt(ctx, m, &mut out)?;
                handles -= 1;
            }
            let nested = level < NESTING;
            match self.statement_kind() {
                StmtKind::StaticLet => self.static_let(ctx, &mut m.names, &mut out)?,
                StmtKind::List => self.list_let(ctx, &mut m.names, &mut out)?,
                StmtKind::Push => self.push_stmt(ctx, &mut out),
                StmtKind::Pop => self.pop_stmt(ctx, &mut m.names, &mut out),
                StmtKind::MutCall => self.static_mut_call(ctx, &mut m.names, &mut out)?,
                StmtKind::HwMutCall => self.hw_mut_call(ctx, m, &mut out)?,
                StmtKind::Diagnostic => self.diagnostic(ctx, &mut out),
                StmtKind::MutBinding => self.binding(ctx, &mut m.names, &mut out, true)?,
                StmtKind::Assign => self.assign(ctx, &mut m.names, &mut out)?,
                StmtKind::Wire => self.wire(ctx, &mut m.names, &mut out)?,
                StmtKind::Reg if m.clocked => self.reg(ctx, &mut m.names, &mut out, &mut regs)?,
                StmtKind::Instance if instances < INSTANCES => {
                    if self.instance(ctx, m, &mut out)? {
                        instances += 1;
                        // A record after the child pins the order of the
                        // records of the parent and the child.
                        if self.tape.below(2) == 0 {
                            self.diagnostic(ctx, &mut out);
                        }
                    }
                }
                StmtKind::Repeat if nested => self.repeat(ctx, m, &mut out, level)?,
                StmtKind::Branch if nested => self.branch(ctx, m, &mut out, level)?,
                StmtKind::Assert => {
                    let c = self.assertion(self.reach(ctx), &ctx.envs);
                    out.push(Stmt::Assert(c, "holds".to_owned()));
                }
                _ => self.binding(ctx, &mut m.names, &mut out, false)?,
            }
            self.key_group(ctx, &mut m.names, &mut out)?;
            if level == 0 {
                self.record_group(ctx, m, &mut out)?;
            }
            self.query_group(ctx, &mut m.names, &mut out)?;
        }
        for _ in 0..extra {
            self.enum_stmt(ctx, &mut m.names, m.clocked, &mut out, &mut eregs)?;
        }
        for _ in 0..handles {
            self.handle_stmt(ctx, m, &mut out)?;
        }
        self.close_regs(ctx, regs, &mut out)?;
        self.close_enum_regs(ctx, eregs, &mut out);
        self.close_pending(ctx, &mut out)?;
        if level > 0 {
            self.ops.truncate(ops);
            self.kids.truncate(kids);
        }
        Ok(out)
    }

    /// The `:=` of each register. The wanted type is read from `ctx` now: a
    /// write to a root since the declaration may have dropped the type
    /// expression, and a copy kept from the declaration would print it.
    pub(super) fn close_regs(
        &mut self,
        ctx: &Ctx,
        regs: Vec<String>,
        out: &mut Vec<Stmt>,
    ) -> Built {
        for r in regs {
            let want = ctx
                .hw
                .iter()
                .find(|h| matches!(&h.expr, HExpr::Name(n) if *n == r))
                .map(Want::of)
                .ok_or(Fault::Type)?;
            out.push(Stmt::Connect(Place::Name(r), self.driver(ctx, &want)));
        }
        Ok(())
    }

    /// `let` or `let mut`, with or without its type.
    pub(super) fn binding(
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
    fn static_let(&mut self, ctx: &mut Ctx, names: &mut Names, out: &mut Vec<Stmt>) -> Built {
        let shape = self.tape.below(8);
        if shape == 2 {
            let value = self.sexpr(Kind::Str, stat::DEPTH, self.reach(ctx));
            let (value, vs) = if let Some(vs) = self.values(&value, &ctx.envs) {
                (value, vs)
            } else {
                let (e, v) = Builder::empty_string();
                (e, vec![v; ctx.envs.len()])
            };
            let name = names.fresh("s");
            for (env, v) in ctx.envs.iter_mut().zip(vs) {
                env.statics.insert(name.clone(), v);
            }
            ctx.statics.push((name.clone(), STy::Str));
            out.push(Stmt::StaticLet(name, STy::Str, value));
            return Ok(());
        }
        if shape >= 6 {
            let ty = self.static_container_ty();
            let value = self.container(&ty, stat::DEPTH, self.reach(ctx));
            let vs = self.values(&value, &ctx.envs).ok_or(Fault::Type)?;
            let name = names.fresh("s");
            for (env, v) in ctx.envs.iter_mut().zip(vs) {
                env.statics.insert(name.clone(), v);
            }
            ctx.statics.push((name.clone(), ty.clone()));
            out.push(Stmt::StaticLet(name, ty, value));
            return Ok(());
        }
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
        ctx.statics.push((name.clone(), ty.clone()));
        out.push(Stmt::StaticLet(name, ty, value));
        Ok(())
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
        let shown = self.query_ty(ctx, ty.clone(), &want);
        out.push(Stmt::Wire(name.clone(), shown));
        self.add_op(&name, RTy::of(&ty).map(|t| RTy::Wire(Box::new(t))));
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
        regs: &mut Vec<String>,
    ) -> Built {
        let (ty, want) = self.decl(ctx)?;
        let reset = self.fit(&want.types, self.reach(ctx), &ctx.envs);
        let name = names.fresh("r");
        let shown = self.query_ty(ctx, ty.clone(), &want);
        out.push(Stmt::Reg(name.clone(), shown, reset));
        self.add_op(&name, RTy::of(&ty).map(|t| RTy::Reg(Box::new(t))));
        ctx.hw.push(Hw {
            expr: HExpr::Name(name.clone()),
            ty: want.ty.clone(),
            types: want.types.clone(),
            mutable: false,
        });
        regs.push(name);
        Ok(())
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
        let e = if let Some(e) = self.container_probe(&names, &envs) {
            e
        } else if self.fns.is_empty() {
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
                    STy::Bool => SExpr::Bool(self.tape.flag()),
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
