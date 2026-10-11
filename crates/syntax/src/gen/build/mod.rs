// SPDX-License-Identifier: Apache-2.0
//! Random well-typed slice-1 programs from a tape of random numbers.
//!
//! As in `core_ir::gen`, each choice takes the next number of the tape, an
//! exhausted tape gives 0, and choice 0 is always the simplest option, so a
//! failing program shrinks with its tape.
//!
//! Each program elaborates by construction:
//!
//! - Names are a kind prefix and a number, so they are unique, never a
//!   keyword, and have no `_` (the twin adds `_`).
//! - Each static position takes a candidate that `super::eval` evaluates in
//!   each env of its env set (module contexts × loop iterations, split by
//!   `comptime if`), or a fallback literal (`stat`). No static fault occurs.
//! - All signatures come first. Their port widths hold over the full range
//!   of the module arguments, so each context gives valid ports. Module `k`
//!   instantiates only modules `j > k`, so no cycle occurs. A body comes
//!   after all its parents, so its contexts are known; a module that no
//!   parent reaches is dropped.
//! - A wire and a child input bind right after their declaration, a register
//!   at the end of its frame, and each output at the end of the module. A
//!   value reads only earlier values, and values leave loops and branches
//!   through `let mut` accumulators, so no combinational cycle occurs.

/// Counts one event in the statistics of the tests.
macro_rules! note {
    ($builder:expr, $field:ident) => {
        #[cfg(test)]
        {
            $builder.stats.$field += 1;
        }
    };
}

mod body;
mod hw;
mod stat;

use super::eval::{Env, Fault, Scope, Value, concrete, eval};
use super::program::{
    ComptimeFn, HExpr, Item, Place, Ports, Program, SBin, SExpr, Scalar, StaticTy, Stmt, Ty,
};
use num_bigint::{BigInt, BigUint};
use proptest::collection::vec;
use proptest::prelude::*;
use stat::{Kind, Reach, bin, int};
use std::collections::BTreeMap;

/// Size caps (Ruling 10).
const MODULES: u32 = 4;
const PARAMS: u32 = 3;
const INPUTS: u32 = 4;
const OUTPUTS: u32 = 3;
const CONSTS: u32 = 3;
const FNS: u32 = 2;
const HELPERS: u32 = 2;
const MODULE_STMTS: u32 = 8;
const NESTED_STMTS: u32 = 4;
const NESTING: u32 = 2;
const ENVS: usize = 64;
const INSTANCES: u32 = 3;
const CONTEXTS: usize = 3;
/// The sample of a `comptime fn` body (Ruling 5).
const SAMPLE_INTS: [i64; 5] = [-6, -1, 0, 3, 6];

/// Random well-typed slice-1 programs.
pub fn typed() -> impl Strategy<Value = Program> {
    vec(any::<u32>(), 0..4096).prop_map(build)
}

/// `cycles` random `in=` lines for the top ports: the domain reset first for
/// a clocked top, with the bias of `core_ir::gen::resets`, then each input
/// in byte order.
pub fn lines(ports: &Ports, cycles: usize) -> impl Strategy<Value = Vec<String>> + use<> {
    let clocked = ports.clocked;
    let names: Vec<String> = ports.inputs.iter().map(|(n, _)| n.clone()).collect();
    let values: Vec<BoxedStrategy<String>> =
        ports.inputs.iter().map(|(_, t)| port_value(*t)).collect();
    (core_ir::r#gen::resets(cycles), vec(values, cycles)).prop_map(move |(resets, rows)| {
        resets
            .into_iter()
            .zip(rows)
            .map(|(reset, row)| {
                let reset = clocked.then(|| format!("clock$0rst {reset}"));
                let pairs = names.iter().zip(row).map(|(n, v)| format!("{n} {v}"));
                let all: Vec<String> = reset.into_iter().chain(pairs).collect();
                format!("in=({})", all.join(" "))
            })
            .collect()
    })
}

/// A random value of a port type, in decimal.
fn port_value(t: Scalar) -> BoxedStrategy<String> {
    match t {
        Scalar::Bool => any::<bool>().prop_map(|b| b.to_string()).boxed(),
        Scalar::UInt(w) | Scalar::SInt(w) => {
            let signed = matches!(t, Scalar::SInt(_));
            vec(any::<u8>(), w.div_ceil(8) as usize)
                .prop_map(move |bytes| {
                    let bits = BigUint::from_bytes_le(&bytes) & ((BigUint::from(1u8) << w) - 1u8);
                    let mut v = BigInt::from(bits);
                    if signed && v >= BigInt::from(1) << (w - 1) {
                        v -= BigInt::from(1) << w;
                    }
                    v.to_string()
                })
                .boxed()
        }
    }
}

/// The program of a tape.
fn build(tape: Vec<u32>) -> Program {
    Builder::new(tape).program().unwrap_or_else(|_| smallest())
}

/// The program of the empty tape. `build` returns it if the scope or the
/// top ports of a program fault, which the checks of the builder exclude;
/// `programs_cover_slice_1` checks that no program does.
fn smallest() -> Program {
    Program {
        items: vec![Item::Module {
            name: "M0".to_owned(),
            params: Vec::new(),
            clocked: false,
            body: vec![
                Stmt::Output("o0".to_owned(), Ty::Bool),
                Stmt::Connect(
                    Place::Name("o0".to_owned()),
                    HExpr::Static(SExpr::Bool(false)),
                ),
            ],
        }],
        top: "M0".to_owned(),
        args: Vec::new(),
        ports: Ports {
            clocked: false,
            inputs: Vec::new(),
            outputs: vec![("o0".to_owned(), Scalar::Bool)],
        },
        probe: (int(0), Value::Int(BigInt::ZERO)),
    }
}

/// The ports of the module `top` at the arguments `args`, byte-sorted.
pub(crate) fn ports(items: &[Item], top: &str, args: &[Value]) -> Result<Ports, Fault> {
    let scope = Scope::new(items)?;
    let Some(Item::Module {
        params,
        clocked,
        body,
        ..
    }) = items
        .iter()
        .find(|i| matches!(i, Item::Module { name, .. } if name == top))
    else {
        return Err(Fault::Type);
    };
    if params.len() != args.len() {
        return Err(Fault::Type);
    }
    let env = Env {
        statics: params
            .iter()
            .map(|(n, _)| n.clone())
            .zip(args.iter().cloned())
            .collect(),
    };
    let mut ports = Ports {
        clocked: *clocked,
        inputs: Vec::new(),
        outputs: Vec::new(),
    };
    for s in body {
        match s {
            Stmt::Input(n, t) => ports.inputs.push((n.clone(), concrete(t, &env, &scope)?)),
            Stmt::Output(n, t) => ports.outputs.push((n.clone(), concrete(t, &env, &scope)?)),
            _ => {}
        }
    }
    ports.inputs.sort_by(|a, b| a.0.cmp(&b.0));
    ports.outputs.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(ports)
}

/// The tape of choices. A copy of `below`, `between`, `index`, and `flag`
/// of the `Tape` of `core_ir::gen` (`crates/core-ir/src/gen/mod.rs`), which
/// carries the core `Config` (Ruling 16).
struct Tape {
    numbers: std::vec::IntoIter<u32>,
}

impl Tape {
    /// A number below `n`, or 0 if `n` is 0.
    fn below(&mut self, n: u32) -> u32 {
        self.numbers.next().unwrap_or(0).checked_rem(n).unwrap_or(0)
    }

    /// A number from `lo` to `hi`.
    fn between(&mut self, lo: u32, hi: u32) -> u32 {
        lo + self.below(hi - lo + 1)
    }

    /// An index into a list of `len` elements.
    fn index(&mut self, len: usize) -> usize {
        (self.numbers.next().unwrap_or(0) as usize)
            .checked_rem(len)
            .unwrap_or(0)
    }

    fn flag(&mut self) -> bool {
        self.below(2) == 1
    }
}

/// Fresh names: a kind prefix and a counter per kind.
#[derive(Default)]
struct Names(BTreeMap<&'static str, u32>);

impl Names {
    fn fresh(&mut self, prefix: &'static str) -> String {
        let n = self.0.entry(prefix).or_insert(0);
        let name = format!("{prefix}{n}");
        *n += 1;
        name
    }
}

/// A hardware name in scope: its expression (`x` or `u.q`), its type
/// expression if one is valid here, and its concrete type in each env.
#[derive(Clone, Debug)]
struct Hw {
    expr: HExpr,
    ty: Option<Ty>,
    types: Vec<Scalar>,
    mutable: bool,
}

/// The scope of a frame: the env set, the static names, the hardware
/// names, and how many helpers a call can name.
#[derive(Clone, Debug, Default)]
struct Ctx {
    envs: Vec<Env>,
    statics: Vec<(String, StaticTy)>,
    hw: Vec<Hw>,
    helpers: usize,
}

impl Ctx {
    /// The scope of a nested frame whose env `i` extends `parents[i]`.
    fn derive(&self, parents: &[usize], envs: Vec<Env>) -> Ctx {
        let hw = self
            .hw
            .iter()
            .map(|h| Hw {
                types: parents
                    .iter()
                    .filter_map(|&p| h.types.get(p).copied())
                    .collect(),
                ..h.clone()
            })
            .collect();
        Ctx {
            envs,
            statics: self.statics.clone(),
            hw,
            helpers: self.helpers,
        }
    }
}

/// A helper with the concrete types of its formals and result; they have
/// literal or `const` widths, so one type holds everywhere.
#[derive(Clone)]
struct Helper {
    name: String,
    params: Vec<(String, Ty, Scalar)>,
    ret: (Ty, Scalar),
    body: Vec<Stmt>,
    result: HExpr,
}

/// A module signature; its port widths hold over the whole domain.
#[derive(Clone)]
struct Sig {
    name: String,
    params: Vec<(String, StaticTy)>,
    clocked: bool,
    inputs: Vec<(String, Ty)>,
    outputs: Vec<(String, Ty)>,
}

/// The module whose body is under construction.
struct Module {
    index: usize,
    clocked: bool,
    names: Names,
}

#[cfg(test)]
#[derive(Debug, Default)]
struct Stats {
    widths: u32,
    width_fallbacks: u32,
    calls: u32,
    call_fallbacks: u32,
}

struct Builder {
    tape: Tape,
    consts: Vec<(String, StaticTy, SExpr)>,
    fns: Vec<ComptimeFn>,
    helpers: Vec<Helper>,
    sigs: Vec<Sig>,
    bodies: Vec<Option<Vec<Stmt>>>,
    /// The distinct argument tuples of each module.
    contexts: Vec<Vec<Vec<Value>>>,
    scope: Scope,
    #[cfg(test)]
    stats: Stats,
}

impl Builder {
    fn new(tape: Vec<u32>) -> Builder {
        Builder {
            tape: Tape {
                numbers: tape.into_iter(),
            },
            consts: Vec::new(),
            fns: Vec::new(),
            helpers: Vec::new(),
            sigs: Vec::new(),
            bodies: Vec::new(),
            contexts: Vec::new(),
            scope: Scope::default(),
            #[cfg(test)]
            stats: Stats::default(),
        }
    }

    fn program(&mut self) -> Result<Program, Fault> {
        self.consts()?;
        self.fns()?;
        self.helpers();
        self.signatures();
        let params = self
            .sigs
            .first()
            .map(|s| s.params.clone())
            .unwrap_or_default();
        let args: Vec<Value> = params.iter().map(|(_, t)| self.top_value(*t)).collect();
        self.contexts = vec![Vec::new(); self.sigs.len()];
        if let Some(top) = self.contexts.first_mut() {
            top.push(args.clone());
        }
        self.bodies = vec![None; self.sigs.len()];
        for k in 0..self.sigs.len() {
            self.body(k);
        }
        let probe = self.probe();
        let items = self.items();
        let ports = ports(&items, "M0", &args)?;
        Ok(Program {
            items,
            top: "M0".to_owned(),
            args,
            ports,
            probe,
        })
    }

    /// An element of `xs`.
    fn pick<T: Copy, const N: usize>(&mut self, xs: &[T; N]) -> T {
        // `index` is below `N`.
        xs[self.tape.index(N)]
    }

    /// What a static candidate of `ctx` can read.
    fn reach<'a>(&self, ctx: &'a Ctx) -> Reach<'a> {
        Reach {
            names: &ctx.statics,
            fns: self.fns.len(),
            envs: Some(&ctx.envs),
        }
    }

    fn const_names(&self) -> Vec<(String, StaticTy)> {
        self.consts
            .iter()
            .map(|(n, t, _)| (n.clone(), *t))
            .collect()
    }

    fn file_items(&self) -> Vec<Item> {
        let consts = self.consts.iter().map(|(name, ty, value)| Item::Const {
            name: name.clone(),
            ty: *ty,
            value: value.clone(),
        });
        let fns = self.fns.iter().cloned().map(Item::ComptimeFn);
        consts.chain(fns).collect()
    }

    /// The items: consts, `comptime fn`s, helpers, and the reached modules.
    fn items(&self) -> Vec<Item> {
        let helpers = self.helpers.iter().map(|h| Item::Helper {
            name: h.name.clone(),
            params: h
                .params
                .iter()
                .map(|(n, t, _)| (n.clone(), t.clone()))
                .collect(),
            ret: h.ret.0.clone(),
            body: h.body.clone(),
            result: h.result.clone(),
        });
        let modules = self.sigs.iter().zip(&self.bodies).filter_map(|(s, b)| {
            b.as_ref().map(|body| Item::Module {
                name: s.name.clone(),
                params: s.params.clone(),
                clocked: s.clocked,
                body: body.clone(),
            })
        });
        self.file_items()
            .into_iter()
            .chain(helpers)
            .chain(modules)
            .collect()
    }

    /// The scope of the consts and `comptime fn`s so far. The builder adds
    /// only consts that evaluate, so it does not fault.
    fn refresh(&mut self) -> Result<(), Fault> {
        self.scope = Scope::new(&self.file_items())?;
        Ok(())
    }

    fn consts(&mut self) -> Result<(), Fault> {
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
    fn static_ty(&mut self, kind: Kind, vs: &[Value]) -> StaticTy {
        let natural = vs
            .iter()
            .all(|v| matches!(v, Value::Int(n) if *n >= BigInt::ZERO));
        match kind {
            Kind::Bool => StaticTy::Bool,
            Kind::Int if natural && self.tape.below(4) != 0 => StaticTy::Nat,
            Kind::Int => StaticTy::Int,
        }
    }

    fn fns(&mut self) -> Result<(), Fault> {
        for k in 0..self.tape.below(FNS + 1) {
            let f = self.comptime_fn(k as usize);
            self.fns.push(f);
            self.refresh()?;
        }
        Ok(())
    }

    /// `f<k>` of Ruling 5, checked on the sample.
    fn comptime_fn(&mut self, k: usize) -> ComptimeFn {
        let name = format!("f{k}");
        let mut params = vec![("x0".to_owned(), StaticTy::Nat)];
        for i in 1..=self.tape.below(3) {
            let t = if self.tape.flag() {
                StaticTy::Bool
            } else {
                StaticTy::Int
            };
            params.push((format!("x{i}"), t));
        }
        let names: Vec<(String, StaticTy)> =
            params.iter().cloned().chain(self.const_names()).collect();
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
            ret: StaticTy::Int,
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
            && self.static_ty(Kind::Int, &vs) == StaticTy::Nat
        {
            f.ret = StaticTy::Nat;
        }
        f
    }

    /// One or two calls `f<k>((x0 - 1), ...)`, in an expression.
    fn step(&mut self, name: &str, params: &[(String, StaticTy)], r: Reach<'_>) -> SExpr {
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
        let arg = |b: &mut Builder, t: StaticTy| b.sexpr(stat::kind(t), 1, r);
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
        let mut rows: Vec<Vec<SExpr>> = (0..=6).map(|n| vec![int(n)]).collect();
        for (_, t) in f.params.iter().skip(1) {
            let values: Vec<SExpr> = match t {
                StaticTy::Bool => vec![SExpr::Bool(false), SExpr::Bool(true)],
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
    params: &[(String, StaticTy)],
    mut arg: impl FnMut(StaticTy, &str) -> SExpr,
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

#[cfg(test)]
mod tests;
