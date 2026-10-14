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
mod container;
mod file;
mod fnvalues;
mod hw;
mod inst;
mod lines;
mod lists;
mod mutcalls;
mod record;
mod stat;
mod strings;

pub use lines::lines;

use super::eval::{Env, Fault, Scope, Value, concrete};
use super::program::{
    ComptimeFn, HExpr, Item, ListFn, MutFn, Ports, Program, SExpr, STy, Scalar, Stmt, StructDef, Ty,
};
use proptest::collection::vec;
use proptest::prelude::*;
use stat::Reach;
use std::collections::BTreeMap;
use std::fmt;

/// The name prefixes of the static kinds: `P` parameter, `C` const, `f`
/// `comptime fn`, `s` static `let`, `j` loop binder. A static name is one
/// of them and digits; the twin must have none.
pub(super) const STATIC_PREFIXES: &str = "PCfsjbSkF";

/// The result of a step whose faults the checks of the builder exclude.
/// A fault reaches `build`, which the coverage test watches.
type Built<T = ()> = Result<T, Fault>;

/// Size caps. They keep one program fast to elaborate in both front
/// ends, and well below their default fuel and depth.
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
/// The most elements of a tuple or an array, and the most levels of
/// nested containers.
const CONTAINER_LEN: u32 = 4;
const CONTAINER_LEVELS: u32 = 3;
/// The most structs, parameters of a struct, and fields of a struct.
const STRUCTS: u32 = 2;
const STRUCT_PARAMS: u32 = 2;
const STRUCT_FIELDS: u32 = 3;
/// The most list builders.
const LIST_FNS: u32 = 2;
/// The most functions with a `mut` formal, static and hardware.
const MUT_FNS: u32 = 2;
const MUT_HELPERS: u32 = 2;
const ENVS: usize = 64;
const INSTANCES: u32 = 3;
const CONTEXTS: usize = 3;
/// The largest first argument (the recursion count) of a `comptime fn`
/// call: the sample check of each body covers `0..=COUNT`.
const COUNT: u32 = 6;
/// The sample of the other `Int` formals of a `comptime fn` body; the
/// first formal takes `0..=COUNT`.
const SAMPLE_INTS: [i64; 5] = [-6, -1, 0, 3, 6];

/// Random well-typed slice-1 programs. A tape on which the builder faults
/// gives its `BuildFault`, never a stand-in program, so that the fault
/// reaches the test that drew the tape.
pub fn typed() -> impl Strategy<Value = Result<Program, BuildFault>> {
    vec(any::<u32>(), 0..4096).prop_map(build)
}

/// A static fault in the scope or the top ports of a program. The checks
/// of the builder exclude it, so it is a bug of the builder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BuildFault(Fault);

impl fmt::Display for BuildFault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the builder of typed programs faults ({:?}), which its checks exclude",
            self.0
        )
    }
}

impl std::error::Error for BuildFault {}

/// The program of a tape.
fn build(tape: Vec<u32>) -> Result<Program, BuildFault> {
    Builder::new(tape).program().map_err(BuildFault)
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
    let env = Env::of(params, args);
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
/// carries the core `Config`; a shared `Tape` would couple the two
/// generators for ten lines.
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
    statics: Vec<(String, STy)>,
    hw: Vec<Hw>,
    helpers: usize,
    /// The mutable lists that this frame declares.
    lists: Vec<String>,
    /// The mutable `Int` roots that this frame declares.
    counters: Vec<String>,
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
            lists: Vec::new(),
            counters: Vec::new(),
        }
    }
}

/// A helper with the concrete types of its formals and result; they have
/// literal or `const` widths, so one type holds everywhere.
#[derive(Clone)]
struct Helper {
    name: String,
    params: Vec<(String, Ty, Scalar)>,
    /// Whether the first formal has the mark `mut`.
    mut_first: bool,
    ret: (Ty, Scalar),
    body: Vec<Stmt>,
    result: HExpr,
}

/// A module signature; its port widths hold over the whole domain.
#[derive(Clone)]
struct Sig {
    name: String,
    params: Vec<(String, STy)>,
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
    tuples: u32,
    leaves: u32,
    arrays: u32,
    leaf_fallbacks: u32,
    selects: u32,
    indexes: u32,
    index_fallbacks: u32,
    lens: u32,
    records: u32,
    zeros: u32,
    fields: u32,
    data_bits: u32,
    arguments: u32,
    argument_fallbacks: u32,
    str_of: u32,
    joins: u32,
    scalars: u32,
    str_lens: u32,
    str_eqs: u32,
    list_lens: u32,
    list_indexes: u32,
    list_calls: u32,
    list_call_fallbacks: u32,
    pushes: u32,
    pops: u32,
    push_fallbacks: u32,
    mut_calls: u32,
    mut_call_fallbacks: u32,
    hw_mut_calls: u32,
    hw_mut_receivers: u32,
    fn_values: u32,
    mut_values: u32,
    hw_values: u32,
    value_calls: u32,
    value_call_fallbacks: u32,
    mut_value_calls: u32,
    hw_value_calls: u32,
    fn_arguments: u32,
}

struct Builder {
    tape: Tape,
    consts: Vec<(String, STy, SExpr)>,
    fns: Vec<ComptimeFn>,
    structs: Vec<StructDef>,
    list_fns: Vec<ListFn>,
    helpers: Vec<Helper>,
    /// The helpers with a `mut` formal; a plain call never names one.
    mut_helpers: Vec<Helper>,
    mut_fns: Vec<MutFn>,
    hw_values: Vec<fnvalues::HwValue>,
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
            structs: Vec::new(),
            list_fns: Vec::new(),
            helpers: Vec::new(),
            mut_helpers: Vec::new(),
            mut_fns: Vec::new(),
            hw_values: Vec::new(),
            sigs: Vec::new(),
            bodies: Vec::new(),
            contexts: Vec::new(),
            scope: Scope::default(),
            #[cfg(test)]
            stats: Stats::default(),
        }
    }

    fn program(&mut self) -> Result<Program, Fault> {
        self.structs()?;
        self.consts()?;
        self.fns()?;
        self.list_fns()?;
        self.mut_fns()?;
        self.helpers()?;
        self.mut_helpers()?;
        self.fn_values()?;
        self.signatures();
        let params = self
            .sigs
            .first()
            .map(|s| s.params.clone())
            .unwrap_or_default();
        let args: Vec<Value> = params.iter().map(|(_, t)| self.top_value(t)).collect();
        self.contexts = vec![Vec::new(); self.sigs.len()];
        if let Some(top) = self.contexts.first_mut() {
            top.push(args.clone());
        }
        self.bodies = vec![None; self.sigs.len()];
        for k in 0..self.sigs.len() {
            self.body(k)?;
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

    /// The items: consts, `comptime fn`s, helpers, and the reached modules.
    fn items(&self) -> Vec<Item> {
        let helpers = self
            .helpers
            .iter()
            .chain(&self.mut_helpers)
            .map(|h| Item::Helper {
                name: h.name.clone(),
                params: h
                    .params
                    .iter()
                    .map(|(n, t, _)| (n.clone(), t.clone()))
                    .collect(),
                mut_first: h.mut_first,
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
            .chain(self.hw_value_items())
            .chain(modules)
            .collect()
    }
}

#[cfg(test)]
mod tests;
