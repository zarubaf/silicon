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
    ($builder:expr, $field:ident, $when:expr) => {
        #[cfg(test)]
        {
            $builder.stats.$field += u32::from($when);
        }
    };
}

/// Records a call of the helper `$i` in the frame of `$ctx`, and counts it
/// as a repeat when the frame called it before or runs it twice.
macro_rules! called {
    ($builder:expr, $ctx:expr, $i:expr) => {
        note!(
            $builder,
            repeat_calls,
            $ctx.called.contains(&$i) || $ctx.looped
        );
        $ctx.called.insert($i);
    };
}

mod body;
mod container;
mod declare;
mod diagnostics;
mod enum_hw;
mod enums;
mod file;
mod fnvalues;
mod handle_lists;
mod handles;
mod hw;
mod hw_match;
mod inst;
mod lines;
mod lists;
mod matches;
mod mutcalls;
mod ports;
mod record;
mod stat;
mod strings;

pub use lines::lines;

use super::eval::{Env, Fault, Scope, Value};
use super::program::{
    ComptimeFn, EnumDef, FTy, HExpr, Item, ListFn, MutFn, Program, SExpr, STy, Scalar, Stmt,
    StructDef, Ty, render_items,
};
use super::records::records;
use super::twin::ports;
use proptest::collection::vec;
use proptest::prelude::*;
use stat::Reach;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;

/// The name prefixes of the static kinds: `P` parameter, `C` const, `f`
/// `comptime fn`, `s` static `let`, `j` loop binder, `B` binder of a static
/// `match`, `G` list of handles, `H` helper that takes resources. The port
/// forms add `A`, `Z`, and `K` for a family and `Y` for the binder of a keyed
/// port: the twin names an entry `A0_3` and a keyed port by its public name.
/// A static name is one of them and digits; the twin must have none.
pub(super) const STATIC_PREFIXES: &str = "PCfsjbSkFBGHAZKY";

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
const MODULE_STMTS: u32 = 10;
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
/// The most functions that call an earlier function with a `mut` formal.
const NESTED_FNS: u32 = 3;
const ENVS: usize = 64;
/// A static `match` replaces one static expression in this many.
const MATCH_ODDS: u32 = 56;
/// A hardware `match` replaces one hardware expression in this many.
const HW_MATCH_ODDS: u32 = 40;
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

/// A side tape of the builder.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lane {
    Side,
    Hand,
    Port,
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

/// A hardware name of an enum type in scope: a port, a register, a wire, or
/// a `let`. It has one type in every env.
#[derive(Clone, Debug)]
struct HwEnum {
    /// A port, a register, a wire, a `let`, or a child output.
    expr: HExpr,
    def: EnumDef,
    /// Whether the value is hardware, not a static binding.
    hardware: bool,
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
    /// The hardware names of an enum type.
    enums: Vec<HwEnum>,
    /// The resources that this frame declared and has not bound yet.
    pending: Vec<handles::Pending>,
    /// The readable names that helpers and groups of handles made. The
    /// draws of the main tape never see them, so that a program with
    /// handles holds the program of the main tape alone; the values of the
    /// handles reach the outputs through `mix_hand`.
    hand: Vec<Hw>,
    /// Whether the scope is a helper body, which has no `hand`.
    local: bool,
    /// The helpers that a call of this frame names.
    called: BTreeSet<usize>,
    /// Whether the frame is the body of a loop with a second iteration.
    looped: bool,
    /// The entries and the keyed ports of the module, readable by the port
    /// tape only, so that a program without port forms is the program of
    /// the other tapes alone; they reach the outputs through `mix_port`.
    port: Vec<Hw>,
}

impl Ctx {
    /// A write to the root `root` changes what a width over it means. A
    /// hardware name whose type expression reads `root` loses the
    /// expression, so later statements do not print it again; they print
    /// a literal type or choose another name.
    fn forget(&mut self, root: &str) {
        for h in &mut self.hw {
            let reads = h.ty.as_ref().is_some_and(|t| match t {
                Ty::UInt(w) | Ty::SInt(w) => crate::program::sexpr(w)
                    .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                    .any(|token| token == root),
                Ty::Bool | Ty::Enum(_) => false,
            });
            if reads {
                h.ty = None;
            }
        }
    }

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
            enums: self.enums.clone(),
            pending: Vec::new(),
            hand: self
                .hand
                .iter()
                .map(|h| Hw {
                    types: parents
                        .iter()
                        .filter_map(|&p| h.types.get(p).copied())
                        .collect(),
                    ..h.clone()
                })
                .collect(),
            local: self.local,
            called: BTreeSet::new(),
            looped: self.looped,
            port: self
                .port
                .iter()
                .map(|h| Hw {
                    types: parents
                        .iter()
                        .filter_map(|&p| h.types.get(p).copied())
                        .collect(),
                    ..h.clone()
                })
                .collect(),
        }
    }

    /// Makes `h` readable to the draws of the hand tape. A helper body has
    /// one pool.
    fn publish(&mut self, h: Hw) {
        if self.local {
            self.hw.push(h);
        } else {
            self.hand.push(h);
        }
    }

    /// The scope with the names of `hand` among the others, for an
    /// expression that the hand tape draws.
    fn view(&self) -> Ctx {
        let mut ctx = self.clone();
        ctx.hw.append(&mut ctx.hand);
        ctx
    }

    /// The scope with the names of `port` among the others, for an
    /// expression that the port tape draws.
    fn port_view(&self) -> Ctx {
        let mut ctx = self.clone();
        ctx.hw.append(&mut ctx.port);
        ctx
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
    /// The enum ports of the module.
    enum_inputs: Vec<(String, EnumDef)>,
    enum_outputs: Vec<(String, EnumDef)>,
    /// The families, keyed ports, and port helper calls of the module.
    plan: ports::PortPlan,
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
    pop_fallbacks: u32,
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
    converted_args: u32,
    /// Identities that two spellings of a finite argument reached.
    aliased_args: u32,
    diagnostics: u32,
    structured_diagnostics: u32,
    effectful_fns: u32,
    nested_fns: u32,
    effectful_calls: u32,
    enum_ctors: u32,
    enum_zeros: u32,
    enum_unpacks: u32,
    enum_consts: u32,
    enum_lets: u32,
    enum_diagnostics: u32,
    enum_probes: u32,
    enum_bits: u32,
    hw_ctors: u32,
    hw_unpacks: u32,
    hw_lets: u32,
    hw_wires: u32,
    hw_regs: u32,
    hw_bits: u32,
    static_matches: u32,
    static_enum_matches: u32,
    static_binders: u32,
    nested_matches: u32,
    complete_matches: u32,
    finite_matches: u32,
    hw_matches: u32,
    hw_enum_matches: u32,
    hw_binders: u32,
    hw_complete_matches: u32,
    hw_expr_scrutinees: u32,
    bind_wire_calls: u32,
    bind_reg_calls: u32,
    bind_input_calls: u32,
    bind_mem_calls: u32,
    direct_mems: u32,
    declare_calls: u32,
    scratch_calls: u32,
    list_groups: u32,
    decl_regs: u32,
    decl_wires: u32,
    decl_mems: u32,
    decl_instances: u32,
    unit_results: u32,
    handle_results: u32,
    tuple_results: u32,
    array_results: u32,
    record_results: u32,
    container_binds: u32,
    caller_child_inputs: u32,
    nested_calls: u32,
    repeat_calls: u32,
    mixed_container_reads: u32,
    mixed_explicit_reads: u32,
    list_input_groups: u32,
    fam_loops: u32,
    fam_arms: u32,
    fam_tops: u32,
    skipped_families: u32,
    empty_entries: u32,
    own_selects: u32,
    own_targets: u32,
    second_loops: u32,
    child_binds: u32,
    child_reads: u32,
    as_strings: u32,
    as_core: u32,
    as_portkeys: u32,
    as_joins: u32,
    as_computed: u32,
    helper_names: u32,
    helper_families: u32,
    helper_chains: u32,
    port_reaches: u32,
    port_lost: u32,
    /// The most arms of one match.
    max_arms: usize,
    /// The most matches open at once.
    max_level: u32,
}

struct Builder {
    tape: Tape,
    /// The same numbers from the end. The forms of enums draw from it, so
    /// a program without them is the program of the main tape alone.
    side: Tape,
    /// The same numbers from the end, mixed. The forms of handles draw
    /// from it, so that a program without them is the program of the other
    /// tapes alone, enums included.
    hand: Tape,
    /// The same numbers from the end, mixed with another constant. The forms
    /// of ports draw from it, so that a program without them is the program
    /// of the other tapes alone.
    port: Tape,
    /// The tape that `on_side`, `on_hand`, or `on_port` has swapped into
    /// `tape`, if any.
    swapped: Option<Lane>,
    /// The binders `B<n>` of static matches made so far.
    binders: u32,
    /// The matches that are open: the arm being built is in this many.
    match_level: u32,
    consts: Vec<(String, STy, SExpr)>,
    fns: Vec<ComptimeFn>,
    structs: Vec<StructDef>,
    enums: Vec<EnumDef>,
    list_fns: Vec<ListFn>,
    helpers: Vec<Helper>,
    /// The helpers that take resources, from the hand tape.
    res_helpers: Vec<handles::ResHelper>,
    /// The structs of handles that those helpers return.
    hstructs: Vec<StructDef>,
    /// The resources that handle forms declare so far, once for each env
    /// that runs the declaration.
    decls: usize,
    /// The most such resources: `MAX_DECLS`, and less in a test of the cap.
    max_decls: usize,
    /// The helpers that a call names.
    called: BTreeSet<usize>,
    /// The shapes of result that the helpers so far return.
    shapes: BTreeSet<usize>,
    /// The helpers that declare a port, from the port tape.
    port_helpers: Vec<ports::PortHelper>,
    /// The helpers that the bodies of reached modules call.
    port_helper_used: BTreeSet<usize>,
    /// The ports that the plans of the signatures declare so far.
    port_count: usize,
    /// The helpers with a `mut` formal; a plain call never names one.
    mut_helpers: Vec<Helper>,
    mut_fns: Vec<MutFn>,
    hw_values: Vec<fnvalues::HwValue>,
    sigs: Vec<Sig>,
    bodies: Vec<Option<Vec<Stmt>>>,
    /// The distinct argument tuples of each module.
    contexts: Vec<Vec<Vec<Value>>>,
    /// The messages `d<n>` made so far.
    messages: u32,
    scope: Scope,
    #[cfg(test)]
    stats: Stats,
    /// The spellings of the finite arguments of each identity.
    #[cfg(test)]
    spellings: BTreeMap<(usize, String), BTreeSet<String>>,
}

impl Builder {
    fn new(tape: Vec<u32>) -> Builder {
        Builder {
            side: Tape {
                numbers: tape.iter().rev().copied().collect::<Vec<_>>().into_iter(),
            },
            hand: Tape {
                numbers: tape
                    .iter()
                    .rev()
                    .map(|n| (n ^ (n >> 16)).wrapping_mul(0xE9B5_DBA5))
                    .collect::<Vec<_>>()
                    .into_iter(),
            },
            port: Tape {
                numbers: tape
                    .iter()
                    .rev()
                    .map(|n| {
                        let m = n.wrapping_mul(0x9E37_79B1);
                        m ^ (m >> 15)
                    })
                    .collect::<Vec<_>>()
                    .into_iter(),
            },
            tape: Tape {
                numbers: tape.into_iter(),
            },
            swapped: None,
            binders: 0,
            match_level: 0,
            consts: Vec::new(),
            fns: Vec::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            list_fns: Vec::new(),
            helpers: Vec::new(),
            res_helpers: Vec::new(),
            hstructs: Vec::new(),
            decls: 0,
            max_decls: handles::MAX_DECLS,
            called: BTreeSet::new(),
            shapes: BTreeSet::new(),
            port_helpers: Vec::new(),
            port_helper_used: BTreeSet::new(),
            port_count: 0,
            mut_helpers: Vec::new(),
            mut_fns: Vec::new(),
            hw_values: Vec::new(),
            sigs: Vec::new(),
            bodies: Vec::new(),
            contexts: Vec::new(),
            messages: 0,
            scope: Scope::default(),
            #[cfg(test)]
            stats: Stats::default(),
            #[cfg(test)]
            spellings: BTreeMap::new(),
        }
    }

    fn program(&mut self) -> Result<Program, Fault> {
        self.enums()?;
        self.structs()?;
        self.consts()?;
        self.fns()?;
        self.list_fns()?;
        self.mut_fns()?;
        self.helpers()?;
        self.mut_helpers()?;
        self.fn_values()?;
        self.nested_fns()?;
        self.signatures();
        self.res_helpers()?;
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
        let named: Vec<(String, Vec<Vec<Value>>)> = self
            .sigs
            .iter()
            .zip(&self.contexts)
            .map(|(s, c)| (s.name.clone(), c.clone()))
            .collect();
        let records = records(&items, &render_items(&items), ("M0", &args), &named)?;
        Ok(Program {
            items,
            top: "M0".to_owned(),
            args,
            ports,
            probe,
            records,
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
                    .map(|(n, t, _)| (n.clone(), FTy::Data(t.clone())))
                    .collect(),
                mut_first: h.mut_first,
                ret: FTy::Data(h.ret.0.clone()),
                body: h.body.clone(),
                result: h.result.clone(),
            });
        // A helper names the module of its child, so it stays out of the
        // file when no module reaches that module.
        let reached = |h: &&handles::ResHelper| {
            h.children
                .iter()
                .all(|(j, _)| self.bodies.get(*j).is_some_and(Option::is_some))
        };
        let res = self
            .res_helpers
            .iter()
            .filter(reached)
            .map(|h| Item::Helper {
                name: h.name.clone(),
                params: h.params.clone(),
                mut_first: false,
                ret: h.ret.clone(),
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
            .chain(self.hstructs.iter().cloned().map(Item::Struct))
            .chain(helpers)
            .chain(res)
            .chain(self.port_helper_items())
            .chain(self.hw_value_items())
            .chain(modules)
            .collect()
    }
}

#[cfg(test)]
mod tests;
