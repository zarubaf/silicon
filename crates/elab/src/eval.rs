// SPDX-License-Identifier: Apache-2.0
//! The evaluator of slice 1 and the static containers, types, and records of slice 2, with the
//! budgets and the cost model of section 5.4 of the front-end spec. Lean `Source.Eval` is its normative definition:
//! each charge here is a charge there, in the same order and at the same node. It reads the
//! checked AST. It recurses over the AST and the calls, so it runs on the front-end thread.
//!
//! A value is static, hardware, or a handle (section 5.1), or a literal with `[]` that waits for
//! the type of a typed use. The child module `hwops` makes the hardware nodes, the child module
//! `call` evaluates the calls, the child module `arms` walks the arms of a hardware `if` and `match`, the child module `pack` packs and unpacks the bits of a value, and the child modules `container` and `place` make and read the
//! static containers. The child module `string` scans and converts the strings, and the child
//! module `list` makes the lists and changes them in place. The child module `types` evaluates
//! the type expressions and the struct specializations, the child module `record` makes and
//! reads the records, the child module `handle` types the handles of a result, the child module `about` writes the text of a result in a message, and the child module `inst` runs the module statements and the
//! instantiations of Lean `Source.Elab`. The child module `store` owns the locals, the frames,
//! the constants, the waiting results, and the change log. The evaluator calls its methods and
//! reads none of its fields.
//!
//! A result that refers to an existing value, such as a local or a constant, stays a
//! reference until a copy pays for it. Thus a read that the cost model does not charge does
//! no work in the size of the value.

mod about;
mod agg;
mod arms;
mod call;
mod container;
mod data;
mod field;
mod generate;
mod handle;
mod hwops;
mod info;
mod inst;
mod list;
mod matching;
mod mem;
mod name;
mod observe;
mod pack;
mod place;
mod record;
mod reflect;
mod source;
mod store;
mod string;
mod target;
#[cfg(test)]
mod tests_agg;
#[cfg(test)]
mod tests_bind;
#[cfg(test)]
mod tests_eq;
#[cfg(test)]
mod tests_if;
#[cfg(test)]
mod tests_lit;
#[cfg(test)]
mod tests_match;
#[cfg(test)]
mod tests_mem;
#[cfg(test)]
mod tests_work_hw;
mod typed;
mod types;

pub use inst::Design;
use inst::family_value;
pub(crate) use inst::{Bind, Elab, Inst, Literal, Mem, Sink, elaborate};
pub(crate) use mem::addr_width;
use store::{ConstStatus, Slot, Store};
use typed::Whole;
use types::prim;

use crate::agg::{Agg, Base};
use crate::hw::{Graph, Handle, HwId, Op, Part, Ref, Root, Seen, Val};
use crate::int::Int;
use crate::limit;
use crate::names::{PathId, Paths, Step, Sym};
use crate::ops::{self, Fault, Fuel};
use crate::scan::{CallArgs, Numbers, Scan, Syms};
use crate::types::{Ty, TyId, Types};
use crate::value::{Evaluated, Value, int_size};
use crate::{Budget, Code, Error};
use parse::ast::{
    BinOp, Builtin, BuiltinArgs, Expr, Ident, Item, NodeId, Pos, Stmt, TypeExpr, UnOp,
};
use parse::{NestedStack, StackError};
use resolve::{DeclId, Kind, Resolved, ResolvedExpr, Target};
use std::collections::{BTreeMap, BTreeSet};

/// The result of an expression. Only `Made` is a new value. The others are references, so a
/// binding of them is a copy.
enum Out {
    Made(Val),
    /// A new value that the cost model treats as a reference: a type name, a domain, a child
    /// input, a child output, or an element of a new container.
    Named(Val),
    /// A copy of a reference to a local that a change reached while the result waited. Lean
    /// keeps the root of such a result, so a static copy, or a static part of it, still holds
    /// the local (section 5.4).
    Kept(Val, Root),
    /// A local or a constant, or an element of one. A call evaluates its arguments in the
    /// caller frame and binds them in a new frame, so a reference names its frame.
    Ref(Ref),
}

impl Out {
    fn is_ref(&self) -> bool {
        !matches!(self, Out::Made(_))
    }

    /// The local that this result keeps holding after a mutation copied its value.
    fn kept(&self) -> Option<Root> {
        match self {
            Out::Kept(_, root) => Some(*root),
            _ => None,
        }
    }
}

impl Opnd {
    /// The operand as a result, so that it can wait in the store.
    fn into_out(self) -> Out {
        match self {
            Opnd::Hw(h) => Out::Made(Val::Hw(h)),
            Opnd::Static(o) => o,
        }
    }

    /// The operand that `into_out` made.
    fn of_out(o: Out) -> Opnd {
        match o {
            Out::Made(Val::Hw(h)) => Opnd::Hw(h),
            o => Opnd::Static(o),
        }
    }
}

/// The record of an open argument of `@typeInfo` (section 9.4, Lean `ArgRec`). Under `Node`, a
/// node with a hardware value is `S011`. `Place` marks the root and the steps of a place that is
/// the whole argument: they read no value, so the check skips them.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ArgRec {
    Node,
    Place,
}

/// An operand at a use that reads it: a hardware value, or a static result.
enum Opnd {
    Hw(HwId),
    Static(Out),
}

/// Which map of targets the names read: the top expression is its own parse, with its own ids.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Names {
    Top,
    File,
}

/// A frame of section 7.3: its path, and its number in the table of frames. The root is 0.
#[derive(Clone, Copy)]
struct FrameRef {
    path: Option<PathId>,
    id: usize,
}

const ROOT: FrameRef = FrameRef { path: None, id: 0 };

/// A named hardware binding: its core name, its value, and the position of the binding.
pub(crate) struct Let {
    pub path: PathId,
    pub value: HwId,
    pub pos: Pos,
}

/// The names of one instantiation. `frames` numbers each frame by its parent and its field
/// pair. `versions` counts the bindings of each source name in each frame. A call result takes
/// no version. `lets` holds the named
/// bindings in evaluation order. Each table grows only with the bindings that run.
#[derive(Default)]
struct Naming {
    frames: BTreeMap<(usize, Sym, Step), usize>,
    versions: BTreeMap<(usize, Sym), u64>,
    lets: Vec<Let>,
    /// The number of the marks of shared conditions (`Op::Share`).
    shares: u64,
}

struct Evaluator<'a> {
    file: &'a Resolved,
    top: Option<&'a ResolvedExpr>,
    names: Names,
    /// The index of each item by the declaration of its name.
    items: BTreeMap<DeclId, usize>,
    /// The value of each number literal, from the pass before the evaluation.
    numbers: Numbers,
    /// The index expressions with a call in their arguments, from the same pass.
    call_args: CallArgs,
    syms: Syms,
    limit: u64,
    depth: u64,
    /// The stack of each thread of the evaluation.
    stack: NestedStack,
    ret: Option<TyId>,
    fuel: Fuel,
    /// The static types of the elaboration: a copy of a type is a copy of its id.
    tys: Types,
    store: Store,
    graph: Graph,
    paths: Paths,
    naming: Naming,
    /// The struct items whose parameter types evaluate now: a use of one is a cycle.
    binding: Vec<usize>,
    /// The item whose body runs, for its call sites.
    item: usize,
    frame: FrameRef,
    elab: Elab,
    /// The innermost guard (section 9.4): its kind, the nesting depth at its start, and the item
    /// of the outermost call under it.
    guard: Option<Guard>,
    /// The static mode (section 9.4), else none. A call sets it in O(1), and the name renders
    /// only in an error.
    mode: Option<Mode>,
    /// The record of the open builtin argument, else none. Each context and each call inside the
    /// argument keeps it, and the end of the argument restores it.
    arg: Option<ArgRec>,
    /// The name of a function value while its signature evaluates: each depth check there
    /// reports at it. A nested level clears it, so it keeps its own positions.
    site: Option<Pos>,
    /// The records of `diagnostic` in evaluation order (section 8.2).
    records: Vec<String>,
    /// The emitted names of the instantiations that started, in order. A record refers to one
    /// by its index, so it copies no text.
    emitted: Vec<String>,
    /// The index in `emitted` of the current instantiation, else none (`-`).
    inst: Option<usize>,
    /// The calls from the module body to the current node: the item index of the callee and
    /// the position of its call, outermost first. A call adds one in O(1), and a record
    /// writes them out after the charge of its bytes.
    calls: Vec<(usize, Pos)>,
    /// The number of the frame of the current call, and 0 in a module body. It tells two calls
    /// of one function apart (section 6.2). A call sets it in O(1), and its return restores it.
    call: usize,
    /// The name of each domain that a read named.
    domains: BTreeMap<DeclId, String>,
    /// The data type of each type with the handle flag that a read of a container made
    /// (`data_ty`).
    data_tys: BTreeMap<TyId, TyId>,
    /// The `let` bindings without a type annotation. The type of such a slot comes from its
    /// value, so `@TypeOf` does not take it as a declared type (section 9.3).
    untyped: BTreeSet<DeclId>,
    /// The lengths of the types and the powers of ten that the records measured.
    lens: crate::serial::Cache,
}

/// The kind of a guard (section 9.4): a hardware arm or a structural context. A family key
/// (`Key`), an index of a `:=` target (`Index`), an `as` key (`Name`), a key of the operand of
/// the builtin `q` (`Query`), and the argument of the builtin `q` (`Arg`) are structural contexts
/// with their own texts.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardKind {
    Arm,
    Structural,
    Key,
    Index,
    Name,
    Query(Builtin),
    /// The argument of the builtin `q` (`@typeInfo`, section 9.4).
    Arg(Builtin),
}

/// The innermost guard: its kind, the nesting depth at its start, and `callee`. The `callee` is
/// the item of the outermost call under the guard. A call records its item only when the guard
/// has no record, so a deeper call keeps it, and the return of the call ends it. The record is
/// an index, so it costs O(1), and the name renders only in an error. The texts of `S016` name
/// the kind and are normative, so they equal those of Lean `Guard`.
#[derive(Clone, Copy)]
pub(crate) struct Guard {
    pub(crate) kind: GuardKind,
    pub(crate) depth: u64,
    pub(crate) callee: Option<usize>,
}

/// The static mode (section 9.4): the `eval` command, or the item of the outermost
/// `comptime fn` of the call chain.
#[derive(Clone, Copy)]
pub(crate) enum Mode {
    Eval,
    Static(usize),
}

impl Guard {
    /// The text of a mutation of the binding `x`.
    pub(crate) fn change(self, x: &str) -> String {
        match self.kind {
            GuardKind::Arm => format!(
                "a hardware arm cannot change `{x}`, a binding from before the arm; change `{x}` \
                 before the `if` or `match`, and use the result in the arm"
            ),
            GuardKind::Structural => format!(
                "a type or a constant cannot change `{x}`; change `{x}` before it, keep the result in a `let`, and use that name here"
            ),
            GuardKind::Key => format!(
                "a port family key cannot change `{x}`; change `{x}` before this statement, keep \
                 the result in a `let`, and use that name in the key"
            ),
            GuardKind::Index => format!(
                "a `:=` target index cannot change `{x}`; change `{x}` before the `:=`, keep the \
                 result in a `let`, and use that name in the index"
            ),
            GuardKind::Name => format!(
                "an `as` key cannot change `{x}`; change `{x}` before this statement, keep the \
                 result in a `let`, and use that name in the key"
            ),
            GuardKind::Query(q) => format!(
                "a key of `@{q}` cannot change `{x}`; change `{x}` before `@{q}`, keep the result \
                 in a `let`, and use that name in the key",
                q = q.name()
            ),
            GuardKind::Arg(q) => format!(
                "an argument of `@{q}` cannot change `{x}`; change `{x}` before `@{q}`, keep the \
                 result in a `let`, and use that name in the argument",
                q = q.name()
            ),
        }
    }

    /// The text of the graph effect `g`.
    pub(crate) fn effect(self, g: &str) -> String {
        match self.kind {
            GuardKind::Arm => format!(
                "a hardware arm has no graph effect such as `{g}`; call `{g}` before the `if` or \
                 `match`, and use its result in the arm"
            ),
            GuardKind::Structural => format!(
                "a type or a constant has no graph effect such as `{g}`; call it before and use the result"
            ),
            GuardKind::Key => format!(
                "a port family key has no graph effect such as `{g}`; call `{g}` before this \
                 statement, keep the result in a `let`, and use that name in the key"
            ),
            GuardKind::Index => format!(
                "a `:=` target index has no graph effect such as `{g}`; call `{g}` before the \
                 `:=`, keep the result in a `let`, and use that name in the index"
            ),
            GuardKind::Name => format!(
                "an `as` key has no graph effect such as `{g}`; call `{g}` before this \
                 statement, keep the result in a `let`, and use that name in the key"
            ),
            GuardKind::Query(q) => format!(
                "a key of `@{q}` has no graph effect such as `{g}`; call `{g}` before `@{q}`, \
                 keep the result in a `let`, and use that name in the key",
                q = q.name()
            ),
            GuardKind::Arg(q) => format!(
                "an argument of `@{q}` has no graph effect such as `{g}`; call `{g}` before \
                 `@{q}`, keep the result in a `let`, and use that name in the argument",
                q = q.name()
            ),
        }
    }
}

/// Why an evaluation stops: its first error, or a deeper level for which the machine cannot
/// give the stack.
pub(crate) enum Stop {
    Error(Error),
    Stack(StackError),
}

type Res<T> = Result<T, Stop>;

fn fail<T>(code: Code, pos: Pos, message: String) -> Res<T> {
    Err(Stop::Error(Error { code, pos, message }))
}

fn at(pos: Pos) -> impl Fn(Fault) -> Stop {
    move |(code, message)| Stop::Error(Error { code, pos, message })
}

fn type_pos(t: &TypeExpr) -> Pos {
    match t {
        TypeExpr::Name { pos, .. }
        | TypeExpr::Index { pos, .. }
        | TypeExpr::Unit { pos }
        | TypeExpr::Tuple { pos, .. }
        | TypeExpr::Array { pos, .. }
        | TypeExpr::Fn { pos, .. }
        | TypeExpr::Builtin { pos, .. } => *pos,
    }
}

fn stmt_pos(s: &Stmt) -> Pos {
    match s {
        Stmt::Local { pos, .. }
        | Stmt::Assign { pos, .. }
        | Stmt::Connect { pos, .. }
        | Stmt::Reg { pos, .. }
        | Stmt::Wire { pos, .. }
        | Stmt::Mem { pos, .. }
        | Stmt::Input { pos, .. }
        | Stmt::Output { pos, .. }
        | Stmt::Inst { pos, .. }
        | Stmt::Ret { pos, .. }
        | Stmt::CtIf { pos, .. }
        | Stmt::CtFor { pos, .. }
        | Stmt::Block { pos, .. }
        | Stmt::Expr { pos, .. }
        | Stmt::Alias { pos, .. } => *pos,
    }
}

impl<'a> Evaluator<'a> {
    /// The evaluator of the file `file` with the budget `budget`. A top expression `top` has
    /// its own map of targets.
    fn new(
        file: &'a Resolved,
        top: Option<&'a ResolvedExpr>,
        budget: Budget,
        scan: Scan,
        elab: Elab,
    ) -> Evaluator<'a> {
        let mut items = BTreeMap::new();
        for (i, item) in file.ast().iter().enumerate() {
            let name = item.name();
            if let Some(Target::Decl(id)) = file.target(name.id) {
                items.insert(id, i);
            }
        }
        #[cfg(test)]
        {
            crate::counters::begin();
            crate::counters::add(crate::counters::Count::Ast, scan.nodes);
        }
        Evaluator {
            file,
            top,
            names: if top.is_some() {
                Names::Top
            } else {
                Names::File
            },
            items,
            numbers: scan.numbers,
            call_args: scan.call_args,
            syms: scan.syms,
            limit: budget.depth,
            depth: 0,
            stack: scan.stack,
            ret: None,
            fuel: Fuel::new(budget.fuel),
            tys: Types::default(),
            store: Store::new(file.ast().len()),
            graph: Graph::default(),
            paths: Paths::default(),
            naming: Naming::default(),
            binding: Vec::new(),
            item: 0,
            frame: ROOT,
            elab,
            guard: None,
            mode: top.map(|_| Mode::Eval),
            arg: None,
            site: None,
            records: Vec::new(),
            emitted: Vec::new(),
            inst: None,
            calls: Vec::new(),
            call: 0,
            domains: BTreeMap::new(),
            untyped: BTreeSet::new(),
            data_tys: BTreeMap::new(),
            lens: crate::serial::Cache::default(),
        }
    }
}

/// The value of `top` in the file scope of `file`, and the used fuel.
pub(crate) fn run(
    file: &Resolved,
    top: &ResolvedExpr,
    budget: Budget,
    scan: Scan,
) -> Res<(Evaluated, u64)> {
    let mut ev = Evaluator::new(
        file,
        Some(top),
        budget,
        scan,
        Elab::new(crate::names::sha16),
    );
    let e = top.expr();
    let out = ev.eval(e)?;
    let out = need(e, out)?;
    let value = ev.static_value(e.pos(), out)?;
    let used = budget.fuel - ev.fuel.left();
    #[cfg_attr(not(test), allow(unused_mut))]
    let mut evaluated = Evaluated::new(value, ev.tys);
    #[cfg(test)]
    {
        evaluated.steps = ev.store.steps();
    }
    Ok((evaluated, used))
}

/// A reference to the constant at the index `i` of the table of constants.
fn const_ref(i: usize) -> Out {
    Out::Ref(Ref {
        root: Root::Const(i),
        path: Vec::new(),
    })
}

/// `[]` outside a typed use has no type: `S010` at the `[]`.
fn no_type<T>(q: Pos) -> Res<T> {
    fail(
        Code::S010,
        q,
        "`[]` needs the type [T; 0] from its context".to_owned(),
    )
}

/// The value of `e`. Only `static_assert` and `error` give no value.
fn need(e: &Expr, out: Option<Out>) -> Res<Out> {
    match out {
        Some(out) => Ok(out),
        None => fail(
            Code::S010,
            e.pos(),
            "`static_assert` gives no value".to_owned(),
        ),
    }
}

impl Evaluator<'_> {
    fn target(&self, id: NodeId) -> Option<Target> {
        match self.names {
            Names::Top => self.top.and_then(|t| t.target(id)),
            Names::File => self.file.target(id),
        }
    }

    /// The declaration of an id: of the file, or of a binder of the top expression.
    fn decl_ref(&self, id: DeclId) -> &resolve::Decl {
        match (self.names, self.top) {
            (Names::Top, Some(top)) => top.decl(self.file, id),
            _ => self.file.decl(id),
        }
    }

    /// The declaration of a binder. Each binder is in the body of an item of the file, or in a
    /// pattern of the top expression.
    fn decl(&self, name: &Ident) -> Res<DeclId> {
        match self.target(name.id) {
            Some(Target::Decl(id)) => Ok(id),
            _ => fail(
                Code::S010,
                name.pos,
                format!("`{}` has no declaration", name.name),
            ),
        }
    }

    /// The symbol of the source name of a declaration.
    fn sym(&self, id: DeclId) -> Sym {
        self.syms.decls.get(&id).copied().unwrap_or(0)
    }

    fn charge(&mut self, pos: Pos, units: u128) -> Res<()> {
        self.fuel.pay(units).map_err(at(pos))
    }

    /// A mutation at `pos` of the local at `root` that a parked result holds charges the size of
    /// the local before the change (section 5.4). The charge pays for the copies that the change
    /// causes, so it comes before the change reaches the history of the local. Each mutation
    /// calls it as its last charge, so it also counts the change of the local.
    fn charge_held(&mut self, pos: Pos, root: Root) -> Res<()> {
        if self.store.is_held(root) {
            let size = self.seen_size(self.store.root(&root).seen());
            self.charge(pos, size)?;
        }
        self.store.mutated(root);
        Ok(())
    }

    fn size(&self, out: &Out) -> u128 {
        self.seen_size(self.store.seen(out))
    }

    /// The size of what a result is.
    fn seen_size(&self, seen: Seen<'_>) -> u128 {
        u128::from(match seen {
            Seen::Static(v) => v.size(),
            Seen::Hw(h) => self.graph.size(h),
            Seen::Handle(_) => 1,
            Seen::Pending(_, p) => self.part_size(p),
            Seen::Agg(a) => a.size(&self.graph, &self.tys),
        })
    }

    /// The size of a part that waits: 1 for `[]`, and 1 more than its parts for a literal.
    fn part_size(&self, p: &Part) -> u64 {
        match p {
            Part::Value(a) => a.size(&self.graph, &self.tys),
            Part::Empty(_) => 1,
            Part::Array(_, ps) | Part::Tuple(_, ps) => {
                1 + ps.iter().map(|p| self.part_size(p)).sum::<u64>()
            }
        }
    }

    /// Whether the result is a hardware aggregate. A reference into a static value is not, and
    /// the check does not walk its path.
    fn is_agg(&self, out: &Out) -> bool {
        match out {
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => matches!(v, Val::Agg(_)),
            Out::Ref(r) => {
                matches!(self.store.root(&r.root), Val::Agg(_))
                    && matches!(self.store.at(r), Seen::Agg(_))
            }
        }
    }

    /// Whether the operand is a hardware aggregate.
    fn opnd_is_agg(&self, o: &Opnd) -> bool {
        matches!(o, Opnd::Static(out) if self.is_agg(out))
    }

    /// A binding copies a reference.
    fn copy(&mut self, pos: Pos, out: &Out) -> Res<()> {
        if out.is_ref() {
            self.charge(pos, self.size(out))?;
        }
        Ok(())
    }

    /// The operand `e` of the node at `pos`, at a use that reads it.
    fn operand(&mut self, pos: Pos, e: &Expr) -> Res<Opnd> {
        let o = self.eval(e)?;
        let o = need(e, o)?;
        let d = self.data(pos, o)?;
        self.arg_hw_opnd(e.pos(), &d)?;
        Ok(d)
    }

    /// The root of a read. The root of a place that is the whole argument of a builtin reads no
    /// value, so it has the record `Place`.
    fn eval_root(&mut self, root: &Expr, place: bool) -> Res<Option<Out>> {
        if place {
            self.with_arg(ArgRec::Place, |ev| ev.eval(root))
        } else {
            self.eval(root)
        }
    }

    /// Runs `act` with the record `rec` of an open builtin argument, and restores the record.
    fn with_arg<T>(&mut self, rec: ArgRec, act: impl FnOnce(&mut Self) -> Res<T>) -> Res<T> {
        let saved = self.arg.replace(rec);
        let r = act(self);
        self.arg = saved;
        r
    }

    /// The operand `e` of the node at `pos`, which evaluates after the operand `a`. The
    /// operand `a` waits in the store, so that `e` cannot change the value that `a` read.
    fn operand_after(&mut self, pos: Pos, a: Opnd, e: &Expr) -> Res<(Opnd, Opnd)> {
        let at = self.store.park(a.into_out());
        let b = self.operand(pos, e)?;
        let a = Opnd::of_out(self.store.resume_one(at));
        Ok((a, b))
    }

    /// A static condition.
    fn test(&self, pos: Pos, s: Seen<'_>) -> Res<bool> {
        match s {
            Seen::Static(Value::Bool(b)) => Ok(*b),
            Seen::Static(v) => fail(
                Code::S010,
                pos,
                format!("a condition is a Bool, not {}", v.text(&self.tys)),
            ),
            Seen::Pending(q, _) => no_type(q),
            s => fail(
                Code::S011,
                pos,
                format!(
                    "a static condition needs a static Bool, not {}",
                    self.text(s)
                ),
            ),
        }
    }

    /// A loop bound is a static `Int`.
    fn bound(&self, pos: Pos, out: &Out) -> Res<()> {
        match self.store.seen(out) {
            Seen::Static(Value::Int(_)) => Ok(()),
            Seen::Static(v) => fail(
                Code::S010,
                pos,
                format!("a loop bound is a static Int, not {}", v.text(&self.tys)),
            ),
            Seen::Pending(q, _) => no_type(q),
            s => fail(
                Code::S011,
                pos,
                format!("a loop bound is a static Int, not {}", self.text(s)),
            ),
        }
    }

    /// A result that is not a literal that waits for its type. `[]` outside a typed use has
    /// no type.
    fn known(&self, out: &Out) -> Res<()> {
        match self.store.seen(out) {
            Seen::Pending(q, _) => no_type(q),
            _ => Ok(()),
        }
    }

    fn bind(&mut self, id: DeclId, slot: Slot) {
        self.store.bind(id, slot);
    }

    /// Runs `act` one level deeper, or gives `S015` at `pos` above the limit. The one call of
    /// `NestedStack::nest` holds the thread: a level that starts a new group of levels runs on
    /// a new thread with the stack of the group, so the stack of each thread stays small for
    /// any nesting depth.
    fn nested<T: Send>(
        &mut self,
        pos: Pos,
        act: impl FnOnce(&mut Self) -> Res<T> + Send,
    ) -> Res<T> {
        if self.limit <= self.depth {
            return fail(
                Code::S015,
                pos,
                format!("the nesting depth goes above {}; raise --depth", self.limit),
            );
        }
        self.depth += 1;
        let site = self.site.take();
        let stack = self.stack;
        #[cfg(test)]
        let run = crate::counters::current();
        let act = move |ev: &mut Self| {
            // A level that starts a thread counts into the run of its parent.
            #[cfg(test)]
            if let Some(run) = run {
                crate::counters::join(run);
            }
            act(ev)
        };
        let r = stack
            .nest(self.depth, self, act)
            .unwrap_or_else(|e| Err(Stop::Stack(e)));
        self.depth -= 1;
        self.site = site;
        r
    }

    /// Runs `act` in a structural context (section 9.4): its guard starts at the current depth,
    /// so it is the innermost guard. Setting and restoring it is O(1).
    pub(super) fn structural<T>(&mut self, act: impl FnOnce(&mut Self) -> Res<T>) -> Res<T> {
        self.guarded(GuardKind::Structural, act)
    }

    /// Runs `act` under a guard of the kind `kind` (Lean `guardedBy`).
    pub(super) fn guarded<T>(
        &mut self,
        kind: GuardKind,
        act: impl FnOnce(&mut Self) -> Res<T>,
    ) -> Res<T> {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Guarded, 1);
        let saved = self.guard.replace(Guard {
            kind,
            depth: self.depth,
            callee: None,
        });
        let r = act(self);
        self.guard = saved;
        r
    }

    /// Runs `act` in the file scope with a new empty frame of locals and the return type
    /// `ret`. The frames below stay, so a reference into them still finds its value.
    fn in_frame<T>(&mut self, ret: Option<TyId>, act: impl FnOnce(&mut Self) -> Res<T>) -> Res<T> {
        self.store.push_frame();
        let saved_ret = std::mem::replace(&mut self.ret, ret);
        let names = std::mem::replace(&mut self.names, Names::File);
        let r = act(self);
        self.store.pop_frame();
        self.ret = saved_ret;
        self.names = names;
        r
    }

    /// Runs `act` in the item `item` and the naming frame `frame`.
    fn in_item<T>(
        &mut self,
        item: usize,
        frame: FrameRef,
        act: impl FnOnce(&mut Self) -> Res<T>,
    ) -> Res<T> {
        let saved = (self.item, self.frame);
        self.item = item;
        self.frame = frame;
        let r = act(self);
        (self.item, self.frame) = saved;
        r
    }

    /// The frame of the field pair `u` and `f` inside the current frame, with its path. Two
    /// frames with one path get one number, so their bindings share the versions.
    fn frame_of(&mut self, u: Sym, f: Step) -> (PathId, FrameRef) {
        let key = (self.frame.id, u, f.clone());
        let child = self.paths.child(self.frame.path, u);
        let path = self.paths.push(child, f);
        let next = self.naming.frames.len() + 1;
        let id = *self.naming.frames.entry(key).or_insert(next);
        (
            path,
            FrameRef {
                path: Some(path),
                id,
            },
        )
    }

    /// The core name `base` of the source name `key` in the current frame, or a version of it.
    fn version(&mut self, key: Sym, base: PathId) -> PathId {
        let k = (self.frame.id, key);
        let v = self.naming.versions.get(&k).copied().unwrap_or(0);
        self.naming.versions.insert(k, v + 1);
        if v == 0 {
            base
        } else {
            self.paths.push(base, Step::Version(v))
        }
    }

    /// The core name of the local `id` in the current frame.
    fn fresh(&mut self, id: DeclId) -> PathId {
        let u = self.sym(id);
        let base = self.paths.child(self.frame.path, u);
        self.version(u, base)
    }

    /// Binds the hardware value `h` to the core name `path`. The result refers to the name.
    fn bind_hw(&mut self, pos: Pos, path: PathId, h: HwId) -> Val {
        self.naming.lets.push(Let {
            path,
            value: h,
            pos,
        });
        let ty = self.graph.ty(h);
        Val::Hw(self.graph.mk(pos, ty, Op::Ref(path), Vec::new()))
    }

    /// A binding of the local `id`. Only a value with a hardware leaf gets a core name. An
    /// aggregate with a hardware leaf takes one version, and each of its hardware leaves gets a
    /// core `let`. An aggregate without one, for example an array of handles, takes no version
    /// (section 7.3).
    fn named(&mut self, pos: Pos, id: DeclId, v: Val) -> Res<Val> {
        match v {
            Val::Hw(h) => {
                let path = self.fresh(id);
                Ok(self.bind_hw(pos, path, h))
            }
            Val::Agg(a) if a.leaves(&self.tys) > 0 => {
                let path = self.fresh(id);
                Ok(Val::Agg(Box::new(self.bind_agg(pos, path, *a)?)))
            }
            v => Ok(v),
        }
    }

    /// The results of the arguments of a call, in order.
    fn args<'e>(&mut self, xs: impl IntoIterator<Item = &'e Expr>) -> Res<Vec<Out>> {
        let base = self.store.parked_len();
        for x in xs {
            let out = self.eval(x)?;
            let out = need(x, out)?;
            self.store.park(out);
        }
        Ok(self.store.resume(base))
    }

    /// A number literal. It pays the size of its value before it copies the value.
    fn number(&mut self, pos: Pos, id: NodeId) -> Res<Option<Out>> {
        let Some(n) = self.numbers.get(&(self.names == Names::Top, id)) else {
            return fail(Code::S010, pos, "the literal has no value".to_owned());
        };
        self.fuel.pay(u128::from(int_size(n))).map_err(at(pos))?;
        Ok(Some(Out::Made(Val::Static(Value::Int(n.clone())))))
    }

    fn made(&mut self, pos: Pos, v: Value) -> Res<Option<Out>> {
        self.charge(pos, u128::from(v.size()))?;
        Ok(Some(Out::Made(Val::Static(v))))
    }

    /// A string literal. Its size counts the characters, and the charge comes before the copy.
    fn string_lit(&mut self, pos: Pos, value: &str) -> Res<Option<Out>> {
        limit::string(value.len() as u128).map_err(at(pos))?;
        let size = 1 + value.chars().count() as u128;
        self.charge(pos, size)?;
        Ok(Some(Out::Made(Val::Static(Value::Str(value.to_owned())))))
    }

    /// A unary operator at `pos` on the operand `arg`.
    fn unary_expr(&mut self, pos: Pos, op: UnOp, arg: &Expr) -> Res<Option<Out>> {
        match self.operand(pos, arg)? {
            Opnd::Static(a) if self.is_agg(&a) => fail(
                Code::S010,
                pos,
                format!(
                    "`{}` does not accept {}",
                    ops::unop_text(op),
                    self.text(self.store.seen(&a))
                ),
            ),
            Opnd::Static(a) => {
                let v = ops::unary(op, self.store.value(&a), &mut self.fuel, &self.tys)
                    .map_err(at(pos))?;
                Ok(Some(Out::Made(Val::Static(v))))
            }
            Opnd::Hw(a) => Ok(Some(Out::Made(self.hw_unary(pos, op, a)?))),
        }
    }

    /// A binary operator, other than `&&` and `||`, at `pos` on the operands `lhs` and `rhs`.
    fn binary_expr(&mut self, pos: Pos, op: BinOp, lhs: &Expr, rhs: &Expr) -> Res<Option<Out>> {
        let a = self.operand(pos, lhs)?;
        let (a, b) = self.operand_after(pos, a, rhs)?;
        self.comparable(pos, op, &a, &b)?;
        if matches!(op, BinOp::Eq | BinOp::Ne) && (self.opnd_is_agg(&a) || self.opnd_is_agg(&b)) {
            return Ok(Some(Out::Made(self.agg_eq(pos, op, &a, &b)?)));
        }
        match (a, b) {
            (Opnd::Static(a), Opnd::Static(b)) if !self.is_agg(&a) && !self.is_agg(&b) => {
                Ok(Some(Out::Made(Val::Static(self.binary(pos, op, &a, &b)?))))
            }
            (a, b) => Ok(Some(Out::Made(self.hw_binary(pos, op, a, b)?))),
        }
    }

    fn eval(&mut self, e: &Expr) -> Res<Option<Out>> {
        self.charge(e.pos(), 1)?;
        if self.arg == Some(ArgRec::Place) {
            // The root and the steps of a place that is the whole argument read no value. The
            // record is `Place` only for the base of such a step, and each other part of the node
            // has the record `Node` (Lean `argNode`).
            return self.with_arg(ArgRec::Node, |ev| ev.eval_node(e, true));
        }
        let o = self.eval_node(e, false)?;
        if let Some(out) = &o {
            self.arg_hw(e.pos(), out)?;
        }
        Ok(o)
    }

    /// The work of the node `e`, after its charge. `place` tells that the node is the base of a
    /// step of a place that is the whole argument of a builtin.
    fn eval_node(&mut self, e: &Expr, place: bool) -> Res<Option<Out>> {
        match e {
            Expr::Num { pos, id, .. } => self.number(*pos, *id),
            Expr::Bool { pos, value } => self.made(*pos, Value::Bool(*value)),
            Expr::Str { pos, value } => self.string_lit(*pos, value),
            Expr::Name { pos, id, name } => Ok(Some(self.name(*pos, *id, name)?)),
            Expr::Match { pos, scrut, arms } => self.match_expr(*pos, scrut, arms),
            Expr::Builtin {
                pos,
                args: BuiltinArgs::TypeOf(operand),
            } => Ok(Some(self.type_of_builtin(*pos, operand)?)),
            Expr::Builtin {
                pos,
                args: BuiltinArgs::TypeInfo(arg),
            } => Ok(Some(self.type_info(*pos, arg)?)),
            Expr::Builtin {
                pos,
                args: BuiltinArgs::Struct(arg),
            } => Ok(Some(self.struct_builtin(*pos, arg)?)),
            Expr::Unary { pos, op, arg } => self.unary_expr(*pos, *op, arg),
            Expr::Binary {
                pos,
                op: op @ (BinOp::Land | BinOp::Lor),
                lhs,
                rhs,
            } => self.select(*pos, *op, lhs, rhs),
            Expr::Binary { pos, op, lhs, rhs } => self.binary_expr(*pos, *op, lhs, rhs),
            Expr::Cond { pos, cond, yes, no } => self.cond(*pos, cond, yes, no),
            Expr::Call {
                pos,
                id,
                callee,
                args,
            } => self.call(*pos, *id, callee, args),
            Expr::Method {
                pos,
                id,
                recv,
                name,
                args,
            } => self.method(*pos, *id, recv, name, args),
            Expr::Index { pos, base, args } => self.index_expr(e, *pos, base, args, place),
            Expr::Unit { .. } | Expr::Tuple { .. } | Expr::Array { .. } => self.container(e),
            Expr::Select { .. }
            | Expr::Field { .. }
            | Expr::Builtin {
                args: BuiltinArgs::Field(..),
                ..
            } => self.read(e, place),
            Expr::ArrayType { pos, elem, len } => {
                let t = self.array_type(*pos, elem, len)?;
                Ok(Some(Out::Made(Val::Static(Value::Type(t)))))
            }
            Expr::FnType { pos, params, ret } => {
                let t = self.fn_type(*pos, params, ret)?;
                Ok(Some(Out::Made(Val::Static(Value::Type(t)))))
            }
            Expr::Path { pos, ty, .. } => self.variant(*pos, ty, &[]),
        }
    }

    /// The index expression `e` at `pos` with the base `base`: the specialization of a type or a
    /// struct, the selection of an entry of a family, or the read of a part.
    fn index_expr(
        &mut self,
        e: &Expr,
        pos: Pos,
        base: &Expr,
        args: &[Expr],
        place: bool,
    ) -> Res<Option<Out>> {
        if let Expr::Name { pos: bp, id, .. } = base
            && let Some(Target::Prelude(k)) = self.target(*id)
            && k.is_type()
        {
            self.charge(*bp, 1)?;
            let t = self.index(pos, k, args)?;
            return Ok(Some(Out::Made(Val::Static(Value::Type(t)))));
        }
        if let Expr::Name { pos: bp, id, .. } = base
            && let Some(i) = self.struct_item(*id)
        {
            self.charge(*bp, 1)?;
            let t = self.spec(pos, i, args)?;
            return Ok(Some(Out::Made(Val::Static(Value::Type(t)))));
        }
        if let Some(out) = self.family_selection(pos, base, args)? {
            return Ok(Some(out));
        }
        self.read(e, place)
    }

    /// An `if` expression. A static condition selects an arm, and a hardware condition makes
    /// a select of both arms.
    fn cond(&mut self, pos: Pos, cond: &Expr, yes: &Expr, no: &Expr) -> Res<Option<Out>> {
        match self.operand(pos, cond)? {
            Opnd::Hw(c) => {
                let ty = self.graph.ty(c);
                if ty != Ty::Bool {
                    return fail(
                        Code::S010,
                        pos,
                        format!("a condition is a Bool, not {}", self.tys.text_of(&ty)),
                    );
                }
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Guarded, 1);
                let saved = self.guard.replace(Guard {
                    kind: GuardKind::Arm,
                    depth: self.depth,
                    callee: None,
                });
                let arms = self
                    .operand(pos, yes)
                    .and_then(|a| self.operand_after(pos, a, no));
                self.guard = saved;
                let (a, b) = arms?;
                Ok(Some(Out::Made(self.mux(pos, c, &a, &b)?)))
            }
            Opnd::Static(c) => {
                if self.test(pos, self.store.seen(&c))? {
                    self.eval(yes)
                } else {
                    self.eval(no)
                }
            }
        }
    }

    /// `&&` or `||`. A static left operand that decides gives its value. A static operand
    /// that does not decide gives the right operand, also a hardware one.
    fn select(&mut self, pos: Pos, op: BinOp, lhs: &Expr, rhs: &Expr) -> Res<Option<Out>> {
        match self.operand(pos, lhs)? {
            a @ Opnd::Static(_) if self.opnd_is_agg(&a) => {
                let b = self.operand(pos, rhs)?;
                Ok(Some(Out::Made(self.hw_binary(pos, op, a, b)?)))
            }
            Opnd::Static(a) => {
                let a = self.test(pos, self.store.seen(&a))?;
                if a == (op == BinOp::Lor) {
                    return Ok(Some(Out::Made(Val::Static(Value::Bool(a)))));
                }
                match self.operand(pos, rhs)? {
                    Opnd::Hw(h) => {
                        let ty = self.graph.ty(h);
                        if ty == Ty::Bool {
                            Ok(Some(Out::Made(Val::Hw(h))))
                        } else {
                            fail(
                                Code::S010,
                                pos,
                                format!("a condition is a Bool, not {}", self.tys.text_of(&ty)),
                            )
                        }
                    }
                    Opnd::Static(b) => {
                        let b = self.test(pos, self.store.seen(&b))?;
                        Ok(Some(Out::Made(Val::Static(Value::Bool(b)))))
                    }
                }
            }
            a @ Opnd::Hw(_) => {
                let b = self.operand(pos, rhs)?;
                Ok(Some(Out::Made(self.hw_binary(pos, op, a, b)?)))
            }
        }
    }

    /// A field of a record, or a port of an instance: a child input is a target, and a child
    /// output is hardware.
    fn field_part(&mut self, pos: Pos, b: Out, field: &Ident) -> Res<Out> {
        let b = match self.store.seen(&b) {
            Seen::Handle(Handle::Inst { id, path, inst, ty }) => {
                let (id, path, inst, ty) = (*id, *path, *inst, *ty);
                let port =
                    self.port_named(pos, (inst, ty), (self.port_sym(field), &field.name), None)?;
                return self.port_out(pos, (id, path), port);
            }
            // A field selection is a data context (section 9.2): a child input is `S017`.
            Seen::Handle(Handle::Res { .. } | Handle::Input { .. }) => {
                self.data(pos, b)?.into_out()
            }
            _ => b,
        };
        if matches!(self.store.seen(&b), Seen::Agg(_)) {
            return self.agg_field(pos, field, b);
        }
        self.record_field(pos, b, field)
    }

    /// `==` and `!=` take no operand whose type holds a function type (section 5.1), else
    /// `S010` at the operator. The check reads the function flag of the type, after both
    /// operands and before each join and each charge.
    fn comparable(&self, pos: Pos, op: BinOp, a: &Opnd, b: &Opnd) -> Res<()> {
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(());
        }
        // One read gives both flags of an operand: the function flag and the enum flag.
        let flags = |o: &Opnd| match o {
            Opnd::Static(o) => {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Flagged, 1);
                if let Seen::Agg(a) = self.store.seen(o) {
                    a.stored_ty()
                        .map_or((false, false), |t| (t.holds_fn(), t.holds_enum()))
                } else {
                    let v = self.store.value(o);
                    (v.holds_fn(), v.holds_enum())
                }
            }
            Opnd::Hw(_) => (false, false),
        };
        let no_function = || {
            fail(
                Code::S010,
                pos,
                format!("`{}` takes no function", ops::binop_text(op)),
            )
        };
        let (a_funcs, a_enums) = flags(a);
        if a_funcs {
            return no_function();
        }
        let (b_funcs, b_enums) = flags(b);
        if b_funcs {
            return no_function();
        }
        // The text names the type of the first operand with the enum flag.
        if let Some(o) = [(a, a_enums), (b, b_enums)]
            .into_iter()
            .find_map(|(o, enums)| enums.then_some(o))
        {
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{}` has no `==`; compare with `match (x) {{ E::V => true, _ => false }}`",
                    self.type_text(o)
                ),
            );
        }
        Ok(())
    }

    /// A binary operator with static operands. A static integer next to a finite operand
    /// takes the type of that operand first. A container operand compares by the common type
    /// of each pair of elements.
    fn binary(&mut self, pos: Pos, op: BinOp, a: &Out, b: &Out) -> Res<Value> {
        let (va, vb) = (self.store.value(a), self.store.value(b));
        if ops::composite(va) || ops::composite(vb) {
            return ops::container_op(op, va, vb, &mut self.fuel, &mut self.tys).map_err(at(pos));
        }
        let mut ca = None;
        let mut cb = None;
        if ops::unifies(op) {
            match (va, vb, va.finite_ty(), vb.finite_ty()) {
                (Value::Int(_), _, _, Some(t)) => {
                    let t = self.tys.mk(t);
                    ca = ops::convert(t, va, &mut self.fuel, &self.tys).map_err(at(pos))?;
                }
                (_, Value::Int(_), Some(t), _) => {
                    let t = self.tys.mk(t);
                    cb = ops::convert(t, vb, &mut self.fuel, &self.tys).map_err(at(pos))?;
                }
                _ => {}
            }
        }
        let va = ca.as_ref().unwrap_or(va);
        let vb = cb.as_ref().unwrap_or(vb);
        ops::binary(op, va, vb, &mut self.fuel, &self.tys).map_err(at(pos))
    }

    /// A name. A constant evaluates at its first use, in the table of constants. A domain
    /// is a handle in the whole body of its module, so it needs no slot.
    /// The path and the type of the local `id` if it is an input port without a hardware leaf.
    fn empty_input(&self, id: DeclId) -> Option<(PathId, TyId)> {
        match self.store.slot(id) {
            Some(Slot {
                value: Val::Agg(a), ..
            }) => match &**a {
                Agg::Ref(Base::Name(path), ty) if self.tys.meta(*ty).leaves.is_zero() => {
                    Some((*path, *ty))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The type of the local `id` if it holds a reference as its root.
    fn ref_type(&self, id: DeclId) -> Option<TyId> {
        match self.store.slot(id) {
            Some(Slot {
                value: Val::Agg(a), ..
            }) => match &**a {
                Agg::Ref(_, ty) => Some(*ty),
                _ => None,
            },
            _ => None,
        }
    }

    /// Keeps the name of the domain `id`: the first read copies the text, and each later read
    /// copies none.
    fn keep_domain(&mut self, id: DeclId, x: &str) {
        self.domains.entry(id).or_insert_with(|| {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::TextBytes, x.len() as u64);
            x.to_string()
        });
    }

    fn name(&mut self, pos: Pos, node: NodeId, x: &str) -> Res<Out> {
        match self.target(node) {
            Some(Target::Prelude(k)) if k.is_type() => Ok(Out::Named(Val::Static(Value::Type(
                self.tys.mk(prim(pos, x, k)?),
            )))),
            Some(Target::Decl(id)) => match self.decl_ref(id).kind {
                Kind::Const => self.constant(pos, x, id),
                Kind::Alias if self.items.contains_key(&id) => self.constant(pos, x, id),
                Kind::Struct => {
                    let Some(&i) = self.items.get(&id) else {
                        return fail(Code::S010, pos, format!("`{x}` is not an item"));
                    };
                    let t = self.spec(pos, i, &[])?;
                    Ok(Out::Named(Val::Static(Value::Type(t))))
                }
                Kind::Enum => {
                    let Some(&i) = self.items.get(&id) else {
                        return fail(Code::S010, pos, format!("`{x}` is not an item"));
                    };
                    let t = self.enum_use(pos, i)?;
                    Ok(Out::Named(Val::Static(Value::Type(t))))
                }
                Kind::Fn if self.decl_ref(id).generic => fail(
                    Code::S010,
                    pos,
                    format!("`{x}` is generic; a generic function is not a value"),
                ),
                Kind::Fn => match self.items.get(&id) {
                    Some(&i) => self.fn_value(pos, i),
                    None => fail(Code::S010, pos, format!("`{x}` is not an item")),
                },
                Kind::Module => fail(Code::S010, pos, format!("`{x}` is not a value")),
                Kind::Family { .. } => family_value(pos, x),
                Kind::Domain => {
                    self.keep_domain(id, x);
                    Ok(Out::Named(Val::Handle(Handle::Domain(id))))
                }
                _ => {
                    let k = self.store.frame_index();
                    // An empty input port refers to its name. The read pays its zero, a new
                    // static value.
                    let empty = self.empty_input(id);
                    if let Some((path, ty)) = empty {
                        Ok(Out::Made(self.read_ref(pos, Base::Name(path), ty)?))
                    } else if self.store.slot(id).is_some() {
                        if let Some(t) = self.ref_type(id) {
                            self.bounded(pos, self.tys.zero_depth(t))?;
                        }
                        Ok(Out::Ref(Ref {
                            root: Root::Local(k, id),
                            path: Vec::new(),
                        }))
                    } else {
                        fail(Code::S011, pos, format!("`{x}` is not a static value"))
                    }
                }
            },
            Some(Target::Prelude(_)) => fail(
                Code::S010,
                pos,
                format!("`{x}` is a builtin; a builtin is not a value"),
            ),
            None => fail(Code::S010, pos, format!("`{x}` is not a value")),
        }
    }

    /// A constant or a `type` item. It evaluates at its first use, in the table of constants,
    /// one level deeper. A use while it is in progress is `S019`.
    fn constant(&mut self, pos: Pos, x: &str, id: DeclId) -> Res<Out> {
        let file = self.file;
        let Some(&i) = self.items.get(&id) else {
            return fail(Code::S010, pos, format!("`{x}` is not an item"));
        };
        let item = file.ast().get(i);
        if !matches!(item, Some(Item::Const { .. } | Item::Alias { .. })) {
            return fail(Code::S010, pos, format!("`{x}` is not a constant"));
        }
        match self.store.const_status(i) {
            ConstStatus::Done => return Ok(const_ref(i)),
            ConstStatus::InProgress => {
                return fail(
                    Code::S019,
                    pos,
                    format!("the constant `{x}` depends on itself"),
                );
            }
            ConstStatus::Fresh => {}
        }
        self.structural(|ev| {
            ev.nested(pos, |ev| {
                ev.store.begin_const(i);
                let c = ev.in_frame(None, |ev| match item {
                    Some(Item::Const {
                        pos: cp, ty, value, ..
                    }) => {
                        let t = ev.type_expr(ty)?;
                        let o = ev.eval(value)?;
                        let o = need(value, o)?;
                        ev.copy(*cp, &o)?;
                        ev.static_position(*cp, "a const", &o)?;
                        ev.static_handle(*cp, "a const", t)?;
                        let o = ev.settle(*cp, t, o)?;
                        Ok((ev.conform(*cp, t, o)?, t))
                    }
                    Some(Item::Alias { ty, .. }) => {
                        let t = ev.type_expr(ty)?;
                        Ok((Value::Type(t), ev.tys.mk(Ty::Type)))
                    }
                    _ => fail(Code::S010, pos, format!("`{x}` is not a constant")),
                })?;
                ev.store.finish_const(i, Val::Static(c.0), c.1);
                Ok(const_ref(i))
            })
        })
    }

    /// A block at `pos`. It charges as a statement. The statements of a module body run as
    /// module statements.
    fn block(&mut self, pos: Pos, ss: &[Stmt]) -> Res<Option<Val>> {
        self.charge(pos, 1)?;
        self.stmts(ss)
    }

    fn stmts(&mut self, ss: &[Stmt]) -> Res<Option<Val>> {
        for s in ss {
            if let Some(r) = self.stmt(s)? {
                return Ok(Some(r));
            }
        }
        Ok(None)
    }

    fn local(
        &mut self,
        pos: Pos,
        mutable: bool,
        name: &Ident,
        ty: Option<&TypeExpr>,
        value: &Expr,
    ) -> Res<Option<Val>> {
        let t = match ty {
            Some(ty) => Some(self.type_expr(ty)?),
            None => None,
        };
        let o = self.eval(value)?;
        let o = need(value, o)?;
        let x = if let Some(t) = t {
            self.typed_use(pos, t, o.is_ref(), o, Whole)?
        } else {
            self.copy(pos, &o)?;
            self.known(&o)?;
            self.store.take(o)
        };
        let id = self.decl(name)?;
        if t.is_none() {
            self.untyped.insert(id);
        }
        let x = self.named(pos, id, x)?;
        let ty = t.or_else(|| x.ty(&self.graph, &mut self.tys));
        self.bind(
            id,
            Slot {
                ty,
                mutable,
                value: x,
            },
        );
        Ok(None)
    }

    /// A statement. The result is the value of a `return`. A statement of a module body makes
    /// hardware, also in a function body (section 9.4).
    fn stmt(&mut self, s: &Stmt) -> Res<Option<Val>> {
        self.charge(stmt_pos(s), 1)?;
        match s {
            Stmt::Local {
                pos,
                mutable,
                name,
                ty,
                value,
            } => self.local(*pos, *mutable, name, ty.as_ref(), value),
            Stmt::Assign { pos, target, value } => self.assign(*pos, target, value),
            Stmt::Ret { pos, value } => {
                let Some(rt) = self.ret else {
                    return fail(Code::S006, *pos, "only a function has `return`".to_owned());
                };
                let Some(value) = value else {
                    return fail(
                        Code::S010,
                        *pos,
                        format!("`return` needs a value of {}", self.tys.text(rt)),
                    );
                };
                let o = self.eval(value)?;
                let o = need(value, o)?;
                let v = self.typed_use(*pos, rt, true, o, Whole)?;
                Ok(Some(v))
            }
            Stmt::CtIf { pos, cond, yes, no } => {
                let c = self.eval(cond)?;
                let c = need(cond, c)?;
                if self.test(*pos, self.store.seen(&c))? {
                    self.block(*pos, yes)
                } else {
                    match no {
                        Some(no) => self.block(*pos, no),
                        None => Ok(None),
                    }
                }
            }
            Stmt::CtFor {
                pos,
                var,
                lo,
                hi,
                body,
            } => self.ct_for(*pos, var, lo, hi, body),
            Stmt::Block { body, .. } => self.stmts(body),
            Stmt::Alias { name, ty, .. } => {
                let t = self.type_expr(ty)?;
                let id = self.decl(name)?;
                let kind = self.tys.mk(Ty::Type);
                self.bind(
                    id,
                    Slot {
                        ty: Some(kind),
                        mutable: false,
                        value: Val::Static(Value::Type(t)),
                    },
                );
                Ok(None)
            }
            Stmt::Expr { value, .. } => {
                if let Some(o) = self.eval(value)? {
                    self.known(&o)?;
                }
                Ok(None)
            }
            Stmt::Connect { pos, .. }
            | Stmt::Reg { pos, .. }
            | Stmt::Wire { pos, .. }
            | Stmt::Mem { pos, .. }
            | Stmt::Inst { pos, .. }
            | Stmt::Input { pos, .. }
            | Stmt::Output { pos, .. } => {
                self.hardware_checks(*pos, s)?;
                self.module_stmt(s)?;
                Ok(None)
            }
        }
    }

    /// A `comptime for`. It charges the sizes of both bounds for the range, then each loop
    /// value before it binds it in the loop frame `<var>$<value>`. The charge of the loop
    /// value `v` also pays the work of the next value `v + 1`.
    fn ct_for(
        &mut self,
        pos: Pos,
        var: &Ident,
        lo: &Expr,
        hi: &Expr,
        body: &[Stmt],
    ) -> Res<Option<Val>> {
        let first = self.eval(lo)?;
        let first = need(lo, first)?;
        self.bound(pos, &first)?;
        let at = self.store.park(first);
        let end = self.eval(hi)?;
        let end = need(hi, end)?;
        let first = self.store.resume_one(at);
        self.bound(pos, &end)?;
        let sizes = self.size(&first) + self.size(&end);
        self.charge(pos, sizes)?;
        let (first, end) = (self.store.take(first), self.store.take(end));
        let (Val::Static(Value::Int(from)), Val::Static(Value::Int(end))) = (&first, &end) else {
            return Ok(None);
        };
        let mut value = from.clone();
        let id = self.decl(var)?;
        let sym = self.sym(id);
        let one = Int::from_u64(1);
        let int = self.tys.mk(Ty::Int);
        while value < *end {
            self.charge(pos, u128::from(int_size(&value)))?;
            let (_, frame) = self.frame_of(sym, Step::Int(value.clone()));
            let item = self.item;
            let slot = Slot {
                ty: Some(int),
                mutable: false,
                value: Val::Static(Value::Int(value.clone())),
            };
            let r = self.in_item(item, frame, |ev| {
                ev.bind(id, slot);
                ev.block(pos, body)
            })?;
            if let Some(r) = r {
                return Ok(Some(r));
            }
            value = value.add(&one);
        }
        Ok(None)
    }
}
