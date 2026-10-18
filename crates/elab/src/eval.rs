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
//! reads the records, and the child module `inst` runs the module statements and the
//! instantiations of Lean `Source.Elab`. The child module `store` owns the locals, the frames,
//! the constants, the waiting results, and the change log. The evaluator calls its methods and
//! reads none of its fields.
//!
//! A result that refers to an existing value, such as a local or a constant, stays a
//! reference until a copy pays for it. Thus a read that the cost model does not charge does
//! no work in the size of the value.

mod agg;
mod arms;
mod call;
mod container;
mod hwops;
mod inst;
mod list;
mod matching;
mod mem;
mod observe;
mod pack;
mod place;
mod record;
mod store;
mod string;
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
pub(crate) use inst::{Bind, Elab, Inst, Literal, Mem, Sink, elaborate};
pub(crate) use mem::addr_width;
use store::{ConstStatus, Slot, Store};
use typed::{Binding, Passed};

use crate::agg::{Agg, Base};
use crate::hw::{Graph, Handle, HwId, Kind as Resource, Op, Part, Ref, Root, Seen, Val};
use crate::int::Int;
use crate::limit;
use crate::names::{PathId, Paths, Step, Sym};
use crate::ops::{self, Fault, Fuel};
use crate::scan::{CallArgs, Numbers, Scan, Syms};
use crate::types::{Ty, TyId, Types};
use crate::value::{Evaluated, Value, int_size};
use crate::{Budget, Code, Error};
use parse::ast::{BinOp, Expr, Ident, Item, NodeId, Pos, Stmt, TypeExpr};
use parse::{NestedStack, StackError};
use resolve::{DeclId, Kind, Prelude, Resolved, ResolvedExpr, Target};
use std::collections::BTreeMap;

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
    /// The innermost guard (section 9.4): its kind and the nesting depth at its start.
    guard: Option<Guard>,
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
    /// The name of each domain that a read named.
    domains: BTreeMap<DeclId, String>,
    /// The lengths of the types and the powers of ten that the records measured.
    lens: crate::serial::Cache,
}

/// The kind of a guard (section 9.4): a hardware arm or a structural context.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardKind {
    Arm,
    Structural,
}

/// The innermost guard: its kind and the nesting depth at its start. The texts of `S016` name
/// the kind and are normative, so they equal those of Lean `Guard`.
#[derive(Clone, Copy)]
pub(crate) struct Guard {
    pub(crate) kind: GuardKind,
    pub(crate) depth: u64,
}

impl Guard {
    /// The text of a mutation of the binding `x`.
    pub(crate) fn change(self, x: &str) -> String {
        match self.kind {
            GuardKind::Arm => "a hardware arm changes a binding from before the arm".to_owned(),
            GuardKind::Structural => format!(
                "a type or a constant cannot change `{x}`; change `{x}` before it, keep the result in a `let`, and use that name here"
            ),
        }
    }

    /// The text of the graph effect `g`.
    pub(crate) fn effect(self, g: &str) -> String {
        match self.kind {
            GuardKind::Arm => format!("a hardware arm has no graph effect such as `{g}`"),
            GuardKind::Structural => format!(
                "a type or a constant has no graph effect such as `{g}`; call it before and use the result"
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
        | TypeExpr::Fn { pos, .. } => *pos,
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
            crate::counters::start(budget.fuel);
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
            site: None,
            records: Vec::new(),
            emitted: Vec::new(),
            inst: None,
            calls: Vec::new(),
            domains: BTreeMap::new(),
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

/// A scalar type of the prelude without its index.
fn prim(pos: Pos, name: &str, k: Prelude) -> Res<Ty> {
    match k {
        Prelude::Bool => Ok(Ty::Bool),
        Prelude::Nat => Ok(Ty::Nat),
        Prelude::Int => Ok(Ty::Int),
        Prelude::Unit => Ok(Ty::Unit),
        Prelude::Type => Ok(Ty::Type),
        Prelude::String => Ok(Ty::String),
        k => {
            let (want, signature) = family_signature(k);
            fail(
                Code::S007,
                pos,
                format!("`{name}` takes {want} argument(s), but it has 0; write `{signature}`"),
            )
        }
    }
}

/// A handle type family for a message (Lean `familyText`): its name, its signature, an example
/// of a use, and its number of index arguments.
pub(crate) struct Family {
    pub name: &'static str,
    pub signature: &'static str,
    pub example: &'static str,
    pub args: usize,
}

/// The text of the handle type family `k`, or `None` for another name.
pub(crate) fn family_text(k: Prelude) -> Option<Family> {
    let (name, signature, example, args) = match k {
        Prelude::Reg => ("Reg", "Reg[T]", "Reg[UInt[8]]", 1),
        Prelude::Wire => ("Wire", "Wire[T]", "Wire[UInt[8]]", 1),
        Prelude::Input => ("Input", "Input[T]", "Input[UInt[8]]", 1),
        Prelude::Mem => ("Mem", "Mem[T, N]", "Mem[UInt[8], 16]", 2),
        Prelude::Instance => ("Instance", "Instance[M, args]", "Instance[Counter, 8]", 1),
        _ => return None,
    };
    Some(Family {
        name,
        signature,
        example,
        args,
    })
}

impl Family {
    /// The `S007` text of a use with `got` arguments, where `want` are right (Lean
    /// `familyArity`).
    pub(crate) fn arity(&self, want: usize, got: usize) -> String {
        format!(
            "`{}` takes {want} argument(s), but it has {got}; write `{}`",
            self.name, self.signature
        )
    }
}

/// The number of arguments of a type family and its signature, for the fix of its `S007`.
fn family_signature(k: Prelude) -> (usize, &'static str) {
    match (k, family_text(k)) {
        (_, Some(f)) => (f.args, f.signature),
        (Prelude::UInt, _) => (1, "UInt[W]"),
        (Prelude::SInt, _) => (1, "SInt[W]"),
        (Prelude::List, _) => (1, "List[T]"),
        _ => (1, ""),
    }
}

/// A handle has no `Ty`, so an assignment keeps its form.
fn same_form(a: Seen<'_>, b: Seen<'_>) -> bool {
    match (a, b) {
        (
            Seen::Handle(Handle::Res { kind, ty, .. }),
            Seen::Handle(Handle::Res {
                kind: k2, ty: t2, ..
            }),
        ) => kind == k2 && ty == t2,
        _ => false,
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

    fn part_text(&self, p: &Part) -> String {
        match p {
            Part::Value(a) => self.text(a.seen()),
            Part::Empty(_) => "`[]`".to_owned(),
            Part::Array(..) => "an array literal with `[]`".to_owned(),
            Part::Tuple(..) => "a tuple literal with `[]`".to_owned(),
        }
    }

    fn text(&self, s: Seen<'_>) -> String {
        match s {
            Seen::Pending(_, p) => format!("{} without a type", self.part_text(p)),
            s => s.text(&self.graph, &self.tys).unwrap_or_default(),
        }
    }

    /// The handle type of the handle `h` (section 5.1), built from the stored ids with no
    /// interning: `Reg[T]`, `Wire[T]`, `Input[T]`, `Mem[T, N]`, or the stored instance type. An
    /// own output and a domain have none.
    fn handle_form(&self, h: &Handle) -> Option<Ty> {
        match h {
            Handle::Res {
                kind: Resource::Reg,
                ty,
                ..
            } => Some(Ty::Reg(*ty)),
            Handle::Res {
                kind: Resource::Wire,
                ty,
                ..
            } => Some(Ty::Wire(*ty)),
            Handle::Res {
                kind: Resource::Output,
                ..
            }
            | Handle::Domain(_) => None,
            Handle::Mem(id) => {
                let m = self.mem(*id)?;
                Some(Ty::Mem(m.word, Int::from_u64(m.depth)))
            }
            Handle::Inst { ty, .. } => Some(self.tys.get(*ty).clone()),
            Handle::Input { port, .. } => Some(Ty::Input(port.ty)),
        }
    }

    /// The value `{a}` of a message (section 6.2, Lean `Val.about`). A handle names its handle
    /// type, an own output its source name, and a domain its name. A literal that waits is `[]`.
    /// Another value names its type, so the text reads no value in full and each type text is
    /// bounded.
    fn about(&self, s: Seen<'_>) -> String {
        match s {
            Seen::Handle(Handle::Res {
                kind: Resource::Output,
                path,
                ..
            }) => format!(
                "the output `{}`",
                self.paths.source(*path, &self.syms.texts)
            ),
            Seen::Handle(Handle::Domain(d)) => format!("the domain `{}`", self.domain_name(*d)),
            Seen::Handle(h) => match self.handle_form(h) {
                Some(t) => format!("a handle of `{}`", self.tys.text_of(&t)),
                None => self.text(s),
            },
            Seen::Pending(..) => "`[]`".to_owned(),
            Seen::Static(v) => format!("a value of `{}`", v.type_text(&self.tys)),
            Seen::Hw(h) => format!("a value of `{}`", self.tys.text_of(&self.graph.ty(h))),
            Seen::Agg(a) => match a.stored_ty() {
                Some(t) => format!("a value of `{}`", self.tys.text(t)),
                None => self.text(s),
            },
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

    /// What the operand is, for a message: a hardware aggregate prints as `hardware T`.
    fn opnd_text(&self, o: &Opnd) -> String {
        match o {
            Opnd::Hw(h) => format!("hardware {}", self.tys.text_of(&self.graph.ty(*h))),
            Opnd::Static(out) => self.text(self.store.seen(out)),
        }
    }

    /// The type of the operand, for a message: a hardware aggregate names its type, and a
    /// static value is what it is.
    fn type_text(&self, o: &Opnd) -> String {
        match o {
            Opnd::Static(out) => match self.store.seen(out) {
                Seen::Agg(a) => a.stored_ty().map(|t| self.tys.text(t)).unwrap_or_default(),
                seen => self.text(seen),
            },
            Opnd::Hw(h) => self.tys.text_of(&self.graph.ty(*h)),
        }
    }

    /// Whether the operand is a hardware aggregate.
    fn opnd_is_agg(&self, o: &Opnd) -> bool {
        matches!(o, Opnd::Static(out) if self.is_agg(out))
    }

    /// Whether the result is a handle: a local, or a leaf of a container of handles. The type of
    /// the root tells if a path can end at a handle, so a reference into a root without the
    /// handle flag walks no path.
    fn is_handle(&self, out: &Out) -> bool {
        match out {
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => matches!(v, Val::Handle(_)),
            Out::Ref(r) => match self.store.root(&r.root) {
                Val::Handle(_) => r.path.is_empty(),
                Val::Agg(a)
                    if !r.path.is_empty() && a.stored_ty().is_some_and(TyId::holds_handles) =>
                {
                    matches!(self.store.at(r), Seen::Handle(_))
                }
                _ => false,
            },
        }
    }

    /// A binding copies a reference.
    fn copy(&mut self, pos: Pos, out: &Out) -> Res<()> {
        if out.is_ref() {
            self.charge(pos, self.size(out))?;
        }
        Ok(())
    }

    /// The check of a static position, before the value is taken. A literal that waits for
    /// its type is `S010` at its first `[]`.
    fn check_static(&self, pos: Pos, out: &Out) -> Res<()> {
        match self.store.seen(out) {
            Seen::Static(_) => Ok(()),
            Seen::Pending(q, _) => no_type(q),
            s => fail(
                Code::S011,
                pos,
                format!(
                    "a static position needs a static value, not {}",
                    self.text(s)
                ),
            ),
        }
    }

    /// The value of a static position at the node `pos`. Another value there is `S011`.
    fn static_value(&self, pos: Pos, out: Out) -> Res<Value> {
        self.check_static(pos, &out)?;
        match self.store.take(out) {
            Val::Static(v) => Ok(v),
            _ => fail(
                Code::S011,
                pos,
                "a static position needs a static value".to_owned(),
            ),
        }
    }

    /// A typed use of a static result at the type `t`. Another value is `S011`.
    fn conform(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Value> {
        self.check_static(pos, &out)?;
        let converted =
            ops::convert(t, self.store.value(&out), &mut self.fuel, &self.tys).map_err(at(pos))?;
        match converted {
            Some(v) => Ok(v),
            None => self.static_value(pos, out),
        }
    }

    /// The typed use of the data `d` at the type `t`.
    fn conform_data(&mut self, pos: Pos, t: TyId, d: Opnd) -> Res<Val> {
        match d {
            Opnd::Static(o) if self.is_handle(&o) => self.handle_wrong(pos, t, self.store.seen(&o)),
            Opnd::Static(o) if self.is_agg(&o) => Ok(self.typed_agg(pos, t, o)?.into_val()),
            Opnd::Static(o) => {
                let v = self.conform(pos, t, o)?;
                Ok(Agg::typed(&mut self.tys, t, v).into_val())
            }
            Opnd::Hw(h) => {
                let ty = self.graph.ty(h);
                if ty == *self.tys.get(t) {
                    Ok(Val::Hw(h))
                } else {
                    fail(
                        Code::S010,
                        pos,
                        format!(
                            "expected {}, but the value is {}",
                            self.tys.text(t),
                            self.tys.text_of(&ty)
                        ),
                    )
                }
            }
        }
    }

    /// `S010` at `pos` when `t` is a handle type at a typed use other than a typed `let` and an
    /// assignment to a `let mut` local. There, a handle type is `S010` until #278 (section 5.4),
    /// with the text of section 6.2. A static position has `static_handle` instead. The caller
    /// charged the copy first.
    pub(super) fn later_handle(&self, pos: Pos, t: TyId) -> Res<()> {
        if self.tys.get(t).is_handle() {
            return fail(
                Code::S010,
                pos,
                format!(
                    "the handle type `{}` is not supported here yet; use it in a typed `let`, or \
                     pass the data value, for example `read(h)`",
                    self.tys.text(t)
                ),
            );
        }
        Ok(())
    }

    /// The typed use at `pos` of `out` at the handle type `t` (section 5.4, Lean `handleUse`).
    /// The handle type of the value equals `t`, else `S010`. The compare is an id compare, it has
    /// no charge, and nothing reads the value. An own output has no handle type, so its text
    /// names the fix: use it as data.
    fn handle_use(&mut self, pos: Pos, t: TyId, out: &Out) -> Res<Val> {
        Ok(Val::Handle(self.handle_leaf(pos, t, out)?))
    }

    /// The handle of `out` at the handle type `t`: the same check as `handle_use`, for a caller
    /// that stores the handle as a leaf of a container.
    pub(super) fn handle_leaf(&mut self, pos: Pos, t: TyId, out: &Out) -> Res<Handle> {
        if let Seen::Handle(h) = self.store.seen(out) {
            let h = h.clone();
            if self.handle_ty(&h) == Some(t) {
                return Ok(h);
            }
        }
        self.handle_wrong(pos, t, self.store.seen(out))
    }

    /// The error at `pos` of a typed use of `v` at the type `t` with the handle flag (Lean
    /// `handleWrong`): `S010` with the text of `handle_use_text`. An own output has no handle
    /// type, so its text names the fix: use it as data.
    fn handle_wrong<T>(&self, pos: Pos, t: TyId, v: Seen<'_>) -> Res<T> {
        if let Seen::Handle(Handle::Res {
            kind: Resource::Output,
            path,
            ..
        }) = v
        {
            let r = self.paths.source(*path, &self.syms.texts);
            return fail(
                Code::S010,
                pos,
                format!(
                    "`{r}` is an output, and an output has no handle type; use `{r}` directly as data"
                ),
            );
        }
        fail(Code::S010, pos, self.handle_use_text(t, &self.about(v)))
    }

    /// The text of a wrong value or leaf `a` at the type `t` with the handle flag (section 6.2,
    /// Lean `handleUseText`). A handle type gives "Typed use at a handle type". Another type, such
    /// as `[Reg[UInt[8]]; 1]`, gives "Typed use at a container of handles".
    pub(super) fn handle_use_text(&self, t: TyId, a: &str) -> String {
        let ty = self.tys.text(t);
        if self.tys.get(t).is_handle() {
            format!(
                "expected `{ty}`, but the value is {a}; a handle type takes only a handle of \
                 exactly this type, so give such a handle or change the type"
            )
        } else {
            format!(
                "expected `{ty}`, but the value is {a}; a value of `{ty}` takes only handles of \
                 exactly its handle types, so give such a value or change the type"
            )
        }
    }

    /// The text "Handle at a data leaf" of section 6.2 (Lean `dataLeafText`): it names the data
    /// type `t` of the position in a container and the handle leaf `a` at it.
    pub(super) fn data_leaf_text(&self, t: TyId, a: &str) -> String {
        format!(
            "expected `{}`, but the value is {a}; a literal element keeps its handle, so read it in \
             the literal, for example `(r, read(r))`",
            self.tys.text(t)
        )
    }

    /// The handle type of `h` as an id (Lean `Handle.ty?`). It reads the stored ids and charges
    /// nothing.
    fn handle_ty(&mut self, h: &Handle) -> Option<TyId> {
        let form = self.handle_form(h)?;
        Some(match h {
            Handle::Inst { ty, .. } => *ty,
            _ => self.tys.mk(form),
        })
    }

    /// The typed use of `out` at `t` after its copy charged. A read of a handle that gives an
    /// aggregate charges the size of the reference when `copies`.
    fn read_use(&mut self, pos: Pos, t: TyId, copies: bool, out: Out) -> Res<Val> {
        let out = self.settle(pos, t, out)?;
        let handle = self.is_handle(&out);
        let d = self.data_at(pos, t, out)?;
        if copies
            && handle
            && let Opnd::Static(o) = &d
            && self.is_agg(o)
        {
            self.charge(pos, self.size(o))?;
        }
        self.conform_data(pos, t, d)
    }

    /// The data of a result at a typed use at the type `t` (Lean `dataAt`). A position of a type
    /// with the handle flag is `raw` (section 9.2), so it reads nothing: a handle and a container
    /// keep their handles. A position of another type reads each handle (`data`).
    pub(super) fn data_at(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Opnd> {
        if t.holds_handles() {
            Ok(Opnd::of_out(out))
        } else {
            self.data(pos, out)
        }
    }

    /// The data of a result at a use that reads it. A register, a wire, and an own output
    /// give a reference to their name in its normal form: the implicit read. Thus a scalar is
    /// hardware, and an aggregate is a lazy reference with no charge. A child input is never read
    /// (`S017`). An instance and a domain are not data.
    fn data(&mut self, pos: Pos, out: Out) -> Res<Opnd> {
        match self.store.seen(&out) {
            Seen::Static(_) | Seen::Agg(_) => Ok(Opnd::Static(out)),
            Seen::Hw(h) => Ok(Opnd::Hw(h)),
            Seen::Pending(q, _) => no_type(q),
            Seen::Handle(Handle::Res { ty, path, .. }) => {
                let (t, path) = (*ty, *path);
                match self.read_ref(pos, Base::Name(path), t)? {
                    Val::Hw(h) => Ok(Opnd::Hw(h)),
                    v => Ok(Opnd::Static(Out::Made(v))),
                }
            }
            Seen::Handle(Handle::Input { .. }) => fail(
                Code::S017,
                pos,
                "an input of a child is a target; it is never read".to_owned(),
            ),
            s @ Seen::Handle(_) => fail(Code::S010, pos, format!("{} is not data", self.text(s))),
        }
    }

    /// `read` at the call `pos` with the results `vs` of its arguments, after its node, its name,
    /// and the copies (section 5.4, Lean `readOf`). `g` is the name of the callee. A child input
    /// is `S017`. An own output, a memory, an instance, a domain, and a value that is not a
    /// handle are `S010`, each with its fix (section 6.2). A register or a wire reads by the
    /// rule of references (`read_ref`), after its depth check. The read gives a hardware name, a
    /// lazy reference with no charge, or a new static value that charged its zero size. The
    /// result refers to the resource, so a binding of it is a copy, and the binding pays for the
    /// leaves before they expand. A new static value is no copy, so its zero size charges once.
    fn read_call(&mut self, pos: Pos, g: &str, vs: &[Out]) -> Res<Option<Out>> {
        let [v] = vs else {
            return fail(
                Code::S007,
                pos,
                format!(
                    "`{g}` takes 1 argument(s), but it has {}; write `read(h)` with one register \
                     or wire",
                    vs.len()
                ),
            );
        };
        match self.store.seen(v) {
            Seen::Handle(Handle::Res {
                kind: Resource::Reg | Resource::Wire,
                ty,
                path,
                ..
            }) => {
                let (t, path) = (*ty, *path);
                let r = self.read_ref(pos, Base::Name(path), t)?;
                Ok(Some(if matches!(r, Val::Static(_)) {
                    Out::Made(r)
                } else {
                    Out::Named(r)
                }))
            }
            Seen::Handle(Handle::Input { path, port, .. }) => {
                let port_name = self.syms.texts.get(port.sym).map_or("", String::as_str);
                fail(
                    Code::S017,
                    pos,
                    format!(
                        "the input `{port_name}` of `{}` is a target only; read the value that \
                         you bind to it",
                        self.paths.source(*path, &self.syms.texts)
                    ),
                )
            }
            s => {
                let hint = match s {
                    Seen::Handle(Handle::Mem(_)) => "read a word with `read_port`",
                    Seen::Handle(Handle::Inst { .. }) => {
                        "read an output of the instance, for example `u.q`"
                    }
                    Seen::Handle(Handle::Domain(_)) => {
                        "a domain has no value, so remove the `read`"
                    }
                    _ => "use the value directly, without `read`",
                };
                fail(
                    Code::S010,
                    pos,
                    format!(
                        "`{g}` takes a register or a wire, not {}; {hint}",
                        self.about(s)
                    ),
                )
            }
        }
    }

    /// The operand `e` of the node at `pos`, at a use that reads it.
    fn operand(&mut self, pos: Pos, e: &Expr) -> Res<Opnd> {
        let o = self.eval(e)?;
        let o = need(e, o)?;
        self.data(pos, o)
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
        let fuel = crate::counters::current();
        let act = move |ev: &mut Self| {
            // A level that starts a thread counts into the run of its parent.
            #[cfg(test)]
            if let Some(fuel) = fuel {
                crate::counters::join(fuel);
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
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Guarded, 1);
        let saved = self.guard.replace(Guard {
            kind: GuardKind::Structural,
            depth: self.depth,
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

    fn eval(&mut self, e: &Expr) -> Res<Option<Out>> {
        self.charge(e.pos(), 1)?;
        match e {
            Expr::Num { pos, id, .. } => self.number(*pos, *id),
            Expr::Bool { pos, value } => self.made(*pos, Value::Bool(*value)),
            Expr::Str { pos, value } => {
                limit::string(value.len() as u128).map_err(at(*pos))?;
                // The size counts the characters, and the charge comes before the copy.
                let size = 1 + value.chars().count() as u128;
                self.charge(*pos, size)?;
                Ok(Some(Out::Made(Val::Static(Value::Str(value.clone())))))
            }
            Expr::Name { pos, id, name } => Ok(Some(self.name(*pos, *id, name)?)),
            Expr::Match { pos, scrut, arms } => self.match_expr(*pos, scrut, arms),
            Expr::Unary { pos, op, arg } => match self.operand(*pos, arg)? {
                Opnd::Static(a) if self.is_agg(&a) => fail(
                    Code::S010,
                    *pos,
                    format!(
                        "`{}` does not accept {}",
                        ops::unop_text(*op),
                        self.text(self.store.seen(&a))
                    ),
                ),
                Opnd::Static(a) => {
                    let v = ops::unary(*op, self.store.value(&a), &mut self.fuel, &self.tys)
                        .map_err(at(*pos))?;
                    Ok(Some(Out::Made(Val::Static(v))))
                }
                Opnd::Hw(a) => Ok(Some(Out::Made(self.hw_unary(*pos, *op, a)?))),
            },
            Expr::Binary {
                pos,
                op: op @ (BinOp::Land | BinOp::Lor),
                lhs,
                rhs,
            } => self.select(*pos, *op, lhs, rhs),
            Expr::Binary { pos, op, lhs, rhs } => {
                let a = self.operand(*pos, lhs)?;
                let (a, b) = self.operand_after(*pos, a, rhs)?;
                self.comparable(*pos, *op, &a, &b)?;
                if matches!(op, BinOp::Eq | BinOp::Ne)
                    && (self.opnd_is_agg(&a) || self.opnd_is_agg(&b))
                {
                    return Ok(Some(Out::Made(self.agg_eq(*pos, *op, &a, &b)?)));
                }
                match (a, b) {
                    (Opnd::Static(a), Opnd::Static(b)) if !self.is_agg(&a) && !self.is_agg(&b) => {
                        Ok(Some(Out::Made(Val::Static(
                            self.binary(*pos, *op, &a, &b)?,
                        ))))
                    }
                    (a, b) => Ok(Some(Out::Made(self.hw_binary(*pos, *op, a, b)?))),
                }
            }
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
            Expr::Index { pos, base, args } => {
                if let Expr::Name { pos: bp, id, .. } = &**base
                    && let Some(Target::Prelude(k)) = self.target(*id)
                    && k.is_type()
                {
                    self.charge(*bp, 1)?;
                    let t = self.index(*pos, k, args)?;
                    return Ok(Some(Out::Made(Val::Static(Value::Type(t)))));
                }
                if let Expr::Name { pos: bp, id, .. } = &**base
                    && let Some(i) = self.struct_item(*id)
                {
                    self.charge(*bp, 1)?;
                    let t = self.spec(*pos, i, args)?;
                    return Ok(Some(Out::Made(Val::Static(Value::Type(t)))));
                }
                self.read(e)
            }
            Expr::Unit { .. } | Expr::Tuple { .. } | Expr::Array { .. } => self.container(e),
            Expr::Select { .. } | Expr::Field { .. } => self.read(e),
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
    fn field(&mut self, pos: Pos, b: Out, field: &Ident) -> Res<Out> {
        let b = match self.store.seen(&b) {
            Seen::Handle(Handle::Inst { .. }) => return self.port_of(pos, b, field),
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

    /// A port of an instance: a child input is a target, and a child output refers to its
    /// name. An output without a hardware leaf is a new static value.
    fn port_of(&mut self, pos: Pos, b: Out, field: &Ident) -> Res<Out> {
        let Seen::Handle(Handle::Inst { id, path, inst, .. }) = self.store.seen(&b) else {
            return self.record_field(pos, b, field);
        };
        let (id, path, inst) = (*id, *path, *inst);
        let port = match self.names {
            Names::Top => None,
            Names::File => self.syms.fields.get(&field.id).copied(),
        }
        .and_then(|s| self.elab.port(inst, s));
        match port {
            Some(q) if q.input => Ok(Out::Named(Val::Handle(Handle::Input {
                inst: id,
                path,
                port: q,
            }))),
            Some(q) => {
                let name = self.paths.child(None, q.sym);
                let v = self.read_ref(pos, Base::Out(path, name), q.ty)?;
                Ok(if matches!(v, Val::Static(_)) {
                    Out::Made(v)
                } else {
                    Out::Named(v)
                })
            }
            None => fail(
                Code::S010,
                pos,
                format!("the instance has no port `{}`", field.name),
            ),
        }
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
    fn block(&mut self, pos: Pos, ss: &[Stmt], module: bool) -> Res<Option<Val>> {
        self.charge(pos, 1)?;
        self.stmts(ss, module)
    }

    fn stmts(&mut self, ss: &[Stmt], module: bool) -> Res<Option<Val>> {
        for s in ss {
            if let Some(r) = self.stmt(s, module)? {
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
            self.typed_use(pos, t, o.is_ref(), o, Binding)?
        } else {
            self.copy(pos, &o)?;
            self.known(&o)?;
            self.store.take(o)
        };
        let id = self.decl(name)?;
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
    /// hardware; elsewhere such a statement is `S011`.
    fn stmt(&mut self, s: &Stmt, module: bool) -> Res<Option<Val>> {
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
                let v = self.typed_use(*pos, rt, true, o, Passed)?;
                // A module body runs on after a `return`, as the walk of Lean `Elab` does.
                Ok((!module).then_some(v))
            }
            Stmt::CtIf { pos, cond, yes, no } => {
                let c = self.eval(cond)?;
                let c = need(cond, c)?;
                if self.test(*pos, self.store.seen(&c))? {
                    self.block(*pos, yes, module)
                } else {
                    match no {
                        Some(no) => self.block(*pos, no, module),
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
            } => self.ct_for(*pos, var, lo, hi, body, module),
            Stmt::Block { body, .. } => self.stmts(body, module),
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
            | Stmt::Input { pos, .. }
            | Stmt::Output { pos, .. }
            | Stmt::Inst { pos, .. }
                if !module =>
            {
                fail(
                    Code::S011,
                    *pos,
                    "a static evaluation makes no hardware".to_owned(),
                )
            }
            _ => {
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
        module: bool,
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
                ev.block(pos, body, module)
            })?;
            if let Some(r) = r {
                return Ok(Some(r));
            }
            value = value.add(&one);
        }
        Ok(None)
    }
}
