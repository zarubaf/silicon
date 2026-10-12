// SPDX-License-Identifier: Apache-2.0
//! The evaluator of slice 1 and the static containers, types, and records of slice 2, with the
//! budgets and the cost model of section 5.4 of the front-end spec. Lean `Source.Eval` is its normative definition:
//! each charge here is a charge there, in the same order and at the same node. It reads the
//! checked AST. It recurses over the AST and the calls, so it runs on the front-end thread.
//!
//! A value is static, hardware, or a handle (section 5.1), or a literal with `[]` that waits for
//! the type of a typed use. The child module `hwops` makes the hardware nodes, the child module
//! `call` evaluates the calls, and the child modules `container` and `place` make and read the
//! static containers. The child module `string` scans and converts the strings, and the child
//! module `list` makes the lists and changes them in place. The child module `types` evaluates
//! the type expressions and the struct specializations, the child module `record` makes and
//! reads the records, and the child module `inst` runs the module statements and the
//! instantiations of Lean `Source.Elab`.
//!
//! A result that refers to an existing value, such as a local or a constant, stays a
//! reference until a copy pays for it. Thus a read that the cost model does not charge does
//! no work in the size of the value.

mod call;
mod container;
mod hwops;
mod inst;
mod list;
mod place;
mod record;
mod string;
mod types;

pub use inst::Design;
pub(crate) use inst::{Bind, Elab, Inst, Literal, PortDecl, Sink, elaborate};

use crate::hw::{Graph, Handle, HwId, Leaf, Op, Part, Ref, Root, Seen, Val};
use crate::int::Int;
use crate::names::{PathId, Paths, Step, Sym};
use crate::ops::{self, Fault, Fuel};
use crate::scan::{Numbers, Scan, Syms};
use crate::types::{Ty, TyId, Types};
use crate::value::{Evaluated, Value, int_size};
use crate::{Budget, Code, Error};
use parse::ast::{BinOp, Expr, Ident, Item, NodeId, Pos, Stmt, TypeExpr};
use parse::{NestedStack, StackError};
use resolve::{DeclId, Kind, Prelude, Resolved, ResolvedExpr, Target};
use std::cell::Cell;
use std::collections::BTreeMap;

/// The state of a constant in the table of constants.
enum Entry {
    NotStarted,
    InProgress,
    Done(Val),
}

/// A local of the current frame. A handle has no `Ty`, so its `ty` is `None`.
struct Slot {
    ty: Option<TyId>,
    mutable: bool,
    value: Val,
}

/// The result of an expression. Only `Made` is a new value. The others are references, so a
/// binding of them is a copy.
enum Out {
    Made(Val),
    /// A new value that the cost model treats as a reference: a type name, a domain, a child
    /// input, a child output, or an element of a new container.
    Named(Val),
    /// A local or a constant, or an element of one. A call evaluates its arguments in the
    /// caller frame and binds them in a new frame, so a reference names its frame.
    Ref(Ref),
}

impl Out {
    fn is_ref(&self) -> bool {
        !matches!(self, Out::Made(_))
    }

    /// The part of a literal that waits for its type. The result is static or waits.
    fn into_part(self) -> Part {
        match self {
            Out::Made(Val::Pending(_, part)) => part,
            Out::Made(Val::Static(v)) | Out::Named(Val::Static(v)) => Part::Value(Leaf::Owned(v)),
            Out::Ref(r) => Part::Value(Leaf::Ref(r)),
            Out::Made(_) | Out::Named(_) => Part::Value(Leaf::Owned(Value::Unit)),
        }
    }
}

/// An operand at a use that reads it: a hardware value, or a static result.
enum Opnd {
    Hw(HwId),
    Static(Out),
}

/// The value that a reference finds when its target is absent. The evaluator binds a local
/// before a use reads it and sets a constant done before a use refers to it, so no reference
/// finds it.
static ABSENT: Val = Val::Static(Value::Bool(false));
static ABSENT_VALUE: Value = Value::Bool(false);

type Frame = BTreeMap<DeclId, Slot>;

/// The values that a result can refer to: the table of constants by item index, and the
/// stack of frames. The last frame is the current frame. A frame holds only the bindings
/// that ran.
struct Store {
    consts: Vec<Entry>,
    frames: Vec<Frame>,
    /// The steps of the walks along paths into values: 1 for each container that a walk
    /// enters. A test counts them, so it checks the work of a walk and not its time.
    steps: Cell<u64>,
    /// The parameters of a frame that refer to an argument of the caller, by the number of
    /// the frame: a module argument refers until the instance statement pays its copy.
    links: BTreeMap<usize, BTreeMap<DeclId, Ref>>,
    /// The recursive size of the values that references copied, and the fuel budget of the
    /// run, for the test of copies before a charge.
    #[cfg(test)]
    copied: (Cell<u64>, u64),
    /// The counters of the work of the string and list operations, for the tests.
    #[cfg(test)]
    work: Work,
}

/// The work of the operations that scan, convert, or walk, counted for the tests: they check
/// the work and not the time. A test finds its counts by the fuel budget of its run, as it
/// finds its copies.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct Work {
    /// The scalars that the charged scans of strings visited.
    pub scanned: Cell<u64>,
    /// The digits that the conversions of `str` made.
    pub converted: Cell<u64>,
}

/// The counts of a run, as `Work` held them at its end.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counts {
    pub scanned: u64,
    pub converted: u64,
}

#[cfg(test)]
pub(crate) static COUNTS: std::sync::Mutex<BTreeMap<u64, Counts>> =
    std::sync::Mutex::new(BTreeMap::new());

/// The copies of each run of a test, by its fuel budget: a test finds its run by a fuel that
/// no other test uses, also when the tests share a process.
#[cfg(test)]
pub(crate) static COPIES: std::sync::Mutex<BTreeMap<u64, u64>> =
    std::sync::Mutex::new(BTreeMap::new());

#[cfg(test)]
impl Drop for Store {
    fn drop(&mut self) {
        if let Ok(mut copies) = COPIES.lock() {
            copies.insert(self.copied.1, self.copied.0.get());
        }
        if let Ok(mut counts) = COUNTS.lock() {
            counts.insert(
                self.copied.1,
                Counts {
                    scanned: self.work.scanned.get(),
                    converted: self.work.converted.get(),
                },
            );
        }
    }
}

/// The element of `v` at the numbers `path`, one for each container below it.
fn element<'a>(v: &'a Value, path: &[usize], steps: &Cell<u64>) -> &'a Value {
    steps.set(steps.get() + path.len() as u64);
    let mut cur = v;
    for &k in path {
        cur = match cur {
            Value::Array(_, xs) | Value::Tuple(xs) | Value::Record(_, xs) | Value::List(_, xs) => {
                xs.get(k).unwrap_or(&ABSENT_VALUE)
            }
            _ => &ABSENT_VALUE,
        };
    }
    cur
}

impl Store {
    /// The element `k` of the container that `cur` finds: one step of a walk along a path.
    fn step<'s>(&self, cur: Seen<'s>, k: usize) -> Seen<'s> {
        match cur {
            Seen::Static(v) => Seen::Static(element(v, &[k], &self.steps)),
            s => s,
        }
    }

    fn frame(&self) -> Option<&Frame> {
        self.frames.last()
    }

    /// The part of the live value of the local at `root` at the numbers `keys`, for a change in
    /// place: one walk down the path. A root that is not a static local has no part.
    fn part_mut(&mut self, root: Root, keys: &[usize]) -> Option<&mut Value> {
        let Root::Local(frame, id) = root else {
            return None;
        };
        self.steps.set(self.steps.get() + keys.len() as u64);
        let Val::Static(value) = &mut self.frames.get_mut(frame)?.get_mut(&id)?.value else {
            return None;
        };
        let mut cur = value;
        for &k in keys {
            cur = match cur {
                Value::Array(_, xs)
                | Value::Tuple(xs)
                | Value::Record(_, xs)
                | Value::List(_, xs) => xs.get_mut(k)?,
                _ => return None,
            };
        }
        Some(cur)
    }

    /// Links the parameter `id` of the frame `frame` to the argument `r` of the caller.
    fn link(&mut self, frame: usize, id: DeclId, r: Ref) {
        self.links.entry(frame).or_default().insert(id, r);
    }

    /// The argument that the parameter `id` of the frame `frame` links to.
    fn linked(&self, frame: usize, id: DeclId) -> Option<&Ref> {
        self.links.get(&frame).and_then(|ls| ls.get(&id))
    }

    /// Removes the links of the frame `frame`, in work for its own links only.
    fn unlink(&mut self, frame: usize) {
        self.links.remove(&frame);
    }

    fn frame_mut(&mut self) -> Option<&mut Frame> {
        self.frames.last_mut()
    }

    fn root(&self, root: &Root) -> &Val {
        match root {
            Root::Local(k, id) => self
                .frames
                .get(*k)
                .and_then(|f| f.get(id))
                .map_or(&ABSENT, |s| &s.value),
            Root::Const(i) => match self.consts.get(*i) {
                Some(Entry::Done(v)) => v,
                _ => &ABSENT,
            },
        }
    }

    /// What the local at `root` holds at the numbers `keys`.
    fn current(&self, root: Root, keys: &[usize]) -> Seen<'_> {
        match self.root(&root) {
            Val::Static(v) => Seen::Static(element(v, keys, &self.steps)),
            v => v.seen(),
        }
    }

    /// What a reference finds.
    fn at<'s>(&'s self, r: &Ref) -> Seen<'s> {
        let root = self.root(&r.root);
        match (root, r.path.is_empty()) {
            (_, true) => root.seen(),
            (Val::Static(v), false) => Seen::Static(element(v, &r.path, &self.steps)),
            _ => Seen::Static(&ABSENT_VALUE),
        }
    }

    /// The static value that a reference finds.
    fn value_at<'s>(&'s self, r: &Ref) -> &'s Value {
        match self.at(r) {
            Seen::Static(v) => v,
            _ => &ABSENT_VALUE,
        }
    }

    /// The static value of a leaf of a literal that waits.
    fn leaf<'s>(&'s self, leaf: &'s Leaf) -> &'s Value {
        match leaf {
            Leaf::Owned(v) => v,
            Leaf::Ref(r) => self.value_at(r),
        }
    }

    fn seen<'s>(&'s self, out: &'s Out) -> Seen<'s> {
        match out {
            Out::Made(v) | Out::Named(v) => v.seen(),
            Out::Ref(r) => self.at(r),
        }
    }

    /// The static value of a result that is static.
    fn value<'s>(&'s self, out: &'s Out) -> &'s Value {
        match self.seen(out) {
            Seen::Static(v) => v,
            _ => &ABSENT_VALUE,
        }
    }

    /// The value of a result as an owned value. A reference copies its value, so the caller
    /// paid for the copy before.
    fn take(&self, out: Out) -> Val {
        match out {
            Out::Made(v) | Out::Named(v) => v,
            Out::Ref(r) => match self.at(&r) {
                Seen::Static(v) => {
                    #[cfg(test)]
                    self.copied.0.set(self.copied.0.get() + v.size());
                    Val::Static(v.clone())
                }
                Seen::Hw(h) => Val::Hw(h),
                Seen::Handle(h) => Val::Handle(h.clone()),
                Seen::Pending(q, p) => Val::Pending(q, p.clone()),
            },
        }
    }
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

/// The key of a binding in a frame: the symbol of its source name, or the result role.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tag {
    Sym(Sym),
    Ret,
}

/// A named hardware binding: its core name, its value, and the position of the binding.
pub(crate) struct Let {
    pub path: PathId,
    pub value: HwId,
    pub pos: Pos,
}

/// The names of one instantiation. `frames` numbers each frame by its parent and its field
/// pair. `versions` counts the bindings of each tag in each frame. `lets` holds the named
/// bindings in evaluation order. Each table grows only with the bindings that run.
#[derive(Default)]
struct Naming {
    frames: BTreeMap<(usize, Sym, Step), usize>,
    versions: BTreeMap<(usize, Tag), u64>,
    lets: Vec<Let>,
}

struct Evaluator<'a> {
    file: &'a Resolved,
    top: Option<&'a ResolvedExpr>,
    names: Names,
    /// The index of each item by the declaration of its name.
    items: BTreeMap<DeclId, usize>,
    /// The value of each number literal, from the pass before the evaluation.
    numbers: Numbers,
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
    /// The nesting depth at the start of the innermost hardware arm (section 9.4).
    arm: Option<u64>,
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

pub(crate) fn expr_pos(e: &Expr) -> Pos {
    match e {
        Expr::Num { pos, .. }
        | Expr::Bool { pos, .. }
        | Expr::Str { pos, .. }
        | Expr::Name { pos, .. }
        | Expr::Unary { pos, .. }
        | Expr::Binary { pos, .. }
        | Expr::Cond { pos, .. }
        | Expr::Call { pos, .. }
        | Expr::Method { pos, .. }
        | Expr::Index { pos, .. }
        | Expr::Field { pos, .. }
        | Expr::Unit { pos }
        | Expr::Tuple { pos, .. }
        | Expr::Array { pos, .. }
        | Expr::Select { pos, .. }
        | Expr::ArrayType { pos, .. } => *pos,
    }
}

fn type_pos(t: &TypeExpr) -> Pos {
    match t {
        TypeExpr::Name { pos, .. }
        | TypeExpr::Index { pos, .. }
        | TypeExpr::Unit { pos }
        | TypeExpr::Tuple { pos, .. }
        | TypeExpr::Array { pos, .. } => *pos,
    }
}

fn stmt_pos(s: &Stmt) -> Pos {
    match s {
        Stmt::Local { pos, .. }
        | Stmt::Assign { pos, .. }
        | Stmt::Connect { pos, .. }
        | Stmt::Reg { pos, .. }
        | Stmt::Wire { pos, .. }
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
        let mut consts = Vec::new();
        for (i, item) in file.ast().iter().enumerate() {
            let name = item.name();
            if let Some(Target::Decl(id)) = file.target(name.id) {
                items.insert(id, i);
            }
            consts.push(Entry::NotStarted);
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
            syms: scan.syms,
            limit: budget.depth,
            depth: 0,
            stack: scan.stack,
            ret: None,
            fuel: Fuel::new(budget.fuel),
            tys: Types::default(),
            store: Store {
                consts,
                frames: vec![Frame::new()],
                steps: Cell::new(0),
                links: BTreeMap::new(),
                #[cfg(test)]
                copied: (Cell::new(0), budget.fuel),
                #[cfg(test)]
                work: Work::default(),
            },
            graph: Graph::default(),
            paths: Paths::default(),
            naming: Naming::default(),
            binding: Vec::new(),
            item: 0,
            frame: ROOT,
            elab,
            arm: None,
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
    let value = ev.static_value(expr_pos(e), out)?;
    let used = budget.fuel - ev.fuel.left();
    let evaluated = Evaluated {
        value,
        types: ev.tys,
        #[cfg(test)]
        steps: ev.store.steps.get(),
    };
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
            expr_pos(e),
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
        _ => fail(
            Code::S007,
            pos,
            format!("`{name}` takes 1 argument(s), but it has 0"),
        ),
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

    /// The declaration of a binder. Each binder is in the body of an item of the file.
    fn decl(&self, name: &Ident) -> Res<DeclId> {
        match self.file.target(name.id) {
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
        })
    }

    /// The size of a part that waits: 1 for `[]`, and 1 more than its parts for a literal.
    fn part_size(&self, p: &Part) -> u64 {
        match p {
            Part::Value(l) => self.store.leaf(l).size(),
            Part::Empty(_) => 1,
            Part::Array(_, ps) | Part::Tuple(_, ps) => {
                1 + ps.iter().map(|p| self.part_size(p)).sum::<u64>()
            }
        }
    }

    fn part_text(&self, p: &Part) -> String {
        match p {
            Part::Value(l) => self.store.leaf(l).text(&self.tys),
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

    /// A typed use of `out` at the type `t`. A literal that waits takes its type. It reads a
    /// handle. A hardware value needs the type `t`.
    fn conform_val(&mut self, pos: Pos, t: TyId, out: Out) -> Res<Val> {
        let out = self.settle(pos, t, out)?;
        match self.data(pos, out)? {
            Opnd::Static(o) => Ok(Val::Static(self.conform(pos, t, o)?)),
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

    /// The data of a result at a use that reads it. A register, a wire, and an own output
    /// give a reference to their name: the implicit read. A child input is never read
    /// (`S017`). An instance and a domain are not data.
    fn data(&mut self, pos: Pos, out: Out) -> Res<Opnd> {
        match self.store.seen(&out) {
            Seen::Static(_) => Ok(Opnd::Static(out)),
            Seen::Hw(h) => Ok(Opnd::Hw(h)),
            Seen::Pending(q, _) => no_type(q),
            Seen::Handle(Handle::Res { ty, path, .. }) => {
                let (ty, path) = (ty.clone(), *path);
                Ok(Opnd::Hw(self.graph.mk(pos, ty, Op::Ref(path), Vec::new())))
            }
            Seen::Handle(Handle::Input { .. }) => fail(
                Code::S017,
                pos,
                "an input of a child is a target; it is never read".to_owned(),
            ),
            s @ Seen::Handle(_) => fail(Code::S010, pos, format!("{} is not data", self.text(s))),
        }
    }

    /// The operand `e` of the node at `pos`, at a use that reads it.
    fn operand(&mut self, pos: Pos, e: &Expr) -> Res<Opnd> {
        let o = self.eval(e)?;
        let o = need(e, o)?;
        self.data(pos, o)
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
        if let Some(frame) = self.store.frame_mut() {
            frame.insert(id, slot);
        }
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
                format!("the nesting depth goes above {}", self.limit),
            );
        }
        self.depth += 1;
        let stack = self.stack;
        let r = stack
            .nest(self.depth, self, act)
            .unwrap_or_else(|e| Err(Stop::Stack(e)));
        self.depth -= 1;
        r
    }

    /// Runs `act` in the file scope with a new empty frame of locals and the return type
    /// `ret`. The frames below stay, so a reference into them still finds its value.
    fn in_frame<T>(&mut self, ret: Option<TyId>, act: impl FnOnce(&mut Self) -> Res<T>) -> Res<T> {
        self.store.frames.push(Frame::new());
        let saved_ret = std::mem::replace(&mut self.ret, ret);
        let names = std::mem::replace(&mut self.names, Names::File);
        let r = act(self);
        self.store.frames.pop();
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

    /// The core name `base` of the tag `key` in the current frame, or a version of it.
    fn version(&mut self, key: Tag, base: PathId) -> PathId {
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
        self.version(Tag::Sym(u), base)
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

    /// A binding of the local `id`. Only hardware gets a core name.
    fn named(&mut self, pos: Pos, id: DeclId, v: Val) -> Val {
        match v {
            Val::Hw(h) => {
                let path = self.fresh(id);
                self.bind_hw(pos, path, h)
            }
            v => v,
        }
    }

    /// The results of the arguments of a call, in order.
    fn args<'e>(&mut self, xs: impl IntoIterator<Item = &'e Expr>) -> Res<Vec<Out>> {
        let mut outs = Vec::new();
        for x in xs {
            let out = self.eval(x)?;
            outs.push(need(x, out)?);
        }
        Ok(outs)
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
        self.charge(expr_pos(e), 1)?;
        match e {
            Expr::Num { pos, id, .. } => self.number(*pos, *id),
            Expr::Bool { pos, value } => self.made(*pos, Value::Bool(*value)),
            Expr::Str { pos, value } => {
                // The size counts the characters, and the charge comes before the copy.
                let size = 1 + value.chars().count() as u128;
                self.charge(*pos, size)?;
                Ok(Some(Out::Made(Val::Static(Value::Str(value.clone())))))
            }
            Expr::Name { pos, id, name } => Ok(Some(self.name(*pos, *id, name)?)),
            Expr::Unary { pos, op, arg } => match self.operand(*pos, arg)? {
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
                let b = self.operand(*pos, rhs)?;
                match (a, b) {
                    (Opnd::Static(a), Opnd::Static(b)) => Ok(Some(Out::Made(Val::Static(
                        self.binary(*pos, *op, &a, &b)?,
                    )))),
                    (a, b) => Ok(Some(Out::Made(self.hw_binary(*pos, *op, a, b)?))),
                }
            }
            Expr::Cond { pos, cond, yes, no } => match self.operand(*pos, cond)? {
                Opnd::Hw(c) => {
                    let ty = self.graph.ty(c);
                    if ty != Ty::Bool {
                        return fail(
                            Code::S010,
                            *pos,
                            format!("a condition is a Bool, not {}", self.tys.text_of(&ty)),
                        );
                    }
                    let saved = self.arm.replace(self.depth);
                    let arms = self
                        .operand(*pos, yes)
                        .and_then(|a| Ok((a, self.operand(*pos, no)?)));
                    self.arm = saved;
                    let (a, b) = arms?;
                    Ok(Some(Out::Made(self.mux(*pos, c, a, b)?)))
                }
                Opnd::Static(c) => {
                    if self.test(*pos, self.store.seen(&c))? {
                        self.eval(yes)
                    } else {
                        self.eval(no)
                    }
                }
            },
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
        }
    }

    /// `&&` or `||`. A static left operand that decides gives its value. A static operand
    /// that does not decide gives the right operand, also a hardware one.
    fn select(&mut self, pos: Pos, op: BinOp, lhs: &Expr, rhs: &Expr) -> Res<Option<Out>> {
        match self.operand(pos, lhs)? {
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
        let Seen::Handle(Handle::Inst { id, path, inst }) = self.store.seen(&b) else {
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
                let h = self.graph.mk(pos, q.ty, Op::Out(path, q.sym), Vec::new());
                Ok(Out::Named(Val::Hw(h)))
            }
            None => fail(
                Code::S010,
                pos,
                format!("the instance has no port `{}`", field.name),
            ),
        }
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
    fn name(&mut self, pos: Pos, node: NodeId, x: &str) -> Res<Out> {
        match self.target(node) {
            Some(Target::Prelude(k)) if k.is_type() => Ok(Out::Named(Val::Static(Value::Type(
                self.tys.mk(prim(pos, x, k)?),
            )))),
            Some(Target::Decl(id)) => match self.file.decl(id).kind {
                Kind::Const => self.constant(pos, x, id),
                Kind::Alias if self.items.contains_key(&id) => self.constant(pos, x, id),
                Kind::Struct => {
                    let Some(&i) = self.items.get(&id) else {
                        return fail(Code::S010, pos, format!("`{x}` is not an item"));
                    };
                    let t = self.spec(pos, i, &[])?;
                    Ok(Out::Named(Val::Static(Value::Type(t))))
                }
                Kind::Fn | Kind::Module => fail(
                    Code::S010,
                    pos,
                    format!("`{x}` is a function; slice 1 has no function values"),
                ),
                Kind::Domain => Ok(Out::Named(Val::Handle(Handle::Domain))),
                _ => {
                    let k = self.store.frames.len().saturating_sub(1);
                    if self.store.frame().is_some_and(|f| f.contains_key(&id)) {
                        Ok(Out::Ref(Ref {
                            root: Root::Local(k, id),
                            path: Vec::new(),
                        }))
                    } else if let Some(r) = self.store.linked(k, id) {
                        Ok(Out::Ref(r.clone()))
                    } else {
                        fail(Code::S011, pos, format!("`{x}` is not a static value"))
                    }
                }
            },
            _ => fail(
                Code::S010,
                pos,
                format!("`{x}` is a function; slice 1 has no function values"),
            ),
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
        match self.store.consts.get(i) {
            Some(Entry::Done(_)) => return Ok(const_ref(i)),
            Some(Entry::InProgress) => {
                return fail(
                    Code::S019,
                    pos,
                    format!("the constant `{x}` depends on itself"),
                );
            }
            _ => {}
        }
        self.nested(pos, |ev| {
            ev.store.consts[i] = Entry::InProgress;
            let c = ev.in_frame(None, |ev| match item {
                Some(Item::Const {
                    pos: cp, ty, value, ..
                }) => {
                    let t = ev.type_expr(ty)?;
                    let o = ev.eval(value)?;
                    let o = need(value, o)?;
                    ev.copy(*cp, &o)?;
                    let o = ev.settle(*cp, t, o)?;
                    ev.conform(*cp, t, o)
                }
                Some(Item::Alias { ty, .. }) => Ok(Value::Type(ev.type_expr(ty)?)),
                _ => fail(Code::S010, pos, format!("`{x}` is not a constant")),
            })?;
            ev.store.consts[i] = Entry::Done(Val::Static(c));
            Ok(const_ref(i))
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
        self.copy(pos, &o)?;
        let x = if let Some(t) = t {
            self.conform_val(pos, t, o)?
        } else {
            self.known(&o)?;
            self.store.take(o)
        };
        let id = self.decl(name)?;
        let x = self.named(pos, id, x);
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
                self.charge(*pos, self.size(&o))?;
                let v = self.conform_val(*pos, rt, o)?;
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
        let end = self.eval(hi)?;
        let end = need(hi, end)?;
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
