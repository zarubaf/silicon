// SPDX-License-Identifier: Apache-2.0
//! The evaluator of slice 1 and the static containers of slice 2, with the budgets and the cost
//! model of section 5.4 of the front-end spec. Lean `Source.Eval` is its normative definition:
//! each charge here is a charge there, in the same order and at the same node. It reads the
//! checked AST. It recurses over the AST and the calls, so it runs on the front-end thread.
//!
//! A value is static, hardware, or a handle (section 5.1), or a literal with `[]` that waits for
//! the type of a typed use. The child module `hwops` makes the hardware nodes, the child modules
//! `container` and `place` make and read the static containers, and the child module `inst`
//! runs the module statements and the instantiations of Lean `Source.Elab`.
//!
//! A result that refers to an existing value, such as a local or a constant, stays a
//! reference until a copy pays for it. Thus a read that the cost model does not charge does
//! no work in the size of the value.

mod container;
mod hwops;
mod inst;
mod place;
mod types;

pub use inst::Design;
pub(crate) use inst::{Bind, Elab, Inst, Literal, PortDecl, Sink, elaborate};

use crate::hw::{Graph, Handle, HwId, Leaf, Op, Part, Ref, Root, Seen, Val};
use crate::int::Int;
use crate::names::{PathId, Paths, Role, Step, Sym};
use crate::ops::{self, Fault, Fuel, str_text};
use crate::scan::{Numbers, Scan, Syms};
use crate::types::{Ty, TyId, Types};
use crate::value::{Evaluated, Value, int_size};
use crate::{Budget, Code, Error};
use parse::ast::{BinOp, Expr, Ident, Item, NodeId, Param, Pos, Stmt, TypeExpr};
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

/// A local of the current frame. A string, a type, and a handle have no `Ty`, so their `ty`
/// is `None`.
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
    links: BTreeMap<(usize, DeclId), Ref>,
    /// The recursive size of the values that references copied, and the fuel budget of the
    /// run, for the test of copies before a charge.
    #[cfg(test)]
    copied: (Cell<u64>, u64),
}

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
    }
}

/// The element of `v` at the numbers `path`, one for each container below it.
fn element<'a>(v: &'a Value, path: &[usize], steps: &Cell<u64>) -> &'a Value {
    steps.set(steps.get() + path.len() as u64);
    let mut cur = v;
    for &k in path {
        cur = match cur {
            Value::Array(_, xs) | Value::Tuple(xs) => xs.get(k).unwrap_or(&ABSENT_VALUE),
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
    /// The item whose body runs, for its call sites.
    item: usize,
    frame: FrameRef,
    elab: Elab,
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
            },
            graph: Graph::default(),
            paths: Paths::default(),
            naming: Naming::default(),
            item: 0,
            frame: ROOT,
            elab,
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
        _ => fail(
            Code::S007,
            pos,
            format!("`{name}` takes 1 argument(s), but it has 0"),
        ),
    }
}

/// A string, a type, and a handle have no `Ty`, so an assignment keeps their form.
fn same_form(a: Seen<'_>, b: Seen<'_>) -> bool {
    match (a, b) {
        (Seen::Static(Value::Str(_)), Seen::Static(Value::Str(_)))
        | (Seen::Static(Value::Type(_)), Seen::Static(Value::Type(_))) => true,
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
        u128::from(match self.store.seen(out) {
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
    fn args(&mut self, xs: &[Expr]) -> Res<Vec<Out>> {
        let mut outs = Vec::with_capacity(xs.len());
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
                    let a = self.operand(*pos, yes)?;
                    let b = self.operand(*pos, no)?;
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
            Expr::Index { pos, base, args } => {
                if let Expr::Name { pos: bp, id, .. } = &**base
                    && let Some(Target::Prelude(k)) = self.target(*id)
                    && k.is_type()
                {
                    self.charge(*bp, 1)?;
                    let t = self.index(*pos, k, args)?;
                    return Ok(Some(Out::Made(Val::Static(Value::Type(t)))));
                }
                self.read(e)
            }
            Expr::Field { pos, base, field } => {
                let b = self.eval(base)?;
                let b = need(base, b)?;
                self.field(*pos, &b, field)
            }
            Expr::Unit { .. } | Expr::Tuple { .. } | Expr::Array { .. } => self.container(e),
            Expr::Select { .. } => self.read(e),
            // TODO(#178): elaborate the array type `[T; N]` (plan step 17).
            Expr::ArrayType { pos, .. } => fail(
                Code::S010,
                *pos,
                "the array type `[T; N]` is not elaborated yet".to_owned(),
            ),
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

    /// A port of an instance: a child input is a target, and a child output is hardware.
    fn field(&mut self, pos: Pos, b: &Out, field: &Ident) -> Res<Option<Out>> {
        let Seen::Handle(Handle::Inst { id, path, inst }) = self.store.seen(b) else {
            return fail(
                Code::S010,
                pos,
                format!(
                    "{} has no field `{}`",
                    self.text(self.store.seen(b)),
                    field.name
                ),
            );
        };
        let (id, path, inst) = (*id, *path, *inst);
        let port = match self.names {
            Names::Top => None,
            Names::File => self.syms.fields.get(&field.id).copied(),
        }
        .and_then(|s| self.elab.port(inst, s));
        match port {
            Some(q) if q.input => Ok(Some(Out::Named(Val::Handle(Handle::Input {
                inst: id,
                path,
                port: q,
            })))),
            Some(q) => {
                let h = self.graph.mk(pos, q.ty, Op::Out(path, q.sym), Vec::new());
                Ok(Some(Out::Named(Val::Hw(h))))
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
                    } else if let Some(r) = self.store.links.get(&(k, id)) {
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

    fn constant(&mut self, pos: Pos, x: &str, id: DeclId) -> Res<Out> {
        let file = self.file;
        let Some(&i) = self.items.get(&id) else {
            return fail(Code::S010, pos, format!("`{x}` is not an item"));
        };
        let Some(Item::Const {
            pos: cp, ty, value, ..
        }) = file.ast().get(i)
        else {
            return fail(Code::S010, pos, format!("`{x}` is not a constant"));
        };
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
            let c = ev.in_frame(None, |ev| {
                let t = ev.type_expr(ty)?;
                let o = ev.eval(value)?;
                let o = need(value, o)?;
                ev.copy(*cp, &o)?;
                let o = ev.settle(*cp, t, o)?;
                ev.conform(*cp, t, o)
            })?;
            ev.store.consts[i] = Entry::Done(Val::Static(c));
            Ok(const_ref(i))
        })
    }

    /// A call of a function item, a prelude function, or a type.
    fn call(&mut self, pos: Pos, node: NodeId, f: &Expr, xs: &[Expr]) -> Res<Option<Out>> {
        if let Expr::Name {
            pos: fp,
            id: fid,
            name: g,
        } = f
        {
            match self.target(*fid) {
                Some(Target::Decl(id))
                    if matches!(
                        self.file.decl(id).kind,
                        Kind::Const | Kind::Fn | Kind::Module
                    ) =>
                {
                    return self.call_fn(pos, node, *fp, g, id, xs);
                }
                Some(Target::Prelude(h)) if !h.is_type() => {
                    return self.call_prelude(pos, *fp, g, h, xs);
                }
                _ => {}
            }
        }
        let t = self.eval(f)?;
        let t = need(f, t)?;
        match (self.store.seen(&t), xs) {
            (Seen::Static(Value::Type(t)), [x]) => {
                let t = *t;
                let a = self.eval(x)?;
                let a = need(x, a)?;
                self.charge(pos, self.size(&a))?;
                Ok(Some(Out::Made(Val::Static(self.conform(pos, t, a)?))))
            }
            (Seen::Static(Value::Type(_)), _) => {
                fail(Code::S007, pos, "a constructor takes 1 argument".to_owned())
            }
            (v, _) => fail(
                Code::S010,
                pos,
                format!("{} is not a function", self.text(v)),
            ),
        }
    }

    /// A call of a function item. It runs in the call frame `<fn>$<k>c`. A hardware argument
    /// and a hardware result get a core name in that frame.
    fn call_fn(
        &mut self,
        pos: Pos,
        node: NodeId,
        fp: Pos,
        g: &str,
        id: DeclId,
        xs: &[Expr],
    ) -> Res<Option<Out>> {
        self.charge(fp, 1)?;
        let file = self.file;
        let i = self.items.get(&id).copied().unwrap_or(usize::MAX);
        let Some(Item::Fn {
            pos: ip,
            comptime,
            name: fn_name,
            params,
            ret,
            body,
        }) = file.ast().get(i)
        else {
            return fail(Code::S010, fp, format!("`{g}` is not a function"));
        };
        let vs = self.args(xs)?;
        if params.len() != vs.len() {
            return fail(
                Code::S007,
                pos,
                format!(
                    "`{g}` takes {} argument(s), but it has {}",
                    params.len(),
                    vs.len()
                ),
            );
        }
        // A call outside a body runs on static values only, so its site never names hardware.
        let site = self
            .syms
            .calls
            .get(self.item)
            .and_then(|m| m.get(&node))
            .copied()
            .unwrap_or(0);
        let u = self.syms.items.get(i).copied().unwrap_or(0);
        self.nested(pos, |ev| {
            ev.in_frame(None, |ev| {
                let (path, frame) = ev.frame_of(u, Step::Call(site));
                ev.in_item(i, frame, |ev| {
                    for (q, v) in params.iter().zip(vs) {
                        ev.param(pos, *comptime, q, v)?;
                    }
                    let rt = ev.type_expr(ret)?;
                    ev.ret = Some(rt);
                    match ev.block(*ip, body, false)? {
                        Some(Val::Hw(h)) => {
                            let role = ev.paths.push(path, Step::Role(Role::Ret));
                            let name = ev.version(Tag::Ret, role);
                            Ok(Some(Out::Made(ev.bind_hw(pos, name, h))))
                        }
                        Some(v) => Ok(Some(Out::Made(v))),
                        None => fail(
                            Code::S010,
                            pos,
                            format!("`{}` ends without `return`", fn_name.name),
                        ),
                    }
                })
            })
        })
    }

    /// Binds a parameter of a call. Its type can use the parameters before it. A static
    /// parameter needs a static argument.
    fn param(&mut self, pos: Pos, comptime: bool, q: &Param, v: Out) -> Res<()> {
        let t = self.type_expr(&q.ty)?;
        self.charge(pos, self.size(&v))?;
        let x = if comptime || q.comptime {
            let v = self.settle(pos, t, v)?;
            Val::Static(self.conform(pos, t, v)?)
        } else {
            self.conform_val(pos, t, v)?
        };
        let id = self.decl(&q.name)?;
        let x = self.named(pos, id, x);
        self.bind(
            id,
            Slot {
                ty: Some(t),
                mutable: false,
                value: x,
            },
        );
        Ok(())
    }

    fn call_prelude(
        &mut self,
        pos: Pos,
        fp: Pos,
        g: &str,
        builtin: Prelude,
        xs: &[Expr],
    ) -> Res<Option<Out>> {
        self.charge(fp, 1)?;
        let vs = self.args(xs)?;
        if builtin == Prelude::Len {
            return self.len(pos, vs);
        }
        let mut sizes = 0u128;
        for v in &vs {
            sizes += self.size(v);
        }
        self.charge(pos, sizes)?;
        let mut vs = vs;
        if matches!(builtin, Prelude::Resize | Prelude::Reinterpret) && vs.len() == 2 {
            let (Some(v), Some(t)) = (vs.pop(), vs.pop()) else {
                return fail(Code::S010, pos, format!("`{g}` needs two arguments"));
            };
            self.check_static(pos, &t)?;
            let Value::Type(ty) = self.store.value(&t) else {
                return fail(
                    Code::S010,
                    pos,
                    format!(
                        "`{g}` needs a type, not {}",
                        self.store.value(&t).text(&self.tys)
                    ),
                );
            };
            let ty = *ty;
            return match self.data(pos, v)? {
                Opnd::Static(v) => {
                    let v = self.store.value(&v);
                    let made = if builtin == Prelude::Resize {
                        ops::resize(ty, v, &mut self.fuel, &self.tys)
                    } else {
                        ops::reinterpret(ty, v, &mut self.fuel, &self.tys)
                    };
                    Ok(Some(Out::Made(Val::Static(made.map_err(at(pos))?))))
                }
                Opnd::Hw(x) => Ok(Some(Out::Made(self.hw_convert(pos, builtin, ty, x)?))),
            };
        }
        match (builtin, vs.as_slice()) {
            (Prelude::StaticAssert, [c, m]) => {
                self.check_static(pos, c)?;
                self.check_static(pos, m)?;
                match (self.store.value(c), self.store.value(m)) {
                    (Value::Bool(true), Value::Str(_)) => Ok(None),
                    (Value::Bool(false), Value::Str(m)) => fail(
                        Code::S014,
                        pos,
                        format!("static assertion failed: {}", str_text(m)),
                    ),
                    (c, m) => fail(
                        Code::S010,
                        pos,
                        format!(
                            "`{g}` does not accept [{}, {}]",
                            c.text(&self.tys),
                            m.text(&self.tys)
                        ),
                    ),
                }
            }
            (Prelude::Error, [m]) => {
                self.check_static(pos, m)?;
                match self.store.value(m) {
                    Value::Str(m) => fail(Code::S014, pos, format!("error: {}", str_text(m))),
                    m => fail(
                        Code::S010,
                        pos,
                        format!("`{g}` does not accept {}", m.text(&self.tys)),
                    ),
                }
            }
            (_, vs) => {
                let texts: Vec<String> = vs.iter().map(|v| self.text(self.store.seen(v))).collect();
                fail(
                    Code::S010,
                    pos,
                    format!("`{g}` does not accept [{}]", texts.join(", ")),
                )
            }
        }
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
            // TODO(#178): elaborate the `type` statement (plan step 17).
            Stmt::Alias { pos, .. } => fail(
                Code::S010,
                *pos,
                "the `type` statement is not elaborated yet".to_owned(),
            ),
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
