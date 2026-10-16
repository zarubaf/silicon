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

mod agg;
mod call;
mod container;
mod history;
mod hwops;
mod inst;
mod list;
mod mem;
mod observe;
mod place;
mod record;
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
mod tests_mem;
#[cfg(test)]
mod tests_work_hw;
mod types;

pub use inst::Design;
pub(crate) use inst::{Bind, Elab, Inst, Literal, Mem, Sink, elaborate};
pub(crate) use mem::addr_width;

use crate::agg::{Agg, Base};
use crate::hw::{Graph, Handle, HwId, Op, Part, Ref, Root, Seen, Val};
use crate::int::Int;
use crate::names::{PathId, Paths, Step, Sym};
use crate::ops::{self, Fault, Fuel};
use crate::scan::{CallArgs, Numbers, Scan, Syms};
use crate::types::{Ty, TyId, Types};
use crate::value::{Evaluated, Value, int_size};
use crate::{Budget, Code, Error};
use parse::ast::{BinOp, Expr, Ident, Item, NodeId, Pos, Stmt, TypeExpr};
use parse::{NestedStack, StackError};
use resolve::{DeclId, Kind, Prelude, Resolved, ResolvedExpr, Target};
#[cfg(test)]
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

/// The state of a constant in the table of constants. A done constant keeps its declared
/// type, so a read through it knows the type of each part without a walk.
enum Entry {
    NotStarted,
    InProgress,
    Done(Val, TyId),
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

/// The value that a reference finds when its target is absent. The evaluator binds a local
/// before a use reads it and sets a constant done before a use refers to it, so no reference
/// finds it.
static ABSENT: Val = Val::Static(Value::Bool(false));
static ABSENT_VALUE: Value = Value::Bool(false);

type Frame = BTreeMap<DeclId, Slot>;

/// The part of an aggregate root that a read waits at, with the root not held yet. The cursor
/// follows the steps of the read, so one path names the part.
struct Cursor {
    part: Ref,
    /// The length of the path of the parked reference. After a mutation copied the reference,
    /// the steps of `part` past this length lead into the copy.
    base: usize,
    /// A path from the root to a hardware leaf that follows the heavy part of each node, with
    /// the length of its common prefix with the path of the part. A part on the witness holds a
    /// hardware leaf, so it is no static part and its decision walks nothing. `None` until the
    /// first decision.
    witness: Option<Witness>,
    /// The steps that the read has left, so the witness need not go deeper than the read can.
    left: usize,
    /// The numbers of the steps of the read from the parked reference, while each step had one.
    /// A step with no number ends the trail (`exact`). The read ends at the part with the path of
    /// the reference followed by the trail.
    trail: Vec<usize>,
    exact: bool,
    /// Whether the path still follows the read. A step with no number, or a decided hold, ends
    /// it. A cursor that is not live stays in the table, because the log rebuilds the old value
    /// when a change replaced the part of the read.
    live: bool,
}

/// A path to a hardware leaf, and what is known of its end.
struct Witness {
    path: Vec<usize>,
    /// The length of the common prefix of `path` and the path of the part.
    common: usize,
    /// The path ends at a hardware leaf or a reference, so a part below it has no root.
    closed: bool,
}

impl Cursor {
    /// Whether the witness shows that the part has no static value to hold: the part lies on the
    /// witness, or below its closed end.
    fn on_witness(&self) -> bool {
        let n = self.part.path.len();
        self.witness
            .as_ref()
            .is_some_and(|w| w.common == n.min(w.path.len()) && (n <= w.path.len() || w.closed))
    }
}

/// What the decision of a cursor finds: a static part, or a witness for the part that is none.
enum Located {
    Static,
    Open(Witness),
}

impl Cursor {
    /// The path of the part that the read waits at. A cursor that is not live waits at the path
    /// of its parked reference.
    fn waits_at(&self) -> &[usize] {
        let n = if self.live {
            self.part.path.len()
        } else {
            self.base
        };
        self.part.path.get(..n).unwrap_or_default()
    }
}

/// The values that a result can refer to: the table of constants by item index, and the
/// stack of frames. The last frame is the current frame. A frame holds only the bindings
/// that ran.
struct Store {
    consts: Vec<Entry>,
    frames: Vec<Frame>,
    /// The steps of the walks along paths into values: 1 for each container that a walk
    /// enters. A test counts them, so it checks the work of a walk and not its time.
    #[cfg(test)]
    steps: Cell<u64>,
    /// The parameters of a frame that refer to an argument of the caller, by the number of
    /// the frame: a module argument refers until the instance statement pays its copy.
    links: BTreeMap<usize, BTreeMap<DeclId, Ref>>,
    /// The results that wait while a later operand of their node evaluates. A mutation of a
    /// local goes to its history and visits none of them. The resume of a result that refers to
    /// the local reads the history, so a result keeps the value that its expression read.
    parked: Vec<Out>,
    /// The mark of each parked result that refers to a local, by its position.
    marks: Vec<Option<history::Mark>>,
    /// The old local that the walk of a read finds in place of a live one (`history::View`).
    view: Option<history::View>,
    /// The number of parked results that hold each local (section 5.4): a reference to a static
    /// value in the local, from its park to its resume. A copy does not end the hold. The
    /// local that each parked result holds, if any, by its position.
    holds: BTreeMap<Root, usize>,
    held_by: Vec<Option<Root>>,
    /// The read that waits at a part of an aggregate root and has not held the root yet, by the
    /// position of its parked result: the path of the part. The decision to hold comes at the
    /// first change of the root during that index (`decide_holds`), so an index that leaves the
    /// root alone walks no path.
    cursors: Vec<Option<Cursor>>,
    /// The parked results with an index that evaluates now, by their local.
    armed: BTreeMap<Root, Vec<usize>>,
    /// The changes of each local that a read waits at, from the oldest. A change appends one
    /// entry, and no read copies the local for it.
    history: BTreeMap<Root, history::History>,
    /// The roots with an open window (section 9.1). A root has at most one, since a second one is
    /// `S008`. The
    /// root names its frame, so a call switches no frame of this table and copies nothing.
    pending: BTreeSet<Root>,
}

impl Store {
    /// Counts `n` steps of a walk along a path into a stored value.
    fn stepped(&self, n: u64) {
        self.add_steps(n);
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Stepped, n);
    }

    /// Adds `n` to the step count of the store, without the run counter.
    #[cfg(test)]
    pub(crate) fn add_steps(&self, n: u64) {
        self.steps.set(self.steps.get() + n);
    }

    /// The tests count the steps of a walk; a release build does not.
    #[cfg(not(test))]
    #[allow(clippy::unused_self)]
    pub(crate) fn add_steps(&self, _n: u64) {}

    /// The element of `v` at the numbers `path`, one for each container below it.
    fn element<'a>(&self, v: &'a Value, path: &[usize]) -> &'a Value {
        self.stepped(path.len() as u64);
        let mut cur = v;
        for &k in path {
            cur = match cur {
                Value::Array(_, xs)
                | Value::Tuple(_, xs)
                | Value::Record(_, xs)
                | Value::List(_, xs) => xs.get(k).unwrap_or(&ABSENT_VALUE),
                _ => &ABSENT_VALUE,
            };
        }
        cur
    }

    /// What the aggregate `a` finds at the numbers `path`, one for each container node below it. A
    /// static part continues as a static value. A reference or a hardware leaf does not continue: a
    /// step into it makes a new reference, which no path names, so the walk finds nothing there.
    fn agg_part<'a>(&self, a: &'a Agg, path: &[usize]) -> Option<Seen<'a>> {
        let mut cur = a.seen();
        for (i, &k) in path.iter().enumerate() {
            cur = match cur {
                Seen::Agg(Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p)) => {
                    self.stepped(1);
                    p.0.get(k).map_or(Seen::Static(&ABSENT_VALUE), Agg::seen)
                }
                Seen::Static(v) => return Some(Seen::Static(self.element(v, &path[i..]))),
                _ => return None,
            };
        }
        Some(cur)
    }

    /// The part that `agg_part` finds, or the absent value below a reference or a hardware leaf.
    fn agg_element<'a>(&self, a: &'a Agg, path: &[usize]) -> Seen<'a> {
        self.agg_part(a, path)
            .unwrap_or(Seen::Static(&ABSENT_VALUE))
    }

    /// The element `k` of the container that `cur` finds: one step of a walk along a path.
    fn step<'s>(&self, cur: Seen<'s>, k: usize) -> Seen<'s> {
        match cur {
            Seen::Static(v) => Seen::Static(self.element(v, &[k])),
            Seen::Agg(a) => self.agg_element(a, &[k]),
            s => s,
        }
    }

    fn frame(&self) -> Option<&Frame> {
        self.frames.last()
    }

    /// Parks the result `o` while a later operand of its node evaluates. It returns the
    /// position to resume from. A reference to a local opens a window of the history of the
    /// local, so that a change of the local goes to the log and the resume of the reference
    /// finds the old value there.
    fn park(&mut self, o: Out) -> usize {
        let at = self.parked.len();
        let mut holds = None;
        let mut mark = None;
        if let Out::Ref(r) = &o
            && let Root::Local(..) = r.root
        {
            let root = r.root;
            mark = Some(self.open_log(root));
            // A part that is a static value holds the local, also in an aggregate root.
            let static_part = match self.root(&root) {
                Val::Static(_) => true,
                Val::Agg(_) => matches!(self.at(r), Seen::Static(_)),
                _ => false,
            };
            if static_part {
                *self.holds.entry(root).or_default() += 1;
                holds = Some(root);
            }
        }
        if let Out::Kept(Val::Static(_), root) = &o {
            *self.holds.entry(*root).or_default() += 1;
            holds = Some(*root);
        }
        self.parked.push(o);
        self.marks.push(mark);
        self.held_by.push(holds);
        self.cursors.push(None);
        at
    }

    /// The result parked at `at` holds the local at `root` from now on: a read waits at a static
    /// part of the aggregate root (Lean reads the part again from the live root after each
    /// index). A hold that exists already stays as it is.
    fn hold_parked(&mut self, at: usize, root: Root) {
        if let Some(slot @ None) = self.held_by.get_mut(at) {
            *slot = Some(root);
            *self.holds.entry(root).or_default() += 1;
        }
    }

    /// The read parked at `at` waits at the part `r` of an aggregate root, and a later index
    /// with a call may hold the root there.
    fn cursor(&mut self, at: usize, r: Ref) {
        if let Some(slot) = self.cursors.get_mut(at) {
            *slot = Some(Cursor {
                base: r.path.len(),
                part: r,
                witness: None,
                left: 0,
                trail: Vec::new(),
                exact: true,
                live: true,
            });
        }
    }

    /// The read parked at `at` waits at the part `r` of a static local. It decides no hold, since a
    /// reference to a part of a static local holds it already, but it keeps the trail of its steps.
    fn cursor_static(&mut self, at: usize, r: Ref) {
        if let Some(slot) = self.cursors.get_mut(at) {
            *slot = Some(Cursor {
                base: r.path.len(),
                part: r,
                witness: None,
                left: 0,
                trail: Vec::new(),
                exact: true,
                live: false,
            });
        }
    }

    /// The walk of the read takes the step `k` from the part of the cursor at `at`. A step with no
    /// number ends the cursor, because no static part follows it.
    fn cursor_step(&mut self, at: usize, k: Option<usize>) {
        let Some(slot) = self.cursors.get_mut(at) else {
            return;
        };
        if let Some(c) = slot.as_mut() {
            match k {
                Some(number) if c.exact => c.trail.push(number),
                _ => c.exact = false,
            }
        }
        match (k, slot.as_mut()) {
            (Some(k), Some(c)) if c.live => {
                if let Some(w) = c.witness.as_mut()
                    && w.common == c.part.path.len()
                    && w.path.get(w.common) == Some(&k)
                {
                    w.common += 1;
                }
                c.part.path.push(k);
            }
            (_, Some(c)) => c.live = false,
            _ => {}
        }
    }

    /// An index with a call of the read at `at` evaluates: the first change of the local in that
    /// time decides the hold.
    fn arm(&mut self, at: usize, left: usize) {
        if let Some(Some(c)) = self.cursors.get_mut(at)
            && c.live
        {
            c.left = left;
            let root = c.part.root;
            self.armed.entry(root).or_default().push(at);
        }
    }

    /// The index of the read at `at` finished. A decision that a change made stays made.
    fn disarm(&mut self, at: usize) {
        let root = match self.cursors.get(at) {
            Some(Some(p)) => p.part.root,
            _ => return,
        };
        if let Some(list) = self.armed.get_mut(&root) {
            if let Some(i) = list.iter().rposition(|&a| a == at) {
                list.remove(i);
            }
            if list.is_empty() {
                self.armed.remove(&root);
            }
        }
    }

    /// Decides the holds of the reads with an index that evaluates now, before a change of the
    /// local at `root`: the part of a cursor that is a static value holds the local, as Lean
    /// reads the part again from the live root. The decision uses the root as the index found
    /// it, so it comes before the first change. A part on the witness holds a hardware leaf
    /// and needs no walk. Otherwise the decision walks the path of the part once. A static part
    /// holds, and the charge of the held root pays for the walk. Any other part gives a new
    /// witness through it, and the read has at most as many steps left as the witness is deep.
    /// A node without a hardware leaf is a static value (`Agg::finish`), so the heavy part of a
    /// node leads to a leaf. Each walk that makes a new witness enters a part with at most half
    /// the hardware leaves of the part before it. Thus a read walks at most log2 L plus one
    /// times its steps, where L is the number of hardware leaves of the root.
    fn decide_holds(&mut self, root: Root) {
        let Some(list) = self.armed.remove(&root) else {
            return;
        };
        for at in list {
            let located = match self.cursors.get(at) {
                Some(Some(c)) if c.live && !c.on_witness() => Some(self.locate(at, c)),
                _ => None,
            };
            match located {
                Some(Located::Static) => {
                    self.hold_parked(at, root);
                    if let Some(Some(c)) = self.cursors.get_mut(at) {
                        c.live = false;
                    }
                }
                Some(Located::Open(w)) => {
                    if let Some(Some(c)) = self.cursors.get_mut(at) {
                        c.witness = Some(w);
                    }
                }
                None => {}
            }
        }
    }

    /// Walks the path of the cursor at `at` once: down the live root, or down the copy that a
    /// mutation made once the result is a copy. A part that is a static value, or an absent one,
    /// is `Static`. Else the witness goes through the part along the heavy part of each node,
    /// for as many steps as the read has left. A path that ends below a reference or a hardware
    /// leaf closes the witness there: as in Lean, such a part has no root.
    fn locate(&self, at: usize, c: &Cursor) -> Located {
        let path = &c.part.path;
        let old = match (self.parked.get(at), self.marks.get(at)) {
            (Some(Out::Ref(_)), Some(Some(mark))) => {
                if self.restarted(*mark, c.waits_at())
                    && self.old_root(*mark, c.waits_at()).is_none()
                {
                    // An element that a `pop` took out is a static value.
                    return Located::Static;
                }
                self.old_root(*mark, c.waits_at())
            }
            _ => None,
        };
        let (value, rel) = match (self.parked.get(at), old) {
            (Some(Out::Kept(v, _)), _) => (v, path.get(c.base..).unwrap_or_default()),
            (_, Some(old)) => (old, &path[..]),
            _ => (self.root(&c.part.root), &path[..]),
        };
        let skipped = path.len() - rel.len();
        let closed_at = |n: usize| {
            Located::Open(Witness {
                path: path.get(..n).unwrap_or_default().to_vec(),
                common: n,
                closed: true,
            })
        };
        let a = match value {
            Val::Agg(a) => a,
            Val::Hw(_) => return closed_at(skipped),
            _ => return Located::Static,
        };
        let mut cur: &Agg = a;
        for (i, &k) in rel.iter().enumerate() {
            cur = match cur {
                Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) => {
                    self.stepped(1);
                    match p.0.get(k) {
                        Some(x) => x,
                        None => return Located::Static,
                    }
                }
                Agg::Static(_) => return Located::Static,
                Agg::Hw(_) | Agg::Ref(..) => return closed_at(skipped + i),
            };
        }
        let mut witness = Witness {
            path: path.clone(),
            common: path.len(),
            closed: false,
        };
        let limit = path.len().saturating_add(c.left);
        loop {
            match cur {
                Agg::Static(_) => return Located::Static,
                Agg::Hw(_) | Agg::Ref(..) => {
                    witness.closed = true;
                    break;
                }
                Agg::Array(n, p) | Agg::Tuple(n, p) | Agg::Record(n, p) => {
                    let next = if n.leaves > 0 && witness.path.len() < limit {
                        p.0.get(n.heavy)
                    } else {
                        None
                    };
                    let Some(next) = next else { break };
                    self.stepped(1);
                    witness.path.push(n.heavy);
                    cur = next;
                }
            }
        }
        Located::Open(witness)
    }

    /// Takes the results parked from the position `from` out of the table, with their marks, and
    /// ends the holds and the cursors of their positions. The windows stay open: the caller
    /// closes each one after it reads the history.
    fn release(&mut self, from: usize) -> (Vec<Out>, Vec<Option<history::Mark>>) {
        let from = from.min(self.parked.len());
        let outs = self.parked.split_off(from);
        let marks = self.marks.split_off(from.min(self.marks.len()));
        self.cursors.truncate(from);
        for root in self.held_by.split_off(from).into_iter().flatten() {
            if let Some(n) = self.holds.get_mut(&root) {
                *n -= 1;
                if *n == 0 {
                    self.holds.remove(&root);
                }
            }
        }
        (outs, marks)
    }

    /// Takes the results parked from the position `from` back, in their order. Parks and
    /// resumes nest like the evaluations that they wrap. A result that refers to a local gets
    /// the value that it had when it parked: a part that a change reached becomes a copy of its
    /// old value, and any other part stays a reference. Every site that takes results back
    /// passes here, so none can miss a change.
    fn resume(&mut self, from: usize) -> Vec<Out> {
        let (outs, marks) = self.release(from);
        let settled = outs
            .into_iter()
            .zip(marks.iter())
            .map(|(out, mark)| match mark {
                Some(mark) => self.resolved(out, *mark),
                None => out,
            })
            .collect();
        for mark in marks.into_iter().flatten() {
            self.close_log(mark.root);
        }
        settled
    }

    /// Takes back the one result parked at `at`. A later evaluation that failed can leave its
    /// own results parked after it, so the result is the first one.
    fn resume_one(&mut self, at: usize) -> Out {
        let (outs, marks) = self.release(at);
        let mut outs = outs.into_iter();
        let mut first = outs.next().unwrap_or(Out::Made(Val::Static(Value::Unit)));
        if let Some(Some(mark)) = marks.first() {
            first = self.resolved(first, *mark);
        }
        for mark in marks.into_iter().flatten() {
            self.close_log(mark.root);
        }
        first
    }

    /// Opens a window of `root`: `false`, with no change, if a window of it is open already.
    fn open_window(&mut self, root: Root) -> bool {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Windows, 1);
        self.pending.insert(root)
    }

    /// Closes the window of `root`.
    fn shut_window(&mut self, root: Root) {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Windows, 1);
        self.pending.remove(&root);
    }

    /// Whether a parked result holds the local at `root` (section 5.4).
    fn is_held(&mut self, root: Root) -> bool {
        self.decide_holds(root);
        self.holds.contains_key(&root)
    }

    /// The part of the live value of the local at `root` at the numbers `keys`, for a change in
    /// place: one walk down the path. A root that is not a static local has no part.
    fn part_mut(&mut self, root: Root, keys: &[usize]) -> Option<&mut Value> {
        let Root::Local(frame, id) = root else {
            return None;
        };
        self.stepped(keys.len() as u64);
        let Val::Static(value) = &mut self.frames.get_mut(frame)?.get_mut(&id)?.value else {
            return None;
        };
        let mut cur = value;
        for &k in keys {
            cur = match cur {
                Value::Array(_, xs)
                | Value::Tuple(_, xs)
                | Value::Record(_, xs)
                | Value::List(_, xs) => xs.get_mut(k)?,
                _ => return None,
            };
        }
        Some(cur)
    }

    /// Takes the value of the local at `root` out of its slot, for a change that rebuilds it.
    /// The caller puts the new value back with `put_root`.
    fn take_root(&mut self, root: &Root) -> Val {
        let Root::Local(k, id) = root else {
            return Val::Static(Value::Unit);
        };
        match self.frames.get_mut(*k).and_then(|f| f.get_mut(id)) {
            Some(slot) => std::mem::replace(&mut slot.value, Val::Static(Value::Unit)),
            None => Val::Static(Value::Unit),
        }
    }

    /// Puts `v` into the slot of the local at `root`.
    fn put_root(&mut self, root: &Root, v: Val) {
        if let Root::Local(k, id) = root
            && let Some(slot) = self.frames.get_mut(*k).and_then(|f| f.get_mut(id))
        {
            slot.value = v;
        }
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
        if let Some(old) = self.viewed(root) {
            return old;
        }
        match root {
            Root::Local(k, id) => self
                .frames
                .get(*k)
                .and_then(|f| f.get(id))
                .map_or(&ABSENT, |s| &s.value),
            Root::Const(i) => match self.consts.get(*i) {
                Some(Entry::Done(v, _)) => v,
                _ => &ABSENT,
            },
        }
    }

    /// The type of the local or the constant at `root`, if it has one.
    fn root_ty(&self, root: &Root) -> Option<TyId> {
        match root {
            Root::Local(k, id) => self.frames.get(*k).and_then(|f| f.get(id))?.ty,
            Root::Const(i) => match self.consts.get(*i) {
                Some(Entry::Done(_, t)) => Some(*t),
                _ => None,
            },
        }
    }

    /// What the local at `root` holds at the numbers `keys`.
    fn current(&self, root: Root, keys: &[usize]) -> Seen<'_> {
        match self.root(&root) {
            Val::Static(v) => Seen::Static(self.element(v, keys)),
            Val::Agg(a) => self.agg_element(a, keys),
            v => v.seen(),
        }
    }

    /// What a reference finds.
    fn at<'s>(&'s self, r: &Ref) -> Seen<'s> {
        let root = self.root(&r.root);
        match (root, r.path.is_empty()) {
            (_, true) => root.seen(),
            (Val::Static(v), false) => Seen::Static(self.element(v, &r.path)),
            (Val::Agg(a), false) => self.agg_element(a, &r.path),
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

    /// The part of a literal that waits for its type. A reference copies its value now, so the
    /// literal keeps the value that its expression read. The typed use that settles the literal
    /// charges the size of each part.
    fn part(&self, o: Out) -> Part {
        match self.take(o) {
            Val::Pending(_, part) => part,
            Val::Static(v) => Part::Value(Agg::Static(v)),
            Val::Hw(h) => Part::Value(Agg::Hw(h)),
            Val::Agg(a) => Part::Value(*a),
            Val::Handle(_) => Part::Value(Agg::Static(Value::Unit)),
        }
    }

    fn seen<'s>(&'s self, out: &'s Out) -> Seen<'s> {
        match out {
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => v.seen(),
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
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => v,
            Out::Ref(r) => Self::own(self.at(&r)),
        }
    }

    /// What `seen` finds, as an owned value. A static value and an aggregate copy, so the caller
    /// paid for the copy before.
    fn own(seen: Seen<'_>) -> Val {
        match seen {
            Seen::Static(v) => {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Copies, v.size());
                Val::Static(v.clone())
            }
            Seen::Hw(h) => Val::Hw(h),
            Seen::Handle(h) => Val::Handle(h.clone()),
            Seen::Pending(q, p) => Val::Pending(q, p.clone()),
            Seen::Agg(a) => {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Copies, static_size(a));
                Val::Agg(Box::new(a.clone()))
            }
        }
    }

    /// What the value `v` holds at the numbers `path`.
    fn part_of<'a>(&self, v: &'a Val, path: &[usize]) -> Seen<'a> {
        match v {
            Val::Static(x) => Seen::Static(self.element(x, path)),
            Val::Agg(a) => self.agg_element(a, path),
            v => v.seen(),
        }
    }
}

/// The recursive size of the static parts of `a`: the values that a clone of it copies. The walk
/// keeps its own stack.
#[cfg(test)]
fn static_size(a: &Agg) -> u64 {
    let mut total = 0u64;
    let mut work = vec![a];
    while let Some(x) = work.pop() {
        match x {
            Agg::Static(v) => total = total.saturating_add(v.size()),
            Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) => work.extend(p.0.iter()),
            Agg::Hw(_) | Agg::Ref(..) => {}
        }
    }
    total
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
        | Expr::ArrayType { pos, .. }
        | Expr::FnType { pos, .. } => *pos,
    }
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
        let mut consts = Vec::new();
        for (i, item) in file.ast().iter().enumerate() {
            let name = item.name();
            if let Some(Target::Decl(id)) = file.target(name.id) {
                items.insert(id, i);
            }
            consts.push(Entry::NotStarted);
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
            store: Store {
                consts,
                frames: vec![Frame::new()],
                #[cfg(test)]
                steps: Cell::new(0),
                parked: Vec::new(),
                marks: Vec::new(),
                view: None,
                holds: BTreeMap::new(),
                held_by: Vec::new(),
                cursors: Vec::new(),
                armed: BTreeMap::new(),
                history: BTreeMap::new(),
                pending: BTreeSet::new(),
                links: BTreeMap::new(),
            },
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
    let value = ev.static_value(expr_pos(e), out)?;
    let used = budget.fuel - ev.fuel.left();
    #[cfg_attr(not(test), allow(unused_mut))]
    let mut evaluated = Evaluated::new(value, ev.tys);
    #[cfg(test)]
    {
        evaluated.steps = ev.store.steps.get();
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

    /// A mutation at `pos` of the local at `root` that a parked result holds charges the size of
    /// the local before the change (section 5.4). The charge pays for the copies that the change
    /// causes, so it comes before the change reaches the history of the local.
    fn charge_held(&mut self, pos: Pos, root: Root) -> Res<()> {
        if !self.store.is_held(root) {
            return Ok(());
        }
        let size = self.seen_size(self.store.root(&root).seen());
        self.charge(pos, size)
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

    /// Whether the operand is a hardware aggregate.
    fn opnd_is_agg(&self, o: &Opnd) -> bool {
        matches!(o, Opnd::Static(out) if self.is_agg(out))
    }

    /// Whether the result is a handle. A handle is the whole value of a local, so a reference
    /// with a path is none, and the check does not walk it.
    fn is_handle(&self, out: &Out) -> bool {
        match out {
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => matches!(v, Val::Handle(_)),
            Out::Ref(r) => r.path.is_empty() && matches!(self.store.root(&r.root), Val::Handle(_)),
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
            Opnd::Static(o) if self.is_agg(&o) => Ok(self.typed_agg(pos, t, o)?.into_val()),
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

    /// The copy of `out` when `copies`, then its typed use at `t` at `pos`. The copy charges the
    /// size of the result, and a handle has the size 1. A typed use then reads a handle. A read
    /// of an aggregate gives a reference, and its binding expands the reference into its
    /// leaves. Thus the copy also charges the size of the reference, the zero size of its type,
    /// before the typed use.
    fn copy_use(&mut self, pos: Pos, t: TyId, copies: bool, out: Out) -> Res<Val> {
        if copies {
            self.charge(pos, self.size(&out))?;
        }
        self.read_use(pos, t, copies, out)
    }

    /// The typed use of `out` at `t` after its copy charged. A read of a handle that gives an
    /// aggregate charges the size of the reference when `copies`.
    fn read_use(&mut self, pos: Pos, t: TyId, copies: bool, out: Out) -> Res<Val> {
        let out = self.settle(pos, t, out)?;
        let handle = self.is_handle(&out);
        let d = self.data(pos, out)?;
        if copies
            && handle
            && let Opnd::Static(o) = &d
            && self.is_agg(o)
        {
            self.charge(pos, self.size(o))?;
        }
        self.conform_data(pos, t, d)
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
                let (ty, path) = (ty.clone(), *path);
                let t = self.tys.mk(ty);
                match self.normalize(pos, Agg::Ref(Base::Name(path), t))? {
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
    /// aggregate takes one version, and each of its hardware leaves gets a core `let`.
    fn named(&mut self, pos: Pos, id: DeclId, v: Val) -> Res<Val> {
        match v {
            Val::Hw(h) => {
                let path = self.fresh(id);
                Ok(self.bind_hw(pos, path, h))
            }
            Val::Agg(a) => {
                let path = self.fresh(id);
                Ok(Val::Agg(Box::new(self.bind_agg(pos, path, *a)?)))
            }
            v => Ok(v),
        }
    }

    /// The results of the arguments of a call, in order.
    fn args<'e>(&mut self, xs: impl IntoIterator<Item = &'e Expr>) -> Res<Vec<Out>> {
        let base = self.store.parked.len();
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
            Seen::Handle(Handle::Res { .. } | Handle::Mem(_) | Handle::Input { .. }) => {
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
                let name = self.paths.child(None, q.sym);
                let t = self.tys.mk(q.ty);
                let v = self.normalize(pos, Agg::Ref(Base::Out(path, name), t))?;
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
        let holds = |o: &Opnd| match o {
            Opnd::Static(o) => {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Flagged, 1);
                match self.store.seen(o) {
                    Seen::Agg(a) => a.stored_ty().is_some_and(TyId::holds_fn),
                    _ => self.store.value(o).holds_fn(),
                }
            }
            Opnd::Hw(_) => false,
        };
        if matches!(op, BinOp::Eq | BinOp::Ne) && (holds(a) || holds(b)) {
            return fail(
                Code::S010,
                pos,
                format!("`{}` takes no function", ops::binop_text(op)),
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
        match self.store.frame().and_then(|f| f.get(&id)) {
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
                Kind::Fn if self.file.decl(id).generic => fail(
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
                    let k = self.store.frames.len().saturating_sub(1);
                    // An empty input port refers to its name. The read pays its zero, a new
                    // static value.
                    let empty = self.empty_input(id);
                    if let Some((path, ty)) = empty {
                        Ok(Out::Made(
                            self.normalize(pos, Agg::Ref(Base::Name(path), ty))?,
                        ))
                    } else if self.store.frame().is_some_and(|f| f.contains_key(&id)) {
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
        match self.store.consts.get(i) {
            Some(Entry::Done(..)) => return Ok(const_ref(i)),
            Some(Entry::InProgress) => {
                return fail(
                    Code::S019,
                    pos,
                    format!("the constant `{x}` depends on itself"),
                );
            }
            _ => {}
        }
        self.structural(|ev| {
            ev.nested(pos, |ev| {
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
                        Ok((ev.conform(*cp, t, o)?, t))
                    }
                    Some(Item::Alias { ty, .. }) => {
                        let t = ev.type_expr(ty)?;
                        Ok((Value::Type(t), ev.tys.mk(Ty::Type)))
                    }
                    _ => fail(Code::S010, pos, format!("`{x}` is not a constant")),
                })?;
                ev.store.consts[i] = Entry::Done(Val::Static(c.0), c.1);
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
            self.copy_use(pos, t, o.is_ref(), o)?
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
                let v = self.copy_use(*pos, rt, true, o)?;
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
