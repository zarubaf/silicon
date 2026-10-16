// SPDX-License-Identifier: Apache-2.0
//! The store of the evaluator: the values that a result can refer to (the table of constants and
//! the stack of frames), the results that wait while a later operand evaluates, the cursors and
//! holds of the waiting reads, and the history of the locals that they wait at.

mod history;

pub(super) use history::{Edit, Mark, split_root};

use super::Out;
use crate::agg::Agg;
use crate::hw::{Part, Ref, Root, Seen, Val};
use crate::types::TyId;
use crate::value::Value;
use resolve::DeclId;
#[cfg(test)]
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

/// The state of a constant in the table of constants. A done constant keeps its declared
/// type, so a read through it knows the type of each part without a walk.
pub(super) enum Entry {
    NotStarted,
    InProgress,
    Done(Val, TyId),
}

/// A local of the current frame. A handle has no `Ty`, so its `ty` is `None`.
pub(super) struct Slot {
    pub(super) ty: Option<TyId>,
    pub(super) mutable: bool,
    pub(super) value: Val,
}

/// The value that a reference finds when its target is absent. The evaluator binds a local
/// before a use reads it and sets a constant done before a use refers to it, so no reference
/// finds it.
static ABSENT: Val = Val::Static(Value::Bool(false));
static ABSENT_VALUE: Value = Value::Bool(false);

pub(super) type Frame = BTreeMap<DeclId, Slot>;

/// The part of an aggregate root that a read waits at, with the root not held yet. The cursor
/// follows the steps of the read, so one path names the part.
pub(super) struct Cursor {
    pub(super) part: Ref,
    /// The length of the path of the parked reference. The trail of the steps follows it.
    pub(super) base: usize,
    /// A path from the root to a hardware leaf that follows the heavy part of each node, with
    /// the length of its common prefix with the path of the part. A part on the witness holds a
    /// hardware leaf, so it is no static part and its decision walks nothing. `None` until the
    /// first decision.
    pub(super) witness: Option<Witness>,
    /// The steps that the read has left, so the witness need not go deeper than the read can.
    pub(super) left: usize,
    /// The numbers of the steps of the read from the parked reference, while each step had one.
    /// A step with no number ends the trail (`exact`). The read ends at the part with the path of
    /// the reference followed by the trail.
    pub(super) trail: Vec<usize>,
    pub(super) exact: bool,
    /// Whether the path still follows the read. A step with no number, or a decided hold, ends
    /// it. A cursor that is not live stays in the table, because the log rebuilds the old value
    /// when a change replaced the part of the read.
    pub(super) live: bool,
}

/// A path to a hardware leaf, and what is known of its end.
pub(super) struct Witness {
    pub(super) path: Vec<usize>,
    /// The length of the common prefix of `path` and the path of the part.
    pub(super) common: usize,
    /// The path ends at a hardware leaf or a reference, so a part below it has no root.
    pub(super) closed: bool,
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
pub(super) enum Located {
    Static,
    Open(Witness),
}

/// The values that a result can refer to: the table of constants by item index, and the
/// stack of frames. The last frame is the current frame. A frame holds only the bindings
/// that ran.
pub(super) struct Store {
    pub(super) consts: Vec<Entry>,
    pub(super) frames: Vec<Frame>,
    /// The steps of the walks along paths into values: 1 for each container that a walk
    /// enters. A test counts them, so it checks the work of a walk and not its time.
    #[cfg(test)]
    pub(super) steps: Cell<u64>,
    /// The parameters of a frame that refer to an argument of the caller, by the number of
    /// the frame: a module argument refers until the instance statement pays its copy.
    links: BTreeMap<usize, BTreeMap<DeclId, Ref>>,
    /// The results that wait while a later operand of their node evaluates. A mutation of a
    /// local goes to its history and visits none of them. The resume of a result that refers to
    /// the local reads the history, so a result keeps the value that its expression read.
    pub(super) parked: Vec<Out>,
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
    /// The number of mutations of each local: an assignment, a `push`, a `pop`, and a write-back.
    /// An index compares the number of the local of its base before and after its own index
    /// evaluates, so it finds in constant work that the index changed the root (section 5.4). The
    /// root names its frame, so a mutation in a callee frame is another local.
    changes: BTreeMap<Root, u64>,
    /// The changes of each local that a read waits at, from the oldest. A change appends one
    /// entry, and no read copies the local for it.
    history: BTreeMap<Root, history::History>,
    /// The roots with an open window (section 9.1). A root has at most one, since a second one is
    /// `S008`. The
    /// root names its frame, so a call switches no frame of this table and copies nothing.
    pending: BTreeSet<Root>,
}

impl Store {
    /// The store with `items` constants not started and the root frame.
    pub(super) fn new(items: usize) -> Store {
        Store {
            consts: (0..items).map(|_| Entry::NotStarted).collect(),
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
            changes: BTreeMap::new(),
            history: BTreeMap::new(),
            pending: BTreeSet::new(),
            links: BTreeMap::new(),
        }
    }

    /// Counts `n` steps of a walk along a path into a stored value.
    pub(super) fn stepped(&self, n: u64) {
        self.add_steps(n);
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Stepped, n);
    }

    /// Adds `n` to the step count of the store, without the run counter.
    #[cfg(test)]
    pub(super) fn add_steps(&self, n: u64) {
        self.steps.set(self.steps.get() + n);
    }

    /// The tests count the steps of a walk; a release build does not.
    #[cfg(not(test))]
    #[allow(clippy::unused_self)]
    pub(super) fn add_steps(&self, _n: u64) {}

    /// The element of `v` at the numbers `path`, one for each container below it.
    pub(super) fn element<'a>(&self, v: &'a Value, path: &[usize]) -> &'a Value {
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
    pub(super) fn agg_part<'a>(&self, a: &'a Agg, path: &[usize]) -> Option<Seen<'a>> {
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
    pub(super) fn agg_element<'a>(&self, a: &'a Agg, path: &[usize]) -> Seen<'a> {
        self.agg_part(a, path)
            .unwrap_or(Seen::Static(&ABSENT_VALUE))
    }

    /// The element `k` of the container that `cur` finds: one step of a walk along a path.
    pub(super) fn step<'s>(&self, cur: Seen<'s>, k: usize) -> Seen<'s> {
        match cur {
            Seen::Static(v) => Seen::Static(self.element(v, &[k])),
            Seen::Agg(a) => self.agg_element(a, &[k]),
            s => s,
        }
    }

    pub(super) fn frame(&self) -> Option<&Frame> {
        self.frames.last()
    }

    /// Parks the result `o` while a later operand of its node evaluates. It returns the
    /// position to resume from. A reference to a local opens a window of the history of the
    /// local, so that a change of the local goes to the log and the resume of the reference
    /// finds the old value there.
    pub(super) fn park(&mut self, o: Out) -> usize {
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
    pub(super) fn hold_parked(&mut self, at: usize, root: Root) {
        if let Some(slot @ None) = self.held_by.get_mut(at) {
            *slot = Some(root);
            *self.holds.entry(root).or_default() += 1;
        }
    }

    /// The read parked at `at` waits at the part `r` of an aggregate root, and a later index
    /// with a call may hold the root there.
    pub(super) fn cursor(&mut self, at: usize, r: Ref) {
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
    pub(super) fn cursor_static(&mut self, at: usize, r: Ref) {
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
    pub(super) fn cursor_step(&mut self, at: usize, k: Option<usize>) {
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
    pub(super) fn arm(&mut self, at: usize, left: usize) {
        if let Some(Some(c)) = self.cursors.get_mut(at)
            && c.live
        {
            c.left = left;
            let root = c.part.root;
            self.armed.entry(root).or_default().push(at);
        }
    }

    /// The index of the read at `at` finished. A decision that a change made stays made.
    pub(super) fn disarm(&mut self, at: usize) {
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
    pub(super) fn decide_holds(&mut self, root: Root) {
        let Some(list) = self.armed.remove(&root) else {
            return;
        };
        for at in list {
            let located = match self.cursors.get(at) {
                Some(Some(c)) if c.live && !c.on_witness() => Some(self.locate(c)),
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

    /// Walks the path of the cursor once down the live root. A read ends at its first index that
    /// changes the root, so the window of a read that decides a hold is empty and the live root is
    /// the root that the index found. A part that is a static value, or an absent one,
    /// is `Static`. Else the witness goes through the part along the heavy part of each node,
    /// for as many steps as the read has left. A path that ends below a reference or a hardware
    /// leaf closes the witness there: as in Lean, such a part has no root.
    pub(super) fn locate(&self, c: &Cursor) -> Located {
        let path = &c.part.path;
        let value = self.root(&c.part.root);
        let closed_at = |n: usize| {
            Located::Open(Witness {
                path: path.get(..n).unwrap_or_default().to_vec(),
                common: n,
                closed: true,
            })
        };
        let a = match value {
            Val::Agg(a) => a,
            Val::Hw(_) => return closed_at(0),
            _ => return Located::Static,
        };
        let mut cur: &Agg = a;
        for (i, &k) in path.iter().enumerate() {
            cur = match cur {
                Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) => {
                    self.stepped(1);
                    match p.0.get(k) {
                        Some(x) => x,
                        None => return Located::Static,
                    }
                }
                Agg::Static(_) => return Located::Static,
                Agg::Hw(_) | Agg::Ref(..) => return closed_at(i),
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
    pub(super) fn release(&mut self, from: usize) -> (Vec<Out>, Vec<Option<history::Mark>>) {
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
    pub(super) fn resume(&mut self, from: usize) -> Vec<Out> {
        let (outs, marks) = self.release(from);
        // The latest mark first: reads of one part then undo each entry of the log once.
        let mut settled: Vec<Out> = outs
            .into_iter()
            .zip(marks.iter())
            .rev()
            .map(|(out, mark)| match mark {
                Some(mark) => self.resolved(out, *mark),
                None => out,
            })
            .collect();
        settled.reverse();
        for mark in marks.into_iter().flatten() {
            self.close_log(mark.root);
        }
        settled
    }

    /// Takes back the one result parked at `at`. A later evaluation that failed can leave its
    /// own results parked after it, so the result is the first one.
    pub(super) fn resume_one(&mut self, at: usize) -> Out {
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
    pub(super) fn open_window(&mut self, root: Root) -> bool {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Windows, 1);
        self.pending.insert(root)
    }

    /// Closes the window of `root`.
    pub(super) fn shut_window(&mut self, root: Root) {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Windows, 1);
        self.pending.remove(&root);
    }

    /// Counts a mutation of the local at `root`.
    pub(super) fn mutated(&mut self, root: Root) {
        *self.changes.entry(root).or_default() += 1;
    }

    /// The number of mutations of the local at `root` so far.
    pub(super) fn changes_of(&self, root: Root) -> u64 {
        self.changes.get(&root).copied().unwrap_or(0)
    }

    /// Whether a parked result holds the local at `root` (section 5.4).
    pub(super) fn is_held(&mut self, root: Root) -> bool {
        self.decide_holds(root);
        self.holds.contains_key(&root)
    }

    /// The part of the live value of the local at `root` at the numbers `keys`, for a change in
    /// place: one walk down the path. A root that is not a static local has no part.
    pub(super) fn part_mut(&mut self, root: Root, keys: &[usize]) -> Option<&mut Value> {
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
    pub(super) fn take_root(&mut self, root: &Root) -> Val {
        let Root::Local(k, id) = root else {
            return Val::Static(Value::Unit);
        };
        match self.frames.get_mut(*k).and_then(|f| f.get_mut(id)) {
            Some(slot) => std::mem::replace(&mut slot.value, Val::Static(Value::Unit)),
            None => Val::Static(Value::Unit),
        }
    }

    /// Puts `v` into the slot of the local at `root`.
    pub(super) fn put_root(&mut self, root: &Root, v: Val) {
        if let Root::Local(k, id) = root
            && let Some(slot) = self.frames.get_mut(*k).and_then(|f| f.get_mut(id))
        {
            slot.value = v;
        }
    }

    /// Links the parameter `id` of the frame `frame` to the argument `r` of the caller.
    pub(super) fn link(&mut self, frame: usize, id: DeclId, r: Ref) {
        self.links.entry(frame).or_default().insert(id, r);
    }

    /// The argument that the parameter `id` of the frame `frame` links to.
    pub(super) fn linked(&self, frame: usize, id: DeclId) -> Option<&Ref> {
        self.links.get(&frame).and_then(|ls| ls.get(&id))
    }

    /// Removes the links of the frame `frame`, in work for its own links only.
    pub(super) fn unlink(&mut self, frame: usize) {
        self.links.remove(&frame);
    }

    pub(super) fn frame_mut(&mut self) -> Option<&mut Frame> {
        self.frames.last_mut()
    }

    pub(super) fn root(&self, root: &Root) -> &Val {
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
    pub(super) fn root_ty(&self, root: &Root) -> Option<TyId> {
        match root {
            Root::Local(k, id) => self.frames.get(*k).and_then(|f| f.get(id))?.ty,
            Root::Const(i) => match self.consts.get(*i) {
                Some(Entry::Done(_, t)) => Some(*t),
                _ => None,
            },
        }
    }

    /// What the local at `root` holds at the numbers `keys`.
    pub(super) fn current(&self, root: Root, keys: &[usize]) -> Seen<'_> {
        match self.root(&root) {
            Val::Static(v) => Seen::Static(self.element(v, keys)),
            Val::Agg(a) => self.agg_element(a, keys),
            v => v.seen(),
        }
    }

    /// What a reference finds.
    pub(super) fn at<'s>(&'s self, r: &Ref) -> Seen<'s> {
        let root = self.root(&r.root);
        match (root, r.path.is_empty()) {
            (_, true) => root.seen(),
            (Val::Static(v), false) => Seen::Static(self.element(v, &r.path)),
            (Val::Agg(a), false) => self.agg_element(a, &r.path),
            _ => Seen::Static(&ABSENT_VALUE),
        }
    }

    /// The static value that a reference finds.
    pub(super) fn value_at<'s>(&'s self, r: &Ref) -> &'s Value {
        match self.at(r) {
            Seen::Static(v) => v,
            _ => &ABSENT_VALUE,
        }
    }

    /// The part of a literal that waits for its type. A reference copies its value now, so the
    /// literal keeps the value that its expression read. The typed use that settles the literal
    /// charges the size of each part.
    pub(super) fn part(&self, o: Out) -> Part {
        match self.take(o) {
            Val::Pending(_, part) => part,
            Val::Static(v) => Part::Value(Agg::Static(v)),
            Val::Hw(h) => Part::Value(Agg::Hw(h)),
            Val::Agg(a) => Part::Value(*a),
            Val::Handle(_) => Part::Value(Agg::Static(Value::Unit)),
        }
    }

    pub(super) fn seen<'s>(&'s self, out: &'s Out) -> Seen<'s> {
        match out {
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => v.seen(),
            Out::Ref(r) => self.at(r),
        }
    }

    /// The static value of a result that is static.
    pub(super) fn value<'s>(&'s self, out: &'s Out) -> &'s Value {
        match self.seen(out) {
            Seen::Static(v) => v,
            _ => &ABSENT_VALUE,
        }
    }

    /// The value of a result as an owned value. A reference copies its value, so the caller
    /// paid for the copy before.
    pub(super) fn take(&self, out: Out) -> Val {
        match out {
            Out::Made(v) | Out::Named(v) | Out::Kept(v, _) => v,
            Out::Ref(r) => Self::own(self.at(&r)),
        }
    }

    /// What `seen` finds, as an owned value. A static value and an aggregate copy, so the caller
    /// paid for the copy before.
    pub(super) fn own(seen: Seen<'_>) -> Val {
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
    pub(super) fn part_of<'a>(&self, v: &'a Val, path: &[usize]) -> Seen<'a> {
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
