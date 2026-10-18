// SPDX-License-Identifier: Apache-2.0
//! The store of the evaluator: the values that a result can refer to (the table of constants and
//! the stack of frames), the results that wait while a later operand evaluates, the cursors and
//! holds of the waiting reads, and the history of the locals that they wait at.

mod cursor;
mod history;
mod park;

pub(super) use history::Mark;

use super::Out;
use crate::agg::Agg;
use crate::hw::{Part, Ref, Root, Seen, Val};
use crate::ops::{Fault, Fuel};
use crate::types::TyId;
use crate::value::Value;
use cursor::Cursor;
use resolve::DeclId;
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

/// How far a constant is: not started, in progress, or done.
#[derive(Clone, Copy)]
pub(super) enum ConstStatus {
    Fresh,
    InProgress,
    Done,
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

type Frame = BTreeMap<DeclId, Slot>;

/// The values that a result can refer to: the table of constants by item index, and the
/// stack of frames. The last frame is the current frame. A frame holds only the bindings
/// that ran.
pub(super) struct Store {
    consts: Vec<Entry>,
    frames: Vec<Frame>,
    /// The steps of the walks along paths into values: 1 for each container that a walk
    /// enters. A test counts them, so it checks the work of a walk and not its time.
    #[cfg(test)]
    steps: Cell<u64>,
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
        }
    }

    /// Counts `n` steps of a walk along a path into a stored value.
    fn stepped(&self, n: u64) {
        self.add_steps(n);
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Stepped, n);
    }

    /// Adds `n` to the step count of the store, without the run counter.
    #[cfg(test)]
    fn add_steps(&self, n: u64) {
        self.steps.set(self.steps.get() + n);
    }

    /// The tests count the steps of a walk; a release build does not.
    #[cfg(not(test))]
    #[allow(clippy::unused_self)]
    fn add_steps(&self, _n: u64) {}

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
                Seen::Agg(
                    Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) | Agg::List(_, p),
                ) => {
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
    pub(super) fn step<'s>(&self, cur: Seen<'s>, k: usize) -> Seen<'s> {
        match cur {
            Seen::Static(v) => Seen::Static(self.element(v, &[k])),
            Seen::Agg(a) => self.agg_element(a, &[k]),
            s => s,
        }
    }

    /// Starts a new empty frame, the current one.
    pub(super) fn push_frame(&mut self) {
        self.frames.push(Frame::new());
    }

    /// Ends the current frame.
    pub(super) fn pop_frame(&mut self) {
        self.frames.pop();
    }

    /// The number of the current frame. A reference to a local names its frame by this number.
    pub(super) fn frame_index(&self) -> usize {
        self.frames.len().saturating_sub(1)
    }

    /// Binds the local `id` in the current frame.
    pub(super) fn bind(&mut self, id: DeclId, slot: Slot) {
        if let Some(frame) = self.frames.last_mut() {
            frame.insert(id, slot);
        }
    }

    /// The local `id` of the current frame.
    pub(super) fn slot(&self, id: DeclId) -> Option<&Slot> {
        self.frames.last().and_then(|f| f.get(&id))
    }

    /// Removes the local `id` from the current frame and gives it.
    pub(super) fn unbind(&mut self, id: DeclId) -> Option<Slot> {
        self.frames.last_mut().and_then(|f| f.remove(&id))
    }

    /// How far the constant at the index `i` of the items is.
    pub(super) fn const_status(&self, i: usize) -> ConstStatus {
        match self.consts.get(i) {
            Some(Entry::Done(..)) => ConstStatus::Done,
            Some(Entry::InProgress) => ConstStatus::InProgress,
            _ => ConstStatus::Fresh,
        }
    }

    /// The constant at the index `i` starts to evaluate.
    pub(super) fn begin_const(&mut self, i: usize) {
        if let Some(entry) = self.consts.get_mut(i) {
            *entry = Entry::InProgress;
        }
    }

    /// The constant at the index `i` is done, with its value and its declared type.
    pub(super) fn finish_const(&mut self, i: usize, value: Val, ty: TyId) {
        if let Some(entry) = self.consts.get_mut(i) {
            *entry = Entry::Done(value, ty);
        }
    }

    /// The number of results that wait.
    pub(super) fn parked_len(&self) -> usize {
        self.parked.len()
    }

    /// The steps of the walks along paths so far, for a test of their work.
    #[cfg(test)]
    pub(super) fn steps(&self) -> u64 {
        self.steps.get()
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

    /// The part of the live value of the local at `root` at the numbers `keys`, for a change in
    /// place: one walk down the path, which counts its steps. A root that is not a static local
    /// has no part.
    fn part_mut(&mut self, root: Root, keys: &[usize]) -> Option<&mut Value> {
        let Root::Local(..) = root else {
            return None;
        };
        self.stepped(keys.len() as u64);
        self.part_in(root, keys)
    }

    /// `part_mut` without the count of its steps, for a walk that an earlier call counted.
    fn part_in(&mut self, root: Root, keys: &[usize]) -> Option<&mut Value> {
        let Root::Local(frame, id) = root else {
            return None;
        };
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

    /// Pushes `w` onto the list at `keys` of the static local at `root`. The caller made a `Before` token
    /// first and logs the change with `log_push` on it.
    pub(super) fn push_static(&mut self, root: Root, keys: &[usize], w: Value) {
        self.decide_holds(root);
        if let Some(Value::List(_, ys)) = self.part_mut(root, keys) {
            ys.push(w);
        }
    }

    /// Pops the last element of the list at `keys` of the static local at `root`, if there is
    /// a list. The caller made a `Before` token
    /// first and logs the change with `log_pop` on it.
    pub(super) fn pop_static(&mut self, root: Root, keys: &[usize]) -> Option<Value> {
        self.decide_holds(root);
        match self.part_mut(root, keys) {
            Some(Value::List(_, ys)) => Some(ys.pop().unwrap_or(Value::Unit)),
            _ => None,
        }
    }

    /// Pops the last element of the list at `keys` of the static local at `root`, after it pays
    /// the size of that element from `fuel`. No read waits at the local, so nothing is logged.
    /// The walk down the path happens once, and a payment that fails leaves the list as it is.
    /// `None` if the part is no list. The pay takes the fuel as a parameter because it must come
    /// between the look at the element and its removal.
    pub(super) fn pop_paying(
        &mut self,
        root: Root,
        keys: &[usize],
        fuel: &mut Fuel,
    ) -> Option<Result<Value, Fault>> {
        self.decide_holds(root);
        let Some(Value::List(_, ys)) = self.part_mut(root, keys) else {
            return None;
        };
        if let Err(fault) = fuel.pay(u128::from(ys.last().map_or(0, Value::size))) {
            return Some(Err(fault));
        }
        let popped = ys.pop().unwrap_or(Value::Unit);
        self.mutated(root);
        Some(Ok(popped))
    }

    /// Takes the aggregate root of the local at `root` out of its slot, for a change along
    /// `keys` that the caller makes on it. The caller gives it back with `put_back`, and logs the
    /// change with `log_push` or `log_pop` on a `Before` token made before this call.
    pub(super) fn take_agg(&mut self, root: Root, keys: &[usize]) -> Option<Box<Agg>> {
        self.decide_holds(root);
        self.add_steps(keys.len() as u64);
        match self.take_root(&root) {
            Val::Agg(a) => Some(a),
            _ => None,
        }
    }

    /// Takes the value of the local at `root` out of its slot, for a change that rebuilds it.
    fn take_root(&mut self, root: &Root) -> Val {
        let Root::Local(k, id) = root else {
            return Val::Static(Value::Unit);
        };
        match self.frames.get_mut(*k).and_then(|f| f.get_mut(id)) {
            Some(slot) => std::mem::replace(&mut slot.value, Val::Static(Value::Unit)),
            None => Val::Static(Value::Unit),
        }
    }

    /// Puts `v` into the slot of the local at `root`, after `take_agg` or `take_for_rebind`. It logs
    /// nothing and decides no hold, because the take did both.
    pub(super) fn put_back(&mut self, root: Root, v: Val) {
        if let Root::Local(k, id) = root
            && let Some(slot) = self.frames.get_mut(k).and_then(|f| f.get_mut(&id))
        {
            slot.value = v;
        }
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
            Val::Handle(h) => Part::Value(Agg::Handle(h)),
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
pub(super) fn static_size(a: &Agg) -> u64 {
    let mut total = 0u64;
    let mut work = vec![a];
    while let Some(x) = work.pop() {
        match x {
            Agg::Static(v) => total = total.saturating_add(v.size()),
            Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) | Agg::List(_, p) => {
                work.extend(p.0.iter());
            }
            Agg::Hw(_) | Agg::Ref(..) | Agg::Handle(_) => {}
        }
    }
    total
}
