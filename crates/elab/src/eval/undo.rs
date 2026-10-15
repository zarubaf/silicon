// SPDX-License-Identifier: Apache-2.0
//! The undo log of an aggregate root. A read that waits at a part of a root while an index
//! evaluates sees the root as it was before that index (Lean keeps the old value in its result).
//! A `push` or `pop` into a list part of the root appends one entry here, in constant work,
//! instead of copying the parts that the waiting reads cover. A read then resolves the entries
//! of its window once, when it knows its last step (`Evaluator::resolve`), and a copy of a read
//! undoes the entries first, so that it keeps the old value.
//!
//! A list changes only at its end, so an entry holds the length before the change and, for a
//! `pop`, the element that left. The entries of one root are in the order of the changes, and
//! the reads that wait at the root nest, so the window of a read is the entries from its mark.
//!
//! Every walk keeps to the path of a place, and no walk recurses over the depth of a value.

use super::{Evaluator, Out, Store};
use crate::agg::Agg;
use crate::hw::{Ref, Root, Seen, Val};
use crate::value::Value;

/// A change of the list at `keys` by `push` or `pop`.
pub(super) struct Undo {
    pub(super) keys: Vec<usize>,
    /// The length of the list before the change.
    pub(super) len_before: usize,
    /// The element that a `pop` took out. A `push` has none.
    pub(super) saved: Option<Value>,
    /// The size and the depth of each aggregate node on the path before the change, from the
    /// root, so that a copy gets the stored numbers of its nodes back.
    pub(super) stats: Vec<(u64, u64)>,
}

/// The entries of a root and the number of reads that wait at it.
#[derive(Default)]
pub(super) struct Log {
    pub(super) entries: Vec<Undo>,
    pub(super) open: usize,
}

/// The window of a read, sorted by the path of the list. The entries whose paths start with a
/// given path are one run, so a walk along a path narrows the run one step at a time.
pub(super) struct Win {
    pub(super) root: Root,
    order: Vec<usize>,
}

/// A run of the entries of a window: those whose paths start with the path of `depth` steps.
#[derive(Clone, Copy)]
pub(super) struct Span {
    lo: usize,
    hi: usize,
    depth: usize,
}

impl Win {
    /// The window of the entries from `from`, if there are any.
    fn new(root: Root, entries: &[Undo], from: usize) -> Option<Win> {
        let mut order: Vec<usize> = (from..entries.len()).collect();
        if order.is_empty() {
            return None;
        }
        order.sort_by(|&a, &b| {
            let (x, y) = (
                entries.get(a).map(|e| &e.keys),
                entries.get(b).map(|e| &e.keys),
            );
            x.cmp(&y).then(a.cmp(&b))
        });
        Some(Win { root, order })
    }

    /// The run of all entries, at the root.
    pub(super) fn span(&self) -> Span {
        Span {
            lo: 0,
            hi: self.order.len(),
            depth: 0,
        }
    }

    /// The run after the walk along `path` from the root.
    pub(super) fn span_at(&self, entries: &[Undo], path: &[usize]) -> Span {
        path.iter()
            .fold(self.span(), |span, &k| span.step(self, entries, k))
    }
}

impl Span {
    /// The run after one step to the part `k`.
    pub(super) fn step(self, win: &Win, entries: &[Undo], k: usize) -> Span {
        let run = win.order.get(self.lo..self.hi).unwrap_or_default();
        let key = |e: usize| entries.get(e).and_then(|e| e.keys.get(self.depth)).copied();
        let before = run.partition_point(|&e| key(e).is_none_or(|x| x < k));
        let upto = run.partition_point(|&e| key(e).is_none_or(|x| x <= k));
        Span {
            lo: self.lo + before,
            hi: self.lo + upto,
            depth: self.depth + 1,
        }
    }

    /// The positions of the entries for the list at the path of the run, oldest first and older
    /// than `limit`.
    pub(super) fn here(self, win: &Win, entries: &[Undo], limit: usize) -> Vec<usize> {
        win.order
            .get(self.lo..self.hi)
            .unwrap_or_default()
            .iter()
            .copied()
            .take_while(|&e| entries.get(e).is_some_and(|e| e.keys.len() == self.depth))
            .filter(|&e| e < limit)
            .collect()
    }

    /// The positions of all entries of the run older than `limit`, newest first.
    pub(super) fn all(self, win: &Win, limit: usize) -> Vec<usize> {
        let mut at: Vec<usize> = win
            .order
            .get(self.lo..self.hi)
            .unwrap_or_default()
            .iter()
            .copied()
            .filter(|&e| e < limit)
            .collect();
        at.sort_unstable_by(|a, b| b.cmp(a));
        at
    }
}

/// The size and the depth of each aggregate node of `root` on the path `keys`, from the root.
fn node_stats(root: &Agg, keys: &[usize]) -> Vec<(u64, u64)> {
    let mut stats = Vec::new();
    let mut cur = root;
    for &k in keys {
        let (Agg::Array(n, p) | Agg::Tuple(n, p) | Agg::Record(n, p)) = cur else {
            break;
        };
        stats.push((n.size, n.depth));
        match p.0.get(k) {
            Some(x) => cur = x,
            None => break,
        }
    }
    stats
}

/// The list at the numbers `keys` of the value `v`.
fn list_at<'a>(v: &'a mut Value, keys: &[usize]) -> Option<&'a mut Vec<Value>> {
    let mut cur = v;
    for &k in keys {
        cur = match cur {
            Value::Array(_, xs)
            | Value::Tuple(_, xs)
            | Value::Record(_, xs)
            | Value::List(_, xs) => xs.get_mut(k)?,
            _ => return None,
        };
    }
    match cur {
        Value::List(_, ys) => Some(ys),
        _ => None,
    }
}

/// Undoes the change `e` in `v`, a copy of the part of its root at a path of `at` steps that `e`
/// extends: a push drops the last element, a pop puts its element back, and each node of the
/// copy on the path gets the numbers that it had before the change.
fn undo_in(copy: &mut Val, at: usize, e: &Undo) {
    let rel = e.keys.get(at..).unwrap_or_default();
    let apply = |ys: &mut Vec<Value>| match &e.saved {
        None => {
            ys.pop();
        }
        Some(w) => ys.push(w.clone()),
    };
    match copy {
        Val::Static(value) => {
            if let Some(ys) = list_at(value, rel) {
                apply(ys);
            }
        }
        Val::Agg(root) => {
            let mut cur: &mut Agg = root;
            for (i, &k) in rel.iter().enumerate() {
                match cur {
                    Agg::Array(node, parts)
                    | Agg::Tuple(node, parts)
                    | Agg::Record(node, parts) => {
                        if let Some(&(size, depth)) = e.stats.get(at + i) {
                            node.size = size;
                            node.depth = depth;
                        }
                        let Some(part) = parts.0.get_mut(k) else {
                            return;
                        };
                        cur = part;
                    }
                    Agg::Static(value) => {
                        if let Some(ys) = list_at(value, rel.get(i..).unwrap_or_default()) {
                            apply(ys);
                        }
                        return;
                    }
                    _ => return,
                }
            }
            if let Agg::Static(value) = cur
                && let Some(ys) = list_at(value, &[])
            {
                apply(ys);
            }
        }
        _ => {}
    }
}

/// Whether the entry `e` is for a list at `at` or below it.
fn extends(e: &Undo, at: &[usize]) -> bool {
    e.keys.get(..at.len()) == Some(at)
}

impl Store {
    /// A read parks at the root: the mark of its window.
    pub(super) fn open_log(&mut self, root: Root) -> usize {
        let log = self.undo.entry(root).or_default();
        log.open += 1;
        log.entries.len()
    }

    /// A read at the root resumed. The last one clears the log.
    pub(super) fn close_log(&mut self, root: Root) {
        if let Some(log) = self.undo.get_mut(&root) {
            log.open = log.open.saturating_sub(1);
            if log.open == 0 {
                self.undo.remove(&root);
            }
        }
    }

    pub(super) fn entries(&self, root: Root) -> &[Undo] {
        self.undo
            .get(&root)
            .map_or(&[], |log| log.entries.as_slice())
    }

    /// The numbers of the nodes on the path `keys`, if a read waits at the aggregate root and
    /// so a change must go to the log. They come before the change.
    pub(super) fn stats_before(&self, root: Root, keys: &[usize]) -> Option<Vec<(u64, u64)>> {
        if !self.undo.contains_key(&root) {
            return None;
        }
        match self.root(&root) {
            Val::Agg(a) => Some(node_stats(a, keys)),
            _ => None,
        }
    }

    /// Appends the change `e` to the log of the root.
    pub(super) fn log_edit(&mut self, root: Root, e: Undo) {
        if let Some(log) = self.undo.get_mut(&root) {
            log.entries.push(e);
        }
    }

    /// Takes the read parked at `at` back, and keeps the window of its changes until `finish`.
    pub(super) fn unpark(&mut self, at: usize) -> (Out, Option<Win>) {
        let own = self.cursors.get_mut(at).and_then(Option::take);
        let out = self.resume_one(at);
        let Some(c) = own else {
            return (out, None);
        };
        let root = c.part.root;
        let win = (c.live && matches!(out, Out::Ref(_)))
            .then(|| Win::new(root, self.entries(root), c.mark))
            .flatten();
        if win.is_none() {
            self.close_log(root);
        }
        (out, win)
    }

    /// The read resolved: its window is not needed any more.
    pub(super) fn finish(&mut self, win: &Win) {
        self.close_log(win.root);
    }

    /// The value that the parked result `old` of the root has, as it was before the changes of
    /// the log from `mark`. A reference copies its part, and then undoes each change at or
    /// below the part, newest first.
    pub(super) fn old_copy(&self, root: Root, mark: Option<usize>, old: Out) -> Val {
        let path = match &old {
            Out::Ref(r) => r.path.clone(),
            _ => Vec::new(),
        };
        let mut v = self.take(old);
        if let Some(mark) = mark {
            for e in self
                .entries(root)
                .get(mark..)
                .unwrap_or_default()
                .iter()
                .rev()
            {
                if extends(e, &path) {
                    undo_in(&mut v, path.len(), e);
                }
            }
        }
        v
    }
}

/// How a walk along the steps of a read sees the lists of its window.
pub(super) struct Walk<'w> {
    win: &'w Win,
    span: Span,
    /// Entries older than this apply: after a step into an element that left the list, the
    /// walk is in the element as the pop saved it.
    limit: usize,
    /// The walk is in a saved element.
    saved: bool,
}

impl<'w> Walk<'w> {
    /// Whether the walk is in an element that a pop saved.
    pub(super) fn is_saved(&self) -> bool {
        self.saved
    }

    /// A walk from the root along the path of `r`, if the window is for that root.
    pub(super) fn start(win: Option<&'w Win>, entries: &[Undo], r: &Ref) -> Option<Walk<'w>> {
        let win = win.filter(|w| w.root == r.root)?;
        Some(Walk {
            win,
            span: win.span_at(entries, &r.path),
            limit: usize::MAX,
            saved: false,
        })
    }
}

impl Evaluator<'_> {
    /// The number of elements that the list `xs` had when the read began, if the window changed
    /// it.
    pub(super) fn old_len(&self, w: &Walk<'_>, cur: Seen<'_>) -> Option<usize> {
        let Seen::Static(Value::List(..)) = cur else {
            return None;
        };
        let here = w.span.here(w.win, self.store.entries(w.win.root), w.limit);
        let first = here.first()?;
        self.store
            .entries(w.win.root)
            .get(*first)
            .map(|e| e.len_before)
    }

    /// The step to the element `number` of the container `cur`, in the window. A list that the
    /// window changed gives an element that is below the shortest length it had as the element
    /// of the list now, and an element that left the list as the pop saved it.
    pub(super) fn window_step<'s>(
        &'s self,
        w: &mut Walk<'_>,
        cur: Seen<'s>,
        number: usize,
    ) -> Seen<'s> {
        let entries = self.store.entries(w.win.root);
        let before = w.span;
        w.span = before.step(w.win, entries, number);
        if let Seen::Static(Value::List(_, xs)) = cur {
            let here = before.here(w.win, entries, w.limit);
            let low = here
                .iter()
                .filter_map(|&e| entries.get(e).map(|e| e.len_before))
                .fold(xs.len(), usize::min);
            if number >= low
                && let Some(e) = here.iter().find_map(|&e| {
                    entries
                        .get(e)
                        .filter(|x| x.saved.is_some() && x.len_before == number + 1)
                        .map(|x| (e, x))
                })
                && let Some(saved) = &e.1.saved
            {
                w.limit = e.0;
                w.saved = true;
                return Seen::Static(saved);
            }
        }
        self.store.step(cur, number)
    }

    /// The result `out` of a read, as the window left the part it refers to. A reference to a
    /// part with no change below it stays a reference. Else the result is a copy of the old
    /// value, which still holds the root (`Out::Kept`). `copy` is the value of a part that
    /// left a list, `at` is the path of the part, and `w` is the walk to it.
    pub(super) fn resolve(
        &mut self,
        w: Option<Walk<'_>>,
        out: Out,
        copy: Option<Value>,
        at: &[usize],
    ) -> Out {
        let Some(w) = w else {
            return out;
        };
        let root = w.win.root;
        let positions = w.span.all(w.win, w.limit);
        if positions.is_empty() && !w.saved {
            return out;
        }
        let mut v = match copy {
            Some(x) => Val::Static(x),
            None => self.store.take(out),
        };
        let entries = self.store.entries(root);
        for e in positions.iter().filter_map(|&e| entries.get(e)) {
            undo_in(&mut v, at.len(), e);
        }
        Out::Kept(v, root)
    }
}

impl Evaluator<'_> {
    /// The result `out` of a read that took no step into a value, as the window left it.
    pub(super) fn resolve_ref(&mut self, win: Option<&Win>, out: Out) -> Out {
        let Out::Ref(r) = &out else {
            return out;
        };
        let Some(w) = Walk::start(win, self.store.entries(r.root), r) else {
            return out;
        };
        let at = r.path.clone();
        self.resolve(Some(w), out, None, &at)
    }
}
