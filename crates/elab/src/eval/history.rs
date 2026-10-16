// SPDX-License-Identifier: Apache-2.0
//! The history of a root that a read waits at. A read that waits at a part of a root while an
//! index evaluates sees the root as it was before that index (Lean keeps the old value in its
//! result). A `push` or `pop` into a list part of the root appends one entry here, instead of
//! copying the parts that the waiting reads cover. A read then resolves the entries of its
//! window once, when it knows its last step (`Evaluator::resolve_ref`), and a copy of a read
//! undoes the entries first, so that it keeps the old value.
//!
//! A list changes only at its end, so an entry holds, for a `pop`, the element that left. The
//! entries of one root are in the order of the changes, and the reads that wait at the root
//! nest, so the window of a read is the entries from its mark.
//!
//! The entries have an index by path: a trie with one node for each path that a change named
//! and for each prefix of it. Each node lists the entries at or below its path, in order. Thus
//! the window of a read at a path is a binary search at one node, and a read handles only the
//! entries that reach its part.
//!
//! Every walk keeps to the path of a place, and no walk recurses over the depth of a value.

use super::{Evaluator, Out, Store};
use crate::agg::Agg;
use crate::hw::{Root, Val};
use crate::value::Value;
use std::collections::BTreeMap;

/// A change of the list at the numbers of its entry.
pub(super) enum Change {
    Push,
    /// The element that the `pop` took out.
    Pop(Value),
}

/// A change of the list at `keys`.
pub(super) struct Entry {
    pub(super) keys: Vec<usize>,
    pub(super) change: Change,
    /// The size and the depth of each aggregate node on the path before the change, from the
    /// root, so that a copy gets the stored numbers of its nodes back.
    pub(super) stats: Vec<(u64, u64)>,
}

/// A node of the index by path.
#[derive(Default)]
struct Node {
    children: BTreeMap<usize, usize>,
    /// The entries whose path starts with the path of the node, in the order of the changes.
    below: Vec<usize>,
}

/// The entries of a root, their index by path, and the number of reads that wait at the root.
pub(super) struct History {
    entries: Vec<Entry>,
    /// The index by path. The node 0 is the root.
    nodes: Vec<Node>,
    pub(super) open: usize,
}

impl History {
    fn new() -> History {
        History {
            entries: Vec::new(),
            nodes: vec![Node::default()],
            open: 0,
        }
    }

    /// The node of the path `path`, if a change named it or an extension of it.
    fn node(&self, path: &[usize]) -> Option<&Node> {
        let mut at = 0usize;
        for k in path {
            at = *self.nodes.get(at)?.children.get(k)?;
        }
        self.nodes.get(at)
    }

    /// Appends the entry `e`, and lists it at the node of each prefix of its path.
    fn append(&mut self, e: Entry) {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Logged, 1);
        let pos = self.entries.len();
        let mut at = 0usize;
        if let Some(node) = self.nodes.get_mut(at) {
            node.below.push(pos);
        }
        for &k in &e.keys {
            let known = self.nodes.get(at).and_then(|n| n.children.get(&k)).copied();
            at = if let Some(next) = known {
                next
            } else {
                self.nodes.push(Node::default());
                let next = self.nodes.len() - 1;
                if let Some(node) = self.nodes.get_mut(at) {
                    node.children.insert(k, next);
                }
                next
            };
            if let Some(node) = self.nodes.get_mut(at) {
                node.below.push(pos);
            }
        }
        self.entries.push(e);
    }

    /// The positions of the entries from `mark` at or below `path`, in the order of the changes.
    fn window(&self, path: &[usize], mark: usize) -> &[usize] {
        let Some(node) = self.node(path) else {
            return &[];
        };
        let from = node.below.partition_point(|&p| p < mark);
        node.below.get(from..).unwrap_or_default()
    }
}

/// The window of a read: the entries of a root from its mark on.
pub(super) struct Win {
    pub(super) root: Root,
    mark: usize,
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
fn undo_in(copy: &mut Val, at: usize, e: &Entry) {
    let rel = e.keys.get(at..).unwrap_or_default();
    let apply = |ys: &mut Vec<Value>| match &e.change {
        Change::Push => {
            ys.pop();
        }
        Change::Pop(w) => ys.push(w.clone()),
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

impl Store {
    /// A read parks at the root: the mark of its window.
    pub(super) fn open_log(&mut self, root: Root) -> usize {
        let log = self.history.entry(root).or_insert_with(History::new);
        log.open += 1;
        log.entries.len()
    }

    /// A read at the root resumed. The last one clears the log.
    pub(super) fn close_log(&mut self, root: Root) {
        if let Some(log) = self.history.get_mut(&root) {
            log.open = log.open.saturating_sub(1);
            if log.open == 0 {
                self.history.remove(&root);
            }
        }
    }

    /// The number of entries of the log of the root.
    fn logged(&self, root: Root) -> usize {
        self.history.get(&root).map_or(0, |log| log.entries.len())
    }

    /// The numbers of the nodes on the path `keys`, if a read waits at the aggregate root and
    /// so a change must go to the log. They come before the change.
    pub(super) fn stats_before(&self, root: Root, keys: &[usize]) -> Option<Vec<(u64, u64)>> {
        if !self.history.contains_key(&root) {
            return None;
        }
        match self.root(&root) {
            Val::Agg(a) => Some(node_stats(a, keys)),
            _ => None,
        }
    }

    /// Appends the change `e` to the log of the root.
    pub(super) fn log_edit(&mut self, root: Root, e: Entry) {
        if let Some(log) = self.history.get_mut(&root) {
            log.append(e);
        }
    }

    /// Takes the read parked at `at` back, and keeps the window of its changes until `finish`.
    pub(super) fn unpark(&mut self, at: usize) -> (Out, Option<Win>) {
        self.activate(at);
        let own = self.cursors.get_mut(at).and_then(Option::take);
        let out = self.resume_one(at);
        let Some(c) = own else {
            return (out, None);
        };
        let root = c.part.root;
        let win = (matches!(out, Out::Ref(_)) && self.logged(root) > c.mark)
            .then_some(Win { root, mark: c.mark });
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
        if let (Some(mark), Some(log)) = (mark, self.history.get(&root)) {
            let window = log.window(&path, mark);
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Logged, 1 + window.len() as u64);
            for e in window.iter().rev().filter_map(|&p| log.entries.get(p)) {
                #[cfg(test)]
                crate::counters::add(
                    crate::counters::Count::Copies,
                    match &e.change {
                        Change::Push => 0,
                        Change::Pop(w) => w.size(),
                    },
                );
                undo_in(&mut v, path.len(), e);
            }
        }
        v
    }
}

impl Evaluator<'_> {
    /// The result `out` of a read, as the window left the part it refers to. A part that no
    /// change reaches stays a reference. A part at or above a changed list gets a copy of its
    /// old value, which still holds the root (`Out::Kept`). No step of a read goes into a list
    /// that its window changed: a list has no hardware leaf, so the segment of the read ends
    /// before the index into it, and the part before the index resolves here.
    pub(super) fn resolve_ref(&mut self, win: Option<&Win>, out: Out) -> Out {
        let (Some(win), Out::Ref(r)) = (win, &out) else {
            return out;
        };
        if win.root != r.root {
            return out;
        }
        let Some(log) = self.store.history.get(&r.root) else {
            return out;
        };
        let window = log.window(&r.path, win.mark);
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Logged, 1 + window.len() as u64);
        if window.is_empty() {
            return out;
        }
        let at = r.path.len();
        let mut v = self.store.take(out);
        for e in window.iter().rev().filter_map(|&p| log.entries.get(p)) {
            #[cfg(test)]
            crate::counters::add(
                crate::counters::Count::Copies,
                match &e.change {
                    Change::Push => 0,
                    Change::Pop(w) => w.size(),
                },
            );
            undo_in(&mut v, at, e);
        }
        Out::Kept(v, win.root)
    }
}
