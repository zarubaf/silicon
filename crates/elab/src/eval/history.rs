// SPDX-License-Identifier: Apache-2.0
//! The history of a local that a read waits at. A read that waits at a part of a local while an
//! index evaluates sees the local as it was before that index (Lean keeps the old value in its
//! result). Each change of the local while a read waits appends one entry here, instead of
//! copying the parts that the waiting reads cover:
//!
//! - `Push` and `Pop` change a list part at its end. A `Pop` keeps the element that left.
//! - `Replace` writes a part of a static local. It keeps the part that left.
//! - `Rebind` binds the whole local again, for an assignment to the local and for a write that
//!   gives a hardware leaf its next version. It keeps the local that left.
//!
//! The entries of one local are in the order of the changes. The reads that wait at the local
//! nest, so the window of a read is the entries from its mark.
//!
//! The entries have an index by path: a trie with one node for each path that a change named
//! and for each prefix of it. Each node lists the entries at or below its path, the `Replace`
//! and `Rebind` entries at the path itself, and the `Pop` entries of the list at the path by the
//! length that the list had. Thus the window of a read at a path is a binary search at one node,
//! and a read handles only the entries that reach its part.
//!
//! A read resolves its result once, when it knows its last step (`Store::old_part`). The old
//! part is the part as it was at the mark of the read. It starts from the earliest entry in the
//! window that replaced the part or a part above it (`Replace`, `Rebind`, or the first `Pop` of a
//! list above that took out the element of the path), else from the live part. Then it undoes
//! the entries at or below the path that came before that start, newest first. A part that no
//! entry reaches stays a reference.
//!
//! Every walk keeps to the path of a place, and no walk recurses over the depth of a value.

use super::{Evaluator, Out, Store};
use crate::agg::Agg;
use crate::hw::{Root, Val};
use crate::value::Value;
use std::collections::BTreeMap;

/// A change of a local.
pub(super) enum Change {
    Push,
    /// A `pop`: the element that left, and the length that the list had before.
    Pop {
        saved: Value,
        len: usize,
    },
    /// A write into the part of a static local: the part that left.
    Replace(Value),
    /// A write that binds the local again: the local that left.
    Rebind(Val),
}

/// A change of the part at `keys`.
pub(super) struct Entry {
    keys: Vec<usize>,
    change: Change,
    /// The size and the depth of each aggregate node on the path before a `Push` or a `Pop`,
    /// from the root, so that a copy gets the stored numbers of its nodes back.
    stats: Vec<(u64, u64)>,
}

impl Entry {
    /// A `push` into the list at `keys`.
    pub(super) fn push(keys: Vec<usize>, stats: Vec<(u64, u64)>) -> Entry {
        Entry {
            keys,
            change: Change::Push,
            stats,
        }
    }

    /// A `pop` of the list at `keys`, which had `len` elements.
    pub(super) fn pop(keys: Vec<usize>, saved: Value, len: usize, stats: Vec<(u64, u64)>) -> Entry {
        Entry {
            keys,
            change: Change::Pop { saved, len },
            stats,
        }
    }

    /// A write that replaced the part of a static local at `keys`.
    pub(super) fn replace(keys: Vec<usize>, old: Value) -> Entry {
        Entry {
            keys,
            change: Change::Replace(old),
            stats: Vec::new(),
        }
    }

    /// A write that bound the whole local again.
    pub(super) fn rebind(old: Val) -> Entry {
        Entry {
            keys: Vec::new(),
            change: Change::Rebind(old),
            stats: Vec::new(),
        }
    }
}

/// A node of the index by path.
#[derive(Default)]
struct Node {
    children: BTreeMap<usize, usize>,
    /// The entries whose path starts with the path of the node, in the order of the changes.
    below: Vec<usize>,
    /// The `Replace` and `Rebind` entries at the path of the node.
    own: Vec<usize>,
    /// The `Pop` entries of the list at the path of the node, by the length of the list before.
    pops: BTreeMap<usize, Vec<usize>>,
}

/// The entry that a part resolves from, and the number of steps of the path that it consumed.
struct Start {
    pos: usize,
    used: usize,
}

/// The first position of `list` from `mark` on, if there is one.
fn first_from(list: &[usize], mark: usize) -> Option<usize> {
    list.get(list.partition_point(|&p| p < mark)).copied()
}

/// The entries of a local, their index by path, and the number of reads that wait at the local.
pub(super) struct History {
    entries: Vec<Entry>,
    /// The index by path. The node 0 is the root.
    nodes: Vec<Node>,
    open: usize,
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
        if let Some(node) = self.nodes.get_mut(at) {
            match &e.change {
                Change::Replace(_) | Change::Rebind(_) => node.own.push(pos),
                Change::Pop { len, .. } => node.pops.entry(*len).or_default().push(pos),
                Change::Push => {}
            }
        }
        self.entries.push(e);
    }

    /// The local that the `Rebind` entry at `pos` took out.
    fn saved(&self, pos: usize) -> Option<&Val> {
        match &self.entries.get(pos)?.change {
            Change::Rebind(old) => Some(old),
            _ => None,
        }
    }

    /// The positions of the entries from `mark` at or below `path`, in the order of the changes.
    fn window(&self, path: &[usize], mark: usize) -> &[usize] {
        let Some(node) = self.node(path) else {
            return &[];
        };
        node.below
            .get(node.below.partition_point(|&p| p < mark)..)
            .unwrap_or_default()
    }

    /// The earliest entry from `mark` on that replaced the part at `path` or a part above it:
    /// a `Replace` or `Rebind` at a prefix of the path, or the first `Pop` of a list at a prefix
    /// that took out the element that the path names (its list had one element more than the
    /// number of the step). Later entries at the path act on the new part.
    fn start(&self, path: &[usize], mark: usize) -> Option<Start> {
        let mut best: Option<Start> = None;
        let mut at = Some(0usize);
        for d in 0..=path.len() {
            let Some(node) = at.and_then(|n| self.nodes.get(n)) else {
                break;
            };
            let own = first_from(&node.own, mark).map(|pos| Start { pos, used: d });
            let pop = path
                .get(d)
                .and_then(|k| node.pops.get(&(k + 1)))
                .and_then(|list| first_from(list, mark))
                .map(|pos| Start { pos, used: d + 1 });
            for s in own.into_iter().chain(pop) {
                if best.as_ref().is_none_or(|b| s.pos < b.pos) {
                    best = Some(s);
                }
            }
            at = path.get(d).and_then(|k| node.children.get(k)).copied();
        }
        best
    }
}

/// A read that waits at a part of a local: the local, and the length of its log when the read
/// parked. The window of the read is the entries from there on. The log lives while a read
/// waits, so a mark never outlives its log.
#[derive(Clone, Copy)]
pub(super) struct Mark {
    pub(super) root: Root,
    at: usize,
}

/// The local that a read walks as it was: the log entry that took the local out. While it is set,
/// `Store::root` returns that old local in place of the live one. It is the one global mode of
/// the store. It spans `Store::unpark` to `Store::finish` of one read, and in that time only
/// the walk of the read runs (`Evaluator::follow`): its indices have evaluated, so no user code
/// runs and no change reaches the local.
#[derive(Clone, Copy)]
pub(super) struct View {
    root: Root,
    pos: usize,
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

/// The part of the value `v` at the numbers `keys`.
fn value_at<'a>(v: &'a mut Value, keys: &[usize]) -> Option<&'a mut Value> {
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
    Some(cur)
}

/// Undoes the change `e` in `copy`, a copy of the part of its local at a path of `at` steps that
/// `e` extends: a push drops the last element, a pop puts its element back, a write puts its
/// part back, and each node of the copy on the path gets the numbers that it had before the
/// change.
fn undo_in(copy: &mut Val, at: usize, e: &Entry) {
    let rel = e.keys.get(at..).unwrap_or_default();
    let apply = |part: &mut Value| match (&e.change, part) {
        (Change::Push, Value::List(_, ys)) => {
            ys.pop();
        }
        (Change::Pop { saved, .. }, Value::List(_, ys)) => ys.push(saved.clone()),
        (Change::Replace(saved), part) => *part = saved.clone(),
        _ => {}
    };
    match copy {
        Val::Static(value) => {
            if let Some(part) = value_at(value, rel) {
                apply(part);
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
                        if let Some(part) = value_at(value, rel.get(i..).unwrap_or_default()) {
                            apply(part);
                        }
                        return;
                    }
                    _ => return,
                }
            }
            if let Agg::Static(value) = cur {
                apply(value);
            }
        }
        _ => {}
    }
}

/// The node of `a` at the numbers `keys`, if the path stays inside container nodes.
fn node_at<'a>(a: &'a mut Agg, keys: &[usize]) -> Option<&'a mut Agg> {
    let mut cur = a;
    for &k in keys {
        cur = match cur {
            Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) => p.0.get_mut(k)?,
            _ => return None,
        };
    }
    Some(cur)
}

/// The local `root` twice, for a write that binds it again at the numbers `keys`: the copy that
/// the write consumes, and the local itself, which goes to the log. The copy has no part at
/// `keys` when the path stays inside container nodes, so the clone costs the rest of the local
/// and not the part that the write replaces. A path that ends inside a static part clones that
/// part with the replaced element, and a static local clones as a whole.
///
/// The clone costs at most the size of the local. The charge of a hardware write is the new size
/// of the root, which covers the rest. A static local with a waiting read is held, so the write
/// charges its size before it. A write that leaves an aggregate root with no hardware leaf turns
/// the root static, and a static root becomes an aggregate again only by a write that charges
/// its new size. Thus the clone of a write with a lower charge is paid once for each build of the
/// aggregate root, by the charge that built it. The clone comes after the charges of the write.
pub(super) fn split_root(root: Val, keys: &[usize]) -> (Val, Val) {
    match root {
        Val::Agg(mut a) => {
            let taken =
                node_at(&mut a, keys).map(|part| std::mem::replace(part, Agg::Static(Value::Unit)));
            let copy = (*a).clone();
            if let Some(part) = taken
                && let Some(slot) = node_at(&mut a, keys)
            {
                *slot = part;
            }
            (Val::Agg(Box::new(copy)), Val::Agg(a))
        }
        other => (other.clone(), other),
    }
}

impl Store {
    /// A read parks at the local: the mark of its window.
    pub(super) fn open_log(&mut self, root: Root) -> Mark {
        let log = self.history.entry(root).or_insert_with(History::new);
        log.open += 1;
        Mark {
            root,
            at: log.entries.len(),
        }
    }

    /// A read at the local resumed. The last one clears the log.
    pub(super) fn close_log(&mut self, root: Root) {
        if let Some(log) = self.history.get_mut(&root) {
            log.open = log.open.saturating_sub(1);
            if log.open == 0 {
                self.history.remove(&root);
            }
        }
    }

    /// The number of entries in the log of the local.
    fn logged(&self, root: Root) -> usize {
        self.history.get(&root).map_or(0, |log| log.entries.len())
    }

    /// The numbers of the nodes on the path `keys`, if a read waits at the local and so a change
    /// must go to the log. They come before the change.
    pub(super) fn stats_before(&self, root: Root, keys: &[usize]) -> Option<Vec<(u64, u64)>> {
        self.history.get(&root)?;
        Some(match self.root(&root) {
            Val::Agg(a) => node_stats(a, keys),
            _ => Vec::new(),
        })
    }

    /// Whether a read waits at the local, so that a change goes to the log.
    pub(super) fn is_logged(&self, root: Root) -> bool {
        self.history.contains_key(&root)
    }

    /// Appends the change `e` to the log of the local.
    pub(super) fn log_edit(&mut self, root: Root, e: Entry) {
        if let Some(log) = self.history.get_mut(&root) {
            log.append(e);
        }
    }

    /// The position of the entry in the window that starts the old part at `path` of the local:
    /// the earliest entry that replaced it or a part above it.
    fn restart_of(&self, mark: Mark, path: &[usize]) -> Option<usize> {
        self.history
            .get(&mark.root)?
            .start(path, mark.at)
            .map(|s| s.pos)
    }

    /// Whether the window has an entry that replaced the part at `path` of the local or a part
    /// above it.
    pub(super) fn restarted(&self, mark: Mark, path: &[usize]) -> bool {
        self.restart_of(mark, path).is_some()
    }

    /// The old local in the log for the part at `path`, if a write that bound the local again
    /// started the old part. The hold decisions of a read walk it in place of a copy.
    pub(super) fn old_root(&self, mark: Mark, path: &[usize]) -> Option<&Val> {
        let log = self.history.get(&mark.root)?;
        log.saved(log.start(path, mark.at)?.pos)
    }

    /// Whether the log has entries from the mark on.
    fn changed_since(&self, mark: Mark) -> bool {
        self.logged(mark.root) > mark.at
    }

    /// Takes the read parked at `at` back. A read that follows the steps of its index at a part
    /// of an aggregate root and holds no root keeps its window until `finish`, so that its steps
    /// walk the root and the result resolves once at its last step (`Evaluator::resolve_ref`).
    /// While no change replaced the part or a part above it, the steps walk the live root. After
    /// a write that bound the root again, they walk the old root in the log (`View`), so the
    /// read copies only the part that it ends at. Any other read resolves now: its steps go on
    /// from the old value.
    pub(super) fn unpark(&mut self, at: usize) -> (Out, Option<Mark>) {
        let quiet = matches!(self.held_by.get(at), Some(None));
        let cursor = self.cursors.get_mut(at).and_then(Option::take);
        let (outs, marks) = self.release(at);
        let out = outs
            .into_iter()
            .next()
            .unwrap_or(Out::Made(Val::Static(crate::value::Value::Unit)));
        let mut marks = marks.into_iter();
        let mark = marks.next().flatten();
        for later in marks.flatten() {
            self.close_log(later.root);
        }
        let Some(mark) = mark else {
            return (out, None);
        };
        if let (true, Some(c), Out::Ref(_)) = (quiet, &cursor, &out) {
            match self.restart_of(mark, c.waits_at()) {
                None if self.changed_since(mark) => return (out, Some(mark)),
                None => {
                    self.close_log(mark.root);
                    return (out, None);
                }
                Some(pos)
                    if self
                        .history
                        .get(&mark.root)
                        .and_then(|l| l.saved(pos))
                        .is_some() =>
                {
                    self.view = Some(View {
                        root: mark.root,
                        pos,
                    });
                    return (out, Some(mark));
                }
                Some(_) => {}
            }
        }
        let out = self.resolved(out, mark);
        self.close_log(mark.root);
        (out, None)
    }

    /// The read resolved: its window and its view are not needed any more.
    pub(super) fn finish(&mut self, mark: &Mark) {
        self.view = None;
        self.close_log(mark.root);
    }

    /// The old local that the walk of a read finds in place of the live `root`, if a view is
    /// set for it.
    pub(super) fn viewed(&self, root: &Root) -> Option<&Val> {
        let view = self.view.as_ref()?;
        if view.root != *root {
            return None;
        }
        self.history.get(root)?.saved(view.pos)
    }

    /// The part at `path` of the local, as it was at the mark of a read, if a change in its
    /// window reached it. A part that no change reaches is the same as the live part, so it
    /// needs no copy.
    pub(super) fn old_part(&self, mark: Mark, path: &[usize]) -> Option<Val> {
        let log = self.history.get(&mark.root)?;
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Logged, 1);
        let start = log.start(path, mark.at);
        let below = log.window(path, mark.at);
        let upto = start
            .as_ref()
            .map_or(below.len(), |s| below.partition_point(|&p| p < s.pos));
        let undo = below.get(..upto).unwrap_or_default();
        if start.is_none() && undo.is_empty() {
            return None;
        }
        let mut v = match &start {
            None => Store::own(self.current(mark.root, path)),
            Some(s) => {
                let rel = path.get(s.used..)?;
                match &log.entries.get(s.pos)?.change {
                    Change::Pop { saved: part, .. } | Change::Replace(part) => {
                        Store::own(crate::hw::Seen::Static(self.element(part, rel)))
                    }
                    Change::Rebind(old) => Store::own(self.part_of(old, rel)),
                    Change::Push => return None,
                }
            }
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Logged, undo.len() as u64);
        for e in undo.iter().rev().filter_map(|&p| log.entries.get(p)) {
            #[cfg(test)]
            crate::counters::add(
                crate::counters::Count::Copies,
                match &e.change {
                    Change::Push | Change::Rebind(_) => 0,
                    Change::Pop { saved: w, .. } | Change::Replace(w) => w.size(),
                },
            );
            undo_in(&mut v, path.len(), e);
        }
        Some(v)
    }

    /// The result `out`, as the window of the read at `mark` left the part it refers to: a part
    /// that a change reached becomes a copy of its old value, which still holds the local
    /// (`Out::Kept`), and any other result stays as it is.
    pub(super) fn resolved(&self, out: Out, mark: Mark) -> Out {
        let Out::Ref(r) = out else {
            return out;
        };
        if r.root != mark.root {
            return Out::Ref(r);
        }
        match self.old_part(mark, &r.path) {
            Some(v) => Out::Kept(v, mark.root),
            None => Out::Ref(r),
        }
    }
}

impl Evaluator<'_> {
    /// The result `out` of a read, as the window left the part it refers to. No step of a read
    /// goes into a list that its window changed: a list has no hardware leaf, so the segment of
    /// the read ends before the index into it, and the part before the index resolves here.
    pub(super) fn resolve_ref(&mut self, mark: Option<&Mark>, out: Out) -> Out {
        let Some(mark) = mark else {
            return out;
        };
        self.store.resolved(out, *mark)
    }
}
