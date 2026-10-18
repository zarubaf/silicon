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
//! A waiting read copies at most the part where it ends. The exceptions are these:
//!
//! - A step of the read goes into a list or a part that a change reached (`Walk::Split`). The
//!   first steps walk the live local. An index in the old range of the list, which the log gives
//!   (`Store::old_len`), copies only the element. Else the read copies the list as it was, and
//!   the check of the step fails on it. An index that changed its own root pays for the size of
//!   its result before the result is a new value (#237). The element that a `pop` took out is
//!   the saved value of that `pop`, so a read of it takes the same way. A step into a part that
//!   a write replaced above the read copies the part where the read waits (`Walk::Copy`).
//! - A write that binds an aggregate root again copies the rest of the root once (`split_root`).
//!   A hardware write pays it in its charge. A write that leaves no hardware leaf turns the root
//!   static, and a root becomes an aggregate again only by a charge of its new size.
//! - A write that binds a static root again with a hardware leaf copies the whole root. The root
//!   is held while a read waits, so the write charges its size first.
//!
//! Every other path copies nothing or the part where the read ends: a resume of a reference, a
//! hold decision (it walks the live root, as a read ends at the index that changes it), a view of
//! the old root, an error, and a frame that ends.
//!
//! Every walk keeps to the path of a place, and no walk recurses over the depth of a value.

use super::{Cursor, Store};
use crate::agg::Agg;
use crate::eval::Out;
use crate::hw::{Root, Val};
use crate::value::Value;
use std::collections::BTreeMap;

/// A change of a local.
enum Change {
    /// A `push`, and the length that the list had before.
    Push { len: usize },
    /// A `pop`: the element that left, and the length that the list had before.
    Pop { saved: Agg, len: usize },
    /// A write into the part of a static local: the part that left.
    Replace(Value),
    /// A write that binds the local again: the local that left.
    Rebind(Val),
}

/// A change of the part at `keys`.
struct Edit {
    keys: Vec<usize>,
    change: Change,
    /// The size and the depth of each aggregate node on the path before a `Push` or a `Pop`,
    /// from the root, so that a copy gets the stored numbers of its nodes back.
    stats: Vec<(u64, u64)>,
}

impl Edit {
    /// A `push` into the list at `keys`, which had `len` elements.
    fn push(keys: Vec<usize>, len: usize, stats: Vec<(u64, u64)>) -> Edit {
        Edit {
            keys,
            change: Change::Push { len },
            stats,
        }
    }

    /// A `pop` of the list at `keys`, which had `len` elements.
    fn pop(keys: Vec<usize>, saved: Agg, len: usize, stats: Vec<(u64, u64)>) -> Edit {
        Edit {
            keys,
            change: Change::Pop { saved, len },
            stats,
        }
    }

    /// A write that replaced the part of a static local at `keys`.
    fn replace(keys: Vec<usize>, old: Value) -> Edit {
        Edit {
            keys,
            change: Change::Replace(old),
            stats: Vec::new(),
        }
    }

    /// A write that bound the whole local again.
    fn rebind(old: Val) -> Edit {
        Edit {
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
    /// The entries whose path is the path of the node.
    here: Vec<usize>,
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
    entries: Vec<Edit>,
    /// The index by path. The node 0 is the root.
    nodes: Vec<Node>,
    open: usize,
    /// The last old part that a read resolved, for each path. Reads of one part replay each entry
    /// of the log once, if they resolve the latest mark first. There is one memo for each path
    /// that a read resolved, so the reads of other parts do not evict it. An appended entry
    /// clears them, and they go with the log when the last read resumes.
    memo: BTreeMap<Vec<usize>, Memo>,
}

/// An old part that a read resolved: the mark position, the entry that started the part, and
/// the part. A read with an earlier mark continues from it.
struct Memo {
    at: usize,
    from: Option<usize>,
    part: Val,
}

impl History {
    fn new() -> History {
        History {
            entries: Vec::new(),
            nodes: vec![Node::default()],
            open: 0,
            memo: BTreeMap::new(),
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
    fn append(&mut self, e: Edit) {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Logged, 1);
        self.memo.clear();
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
            node.here.push(pos);
            match &e.change {
                Change::Replace(_) | Change::Rebind(_) => node.own.push(pos),
                Change::Pop { len, .. } => node.pops.entry(*len).or_default().push(pos),
                Change::Push { .. } => {}
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

    /// The depth of the first node, from the depth `from` on, where a walk down `path` passes an
    /// entry from `mark` on and before `before` that has the path of the node. Such an entry
    /// changes a list or a part that the steps of a read go through.
    fn first_crossed(
        &self,
        path: &[usize],
        from: usize,
        mark: usize,
        before: usize,
    ) -> Option<usize> {
        let mut at = Some(0usize);
        for d in 0..path.len() {
            let node = at.and_then(|n| self.nodes.get(n))?;
            if d >= from && first_from(&node.here, mark).is_some_and(|pos| pos < before) {
                return Some(d);
            }
            at = path.get(d).and_then(|k| node.children.get(k)).copied();
        }
        None
    }

    /// The length that the list at `path` had at `mark`: the length before its first `push` or
    /// `pop` from `mark` on. It is the length of the list as the read found it, if no write
    /// replaced the list or a part above it (`start`).
    fn old_len(&self, path: &[usize], mark: usize) -> Option<usize> {
        let node = self.node(path)?;
        let pos = first_from(&node.here, mark)?;
        match self.entries.get(pos)?.change {
            Change::Push { len } | Change::Pop { len, .. } => Some(len),
            _ => None,
        }
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
                .and_then(|k| k.checked_add(1).and_then(|len| node.pops.get(&len)))
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

/// The state of a local before a change of a list, which the log entry of the change needs
/// (`Store::before_list_edit`). It holds the local, the path, and the length of the list that it
/// was made for, so the log entry cannot name another change. It holds nothing while no read
/// waits at the local.
pub(in crate::eval) struct Before(Option<Pending>);

struct Pending {
    root: Root,
    keys: Vec<usize>,
    len: usize,
    stats: Vec<(u64, u64)>,
}

/// A read that waits at a part of a local: the local, and the length of its log when the read
/// parked. The window of the read is the entries from there on. The log lives while a read
/// waits, so a mark never outlives its log.
#[derive(Clone, Copy)]
pub(in crate::eval) struct Mark {
    pub(super) root: Root,
    at: usize,
}

/// How the steps of a read walk (`Store::walk_of`).
enum Walk {
    Live,
    Old(usize),
    /// The first steps walk the live local up to the list that a change reached.
    Split(usize),
    Copy,
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

/// The size and the depth of each aggregate node of `root` on the path `keys`, from the root. A
/// list node at the end of the path counts too, because a `push` and a `pop` change its numbers.
fn node_stats(root: &Agg, keys: &[usize]) -> Vec<(u64, u64)> {
    let mut stats = Vec::new();
    let mut cur = root;
    for &k in keys {
        let (Agg::Array(n, p) | Agg::Tuple(n, p) | Agg::Record(n, p) | Agg::List(n, p)) = cur
        else {
            return stats;
        };
        stats.push((n.size, n.depth));
        match p.0.get(k) {
            Some(x) => cur = x,
            None => return stats,
        }
    }
    if let Agg::List(n, _) = cur {
        stats.push((n.size, n.depth));
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
fn undo_in(copy: &mut Val, at: usize, e: &Edit) {
    let rel = e.keys.get(at..).unwrap_or_default();
    let apply = |part: &mut Value| match (&e.change, part) {
        (Change::Push { .. }, Value::List(_, ys)) => {
            ys.pop();
        }
        (
            Change::Pop {
                saved: Agg::Static(saved),
                ..
            },
            Value::List(_, ys),
        ) => ys.push(saved.clone()),
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
                    | Agg::Record(node, parts)
                    | Agg::List(node, parts) => {
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
            match cur {
                Agg::Static(value) => apply(value),
                Agg::List(node, parts) => {
                    if let Some(&(size, depth)) = e.stats.get(at + rel.len()) {
                        node.size = size;
                        node.depth = depth;
                    }
                    match &e.change {
                        Change::Push { .. } => {
                            parts.0.pop();
                        }
                        Change::Pop { saved, .. } => parts.0.push(saved.clone()),
                        _ => {}
                    }
                }
                _ => {}
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
            Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) | Agg::List(_, p) => {
                p.0.get_mut(k)?
            }
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
fn split_root(root: Val, keys: &[usize]) -> (Val, Val) {
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
    fn stats_before(&self, root: Root, keys: &[usize]) -> Option<Vec<(u64, u64)>> {
        self.history.get(&root)?;
        Some(match self.root(&root) {
            Val::Agg(a) => node_stats(a, keys),
            _ => Vec::new(),
        })
    }

    /// Whether a read waits at the local, so that a change goes to the log.
    fn is_logged(&self, root: Root) -> bool {
        self.history.contains_key(&root)
    }

    /// Appends the change `e` to the log of the local.
    fn log_edit(&mut self, root: Root, e: Edit) {
        if let Some(log) = self.history.get_mut(&root) {
            log.append(e);
        }
    }

    /// The state of the local at `root` before a `push` or a `pop` along `keys` of a list that
    /// has `len` elements. It comes before the change. The change then goes through
    /// `push_static` or `take_agg` with `put_back` (`pop_static` for a `pop`), and the caller
    /// logs it with `log_push` or `log_pop` on this token.
    pub(in crate::eval) fn before_list_edit(
        &self,
        root: Root,
        keys: &[usize],
        len: usize,
    ) -> Before {
        Before(self.stats_before(root, keys).map(|stats| Pending {
            root,
            keys: keys.to_vec(),
            len,
            stats,
        }))
    }

    /// Logs the `push` that `before` was made for, if a read waits at the local.
    pub(in crate::eval) fn log_push(&mut self, before: Before) {
        if let Some(p) = before.0 {
            self.log_edit(p.root, Edit::push(p.keys, p.len, p.stats));
        }
    }

    /// Logs the `pop` of `saved` that `before` was made for, if a read waits at the local.
    pub(in crate::eval) fn log_pop(&mut self, before: Before, saved: &Agg) {
        if let Some(p) = before.0 {
            self.log_edit(p.root, Edit::pop(p.keys, saved.clone(), p.len, p.stats));
        }
    }

    /// Writes `w` over the part of the static local at `keys`, and logs the part that left if a
    /// read waits at the local.
    pub(in crate::eval) fn replace_part(&mut self, root: Root, keys: &[usize], w: Value) {
        self.decide_holds(root);
        if let Some(part) = self.part_mut(root, keys) {
            let old = std::mem::replace(part, w);
            if self.is_logged(root) {
                self.log_edit(root, Edit::replace(keys.to_vec(), old));
            }
        }
    }

    /// Binds the local at `root` again to `y`, and logs the value that left if a read waits at
    /// the local.
    pub(in crate::eval) fn rebind_local(&mut self, root: Root, y: Val) {
        self.decide_holds(root);
        if let Root::Local(frame, id) = root
            && let Some(slot) = self.frames.get_mut(frame).and_then(|f| f.get_mut(&id))
        {
            let old = std::mem::replace(&mut slot.value, y);
            self.log_edit(root, Edit::rebind(old));
        }
    }

    /// Takes the local at `root` out of its slot for a write that binds it again at `keys`. If a
    /// read waits at the local, the log keeps the old local and the caller gets a copy to build
    /// the new one from. The caller gives the new local back with `put_back`.
    pub(in crate::eval) fn take_for_rebind(&mut self, root: Root, keys: &[usize]) -> Val {
        self.decide_holds(root);
        let local = self.take_root(&root);
        if self.is_logged(root) {
            let (work, saved) = split_root(local, keys);
            self.log_edit(root, Edit::rebind(saved));
            work
        } else {
            local
        }
    }

    /// How the steps of the read parked at `at` walk, when it takes its result back. The steps
    /// walk the live local while no entry crossed them and none started the old part. They walk
    /// the old local in the log (`View`) when a write that bound the local again started it and
    /// no entry before that write crossed them. Otherwise the read copies the part where it
    /// waits, because a step goes into a list or a part that a change took out or replaced.
    fn walk_of(&self, mark: Mark, c: &Cursor, quiet: bool) -> Walk {
        let Some(log) = self.history.get(&mark.root) else {
            return Walk::Live;
        };
        let base = c.part.path.get(..c.base).unwrap_or_default();
        let ends = [base, &c.trail].concat();
        let path = if c.exact { &ends[..] } else { base };
        match log.start(path, mark.at) {
            None if !c.exact => {
                if quiet {
                    Walk::Live
                } else {
                    Walk::Copy
                }
            }
            None => match log.first_crossed(&ends, c.base, mark.at, usize::MAX) {
                Some(d) => Walk::Split(d - c.base),
                None => Walk::Live,
            },
            // A `pop` took out the element that the steps name, or a part above it. The read
            // walks the live local up to the list, and the saved element is the old part.
            Some(s) if log.saved(s.pos).is_none() => match log.entries.get(s.pos) {
                Some(Edit {
                    change: Change::Pop { .. },
                    ..
                }) if c.exact && s.used > c.base => Walk::Split(s.used - 1 - c.base),
                _ => Walk::Copy,
            },
            Some(s) => {
                let clear = if c.exact {
                    log.first_crossed(&ends, c.base, mark.at, s.pos).is_none()
                } else {
                    quiet && log.window(base, mark.at).first() == Some(&s.pos)
                };
                if clear { Walk::Old(s.pos) } else { Walk::Copy }
            }
        }
    }

    /// The length that the list at `path` had when the read at `mark` parked, if a `push` or a
    /// `pop` of the list is in its window. The read then checks an index against this length and
    /// resolves the element, with no copy of the list.
    pub(in crate::eval) fn old_len(&self, mark: Mark, path: &[usize]) -> Option<usize> {
        self.history.get(&mark.root)?.old_len(path, mark.at)
    }

    /// Whether the log has entries from the mark on.
    fn changed_since(&self, mark: Mark) -> bool {
        self.logged(mark.root) > mark.at
    }

    /// Takes the read parked at `at` back, with its mark and the number of steps to walk before
    /// the copy. A read that follows the steps of its index at a part of a local keeps its window
    /// until `finish`, so that its steps walk the local and the result resolves once at its last
    /// step (`Evaluator::resolve_ref`). `walk_of` tells how the steps walk: the live local, the
    /// old local in the log (`View`), the live local up to a list that a change reached (the
    /// third result, and the copy is that list), or no walk, and the read resolves now.
    pub(in crate::eval) fn unpark(&mut self, at: usize) -> (Out, Option<Mark>, Option<usize>) {
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
            return (out, None, None);
        };
        if let (Some(c), Out::Ref(_)) = (&cursor, &out) {
            match self.walk_of(mark, c, quiet) {
                Walk::Live if self.changed_since(mark) => return (out, Some(mark), None),
                Walk::Live => {
                    self.close_log(mark.root);
                    return (out, None, None);
                }
                Walk::Split(head) => return (out, Some(mark), Some(head)),
                Walk::Old(pos) => {
                    self.view = Some(View {
                        root: mark.root,
                        pos,
                    });
                    return (out, Some(mark), None);
                }
                Walk::Copy => {}
            }
        }
        let out = self.resolved(out, mark);
        self.close_log(mark.root);
        (out, None, None)
    }

    /// The read resolved: its window and its view are not needed any more.
    pub(in crate::eval) fn finish(&mut self, mark: &Mark) {
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
    fn old_part(&mut self, mark: Mark, path: &[usize]) -> Option<Val> {
        let log = self.history.get(&mark.root)?;
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Logged, 1);
        let start = log.start(path, mark.at);
        let from = start.as_ref().map(|s| s.pos);
        let below = log.window(path, mark.at);
        let upto = from.map_or(below.len(), |pos| below.partition_point(|&p| p < pos));
        let undo = below.get(..upto).unwrap_or_default();
        if start.is_none() && undo.is_empty() {
            return None;
        }
        // A read that parked earlier continues the undo of a later read of the same part: the
        // entries from its mark on and before the mark of the later read are left to undo.
        let memo = log
            .memo
            .get(path)
            .filter(|m| m.from == from && mark.at <= m.at);
        let (mut v, undo) = match memo {
            Some(m) => (
                m.part.clone(),
                undo.get(..undo.partition_point(|&p| p < m.at))
                    .unwrap_or_default(),
            ),
            None => (self.old_start(mark, path, start.as_ref())?, undo),
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Logged, undo.len() as u64);
        for e in undo.iter().rev().filter_map(|&p| log.entries.get(p)) {
            #[cfg(test)]
            crate::counters::add(
                crate::counters::Count::Copies,
                match &e.change {
                    Change::Push { .. } | Change::Rebind(_) => 0,
                    Change::Pop { saved: w, .. } => super::static_size(w),
                    Change::Replace(w) => w.size(),
                },
            );
            undo_in(&mut v, path.len(), e);
        }
        // The memo serves another read that waits at the local. Without one, its clone is waste.
        if let Some(log) = self.history.get_mut(&mark.root).filter(|l| l.open > 1) {
            log.memo.insert(
                path.to_vec(),
                Memo {
                    at: mark.at,
                    from,
                    part: v.clone(),
                },
            );
        }
        Some(v)
    }

    /// The part at `path` before the undo: the live part, or the part that the entry `start`
    /// took out.
    fn old_start(&self, mark: Mark, path: &[usize], start: Option<&Start>) -> Option<Val> {
        let log = self.history.get(&mark.root)?;
        Some(match start {
            None => Store::own(self.current(mark.root, path)),
            Some(s) => {
                let rel = path.get(s.used..)?;
                match &log.entries.get(s.pos)?.change {
                    Change::Pop { saved: part, .. } => Store::own(self.agg_element(part, rel)),
                    Change::Replace(part) => {
                        Store::own(crate::hw::Seen::Static(self.element(part, rel)))
                    }
                    Change::Rebind(old) => Store::own(self.part_of(old, rel)),
                    Change::Push { .. } => return None,
                }
            }
        })
    }

    /// The result `out`, as the window of the read at `mark` left the part it refers to: a part
    /// that a change reached becomes a copy of its old value, which still holds the local
    /// (`Out::Kept`), and any other result stays as it is.
    pub(in crate::eval) fn resolved(&mut self, out: Out, mark: Mark) -> Out {
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
