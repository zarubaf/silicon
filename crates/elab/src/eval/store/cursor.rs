// SPDX-License-Identifier: Apache-2.0
//! The cursors of the reads that wait at a part of an aggregate root, and the decision of
//! their holds.

use super::Store;
use crate::agg::Agg;
use crate::hw::{Ref, Root, Val};

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

impl Store {
    /// The read parked at `at` waits at the part `r` of a local. With `live`, the part is in an
    /// aggregate root and a later index with a call may hold the root there. Without it, the
    /// part is in a static local: it decides no hold, since a reference to a part of a static
    /// local holds it already, but it keeps the trail of its steps.
    pub(in crate::eval) fn cursor(&mut self, at: usize, r: Ref, live: bool) {
        if let Some(slot) = self.cursors.get_mut(at) {
            *slot = Some(Cursor {
                base: r.path.len(),
                part: r,
                witness: None,
                left: 0,
                trail: Vec::new(),
                exact: true,
                live,
            });
        }
    }

    /// The walk of the read takes the step `k` from the part of the cursor at `at`. A step with no
    /// number ends the cursor, because no static part follows it.
    pub(in crate::eval) fn cursor_step(&mut self, at: usize, k: Option<usize>) {
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
    pub(in crate::eval) fn arm(&mut self, at: usize, left: usize) {
        if let Some(Some(c)) = self.cursors.get_mut(at)
            && c.live
        {
            c.left = left;
            let root = c.part.root;
            self.armed.entry(root).or_default().push(at);
        }
    }

    /// The index of the read at `at` finished. A decision that a change made stays made.
    pub(in crate::eval) fn disarm(&mut self, at: usize) {
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
    ///
    /// Each method that changes a local calls it first, and a decision made stays made, so the
    /// store decides the holds before the first change whatever the caller did before.
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
                Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) | Agg::List(_, p) => {
                    self.stepped(1);
                    match p.0.get(k) {
                        Some(x) => x,
                        None => return Located::Static,
                    }
                }
                Agg::Static(_) => return Located::Static,
                Agg::Hw(_) | Agg::Ref(..) | Agg::Handle(_) => return closed_at(i),
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
                Agg::Hw(_) | Agg::Ref(..) | Agg::Handle(_) => {
                    witness.closed = true;
                    break;
                }
                Agg::Array(n, p) | Agg::Tuple(n, p) | Agg::Record(n, p) | Agg::List(n, p) => {
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
}
