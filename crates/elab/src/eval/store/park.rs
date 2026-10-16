// SPDX-License-Identifier: Apache-2.0
//! The results that wait while a later operand evaluates, and the holds of the locals that
//! they refer to.

use super::{Mark, Store};
use crate::eval::Out;
use crate::hw::{Root, Seen, Val};
use crate::value::Value;

impl Store {
    /// Parks the result `o` while a later operand of its node evaluates. It returns the
    /// position to resume from. A reference to a local opens a window of the history of the
    /// local, so that a change of the local goes to the log and the resume of the reference
    /// finds the old value there.
    pub(in crate::eval) fn park(&mut self, o: Out) -> usize {
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

    /// Takes the results parked from the position `from` out of the table, with their marks, and
    /// ends the holds and the cursors of their positions. The windows stay open: the caller
    /// closes each one after it reads the history.
    pub(super) fn release(&mut self, from: usize) -> (Vec<Out>, Vec<Option<Mark>>) {
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
    pub(in crate::eval) fn resume(&mut self, from: usize) -> Vec<Out> {
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
    pub(in crate::eval) fn resume_one(&mut self, at: usize) -> Out {
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

    /// Whether a parked result holds the local at `root` (section 5.4).
    pub(in crate::eval) fn is_held(&mut self, root: Root) -> bool {
        self.decide_holds(root);
        self.holds.contains_key(&root)
    }
}
