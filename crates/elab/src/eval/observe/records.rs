// SPDX-License-Identifier: Apache-2.0
//! The list of the records of `diagnostic` (section 8.2), with the records of the early keys of
//! the reads and places that wait for their walk (`mark_early` in `eval/place`).

use super::super::{Res, Stop};
use crate::Code;
use parse::ast::Pos;

/// The records in evaluation order. A key with a call can evaluate before the walk checks the
/// steps before it. Lean checks those steps first, so the records of such a key are pending until
/// its walk: the walk keeps the records of the keys whose steps passed, and it drops the others.
/// A record that is kept is never taken back. An early key also uses fuel and can change other
/// locals before the check, so the failed check must end the run (`finish`).
#[derive(Default)]
pub(in crate::eval) struct Records {
    kept: Vec<String>,
    pending: Vec<String>,
    /// The number of walks with early keys that have not ended. A walk can wait inside the key of
    /// another, so its records stay pending until the outermost one ends.
    open: usize,
    /// The failed check that dropped the records of an early key and that must end the run.
    dropped: Option<Dropped>,
}

/// A failed check that dropped the records of an early key: its code, its position, and its mark
/// in the pending records while they are pending.
#[derive(Clone, Copy)]
struct Dropped {
    code: Code,
    pos: Pos,
    mark: Option<usize>,
}

impl Records {
    /// Adds the record `text`: pending while an early key evaluates, else kept.
    pub(in crate::eval) fn push(&mut self, text: String) {
        if self.open > 0 {
            self.pending.push(text);
        } else {
            self.kept.push(text);
        }
    }

    /// Opens the pending records of the walk whose first early key evaluates now.
    pub(in crate::eval) fn open(&mut self) {
        self.open += 1;
    }

    /// The mark of the records that an early key makes from now on.
    pub(in crate::eval) fn mark(&self) -> usize {
        self.pending.len()
    }

    /// The walk that `open` started ended. With `cut`, a step before an early key failed its
    /// check `failed`, so the records from the mark `cut` go: Lean never evaluated that key. A
    /// check that failed inside that key goes with them, as Lean never ran it, so the run must
    /// end with `failed`. The pending records become kept when no walk is open any more.
    pub(in crate::eval) fn close(&mut self, cut: Option<(usize, &Stop)>) {
        if let Some((mark, Stop::Error(e))) = cut {
            self.pending.truncate(mark);
            let inside = |d: &Dropped| d.mark.is_some_and(|m| mark <= m);
            if self.dropped.as_ref().is_none_or(inside) {
                self.dropped = Some(Dropped {
                    code: e.code,
                    pos: e.pos,
                    mark: Some(mark),
                });
            }
        }
        debug_assert!(self.open > 0, "a walk closes that did not open");
        self.open -= 1;
        if self.open == 0 {
            self.kept.append(&mut self.pending);
            if let Some(d) = self.dropped.as_mut() {
                d.mark = None;
            }
        }
    }

    /// The kept records at the end of the run with the result `outcome`. A check that dropped
    /// the records of an early key ends the run with its error. A run that went on after it, for
    /// example after an error that a later rule recovers from, would show the early key: its
    /// fuel, its changes, or its records. The assertion then fails, and the early key must wait
    /// for the check.
    pub(in crate::eval) fn finish<T>(&mut self, outcome: &Res<T>) -> Vec<String> {
        debug_assert!(
            ended(self.dropped, outcome),
            "a failed check after an early key did not end the run"
        );
        debug_assert!(
            self.open == 0 && self.pending.is_empty(),
            "a walk is still open"
        );
        std::mem::take(&mut self.kept)
    }
}

/// Whether the run with the result `outcome` ended at the failed check `dropped`, if one dropped
/// the records of an early key.
fn ended<T>(dropped: Option<Dropped>, outcome: &Res<T>) -> bool {
    match dropped {
        None => true,
        Some(d) => matches!(outcome, Err(Stop::Error(e)) if e.code == d.code && e.pos == d.pos),
    }
}
