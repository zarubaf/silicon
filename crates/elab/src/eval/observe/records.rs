// SPDX-License-Identifier: Apache-2.0
//! The list of the records of `diagnostic` (section 8.2), with the records of the early keys of
//! the reads and places that wait for their walk (`mark_early` in `eval/place`).

/// The records in evaluation order. A key with a call can evaluate before the walk checks the
/// steps before it. Lean checks those steps first, so the records of such a key are pending until
/// its walk: the walk keeps the records of the keys whose steps passed, and it drops the others.
/// A record that is kept is never taken back.
#[derive(Default)]
pub(in crate::eval) struct Records {
    kept: Vec<String>,
    pending: Vec<String>,
    /// The number of walks with early keys that have not ended. A walk can wait inside the key of
    /// another, so its records stay pending until the outermost one ends.
    open: usize,
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
    /// check, so the records from the mark `cut` go: Lean never evaluated that key. The pending
    /// records become kept when no walk is open any more.
    pub(in crate::eval) fn close(&mut self, cut: Option<usize>) {
        if let Some(mark) = cut {
            self.pending.truncate(mark);
        }
        self.open = self.open.saturating_sub(1);
        if self.open == 0 {
            self.kept.append(&mut self.pending);
        }
    }

    /// The kept records at the end of the run.
    pub(in crate::eval) fn take(&mut self) -> Vec<String> {
        std::mem::take(&mut self.kept)
    }
}
