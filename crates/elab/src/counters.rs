// SPDX-License-Identifier: Apache-2.0
//! The counters of the work of the walks and the operations, for the tests. A test of the work
//! counts the nodes that a walk visits and the bytes that an operation makes, so it checks the
//! work and not the time. A run counts into the entry of its fuel budget, and a test finds its
//! run by a fuel that no other test uses, as it finds its copies. Thus the tests agree under
//! `cargo test`, where they share a process, as under `nextest`.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::sync::Mutex;

/// The work of one run.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counts {
    /// The scalars that the charged scans of strings visited.
    pub scanned: u64,
    /// The digits that the conversions of `str` made.
    pub converted: u64,
    /// The nodes that `Value::size` and `Value::depth` visited.
    pub walked: u64,
    /// The bytes that the join of two strings made.
    pub joined: u64,
    /// The bytes of text that the serialization of a static value wrote.
    pub serialized: u64,
    /// The nodes that `Value::holds_fn` visited.
    pub flagged: u64,
    /// The parameter types and result types that the function types made.
    pub params: u64,
    /// The windows of places that opened and closed.
    pub windows: u64,
}

/// What a counter counts.
#[derive(Clone, Copy)]
pub(crate) enum Count {
    Scanned,
    Converted,
    Walked,
    Joined,
    Serialized,
    Flagged,
    Params,
    Windows,
}

static COUNTS: Mutex<BTreeMap<u64, Counts>> = Mutex::new(BTreeMap::new());

thread_local! {
    /// The fuel budget of the run that this thread works for.
    static RUN: Cell<Option<u64>> = const { Cell::new(None) };
}

/// Starts the counts of the run with the fuel budget `fuel` on this thread. A thread that the
/// run starts later joins with `join`.
pub(crate) fn start(fuel: u64) {
    if let Ok(mut counts) = COUNTS.lock() {
        counts.insert(fuel, Counts::default());
    }
    join(fuel);
}

/// Makes this thread count into the run with the fuel budget `fuel`.
pub(crate) fn join(fuel: u64) {
    RUN.with(|run| run.set(Some(fuel)));
}

/// Adds `n` to the count of the run of this thread. Work outside a run counts nowhere.
pub(crate) fn add(count: Count, n: u64) {
    let Some(fuel) = RUN.with(Cell::get) else {
        return;
    };
    if let Ok(mut counts) = COUNTS.lock()
        && let Some(c) = counts.get_mut(&fuel)
    {
        let field = match count {
            Count::Scanned => &mut c.scanned,
            Count::Converted => &mut c.converted,
            Count::Walked => &mut c.walked,
            Count::Joined => &mut c.joined,
            Count::Serialized => &mut c.serialized,
            Count::Flagged => &mut c.flagged,
            Count::Params => &mut c.params,
            Count::Windows => &mut c.windows,
        };
        *field += n;
    }
}

/// The counts of the last run with the fuel budget `fuel`.
pub(crate) fn of(fuel: u64) -> Counts {
    COUNTS
        .lock()
        .ok()
        .and_then(|counts| counts.get(&fuel).copied())
        .unwrap_or_default()
}
