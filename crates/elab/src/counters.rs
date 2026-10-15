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
    /// The operands that the check of `==` read the function flag of.
    pub flagged: u64,
    /// The parameter types and result types that the function types made.
    pub params: u64,
    /// The windows of places that opened and closed.
    pub windows: u64,
    /// The pairs of values and of types that an equality or a typed use compared. A type pair
    /// compares two ids.
    pub compared: u64,
    /// The pairs of types that the join of two types visited.
    pub visited: u64,
    /// The nodes of an aggregate that a build or a clone visited.
    pub nodes: u64,
    /// The parts that a selection on an aggregate took.
    pub selected: u64,
    /// The parts that the typed use of an aggregate checked and converted.
    pub typed: u64,
    /// The parts that the binding of an aggregate visited, and the leaves that it made lets for.
    pub bound: u64,
    /// The parts that a reference on the path of a place expanded into.
    pub expanded: u64,
    /// The pairs that the walk of a hardware equality or of a hardware `if` charged.
    pub paired: u64,
    /// The parts that a walk over the leaves of a type visited.
    pub leaves: u64,
    /// The nodes that the path arena gained.
    pub paths: u64,
    /// The containers that a walk along a path into a stored value entered.
    pub stepped: u64,
    /// The steps of work of the table of types: its lookups, and the walks of `Value::ty`.
    pub table: u64,
    /// The expression nodes that scans of the AST visited. The pass before the evaluation scans
    /// each node once. An evaluation that scans an expression again counts here too.
    pub ast: u64,
    /// The lookups of the prefix offset of a part in a word, one for each step on a word.
    pub offsets: u64,
    /// The steps of the loop that builds the write chain of a memory: one for each leaf.
    pub chained: u64,
    /// The core nodes of the memory block, apart from the write chain, that the lowering charged.
    pub blocked: u64,
    /// The second calls of a port that recorded their `S018`.
    pub seconds: u64,
    /// The pieces that the walk of the text of a record visited. The walk runs twice for a
    /// record: once to count its bytes and once to write them.
    pub rendered: u64,
    /// The pieces of the walk of the text of a record that are a leaf: a static value, a
    /// hardware leaf, a name, or a type.
    pub rendered_leaves: u64,
    /// The frames that the walk of the text of a record wrote out.
    pub framed: u64,
    /// The records that `diagnostic` appended.
    pub recorded: u64,
    /// The guards that a hardware arm or a structural context entered.
    pub guarded: u64,
    /// The bytes of a name that the walks of `diagnostic` and the reads of a domain copied into
    /// a new string, outside the text of a record.
    pub copied: u64,
    /// The types that a serialization to a sink without the stored length expanded part by
    /// part. A length pass never expands one.
    pub unfolded: u64,
    /// The bytes of the decimal form of the integers that a run formatted.
    pub formatted: u64,
    /// The powers of ten that the exact check of a digit count built.
    pub powered: u64,
    /// The waiting reads that a change of an aggregate root visited.
    pub settled: u64,
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
    Compared,
    Visited,
    Nodes,
    Selected,
    Typed,
    Bound,
    Expanded,
    Paired,
    Leaves,
    Paths,
    Stepped,
    Table,
    Ast,
    Offsets,
    Chained,
    Blocked,
    Seconds,
    Rendered,
    RenderedLeaves,
    Framed,
    Recorded,
    Guarded,
    Copied,
    Unfolded,
    Formatted,
    Powered,
    Settled,
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

/// The fuel budget of the run that this thread counts into. A thread that works for the run
/// later, such as the lowering thread, joins it with `join`.
pub(crate) fn current() -> Option<u64> {
    RUN.with(Cell::get)
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
            Count::Compared => &mut c.compared,
            Count::Visited => &mut c.visited,
            Count::Nodes => &mut c.nodes,
            Count::Selected => &mut c.selected,
            Count::Typed => &mut c.typed,
            Count::Bound => &mut c.bound,
            Count::Expanded => &mut c.expanded,
            Count::Paired => &mut c.paired,
            Count::Leaves => &mut c.leaves,
            Count::Paths => &mut c.paths,
            Count::Stepped => &mut c.stepped,
            Count::Table => &mut c.table,
            Count::Ast => &mut c.ast,
            Count::Offsets => &mut c.offsets,
            Count::Chained => &mut c.chained,
            Count::Blocked => &mut c.blocked,
            Count::Seconds => &mut c.seconds,
            Count::Rendered => &mut c.rendered,
            Count::RenderedLeaves => &mut c.rendered_leaves,
            Count::Framed => &mut c.framed,
            Count::Recorded => &mut c.recorded,
            Count::Guarded => &mut c.guarded,
            Count::Copied => &mut c.copied,
            Count::Unfolded => &mut c.unfolded,
            Count::Formatted => &mut c.formatted,
            Count::Powered => &mut c.powered,
            Count::Settled => &mut c.settled,
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
