// SPDX-License-Identifier: Apache-2.0
//! The counters of the work of the walks over values, for the tests. A test of the work counts
//! the nodes that a walk visits and the bytes that an operation makes, so it checks the work
//! and not the time. Each counter is global, and `nextest` runs each test in its own process,
//! so a test reads the work of its own run.

use std::sync::atomic::{AtomicU64, Ordering};

/// The nodes that `Value::size` and `Value::depth` visited.
pub(crate) static WALKED: AtomicU64 = AtomicU64::new(0);

/// The bytes that the join of two strings made.
pub(crate) static JOINED: AtomicU64 = AtomicU64::new(0);

/// The bytes of text that the serialization of a static value wrote.
pub(crate) static SERIALIZED: AtomicU64 = AtomicU64::new(0);

/// Adds `n` to the counter.
pub(crate) fn add(counter: &AtomicU64, n: u64) {
    counter.fetch_add(n, Ordering::Relaxed);
}

/// The count of the counter.
pub(crate) fn get(counter: &AtomicU64) -> u64 {
    counter.load(Ordering::Relaxed)
}
