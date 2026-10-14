// SPDX-License-Identifier: Apache-2.0
//! Generates slice-1 source programs for `diff-si`: lifted core designs
//! (`lift`) and typed programs (`build`).
//!
//! The lift fixes the source names, so the map from core vectors to source
//! vectors lives here too. The map is independent of `elab::vectors` on
//! purpose: the oracle of `diff-si` must not reuse the code under test, so
//! the layer order puts this crate before `parse` (ADR 0018).
//!
//! The builder makes typed programs in the form of `program` from a tape,
//! and `eval` computes their static values. The `twin` of a typed program
//! writes out each of its comptime constructs. `mutate` applies one
//! mutation to a typed program and predicts the first error code where the
//! pass order makes it certain.

mod build;
mod eval;
mod expr;
mod lift;
mod memory;
mod mutate;
mod program;
mod twin;

pub use build::{BuildFault, lines, typed};
pub use lift::{Unsupported, lift, vector_in, vector_out};
pub use mutate::{Mutant, mutate};
pub use program::{Ports, Program, Scalar};
pub use twin::{Twin, twin};

use std::fmt::Display;

/// The `in=` line of a source run: the domain reset `clock$0rst` first if
/// `reset` has a value, then the `pairs` of input name and value, in the
/// given order. No LF. Both generators write source vectors with it.
fn in_line<N: Display, V: Display>(
    reset: Option<bool>,
    pairs: impl IntoIterator<Item = (N, V)>,
) -> String {
    let reset = reset.map(|r| format!("clock$0rst {r}"));
    let pairs = pairs.into_iter().map(|(n, v)| format!("{n} {v}"));
    let entries: Vec<String> = reset.into_iter().chain(pairs).collect();
    format!("in=({})", entries.join(" "))
}
