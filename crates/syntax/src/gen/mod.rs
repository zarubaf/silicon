// SPDX-License-Identifier: Apache-2.0
//! Lifts generated core designs to slice-1 source programs. The lift fixes
//! the source names, so the map from core vectors to source vectors lives
//! here too. The map is independent of `elab::vectors` on purpose: the layer
//! order puts `syntax` before `elab`, and the oracle of `diff-si` must not
//! reuse the code under test.
//!
//! The typed mode makes programs in the form of `program`, and `eval`
//! computes their static values.

// The builder of the typed mode (#74) is their first user; it removes the
// `allow`s.
#[allow(dead_code, reason = "the typed builder is not yet here")]
mod eval;
mod expr;
mod lift;
#[allow(dead_code, reason = "the typed builder is not yet here")]
mod program;

pub use lift::{Unsupported, lift, vector_in, vector_out};
