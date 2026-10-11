// SPDX-License-Identifier: Apache-2.0
//! Lifts generated core designs to slice-1 source programs. The lift fixes
//! the source names, so the map from core vectors to source vectors lives
//! here too. The map is independent of `elab::vectors` on purpose: the layer
//! order puts `syntax` before `elab`, and the oracle of `diff-si` must not
//! reuse the code under test.

mod expr;
mod lift;

pub use lift::{Unsupported, lift, vector_in, vector_out};
