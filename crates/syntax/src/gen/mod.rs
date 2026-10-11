// SPDX-License-Identifier: Apache-2.0
//! Lifts generated core designs to slice-1 source programs. The lift fixes
//! the source names, so the map from core vectors to source vectors lives
//! here too. The map is independent of `elab::vectors` on purpose: the layer
//! order puts `syntax` before `elab`, and the oracle of `diff-si` must not
//! reuse the code under test.
//!
//! The typed mode builds random programs in the form of `program` from a
//! tape (`build`), and `eval` computes their static values. The `twin` of
//! a typed program writes out each of its comptime constructs.

mod build;
mod eval;
mod expr;
mod lift;
mod program;
mod twin;

pub use build::{lines, typed};
pub use lift::{Unsupported, lift, vector_in, vector_out};
pub use program::{Ports, Program, Scalar};
pub use twin::{Twin, twin};
