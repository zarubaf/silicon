// SPDX-License-Identifier: Apache-2.0
//! Lifts generated core designs to slice-1 source programs. The lift fixes
//! the source names, so the map from core vectors to source vectors lives
//! here too.

mod expr;
mod lift;

pub use lift::{Unsupported, lift, vector_in, vector_out};
