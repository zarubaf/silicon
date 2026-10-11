// SPDX-License-Identifier: Apache-2.0
//! Helpers that the test suites of the compiler share.

pub mod bins;
pub mod core;
pub(crate) mod directive;
pub(crate) mod outcome;
pub(crate) mod report;
pub mod source;
pub mod spawn;
pub mod suite;

pub use outcome::{Outcome, classify};
pub use report::{Report, parse_report};
pub use suite::root;
