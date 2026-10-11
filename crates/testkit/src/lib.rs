//! Helpers that the test suites of the compiler share.

pub mod bins;
pub mod core;
pub mod directive;
pub mod outcome;
pub mod report;
pub mod source;
pub mod spawn;
pub mod suite;

pub use suite::{root, suites};
