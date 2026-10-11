//! Helpers that the test suites of the compiler share.

pub mod bins;
pub mod core;
pub(crate) mod directive;
pub(crate) mod outcome;
pub(crate) mod report;
pub mod source;
pub mod spawn;
pub mod suite;

pub use suite::root;
