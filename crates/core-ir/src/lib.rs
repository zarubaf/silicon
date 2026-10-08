//! The Silicon core IR: typed bit-vector values, the AST, the text format,
//! the checker, and the interpreter.

pub mod ast;
pub mod check;
pub mod deps;
pub mod diag;
pub mod interp;
mod scc;
pub mod text;
pub mod typed;
mod value;
pub mod vectors;

pub use value::{Bits, Pred};
