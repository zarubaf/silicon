//! The Silicon core IR: typed bit-vector values, the AST, and the text format.

pub mod ast;
pub mod diag;
pub mod text;
mod value;

pub use value::{Bits, Pred};
