//! The elaborator of the Silicon front end: the static values, the static evaluator with the
//! budgets and the cost model, and the digest names. See [the front end
//! design](../../doc/design/2026-10-09-frontend.md), sections 4.4, 4.5, and 5.

mod eval;
pub mod int;
mod ops;
pub mod sha256;
mod stack;
pub mod value;

use parse::StackError;
use parse::ast::Pos;
use resolve::{Resolved, ResolvedExpr};
use std::fmt;
use value::Value;

/// The codes of elaboration that the static evaluator can report (design section 6.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    /// A `return` outside of a function.
    S006,
    /// A wrong number of arguments that only elaboration finds.
    S007,
    /// A type error.
    S010,
    /// A static position has a value that is not static.
    S011,
    /// A value does not fit its type.
    S012,
    /// A static fault: a division by zero, or a negative shift count.
    S013,
    /// A failed `static_assert`, or `error`.
    S014,
    /// The fuel or the nesting depth is exhausted.
    S015,
    /// A constant depends on itself.
    S019,
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Code::S006 => "S006",
            Code::S007 => "S007",
            Code::S010 => "S010",
            Code::S011 => "S011",
            Code::S012 => "S012",
            Code::S013 => "S013",
            Code::S014 => "S014",
            Code::S015 => "S015",
            Code::S019 => "S019",
        })
    }
}

/// The first error of an elaboration. Elaboration stops at it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub code: Code,
    pub pos: Pos,
    pub message: String,
}

/// The budgets of design section 5.4 with their normative defaults.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Budget {
    /// The cost units that the elaboration can use.
    pub fuel: u64,
    /// The most active calls, constants in progress, and instantiations in progress.
    pub depth: u64,
}

impl Default for Budget {
    fn default() -> Budget {
        Budget {
            fuel: 100_000_000,
            depth: 1000,
        }
    }
}

/// The value of a static expression in the file scope of `file`, and the used fuel, as Lean
/// `Eval.evalExpr` gives them. The expression and the file passed the pre-check.
///
/// The evaluator recurses, so it runs on threads with a stack for the syntax depth. A group
/// of nesting levels runs on each thread.
///
/// # Errors
/// Returns an error if the machine cannot give a stack.
pub fn eval(
    file: &Resolved,
    expr: &ResolvedExpr,
    budget: Budget,
) -> Result<Result<(Value, u64), Error>, StackError> {
    let stack = parse::on_stack(file.depth(), || stack::of(file, expr))?;
    let result = parse::on_stack(stack.thread_levels, || eval::run(file, expr, budget, stack))?;
    match result {
        Ok(done) => Ok(Ok(done)),
        Err(eval::Stop::Error(e)) => Ok(Err(e)),
        Err(eval::Stop::Stack(e)) => Err(e),
    }
}

#[cfg(test)]
mod tests;
