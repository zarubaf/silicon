//! The generic pre-check of the Silicon front end: pass 4, with `S005` to `S007`. See [the
//! front end design](../../doc/design/2026-10-09-frontend.md), sections 4.2 and 6. The check
//! needs no static value, so it runs on each item.

mod walk;

use parse::StackError;
use parse::ast::Pos;
use resolve::Resolved;
use std::fmt;

/// The codes of pass 4 that slice 1 can report. `S008` cannot occur in slice 1: it has no
/// `mut` formal, no receiver call, and no expression that mutates a root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    /// A static position names a port, a register, a wire, or an instance.
    S005,
    /// A statement is in a place that does not allow it.
    S006,
    /// A call, an instance, or a type family has the wrong number of arguments.
    S007,
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Code::S005 => "S005",
            Code::S006 => "S006",
            Code::S007 => "S007",
        })
    }
}

/// An error of pass 4. Only the first one is normative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub code: Code,
    pub pos: Pos,
    pub message: String,
}

/// Why a resolved AST does not pass the check.
pub enum Failed {
    /// The errors in position order. At one position, the first error of the walk is first.
    Errors(Vec<Error>),
    /// The machine cannot give the stack for the syntax depth.
    Stack(StackError),
}

/// Checks the items of a resolved AST. The AST is unchanged.
///
/// # Errors
/// Returns the errors of `S005` to `S007`, or an error if the machine cannot give the stack.
pub fn check(resolved: Resolved) -> Result<Resolved, Failed> {
    let errors =
        parse::on_stack(resolved.depth(), || walk::run(&resolved)).map_err(Failed::Stack)?;
    if errors.is_empty() {
        Ok(resolved)
    } else {
        Err(Failed::Errors(errors))
    }
}

#[cfg(test)]
mod tests;
