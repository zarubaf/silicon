// SPDX-License-Identifier: Apache-2.0
//! The elaborator of the Silicon front end: the static values, the evaluator with the budgets
//! and the cost model, the instantiations, and the names. See [the front end
//! design](../../doc/design/2026-10-09-frontend.md), sections 4.4, 4.5, 5, and 7.

mod agg;
mod cover;
mod eval;
mod flatten;
mod hw;
pub mod int;
mod layout;
mod limit;
pub mod names;
mod ops;
mod scan;
mod serial;
pub mod sha256;
mod text;
mod types;
mod unpack;
pub mod value;
pub mod vectors;

pub use eval::Design;
pub use flatten::{Failure, Lowered, check};

use eval::Literal;
use parse::StackError;
use parse::ast::{Expr, Item, Pos};
use resolve::{Resolved, ResolvedExpr};
use std::fmt;
use value::Evaluated;

/// The codes of elaboration that the evaluator can report (design section 6.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    /// A `return` outside of a function.
    S006,
    /// A wrong number of arguments that only elaboration finds.
    S007,
    /// A `mut` actual or a list place that is not a place.
    S008,
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
    /// A hardware arm changes a binding from before the arm.
    S016,
    /// A resource rule: a bad `:=` target, a read of a child input, or a register or a
    /// clocked child in a combinational module.
    S017,
    /// A binding rule: a resource or a child input without exactly one binding.
    S018,
    /// An identity rule: a constant or an instantiation that depends on itself, or two
    /// identities with one core name.
    S019,
    /// A combinational cycle in the lowered design.
    S020,
    /// A `match` that does not cover its scrutinee, or an arm that no value reaches, or a tag
    /// value that two variants of an enum share.
    S021,
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Code::S006 => "S006",
            Code::S007 => "S007",
            Code::S008 => "S008",
            Code::S010 => "S010",
            Code::S011 => "S011",
            Code::S012 => "S012",
            Code::S013 => "S013",
            Code::S014 => "S014",
            Code::S015 => "S015",
            Code::S016 => "S016",
            Code::S017 => "S017",
            Code::S018 => "S018",
            Code::S019 => "S019",
            Code::S020 => "S020",
            Code::S021 => "S021",
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
) -> Result<Result<(Evaluated, u64), Error>, StackError> {
    let scan = parse::on_stack(expr.depth_with(file), || scan::of(file, Some(expr)))?;
    let stack = scan.stack;
    finish(stack.run(|| eval::run(file, expr, budget, scan))?)
}

/// Why an elaboration does not start or does not end: a top selection that is not a module
/// name with literal arguments, or a stack that the machine cannot give.
#[derive(Debug)]
pub enum Abort {
    Usage(String),
    Stack(StackError),
}

/// What an elaboration made: the records of `diagnostic` in evaluation order, and its outcome.
/// An error keeps the records before it (section 8.2).
pub struct Observed {
    pub records: Vec<String>,
    pub outcome: Result<Design, Error>,
}

/// The elaboration of the top selection `top` in `file`, as Lean `Elab.observe` gives it, with
/// the records of both outcomes. `top` is a module name, then literal arguments in
/// parentheses. Its positions are in its own text, parsed with the syntax depth
/// `syntax_depth`. The file passed the pre-check.
///
/// # Errors
/// Returns `Abort::Usage` for a bad top selection, and `Abort::Stack` if the machine cannot
/// give a stack.
pub fn observe(
    file: &Resolved,
    top: &str,
    syntax_depth: usize,
    budget: Budget,
) -> Result<Observed, Abort> {
    observe_with(file, top, syntax_depth, budget, names::sha16)
}

/// The elaboration of the top selection `top` in `file`, as Lean `Elab.elaborate` and the
/// top selection of `silicon-check` give it: the outcome of `observe`.
///
/// # Errors
/// Returns `Abort::Usage` for a bad top selection, and `Abort::Stack` if the machine cannot
/// give a stack.
pub fn elaborate(
    file: &Resolved,
    top: &str,
    syntax_depth: usize,
    budget: Budget,
) -> Result<Result<Design, Error>, Abort> {
    observe(file, top, syntax_depth, budget).map(|o| o.outcome)
}

/// `elaborate` with the digest function `digest` of the emitted names.
#[cfg(test)]
fn elaborate_with(
    file: &Resolved,
    top: &str,
    syntax_depth: usize,
    budget: Budget,
    digest: fn(&str) -> String,
) -> Result<Result<Design, Error>, Abort> {
    observe_with(file, top, syntax_depth, budget, digest).map(|o| o.outcome)
}

/// `observe` with the digest function `digest` of the emitted names.
fn observe_with(
    file: &Resolved,
    top: &str,
    syntax_depth: usize,
    budget: Budget,
    digest: fn(&str) -> String,
) -> Result<Observed, Abort> {
    let (pos, item, params, xs) = top_selection(file, top, syntax_depth)?;
    if params != xs.len() {
        return Ok(Observed {
            records: Vec::new(),
            outcome: Err(Error {
                code: Code::S007,
                pos,
                message: format!(
                    "the top takes {params} argument(s), but it has {}",
                    xs.len()
                ),
            }),
        });
    }
    let scan = parse::on_stack(file.depth(), || scan::of(file, None)).map_err(Abort::Stack)?;
    let stack = scan.stack;
    #[cfg(test)]
    let fuel = budget.fuel;
    let (records, run) = stack
        .run(|| eval::elaborate(file, budget, scan, digest, pos, item, xs))
        .map_err(Abort::Stack)?;
    // The lowering that follows counts into the run, also from the thread that calls it.
    #[cfg(test)]
    counters::join(fuel);
    let outcome = finish(run).map_err(Abort::Stack)?;
    Ok(Observed { records, outcome })
}

/// The result of an evaluation, or the stack error that stopped it.
fn finish<T>(r: Result<T, eval::Stop>) -> Result<Result<T, Error>, StackError> {
    match r {
        Ok(done) => Ok(Ok(done)),
        Err(eval::Stop::Error(e)) => Ok(Err(e)),
        Err(eval::Stop::Stack(e)) => Err(e),
    }
}

/// The top selection `top`: the position of the selection, the index of the first module
/// item with its name, its number of parameters, and the literal arguments.
fn top_selection(
    file: &Resolved,
    top: &str,
    depth: usize,
) -> Result<(Pos, usize, usize, Vec<Literal>), Abort> {
    let bad = || {
        Abort::Usage(format!(
            "the top selection `{top}` is not a module name with literal arguments"
        ))
    };
    let parsed = match parse::parse_expr(top, depth) {
        Ok(Ok(parsed)) => parsed,
        Ok(Err(_)) | Err(parse::DepthError::Range(_)) => return Err(bad()),
        Err(parse::DepthError::Stack(e)) => return Err(Abort::Stack(e)),
    };
    let (pos, m, args): (Pos, &str, &[Expr]) = match parsed.expr() {
        Expr::Call {
            pos, callee, args, ..
        } => match &**callee {
            Expr::Name { name, .. } => (*pos, name, args),
            _ => return Err(bad()),
        },
        Expr::Name { pos, name, .. } => (*pos, name, &[]),
        _ => return Err(bad()),
    };
    let mut xs = Vec::with_capacity(args.len());
    for a in args {
        xs.push(Literal::of(a).ok_or_else(bad)?);
    }
    for (i, item) in file.ast().iter().enumerate() {
        if let Item::Module { name, params, .. } = item
            && name.name == m
        {
            return Ok((pos, i, params.len(), xs));
        }
    }
    Err(Abort::Usage(format!("`{m}` is not a module of the file")))
}

#[cfg(test)]
mod counters;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod tests_containers;

#[cfg(test)]
mod tests_elab;

#[cfg(test)]
mod tests_enum;

#[cfg(test)]
mod tests_fn;

#[cfg(test)]
mod tests_fn_call;

#[cfg(test)]
mod tests_flatten;
#[cfg(test)]
mod tests_flatten_match;

#[cfg(test)]
mod tests_leaves;

#[cfg(test)]
mod tests_match;
#[cfg(test)]
mod tests_memory;

#[cfg(test)]
mod tests_ports;

#[cfg(test)]
mod tests_records;

#[cfg(test)]
mod tests_resources;

#[cfg(test)]
mod tests_strings;

#[cfg(test)]
mod tests_structural;

#[cfg(test)]
mod tests_types;

#[cfg(test)]
mod tests_vectors;

#[cfg(test)]
mod tests_work;

#[cfg(test)]
mod tests_work_enum;
#[cfg(test)]
mod tests_work_match;

#[cfg(test)]
mod tests_work_records;

#[cfg(test)]
mod tests_work_words;
