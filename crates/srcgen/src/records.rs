// SPDX-License-Identifier: Apache-2.0
//! The observation records of a typed program (front-end spec 8.2).
//!
//! Each instantiation records once (decision F15), so the records are the
//! sum over the distinct contexts of each module: the argument tuples that
//! the builder collected in `Builder.contexts`. This is the one identity
//! rule; the walk below adds none. For each context it runs the static
//! statements of the module body, with its loops and `comptime if`s, and
//! keeps the tail of each `diagnostic`: the message and the value, as
//! `observe` prints them after the frames.

use super::eval::{Env, Fault, Logged, Scope, Value, eval, exec_logged, loop_values};
use super::program::{Item, Stmt};

/// The distinct argument tuples of each module, by module name.
pub(crate) type Contexts = [(String, Vec<Vec<Value>>)];

/// The record tails of `items` over `contexts`, in evaluation order. A
/// module without a context makes none.
pub(crate) fn records(items: &[Item], contexts: &Contexts) -> Result<Vec<String>, Fault> {
    let scope = Scope::new(items)?;
    let mut log = Vec::new();
    for item in items {
        let Item::Module {
            name, params, body, ..
        } = item
        else {
            continue;
        };
        let Some((_, tuples)) = contexts.iter().find(|(n, _)| n == name) else {
            continue;
        };
        for tuple in tuples {
            run(body, &mut Env::of(params, tuple), &scope, &mut log)?;
        }
    }
    Ok(log.iter().map(Logged::tail).collect())
}

/// The static statements of a frame. A nested frame works on a copy of the
/// env: its names do not leave it, and the builder gives it no root of its
/// parent to write.
fn run(body: &[Stmt], env: &mut Env, scope: &Scope, log: &mut Vec<Logged>) -> Result<(), Fault> {
    for s in body {
        match s {
            Stmt::StaticLet(..)
            | Stmt::MutLet(..)
            | Stmt::Push(..)
            | Stmt::PopLet(..)
            | Stmt::MutCall { .. }
            | Stmt::Diagnostic(..) => exec_logged(s, env, scope, log)?,
            Stmt::If(c, then, els) => {
                let Value::Bool(taken) = eval(c, env, scope)? else {
                    return Err(Fault::Type);
                };
                let branch = if taken { Some(then) } else { els.as_ref() };
                if let Some(branch) = branch {
                    run(branch, &mut env.clone(), scope, log)?;
                }
            }
            Stmt::For(binder, lo, hi, body) => {
                let (Value::Int(lo), Value::Int(hi)) =
                    (eval(lo, env, scope)?, eval(hi, env, scope)?)
                else {
                    return Err(Fault::Type);
                };
                for value in loop_values(&lo, &hi) {
                    let mut inner = env.clone();
                    inner.statics.insert(binder.clone(), value);
                    run(body, &mut inner, scope, log)?;
                }
            }
            // A frame that no env reaches holds the `error`; it never runs.
            // The builder never emits a `Block`.
            Stmt::Error(_) | Stmt::Block(_) => return Err(Fault::Type),
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{Radix, SBin, SExpr, STy};
    use num_bigint::BigInt;

    fn int(n: i64) -> SExpr {
        SExpr::Int(BigInt::from(n), Radix::Dec)
    }

    fn name(n: &str) -> SExpr {
        SExpr::Name(n.to_owned())
    }

    fn module(params: &[&str], body: Vec<Stmt>) -> Item {
        Item::Module {
            name: "M1".to_owned(),
            params: params.iter().map(|p| ((*p).to_owned(), STy::Int)).collect(),
            clocked: false,
            body,
        }
    }

    fn contexts(tuples: &[i64]) -> Vec<(String, Vec<Vec<Value>>)> {
        let tuples = tuples
            .iter()
            .map(|n| vec![Value::Int(BigInt::from(*n))])
            .collect();
        vec![("M1".to_owned(), tuples)]
    }

    /// Two contexts and a loop of three: each context records its loop
    /// iterations, and a diagnostic outside the loop records once for each
    /// context. The value `P0 * 10 + j0` differs in each record.
    #[test]
    fn a_loop_and_two_contexts_make_each_record_once() {
        let value = SExpr::Binary(
            SBin::Add,
            Box::new(SExpr::Binary(
                SBin::Mul,
                Box::new(name("P0")),
                Box::new(int(10)),
            )),
            Box::new(name("j0")),
        );
        let body = vec![
            Stmt::Diagnostic("d0".to_owned(), name("P0")),
            Stmt::For(
                "j0".to_owned(),
                int(0),
                int(3),
                vec![Stmt::Diagnostic("d1".to_owned(), value)],
            ),
        ];
        let got = records(&[module(&["P0"], body)], &contexts(&[1, 2])).unwrap();
        let want = [
            "(string \"d0\") (int 1)",
            "(string \"d1\") (int 10)",
            "(string \"d1\") (int 11)",
            "(string \"d1\") (int 12)",
            "(string \"d0\") (int 2)",
            "(string \"d1\") (int 20)",
            "(string \"d1\") (int 21)",
            "(string \"d1\") (int 22)",
        ];
        assert_eq!(got, want);
    }

    /// A `comptime if` takes the branch of each context.
    #[test]
    fn a_branch_records_in_the_contexts_that_take_it() {
        let cond = SExpr::Binary(SBin::Gt, Box::new(name("P0")), Box::new(int(1)));
        let body = vec![Stmt::If(
            cond,
            vec![Stmt::Diagnostic("d0".to_owned(), name("P0"))],
            Some(vec![Stmt::Diagnostic("d1".to_owned(), int(-1))]),
        )];
        let got = records(&[module(&["P0"], body)], &contexts(&[1, 2, 3])).unwrap();
        assert_eq!(
            got,
            [
                "(string \"d1\") (int -1)",
                "(string \"d0\") (int 2)",
                "(string \"d0\") (int 3)"
            ]
        );
    }

    /// A module that no context reaches makes no record.
    #[test]
    fn a_module_without_a_context_makes_no_record() {
        let body = vec![Stmt::Diagnostic("d0".to_owned(), int(1))];
        assert_eq!(records(&[module(&[], body)], &contexts(&[])), Ok(vec![]));
    }
}
