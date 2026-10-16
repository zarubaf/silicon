// SPDX-License-Identifier: Apache-2.0
//! The observation records of a typed program (front-end spec 8.2).
//!
//! A record line is `(record <line> <col> <emitted> (<frames>) <message>
//! <value>)`. Each instantiation records once (decision F15), when it
//! elaborates: the walk below starts at the top, runs the static statements
//! of a module body, and elaborates a child at its `instance` statement if
//! its argument tuple is new. The line and the column come from the text of
//! the program, not from the front ends. The builder emits one call frame at
//! most: the call of a `comptime fn` with a `mut` formal, whose `diagnostic`
//! is the only one that runs in a function. The walk ends by checking its
//! argument tuples against the contexts that the builder collected, so the
//! one identity rule is the equality of the argument values.

use std::collections::BTreeMap;

use super::emitted::emitted;
use super::eval::{Env, Fault, Logged, Scope, Value, convert, eval, exec_logged, loop_values};
use super::program::{Item, SExpr, Stmt};

/// The distinct argument tuples of each module, by module name.
pub(crate) type Contexts = [(String, Vec<Vec<Value>>)];

/// A position in the text: the line and the column, both from 1.
type At = (usize, usize);

/// The positions of the statements that make records, from the text of the
/// program. The printer writes one statement in a line, and each message
/// `dK` and each result name of a call is unique in its scope.
#[derive(Default)]
struct Sites {
    /// The `diagnostic` statements, by message.
    diagnostics: BTreeMap<String, At>,
    /// The calls `let s: Int = ...;`, by the module or the function that
    /// holds them and by result name. The position is that of the call
    /// expression.
    calls: BTreeMap<(String, String), At>,
}

impl Sites {
    fn of(text: &str) -> Sites {
        let mut sites = Sites::default();
        let mut scope = String::new();
        for (n, line) in text.lines().enumerate() {
            let code = line.trim_start();
            let col = line.len() - code.len() + 1;
            let head = code
                .strip_prefix("module ")
                .or_else(|| code.strip_prefix("comptime fn "));
            if let Some(rest) = head {
                rest.split('(')
                    .next()
                    .unwrap_or_default()
                    .clone_into(&mut scope);
            } else if let Some(rest) = code.strip_prefix("diagnostic(\"") {
                let message = rest.split('"').next().unwrap_or_default();
                sites.diagnostics.insert(message.to_owned(), (n + 1, col));
            } else if let Some(rest) = code.strip_prefix("let ") {
                let name = rest.split(':').next().unwrap_or_default();
                let lead = "let ".len() + name.len() + ": Int = ".len();
                if rest[name.len()..].starts_with(": Int = ") {
                    sites
                        .calls
                        .insert((scope.clone(), name.to_owned()), (n + 1, col + lead));
                }
            }
        }
        sites
    }
}

/// The module and the emitted name of the instantiation that the walk runs.
struct Frame<'a> {
    module: &'a str,
    emitted: &'a str,
}

struct Walk<'a> {
    items: &'a [Item],
    scope: Scope,
    sites: Sites,
    /// The instantiations that have elaborated, in order.
    done: Vec<(String, Vec<Value>)>,
    lines: Vec<String>,
}

/// The record lines of `items`, whose printed text is `text`, in evaluation
/// order. `top` is the name and the arguments of the top instantiation.
/// `contexts` are the argument tuples that the builder collected.
pub(crate) fn records(
    items: &[Item],
    text: &str,
    top: (&str, &[Value]),
    contexts: &Contexts,
) -> Result<Vec<String>, Fault> {
    let mut walk = Walk {
        items,
        scope: Scope::new(items)?,
        sites: Sites::of(text),
        done: Vec::new(),
        lines: Vec::new(),
    };
    walk.elaborate(top.0, top.1)?;
    for (name, tuples) in contexts {
        let seen = walk.done.iter().filter(|(n, _)| n == name);
        let same = seen.clone().count() == tuples.len()
            && seen.into_iter().all(|(_, t)| tuples.contains(t));
        if !same {
            return Err(Fault::Type);
        }
    }
    Ok(walk.lines)
}

impl Walk<'_> {
    /// The records of module `name` for the arguments `args`, and of the
    /// children that it elaborates.
    fn elaborate(&mut self, name: &str, args: &[Value]) -> Result<(), Fault> {
        self.done.push((name.to_owned(), args.to_vec()));
        let module = self.items.iter().find_map(|item| match item {
            Item::Module {
                name: n,
                params,
                body,
                ..
            } if n == name => Some((params, body)),
            _ => None,
        });
        let (params, body) = module.ok_or(Fault::Type)?;
        let emitted = emitted(name, args);
        let frame = Frame {
            module: name,
            emitted: &emitted,
        };
        self.run(body, &mut Env::of(params, args), &frame)
    }

    /// The arguments of `instance` of `child`, each converted to its
    /// parameter type before it names an instantiation (#188).
    fn converted(&self, child: &str, args: &[SExpr], env: &Env) -> Result<Vec<Value>, Fault> {
        let params = self
            .items
            .iter()
            .find_map(|item| match item {
                Item::Module { name, params, .. } if name == child => Some(params),
                _ => None,
            })
            .ok_or(Fault::Type)?;
        if params.len() != args.len() {
            return Err(Fault::Type);
        }
        args.iter()
            .zip(params)
            .map(|(a, (_, t))| convert(t, eval(a, env, &self.scope)?))
            .collect()
    }

    /// The static statements of a frame. A nested frame works on a copy of
    /// the env: its names do not leave it, and the builder gives it no root
    /// of its parent to write.
    fn run(&mut self, body: &[Stmt], env: &mut Env, frame: &Frame) -> Result<(), Fault> {
        for s in body {
            match s {
                Stmt::StaticLet(..)
                | Stmt::MutLet(..)
                | Stmt::Push(..)
                | Stmt::PopLet(..)
                | Stmt::MutCall { .. }
                | Stmt::Diagnostic(..) => {
                    let mut logged = Vec::new();
                    exec_logged(s, env, &self.scope, &mut logged)?;
                    for l in &logged {
                        let line = self.line(frame, l)?;
                        self.lines.push(line);
                    }
                }
                Stmt::Instance(_, child, args) => {
                    let args = self.converted(child, args, env)?;
                    if !self.done.iter().any(|(n, t)| n == child && *t == args) {
                        self.elaborate(child, &args)?;
                    }
                }
                Stmt::If(c, then, els) => {
                    let Value::Bool(taken) = eval(c, env, &self.scope)? else {
                        return Err(Fault::Type);
                    };
                    let branch = if taken { Some(then) } else { els.as_ref() };
                    if let Some(branch) = branch {
                        self.run(branch, &mut env.clone(), frame)?;
                    }
                }
                Stmt::For(binder, lo, hi, body) => {
                    let (Value::Int(lo), Value::Int(hi)) =
                        (eval(lo, env, &self.scope)?, eval(hi, env, &self.scope)?)
                    else {
                        return Err(Fault::Type);
                    };
                    for value in loop_values(&lo, &hi) {
                        let mut inner = env.clone();
                        inner.statics.insert(binder.clone(), value);
                        self.run(body, &mut inner, frame)?;
                    }
                }
                // A frame that no env reaches holds the `error`; it never
                // runs. The builder never emits a `Block`.
                Stmt::Error(_) | Stmt::Block(_) => return Err(Fault::Type),
                _ => {}
            }
        }
        Ok(())
    }

    /// The record line of `logged`, which a statement of `frame` made.
    fn line(&self, frame: &Frame, logged: &Logged) -> Result<String, Fault> {
        let (line, col) = *self
            .sites
            .diagnostics
            .get(&logged.message)
            .ok_or(Fault::Type)?;
        let mut frames = Vec::new();
        for f in &logged.frames {
            let scope = f.within.as_deref().unwrap_or(frame.module);
            let key = (scope.to_owned(), f.result.clone());
            let (l, c) = *self.sites.calls.get(&key).ok_or(Fault::Type)?;
            frames.push(format!("(call {} {l} {c})", f.callee));
        }
        let frames = frames.join(" ");
        Ok(format!(
            "(record {line} {col} {} ({frames}) {})",
            frame.emitted,
            logged.tail()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{MutFn, Radix, SBin, SExpr, STy, render_items};
    use num_bigint::BigInt;

    fn int(n: i64) -> SExpr {
        SExpr::Int(BigInt::from(n), Radix::Dec)
    }

    fn name(n: &str) -> SExpr {
        SExpr::Name(n.to_owned())
    }

    fn module(name: &str, params: &[&str], body: Vec<Stmt>) -> Item {
        Item::Module {
            name: name.to_owned(),
            params: params.iter().map(|p| ((*p).to_owned(), STy::Int)).collect(),
            clocked: false,
            body,
        }
    }

    fn value(n: i64) -> Value {
        Value::Int(BigInt::from(n))
    }

    fn contexts(m1: &[i64]) -> Vec<(String, Vec<Vec<Value>>)> {
        let tuples = m1.iter().map(|n| vec![value(*n)]).collect();
        vec![("M0".to_owned(), vec![vec![]]), ("M1".to_owned(), tuples)]
    }

    fn instance(u: &str, n: i64) -> Stmt {
        Stmt::Instance(u.to_owned(), "M1".to_owned(), vec![int(n)])
    }

    /// The top elaborates a child at its `instance` statement, once for each
    /// argument tuple: the records of the child come before the next record
    /// of the parent, and a repeated tuple makes none. A loop makes one
    /// record for each iteration at the line of its statement.
    #[test]
    fn a_child_records_at_its_instance_statement_once() {
        let m1 = module(
            "M1",
            &["P0"],
            vec![
                Stmt::Diagnostic("d0".to_owned(), name("P0")),
                Stmt::For(
                    "j0".to_owned(),
                    int(0),
                    int(2),
                    vec![Stmt::Diagnostic(
                        "d1".to_owned(),
                        SExpr::Binary(SBin::Add, Box::new(name("P0")), Box::new(name("j0"))),
                    )],
                ),
            ],
        );
        let m0 = module(
            "M0",
            &[],
            vec![
                Stmt::Diagnostic("d2".to_owned(), int(7)),
                instance("u0", 1),
                instance("u1", 2),
                instance("u2", 1),
                Stmt::Diagnostic("d3".to_owned(), int(8)),
            ],
        );
        let items = [m0, m1];
        let text = render_items(&items);
        let got = records(&items, &text, ("M0", &[]), &contexts(&[1, 2])).unwrap();
        let want = [
            "(record 2 5 M0 () (string \"d2\") (int 7))",
            "(record 9 5 M1$1 () (string \"d0\") (int 1))",
            "(record 11 9 M1$1 () (string \"d1\") (int 1))",
            "(record 11 9 M1$1 () (string \"d1\") (int 2))",
            "(record 9 5 M1$2 () (string \"d0\") (int 2))",
            "(record 11 9 M1$2 () (string \"d1\") (int 2))",
            "(record 11 9 M1$2 () (string \"d1\") (int 3))",
            "(record 6 5 M0 () (string \"d3\") (int 8))",
        ];
        assert_eq!(got, want, "{text}");
    }

    /// A `comptime if` takes the branch of each context, so the child that
    /// it holds elaborates only in the context that takes it.
    #[test]
    fn a_branch_records_in_the_contexts_that_take_it() {
        let cond = SExpr::Binary(SBin::Gt, Box::new(name("P0")), Box::new(int(1)));
        let m1 = module(
            "M1",
            &["P0"],
            vec![Stmt::If(
                cond,
                vec![Stmt::Diagnostic("d0".to_owned(), name("P0"))],
                Some(vec![Stmt::Diagnostic("d1".to_owned(), int(-1))]),
            )],
        );
        let m0 = module("M0", &[], vec![instance("u0", 1), instance("u1", 2)]);
        let items = [m0, m1];
        let text = render_items(&items);
        let got = records(&items, &text, ("M0", &[]), &contexts(&[1, 2])).unwrap();
        let want = [
            "(record 9 9 M1$1 () (string \"d1\") (int -1))",
            "(record 7 9 M1$2 () (string \"d0\") (int 2))",
        ];
        assert_eq!(got, want, "{text}");
    }

    /// A call of a function with a `mut` formal makes one frame, at the
    /// position of the call expression; the record is at the `diagnostic`
    /// of the function.
    #[test]
    fn a_call_makes_a_frame_at_its_expression() {
        let k0 = Item::MutFn(MutFn {
            name: "k0".to_owned(),
            root: STy::Int,
            update: name("x1"),
            ret: name("x1"),
            diag: Some(("d0".to_owned(), name("a0"))),
        });
        let call = |result: &str, receiver| Stmt::MutCall {
            name: result.to_owned(),
            root: "s0".to_owned(),
            f: "k0".to_owned(),
            args: vec![int(4)],
            receiver,
        };
        let body = vec![
            Stmt::MutLet("s0".to_owned(), STy::Int, int(0)),
            call("s1", false),
            Stmt::MutLet("s0".to_owned(), STy::Int, int(0)),
            call("s2", true),
        ];
        let items = [k0, module("M0", &[], body)];
        let text = render_items(&items);
        let want = [
            "(record 3 5 M0 ((call k0 8 19)) (string \"d0\") (int 4))",
            "(record 3 5 M0 ((call k0 10 19)) (string \"d0\") (int 4))",
        ];
        let got = records(&items, &text, ("M0", &[]), &[]).unwrap();
        assert_eq!(got, want, "{text}");
    }

    /// Two spellings of one finite argument give one instantiation: the
    /// argument converts to the parameter type first (#188).
    #[test]
    fn a_plain_and_a_converted_argument_name_one_instantiation() {
        let m1 = Item::Module {
            name: "M1".to_owned(),
            params: vec![("P0".to_owned(), STy::UInt(8))],
            clocked: false,
            body: vec![Stmt::Diagnostic("d0".to_owned(), name("P0"))],
        };
        let converted = SExpr::Convert(STy::UInt(8), Box::new(int(1)));
        let body = vec![
            Stmt::Instance("u0".to_owned(), "M1".to_owned(), vec![int(1)]),
            Stmt::Instance("u1".to_owned(), "M1".to_owned(), vec![converted]),
        ];
        let items = [module("M0", &[], body), m1];
        let text = render_items(&items);
        let contexts = [
            ("M0".to_owned(), vec![vec![]]),
            ("M1".to_owned(), vec![vec![Value::UInt(8, BigInt::from(1))]]),
        ];
        let got = records(&items, &text, ("M0", &[]), &contexts).unwrap();
        assert_eq!(
            got,
            ["(record 6 5 M1$1 () (string \"d0\") (uint 8 1))"],
            "{text}"
        );
    }

    /// The builder and the walk must agree on the argument tuples.
    #[test]
    fn a_context_that_the_walk_misses_is_a_fault() {
        let items = [
            module("M0", &[], vec![instance("u0", 1)]),
            module("M1", &["P0"], vec![]),
        ];
        let text = render_items(&items);
        assert!(records(&items, &text, ("M0", &[]), &contexts(&[1])).is_ok());
        assert_eq!(
            records(&items, &text, ("M0", &[]), &contexts(&[1, 2])),
            Err(Fault::Type)
        );
    }
}
