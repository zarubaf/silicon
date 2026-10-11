// SPDX-License-Identifier: Apache-2.0
//! The source differential tests. A random core design is
//! lifted to a source program. The core interpreter is the oracle: `silicon
//! run` and `silicon-check run` on the source must print its outputs, and
//! the Lean `validate` must accept the elaboration of the source.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow};
use core_ir::ast;
use core_ir::check::check;
use core_ir::r#gen::{self, Config};
use core_ir::interp::Sim;
use core_ir::text::print;
use core_ir::vectors::parse_input;
use proptest::collection::vec;
use proptest::strategy::{Just, Strategy, ValueTree};
use syntax::r#gen::{lift, vector_in, vector_out};

use crate::diff::{CYCLES, ToolFailure, Trace, compare, output, runner};
use crate::repo::Repo;
use crate::{lean_check, silicon};

/// The most test runs of one shrink. Each run starts four processes.
const SHRINK_RUNS: u32 = 256;

/// A core design and its `in=` lines.
type Case = (ast::Design, Vec<String>);

/// The tools under test.
struct Tools {
    lean: PathBuf,
    silicon: PathBuf,
}

/// Builds `silicon` and `silicon-check`, then lifts `count` random core
/// designs, from the seeds `seed`, `seed + 1`, and so on. Returns whether
/// all cases agree. The run stops at the first failure, which it shrinks. A
/// tooling error, for example a missing tool, is an error, not a failure.
pub fn run(repo: &Repo, seed: u64, count: u64) -> Result<bool> {
    let Some(silicon) = silicon::build(&repo.root)? else {
        return Ok(false);
    };
    let Some(lean) = lean_check::build(repo)? else {
        return Ok(false);
    };
    let tools = Tools { lean, silicon };
    let dir = tempfile::tempdir().context("cannot make a temporary directory")?;
    let last = seed.wrapping_add(
        count
            .checked_sub(1)
            .context("the count must be at least 1")?,
    );
    for n in (0..count).map(|k| seed.wrapping_add(k)) {
        let mut tree = cases()
            .new_tree(&mut runner(n))
            .map_err(|e| anyhow!("cannot generate a case for seed {n}: {e}"))?;
        let case = tree.current();
        let Some(message) =
            verdict(&tools, dir.path(), &case).with_context(|| format!("seed {n}"))?
        else {
            continue;
        };
        let first = message.clone();
        let (case, message) = shrink(&mut tree, message, |c| verdict(&tools, dir.path(), c))
            .with_context(|| format!("seed {n}, while shrinking the failure: {first}"))?;
        report(n, &case, &message);
        return Ok(false);
    }
    println!("diff-si: {count} lifted designs agree (seeds {seed} to {last})");
    Ok(true)
}

/// Random designs of the source forms, each with `CYCLES` matching input
/// lines. A design that fails the checker gets no lines, so the case then
/// reports the checker error.
fn cases() -> impl Strategy<Value = Case> {
    r#gen::design_with(Config::source()).prop_flat_map(|design| {
        let lines = check(&design)
            .ok()
            .and_then(|typed| typed.modules().get(typed.top().index()).cloned())
            .map_or_else(
                || Just(Vec::new()).boxed(),
                |top| vec(r#gen::inputs(&top), CYCLES).boxed(),
            );
        (Just(design), lines)
    })
}

/// The `in=` and `out=` lines of the source vectors for `case`, from the
/// core interpreter. The inner error is the message of the checker.
fn reference(case: &Case) -> Result<std::result::Result<Vec<(String, String)>, String>> {
    let (design, lines) = case;
    let typed = match check(design) {
        Ok(typed) => typed,
        Err(e) => {
            return Ok(Err(format!("the generated design fails the checker: {e}")));
        }
    };
    let top = typed
        .modules()
        .get(typed.top().index())
        .context("the design has no top module")?;
    let mut sim = Sim::new(&typed).map_err(|e| anyhow!("the core interpreter rejects it: {e}"))?;
    let mut steps = Vec::new();
    for line in lines {
        let inputs = parse_input(line, top).map_err(|e| anyhow!("{line}: {e}"))?;
        let outputs = sim.step(&inputs);
        steps.push((vector_in(top, &inputs), vector_out(top, &outputs)));
    }
    Ok(Ok(steps))
}

fn top_selection(design: &ast::Design) -> String {
    format!("{}()", design.top.text)
}

/// `None` if the tools agree on `case`, else the message of the
/// disagreement or of a tool failure. A tooling error is an `Err`.
fn verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<String>> {
    match try_verdict(tools, dir, case) {
        Err(error) if error.downcast_ref::<ToolFailure>().is_some() => {
            Ok(Some(format!("{error:#}")))
        }
        other => other,
    }
}

fn try_verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<String>> {
    let steps = match reference(case)? {
        Ok(steps) => steps,
        Err(message) => return Ok(Some(message)),
    };
    let source = lift(&case.0)
        .map_err(|e| anyhow!("the lift rejects the design: {e}\n{}", print(&case.0)))?;
    let file = dir.join("design.si");
    std::fs::write(&file, &source).with_context(|| format!("cannot write {}", file.display()))?;
    let top = top_selection(&case.0);
    let mut stdin = steps
        .iter()
        .map(|(line, _)| line.as_str())
        .collect::<Vec<_>>()
        .join("\n");
    stdin.push('\n');
    let run = |tool: &'static str, binary: &Path| -> Result<Trace> {
        let stdout = output(
            Command::new(binary)
                .arg("run")
                .arg(&file)
                .args(["--top", &top]),
            &stdin,
        )?;
        Ok(Trace {
            tool,
            lines: stdout.lines().map(str::to_owned).collect(),
        })
    };
    let traces = [
        Trace {
            tool: "core",
            lines: steps.iter().map(|(_, out)| out.clone()).collect(),
        },
        run("silicon", &tools.silicon)?,
        run("lean", &tools.lean)?,
    ];
    if let Some(message) = compare(&traces) {
        return Ok(Some(message));
    }
    let elab = output(
        Command::new(&tools.silicon)
            .arg("elab")
            .arg(&file)
            .args(["--top", &top]),
        "",
    )?;
    let sil = dir.join("design.sil");
    std::fs::write(&sil, elab).with_context(|| format!("cannot write {}", sil.display()))?;
    let validated = output(
        Command::new(&tools.lean)
            .arg("validate")
            .arg(&file)
            .arg(&sil)
            .args(["--top", &top]),
        "",
    )?;
    Ok((validated != "ok\n").then(|| format!("validate printed `{validated}`, not `ok`")))
}

/// Shrinks the failing value of `tree` with the proptest algorithm, with at
/// most `SHRINK_RUNS` runs of `test`. `test` gives `Some(message)` for a
/// failure. An `Err` of `test` ends the shrink as an error. Returns the
/// smallest failing value and its message.
fn shrink<T: ValueTree>(
    tree: &mut T,
    message: String,
    mut test: impl FnMut(&T::Value) -> Result<Option<String>>,
) -> Result<(T::Value, String)> {
    let mut best = (tree.current(), message);
    let mut runs = 0;
    let mut simplify = true;
    while runs < SHRINK_RUNS {
        let moved = if simplify {
            tree.simplify()
        } else {
            tree.complicate()
        };
        if !moved {
            break;
        }
        runs += 1;
        let value = tree.current();
        match test(&value)? {
            Some(message) => {
                best = (value, message);
                simplify = true;
            }
            None => simplify = false,
        }
    }
    Ok(best)
}

/// The text of a `tests/source/run` file for the source `source` with the
/// top selection `top` and the `steps` of `(in, out)` lines.
fn reproducer(source: &str, top: &str, steps: &[(String, String)]) -> String {
    let steps = steps
        .iter()
        .map(|(input, out)| format!("// STEP {input} {out}\n"));
    std::iter::once(format!("// TOP {top}\n{source}"))
        .chain(steps)
        .collect()
}

/// Prints the failure of seed `seed`: the message, the core design, and the
/// reproducer.
fn report(seed: u64, case: &Case, message: &str) {
    println!("FAIL seed {seed}: {message}");
    println!("{}", print(&case.0));
    if let (Ok(source), Ok(Ok(steps))) = (lift(&case.0), reference(case)) {
        print!("{}", reproducer(&source, &top_selection(&case.0), &steps));
    }
    println!("Run `cargo xtask diff-si --seed {seed} --count 1` to repeat it.");
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::collection::vec as pvec;
    use proptest::prelude::any;

    fn case(seed: u64) -> (Case, String) {
        let case = cases().new_tree(&mut runner(seed)).unwrap().current();
        let text = print(&case.0);
        (case, text)
    }

    #[test]
    fn the_same_seed_gives_the_same_case() {
        let ((_, lines_a), text_a) = case(7);
        let ((_, lines_b), text_b) = case(7);
        assert_eq!((text_a, &lines_a), (text_b, &lines_b));
        assert_eq!(lines_a.len(), CYCLES);
    }

    #[test]
    fn cases_use_source_forms() {
        for seed in 1..=20 {
            let ((design, _), _) = case(seed);
            assert!(lift(&design).is_ok(), "seed {seed}");
        }
    }

    #[test]
    fn shrink_finds_the_smallest_failure() {
        let mut tree = (0..1000)
            .map(|seed| (0u32..1000).new_tree(&mut runner(seed)).unwrap())
            .find(|tree| tree.current() > 10)
            .unwrap();
        let fails = |n: &u32| Ok((*n >= 10).then(|| "fails".to_owned()));
        let (value, message) = shrink(&mut tree, "fails".to_owned(), fails).unwrap();
        assert_eq!((value, message.as_str()), (10, "fails"));
    }

    #[test]
    fn shrink_stops_after_the_cap() {
        let mut tree = pvec(any::<u32>(), 0..4096)
            .new_tree(&mut runner(1))
            .unwrap();
        let mut calls = 0;
        shrink(&mut tree, "fails".to_owned(), |_| {
            calls += 1;
            Ok(Some("fails".to_owned()))
        })
        .unwrap();
        assert_eq!(calls, SHRINK_RUNS);
    }

    #[test]
    fn a_tooling_error_stops_the_shrink() {
        let mut tree = (0u32..1000).new_tree(&mut runner(1)).unwrap();
        let result = shrink(&mut tree, "fails".to_owned(), |_| Err(anyhow!("no tool")));
        assert!(result.is_err());
    }

    #[test]
    fn the_reproducer_is_a_source_run_file() {
        assert_eq!(
            reproducer(
                "module m0() domains() {\n}\n",
                "m0()",
                &[("in=()".into(), "out=()".into())]
            ),
            "// TOP m0()\nmodule m0() domains() {\n}\n// STEP in=() out=()\n"
        );
    }
}
