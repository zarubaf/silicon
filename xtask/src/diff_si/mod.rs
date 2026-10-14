// SPDX-License-Identifier: Apache-2.0
//! The source differential tests. This driver is independent of the mode:
//! it builds the tools, runs the seed loop, and shrinks the first failure.
//! Each mode supplies a case strategy, a verdict, and a report. The lift
//! mode lifts random core designs to source. The typed mode builds random
//! typed programs and their twins. The mutation mode mutates typed programs.
//! The budget mode runs them at the fuel of their cost.

mod budget;
mod lift;
mod mutation;
mod typed;

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail};
use proptest::strategy::{Strategy, ValueTree};
use testkit::Outcome;
use testkit::source::agree;
use testkit::spawn::spawn;

use crate::diff::{ToolFailure, Trace, output, runner};
use crate::repo::Repo;
use crate::{lean_check, silicon};

/// The most test runs of one shrink. Each run starts four processes in the
/// lift mode, twelve in the typed mode, two in the mutation mode, and at
/// most ten in the budget mode.
const SHRINK_RUNS: u32 = 256;

/// The cases that a run draws.
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub enum Mode {
    /// Random core designs lifted to source programs.
    Lift,
    /// Random typed source programs and their twins.
    Typed,
    /// Random typed source programs with one mutation.
    Mutation,
    /// Random typed source programs with the fuel at the cost.
    Budget,
    /// The lift, typed, mutation, and budget modes.
    All,
}

impl Mode {
    /// The modes that a run of `self` executes, in order.
    fn modes(self) -> &'static [Mode] {
        match self {
            Mode::Lift => &[Mode::Lift],
            Mode::Typed => &[Mode::Typed],
            Mode::Mutation => &[Mode::Mutation],
            Mode::Budget => &[Mode::Budget],
            Mode::All => &[Mode::Lift, Mode::Typed, Mode::Mutation, Mode::Budget],
        }
    }

    /// The name of the mode on the command line.
    fn name(self) -> &'static str {
        match self {
            Mode::Lift => "lift",
            Mode::Typed => "typed",
            Mode::Mutation => "mutation",
            Mode::Budget => "budget",
            Mode::All => "all",
        }
    }
}

/// The command that repeats the case of `seed` in `mode`.
fn repeat(mode: Mode, seed: u64) -> String {
    format!(
        "cargo xtask diff-si --mode {} --seed {seed} --count 1",
        mode.name()
    )
}

/// The tools under test.
pub(super) struct Tools {
    lean: PathBuf,
    silicon: PathBuf,
}

/// Builds `silicon` and `silicon-check`, then runs the cases of `mode`,
/// `count` of each, from the seeds `seed`, `seed + 1`, and so on. Returns
/// whether all cases agree. The run stops at the first failure, which it
/// shrinks. A tooling error, for example a missing tool, is an error, not a
/// failure.
pub fn run(repo: &Repo, mode: Mode, seed: u64, count: u64) -> Result<bool> {
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
    for &mode in mode.modes() {
        let (agree, line) = match mode {
            Mode::Typed => (
                search(
                    typed::cases(),
                    seed,
                    count,
                    |case| typed::verdict(&tools, dir.path(), case),
                    |n, case, message| typed::report(&tools, dir.path(), n, case, message),
                )?,
                format!("diff-si: {count} typed programs agree (seeds {seed} to {last})"),
            ),
            Mode::Lift => {
                let mut tally = lift::Tally::default();
                let agree = search(
                    lift::cases(),
                    seed,
                    count,
                    |case| lift::verdict(&tools, dir.path(), case, &mut tally),
                    |n, case, message| {
                        lift::report(n, case, message);
                        Ok(())
                    },
                )?;
                (agree, tally.summary(seed, last))
            }
            Mode::Mutation => {
                let mut tally = mutation::Tally::new();
                let agree = search(
                    mutation::cases(),
                    seed,
                    count,
                    |case| mutation::verdict(&tools, dir.path(), case, &mut tally),
                    |n, case, message| mutation::report(&tools, dir.path(), n, case, message),
                )?;
                (agree, mutation::summary(count, seed, last, &tally))
            }
            Mode::Budget => (
                search(
                    budget::cases(),
                    seed,
                    count,
                    |case| budget::verdict(&tools, dir.path(), case),
                    |n, case, message| budget::report(&tools, dir.path(), n, case, message),
                )?,
                format!("diff-si: {count} budgets agree (seeds {seed} to {last})"),
            ),
            Mode::All => bail!("the mode `all` is not one mode"),
        };
        if !agree {
            return Ok(false);
        }
        println!("{line}");
    }
    Ok(true)
}

/// Draws a case from `strategy` for each of the seeds `seed`, `seed + 1`,
/// and so on, `count` in all, and asks `verdict` about it. At the first
/// failure it shrinks the case and calls `report` with the seed, the
/// smallest case, and its failure. A mode picks the type `F` of its
/// failure, so that the report can read more than the message. A tooling
/// error of `report` is an error. Returns whether all cases agree.
fn search<C: Clone + std::fmt::Debug, F: std::fmt::Display>(
    strategy: impl Strategy<Value = C>,
    seed: u64,
    count: u64,
    mut verdict: impl FnMut(&C) -> Result<Option<F>>,
    report: impl Fn(u64, &C, &F) -> Result<()>,
) -> Result<bool> {
    for n in (0..count).map(|k| seed.wrapping_add(k)) {
        let mut tree = strategy
            .new_tree(&mut runner(n))
            .map_err(|e| anyhow!("cannot generate a case for seed {n}: {e}"))?;
        let case = tree.current();
        let Some(message) = verdict(&case).with_context(|| format!("seed {n}"))? else {
            continue;
        };
        let first = message.to_string();
        let (case, message) = shrink(&mut tree, message, &mut verdict)
            .with_context(|| format!("seed {n}, while shrinking the failure: {first}"))?;
        report(n, &case, &message)
            .with_context(|| format!("seed {n}, while printing the failure: {message}"))?;
        return Ok(false);
    }
    Ok(true)
}

/// Turns a tool failure into a verdict message. A tooling error stays an
/// `Err`.
fn verdict_of(result: Result<Option<String>>) -> Result<Option<String>> {
    match result {
        Err(error) if error.downcast_ref::<ToolFailure>().is_some() => {
            Ok(Some(format!("{error:#}")))
        }
        other => other,
    }
}

/// The outcome of `command` on `file` with the top selection `top` and the
/// further `flags` in both front ends: the common outcome, or the message
/// of the disagreement or of a front end that misbehaves. A spawn error is
/// the outer `Err`.
fn outcome(
    tools: &Tools,
    command: &str,
    file: &Path,
    top: &str,
    flags: &[&str],
) -> Result<std::result::Result<Outcome, String>> {
    let run = |binary: &Path| {
        let mut front_end = Command::new(binary);
        front_end
            .arg(command)
            .arg(file)
            .args(["--top", top])
            .args(flags);
        spawn(&mut front_end, "").with_context(|| format!("cannot run {}", binary.display()))
    };
    let rust = run(&tools.silicon)?;
    let lean = run(&tools.lean)?;
    Ok(agree(command, &rust, &lean))
}

/// Writes `text` to the file `name` in `dir` and returns its path.
fn write(dir: &Path, name: &str, text: &str) -> Result<PathBuf> {
    let file = dir.join(name);
    std::fs::write(&file, text).with_context(|| format!("cannot write {}", file.display()))?;
    Ok(file)
}

/// The standard input of a `run`: the input lines joined by LF, with a
/// final LF.
fn stdin<'a>(lines: impl IntoIterator<Item = &'a str>) -> String {
    let mut stdin = lines.into_iter().collect::<Vec<_>>().join("\n");
    stdin.push('\n');
    stdin
}

/// The trace of `tool` (the binary `binary`) for the program `file` with the
/// top selection `top` on the input lines `stdin`.
fn run_trace(
    tool: &'static str,
    binary: &Path,
    file: &Path,
    top: &str,
    stdin: &str,
) -> Result<Trace> {
    let stdout = output(
        Command::new(binary)
            .arg("run")
            .arg(file)
            .args(["--top", top]),
        stdin,
    )?;
    Ok(Trace {
        tool,
        lines: stdout.lines().map(str::to_owned).collect(),
    })
}

/// `None` if the Lean `validate` accepts the elaboration of the program
/// `file` with the top selection `top`. The elaboration goes to the file
/// with the extension `sil`.
fn validated(tools: &Tools, file: &Path, top: &str) -> Result<Option<String>> {
    let elab = output(
        Command::new(&tools.silicon)
            .arg("elab")
            .arg(file)
            .args(["--top", top]),
        "",
    )?;
    let sil = file.with_extension("sil");
    std::fs::write(&sil, elab).with_context(|| format!("cannot write {}", sil.display()))?;
    let validated = output(
        Command::new(&tools.lean)
            .arg("validate")
            .arg(file)
            .arg(&sil)
            .args(["--top", top]),
        "",
    )?;
    Ok((validated != "ok\n").then(|| format!("validate printed `{validated}`, not `ok`")))
}

/// Shrinks the failing value of `tree` with the proptest algorithm, with at
/// most `SHRINK_RUNS` runs of `test`. `test` gives `Some(failure)` for a
/// failure. An `Err` of `test` ends the shrink as an error. Returns the
/// smallest failing value and its failure.
fn shrink<T: ValueTree, F>(
    tree: &mut T,
    message: F,
    mut test: impl FnMut(&T::Value) -> Result<Option<F>>,
) -> Result<(T::Value, F)> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::collection::vec as pvec;
    use proptest::prelude::any;

    #[test]
    fn all_runs_the_four_modes_in_order() {
        assert_eq!(
            Mode::All.modes(),
            [Mode::Lift, Mode::Typed, Mode::Mutation, Mode::Budget]
        );
        assert_eq!(Mode::Mutation.modes(), [Mode::Mutation]);
    }

    #[test]
    fn the_modes_draw_one_program_per_seed() {
        for seed in 1..=5 {
            let typed = typed::cases()
                .new_tree(&mut runner(seed))
                .unwrap()
                .current();
            let (mutated, _, _) = mutation::cases()
                .new_tree(&mut runner(seed))
                .unwrap()
                .current();
            let (budgeted, _, _) = budget::cases()
                .new_tree(&mut runner(seed))
                .unwrap()
                .current();
            let text = typed.0.unwrap().text();
            assert_eq!(text, mutated.unwrap().text());
            assert_eq!(text, budgeted.unwrap().text());
        }
    }

    #[test]
    fn the_repeat_command_names_the_mode() {
        assert_eq!(
            repeat(Mode::Typed, 7),
            "cargo xtask diff-si --mode typed --seed 7 --count 1"
        );
    }

    #[test]
    fn the_repeat_command_names_the_mutation_mode() {
        assert_eq!(
            repeat(Mode::Mutation, 7),
            "cargo xtask diff-si --mode mutation --seed 7 --count 1"
        );
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
