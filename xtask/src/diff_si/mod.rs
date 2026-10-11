// SPDX-License-Identifier: Apache-2.0
//! The source differential tests. This driver is independent of the mode:
//! it builds the tools, runs the seed loop, and shrinks the first failure.
//! Each mode supplies a case strategy, a verdict, and a report. The lift
//! mode lifts random core designs to source. The typed mode builds random
//! typed programs and their twins.

mod lift;
mod typed;

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow};
use proptest::strategy::{Strategy, ValueTree};

use crate::diff::{ToolFailure, Trace, output, runner};
use crate::repo::Repo;
use crate::{lean_check, silicon};

/// The most test runs of one shrink. Each run starts four processes.
const SHRINK_RUNS: u32 = 256;

/// The cases that a run draws.
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub enum Mode {
    /// Random core designs lifted to source programs.
    Lift,
    /// Random typed source programs and their twins.
    Typed,
    /// The lift mode, then the typed mode.
    All,
}

impl Mode {
    /// The modes that a run of `self` executes, in order.
    fn modes(self) -> &'static [Mode] {
        match self {
            Mode::Lift => &[Mode::Lift],
            Mode::Typed => &[Mode::Typed],
            Mode::All => &[Mode::Lift, Mode::Typed],
        }
    }

    /// The name of the mode on the command line.
    fn name(self) -> &'static str {
        match self {
            Mode::Lift => "lift",
            Mode::Typed => "typed",
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
        let (agree, what) = match mode {
            Mode::Typed => (
                search(
                    typed::cases(),
                    seed,
                    count,
                    |case| typed::verdict(&tools, dir.path(), case),
                    |n, case, message| typed::report(&tools, dir.path(), n, case, message),
                )?,
                "typed programs",
            ),
            _ => (
                search(
                    lift::cases(),
                    seed,
                    count,
                    |case| lift::verdict(&tools, dir.path(), case),
                    lift::report,
                )?,
                "lifted designs",
            ),
        };
        if !agree {
            return Ok(false);
        }
        println!("diff-si: {count} {what} agree (seeds {seed} to {last})");
    }
    Ok(true)
}

/// Draws a case from `strategy` for each of the seeds `seed`, `seed + 1`,
/// and so on, `count` in all, and asks `verdict` about it. At the first
/// failure it shrinks the case and calls `report` with the seed, the
/// smallest case, and its message. Returns whether all cases agree.
fn search<C: Clone + std::fmt::Debug>(
    strategy: impl Strategy<Value = C>,
    seed: u64,
    count: u64,
    mut verdict: impl FnMut(&C) -> Result<Option<String>>,
    report: impl Fn(u64, &C, &str),
) -> Result<bool> {
    for n in (0..count).map(|k| seed.wrapping_add(k)) {
        let mut tree = strategy
            .new_tree(&mut runner(n))
            .map_err(|e| anyhow!("cannot generate a case for seed {n}: {e}"))?;
        let case = tree.current();
        let Some(message) = verdict(&case).with_context(|| format!("seed {n}"))? else {
            continue;
        };
        let first = message.clone();
        let (case, message) = shrink(&mut tree, message, &mut verdict)
            .with_context(|| format!("seed {n}, while shrinking the failure: {first}"))?;
        report(n, &case, &message);
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

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::collection::vec as pvec;
    use proptest::prelude::any;

    #[test]
    fn all_runs_lift_then_typed() {
        assert_eq!(Mode::All.modes(), [Mode::Lift, Mode::Typed]);
        assert_eq!(Mode::Typed.modes(), [Mode::Typed]);
    }

    #[test]
    fn the_repeat_command_names_the_mode() {
        assert_eq!(
            repeat(Mode::Typed, 7),
            "cargo xtask diff-si --mode typed --seed 7 --count 1"
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
