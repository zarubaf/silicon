// SPDX-License-Identifier: Apache-2.0
//! The budget mode. The fuel equal to the `cost` of a typed program
//! succeeds, and one unit less gives `S015`, in both front ends (front-end
//! spec 5.4 and 11.4, mode 4). A random lower fuel tests the order of the
//! charges, which `cost` does not show. A random depth must give the same
//! outcome in both front ends, and only `S015` may reject.

use std::path::Path;
use std::process::Command;

use anyhow::{Context, Result};
use proptest::prelude::any;
use proptest::strategy::{Just, Strategy};
use srcgen::{BuildFault, Program, typed};
use testkit::{Outcome, parse_report};

use super::{Mode, Tools, outcome, repeat, write};

/// A typed program, or the fault of its builder, and the draws of the
/// lower fuel and of the depth.
pub(super) type Case = (Result<Program, BuildFault>, u32, u32);

/// Random typed programs, each with two draws. The program comes first in
/// the draw, so the seed `n` gives the program of the typed mode.
pub(super) fn cases() -> impl Strategy<Value = Case> {
    typed().prop_flat_map(|program| (Just(program), any::<u32>(), any::<u32>()))
}

/// The total of a `cost` report: the number on its first line, `total N`.
fn total_of(stdout: &[u8]) -> Option<u64> {
    let text = std::str::from_utf8(stdout).ok()?;
    text.lines().next()?.strip_prefix("total ")?.parse().ok()
}

/// A fuel in `1..total` for the draw `pick`, or `None` if there is none.
fn fuel_below(total: u64, pick: u32) -> Option<u64> {
    (total >= 2).then(|| 1 + u64::from(pick) % (total - 1))
}

/// A depth in `1..=8` for the draw `pick`. Generated programs nest up to
/// about ten levels.
fn depth_of(pick: u32) -> u64 {
    1 + u64::from(pick) % 8
}

/// Whether `outcome` is a rejection with the code `S015`.
fn s015(outcome: &Outcome) -> bool {
    outcome.code == 1
        && parse_report(&String::from_utf8_lossy(&outcome.report)).is_some_and(|r| r.code == "S015")
}

/// The exit code and the report of `outcome`, for a message.
fn show(outcome: &Outcome) -> String {
    format!(
        "exit {}, {}",
        outcome.code,
        String::from_utf8_lossy(&outcome.report).trim_end()
    )
}

/// An `elab` run with one budget flag, and the outcome that both front
/// ends must give.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Run {
    flag: &'static str,
    value: u64,
    expect: &'static str,
}

/// A failure of the budget mode: its message, the agreed total of `cost`
/// if the front ends reached it, and the failing `elab` run, if any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Failure {
    message: String,
    total: Option<u64>,
    run: Option<Run>,
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// `None` if both front ends agree on all budget runs of `case`, else the
/// first difference. Its message names the flag and its value. A tooling
/// error, and a fault of the builder, is an `Err`.
pub(super) fn verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<Failure>> {
    let (program, fuel_pick, depth_pick) = case;
    let program = program
        .as_ref()
        .map_err(|e| anyhow::Error::new(e.clone()))?;
    let file = write(dir, "budget.si", &program.text())?;
    let top = program.top();
    let at_cost = |message: String| Failure {
        message,
        total: None,
        run: None,
    };
    let cost = match outcome(tools, "cost", &file, &top, &[])? {
        Ok(cost) if cost.code == 0 => cost,
        Ok(cost) => {
            let message = format!("cost: rejected the program: {}", show(&cost));
            return Ok(Some(at_cost(message)));
        }
        Err(message) => return Ok(Some(at_cost(format!("cost: {message}")))),
    };
    let Some(total) = total_of(&cost.report) else {
        let message = "cost: the report has no `total N` first line".to_owned();
        return Ok(Some(at_cost(message)));
    };
    // `None` if both front ends give the outcome that `run` expects.
    let check = |run: Run, allowed: &dyn Fn(&Outcome) -> bool| -> Result<Option<Failure>> {
        let value = run.value.to_string();
        let message = match outcome(tools, "elab", &file, &top, &[run.flag, &value])? {
            Ok(out) if allowed(&out) => return Ok(None),
            Ok(out) => format!(
                "with `{} {value}`: expected {} (cost is {total}), both gave {}",
                run.flag,
                run.expect,
                show(&out)
            ),
            Err(message) => format!("with `{} {value}`: {message}", run.flag),
        };
        Ok(Some(Failure {
            message,
            total: Some(total),
            run: Some(run),
        }))
    };
    let fuel = |value: u64, expect: &'static str| Run {
        flag: "--fuel",
        value,
        expect,
    };
    if let Some(failure) = check(fuel(total, "success"), &|out| out.code == 0)? {
        return Ok(Some(failure));
    }
    let lower = [total.checked_sub(1), fuel_below(total, *fuel_pick)];
    for value in lower.into_iter().flatten() {
        if let Some(failure) = check(fuel(value, "S015"), &s015)? {
            return Ok(Some(failure));
        }
    }
    let depth = Run {
        flag: "--depth",
        value: depth_of(*depth_pick),
        expect: "success or S015",
    };
    check(depth, &|out| out.code == 0 || s015(out))
}

/// The failing run of `failure` that no budget file holds: a run below
/// `total - 1`, or a `--depth` run. A budget file `// FUEL total` checks
/// the runs at the total and one below it.
fn unfiled(failure: &Failure) -> Option<&Run> {
    let run = failure.run.as_ref()?;
    let filed = run.flag == "--fuel" && failure.total.is_some_and(|t| run.value + 1 >= t);
    (!filed).then_some(run)
}

/// Prints the failure of seed `seed`: the message, a reproducer, and the
/// repeat command. The reproducer is a `tests/source/budget` file if one
/// holds the failing run; its fuel is the agreed total, else the total of
/// `silicon-check`, the reference. Else it is the failing commands and
/// their outputs, for a test of `crates/driver/tests/cli.rs`. A spawn
/// error is an `Err`.
pub(super) fn report(
    tools: &Tools,
    dir: &Path,
    seed: u64,
    case: &Case,
    failure: &Failure,
) -> Result<()> {
    println!("FAIL seed {seed} (budget): {failure}");
    // A failure has a program: a builder fault is an error, not a failure.
    let (Ok(program), _, _) = case else {
        return Ok(());
    };
    let top = program.top();
    let text = program.text();
    let file = write(dir, "report.si", &text)?;
    let run_on = |binary: &Path, command: &str, flags: &[&str]| {
        let mut front_end = Command::new(binary);
        front_end
            .arg(command)
            .arg(&file)
            .args(["--top", &top])
            .args(flags);
        testkit::spawn::spawn(&mut front_end, "")
            .with_context(|| format!("cannot run {}", binary.display()))
    };
    if let Some(run) = unfiled(failure) {
        let value = run.value.to_string();
        let shown = |binary: &Path| -> Result<String> {
            let out = run_on(binary, "elab", &[run.flag, &value])?;
            Ok(format!(
                "exit {:?}\n{}{}",
                out.status.code(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ))
        };
        let outputs = (shown(&tools.silicon)?, shown(&tools.lean)?);
        print!("{}", commands(&text, &top, run, &outputs));
    } else {
        let total = |binary: &Path| -> Result<Option<u64>> {
            Ok(total_of(&run_on(binary, "cost", &[])?.stdout))
        };
        let fuel = match failure.total {
            Some(fuel) => Some(fuel),
            None => match total(&tools.lean)? {
                Some(fuel) => Some(fuel),
                None => total(&tools.silicon)?,
            },
        };
        print!("{}", budget_file(&text, &top, fuel));
    }
    println!("Run `{}` to repeat it.", repeat(Mode::Budget, seed));
    Ok(())
}

/// The reproducer of the run `run` that no budget file holds: the program
/// `text`, the two failing commands, and their `outputs`, Rust then Lean.
fn commands(text: &str, top: &str, run: &Run, outputs: &(String, String)) -> String {
    let args = format!("budget.si --top '{top}' {} {}", run.flag, run.value);
    format!(
        "No budget file holds the run with `{flag} {value}`; both front ends must give {expect}. \
         Add a test to crates/driver/tests/cli.rs that runs these commands through `agree`:\n\
         silicon elab {args}\nsilicon-check elab {args}\n\
         Rust output: {rust}\nLean output: {lean}\nbudget.si:\n{text}",
        flag = run.flag,
        value = run.value,
        expect = run.expect,
        rust = outputs.0.trim_end(),
        lean = outputs.1.trim_end(),
    )
}

/// The text of a `tests/source/budget` file for the program `text`.
fn budget_file(text: &str, top: &str, fuel: Option<u64>) -> String {
    let fuel = fuel.map(|n| format!("// FUEL {n}\n")).unwrap_or_default();
    format!("// TOP {top}\n{fuel}{text}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_total_comes_from_the_first_line() {
        assert_eq!(total_of(b"total 1234\nM0 1000\n"), Some(1234));
        assert_eq!(total_of(b"cost 5\n"), None);
        assert_eq!(total_of(b""), None);
    }

    #[test]
    fn the_random_fuel_stays_below_the_total() {
        assert_eq!(fuel_below(1234, 0), Some(1));
        assert!((1..=1233).contains(&fuel_below(1234, u32::MAX).unwrap()));
        assert_eq!(fuel_below(1, 9), None);
        assert_eq!(depth_of(0), 1);
        assert_eq!(depth_of(7), 8);
        assert_eq!(depth_of(8), 1);
    }

    fn rejected(code: i32, report: &str) -> Outcome {
        Outcome {
            code,
            report: report.as_bytes().to_vec(),
        }
    }

    #[test]
    fn only_s015_is_a_budget_error() {
        assert!(s015(&rejected(1, "error[S015]: 3:5:")));
        assert!(!s015(&rejected(1, "error[S013]: 3:5:")));
        assert!(!s015(&rejected(0, "error[S015]: 3:5:")));
    }

    fn failure_at(flag: &'static str, value: u64) -> Failure {
        Failure {
            message: format!("with `{flag} {value}`: x"),
            total: Some(928),
            run: Some(Run {
                flag,
                value,
                expect: "S015",
            }),
        }
    }

    /// The reproducer that `report` prints for `failure`, without the
    /// tools: the commands, or the budget file at the agreed total.
    fn reproducer_of(failure: &Failure) -> String {
        let text = "module M0() domains() {\n}\n";
        let outputs = (
            "exit Some(0)\n(design)".to_owned(),
            "exit Some(1)\nerror[S015]: 1:1: x".to_owned(),
        );
        match unfiled(failure) {
            Some(run) => commands(text, "M0()", run, &outputs),
            None => budget_file(text, "M0()", failure.total),
        }
    }

    #[test]
    fn a_lower_fuel_failure_prints_its_commands() {
        let got = reproducer_of(&failure_at("--fuel", 37));
        assert!(
            got.contains("silicon elab budget.si --top 'M0()' --fuel 37\n"),
            "{got}"
        );
        assert!(
            got.contains("silicon-check elab budget.si --top 'M0()' --fuel 37\n"),
            "{got}"
        );
        assert!(got.contains("must give S015"), "{got}");
        assert!(got.contains("error[S015]: 1:1: x"), "{got}");
        assert!(!got.contains("// FUEL"), "{got}");
    }

    #[test]
    fn a_depth_failure_prints_its_commands() {
        let got = reproducer_of(&failure_at("--depth", 3));
        assert!(
            got.contains("elab budget.si --top 'M0()' --depth 3\n"),
            "{got}"
        );
        assert!(!got.contains("// FUEL"), "{got}");
    }

    #[test]
    fn a_failure_at_the_cost_or_one_below_is_a_budget_file() {
        for value in [927, 928] {
            let got = reproducer_of(&failure_at("--fuel", value));
            assert!(got.starts_with("// TOP M0()\n// FUEL 928\n"), "{got}");
        }
        let cost = Failure {
            message: "cost: x".to_owned(),
            total: None,
            run: None,
        };
        assert_eq!(unfiled(&cost), None);
    }

    #[test]
    fn the_budget_reproducer_is_a_budget_file() {
        let text = "module M0() domains() {\n}\n";
        assert_eq!(
            budget_file(text, "M0()", Some(57)),
            format!("// TOP M0()\n// FUEL 57\n{text}")
        );
        assert_eq!(
            budget_file(text, "M0()", None),
            format!("// TOP M0()\n{text}")
        );
    }
}
