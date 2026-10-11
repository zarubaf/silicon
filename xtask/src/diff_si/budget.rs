// SPDX-License-Identifier: Apache-2.0
//! The budget mode. The fuel equal to the `cost` of a typed program
//! succeeds, and one unit less gives `S015`, in both front ends (front-end
//! spec 5.4 and 11.4, mode 4). A random lower fuel tests the order of the
//! charges, which `cost` does not show. A random depth must give the same
//! outcome in both front ends, and only `S015` may reject.

use std::path::Path;

use anyhow::Result;
use proptest::prelude::any;
use proptest::strategy::{Just, Strategy};
use syntax::r#gen::{BuildFault, Program, typed};
use testkit::Outcome;

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
    outcome.code == 1 && outcome.report.starts_with(b"error[S015]:")
}

/// The exit code and the report of `outcome`, for a message.
fn show(outcome: &Outcome) -> String {
    format!(
        "exit {}, {}",
        outcome.code,
        String::from_utf8_lossy(&outcome.report).trim_end()
    )
}

/// `None` if both front ends agree on all budget runs of `case`, else the
/// message of the first difference. It names the flag and its value. A
/// tooling error, and a fault of the builder, is an `Err`.
pub(super) fn verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<String>> {
    let (program, fuel_pick, depth_pick) = case;
    let program = program
        .as_ref()
        .map_err(|e| anyhow::Error::new(e.clone()))?;
    let file = write(dir, "budget.si", &program.text())?;
    let top = program.top();
    let cost = match outcome(tools, "cost", &file, &top, &[])? {
        Ok(cost) if cost.code == 0 => cost,
        Ok(cost) => return Ok(Some(format!("cost: rejected the program: {}", show(&cost)))),
        Err(message) => return Ok(Some(format!("cost: {message}"))),
    };
    let Some(total) = total_of(&cost.report) else {
        return Ok(Some(
            "cost: the report has no `total N` first line".to_owned(),
        ));
    };
    let run = |flag: &str, value: u64| -> Result<std::result::Result<Outcome, String>> {
        let value = value.to_string();
        Ok(outcome(tools, "elab", &file, &top, &[flag, &value])?
            .map_err(|message| format!("with `{flag} {value}`: {message}")))
    };
    match run("--fuel", total)? {
        Ok(at) if at.code == 0 => {}
        Ok(at) => {
            return Ok(Some(format!(
                "with `--fuel {total}`: both front ends rejected: {}",
                show(&at)
            )));
        }
        Err(message) => return Ok(Some(message)),
    }
    let lower = [total.checked_sub(1), fuel_below(total, *fuel_pick)];
    for fuel in lower.into_iter().flatten() {
        match run("--fuel", fuel)? {
            Ok(rejected) if s015(&rejected) => {}
            Ok(other) => {
                return Ok(Some(format!(
                    "with `--fuel {fuel}`: expected S015 (cost is {total}), both gave {}",
                    show(&other)
                )));
            }
            Err(message) => return Ok(Some(message)),
        }
    }
    let depth = depth_of(*depth_pick);
    match run("--depth", depth)? {
        Ok(out) if out.code == 0 || s015(&out) => Ok(None),
        Ok(other) => Ok(Some(format!(
            "with `--depth {depth}`: expected success or S015, both gave {}",
            show(&other)
        ))),
        Err(message) => Ok(Some(message)),
    }
}

/// Prints the failure of seed `seed`: the message, the program as a
/// `tests/source/budget` file, and the repeat command. The fuel is the
/// total of `silicon-check`, the reference.
pub(super) fn report(tools: &Tools, dir: &Path, seed: u64, case: &Case, message: &str) {
    println!("FAIL seed {seed} (budget): {message}");
    // A failure has a program: a builder fault is an error, not a failure.
    let (Ok(program), _, _) = case else {
        return;
    };
    let top = program.top();
    let text = program.text();
    let total = |binary: &Path| -> Option<u64> {
        let file = write(dir, "report.si", &text).ok()?;
        let out = testkit::spawn::spawn(
            std::process::Command::new(binary)
                .arg("cost")
                .arg(&file)
                .args(["--top", &top]),
            "",
        )
        .ok()?;
        total_of(&out.stdout)
    };
    let fuel = total(&tools.lean).or_else(|| total(&tools.silicon));
    print!("{}", budget_file(&text, &top, fuel));
    println!("Run `{}` to repeat it.", repeat(Mode::Budget, seed));
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
