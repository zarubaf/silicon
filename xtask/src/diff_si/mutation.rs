// SPDX-License-Identifier: Apache-2.0
//! The mutation mode. One mutation of a typed program goes through both
//! front ends (front-end spec 11.4, mode 3). They must reject it with the
//! same first code, line, and column, or accept it with the same design.
//! Where the pass order makes the first code certain, the generator
//! predicts it, and an agreed code that differs is a failure of the
//! generator.

use std::collections::BTreeMap;
use std::path::Path;

use anyhow::{Context, Result, anyhow};
use proptest::prelude::any;
use proptest::strategy::{Just, Strategy};
use syntax::r#gen::{BuildFault, Program, mutate, typed};
use testkit::{Report, parse_report};

use super::{Mode, Tools, outcome, repeat, write};

/// A typed program, or the fault of its builder, and the draws of the
/// kind and the site of the mutation.
pub(super) type Case = (Result<Program, BuildFault>, u32, u32);

/// The number of mutants by the code that both front ends reported, or by
/// `accepted`.
pub(super) type Tally = BTreeMap<String, u64>;

/// The key of a mutant that both front ends accept.
const ACCEPTED: &str = "accepted";

/// Random typed programs, each with a kind and a site. The program comes
/// first in the draw, so the seed `n` gives the program of the typed mode.
pub(super) fn cases() -> impl Strategy<Value = Case> {
    typed().prop_flat_map(|program| (Just(program), any::<u32>(), any::<u32>()))
}

/// `None` if the front ends agree on the mutant of `case` and the
/// prediction of the generator holds; the agreed code goes into `tally`.
/// Else the message of the disagreement. A tooling error, and a fault of
/// the builder, is an `Err`.
pub(super) fn verdict(
    tools: &Tools,
    dir: &Path,
    case: &Case,
    tally: &mut Tally,
) -> Result<Option<String>> {
    let (program, kind, site) = case;
    let program = program
        .as_ref()
        .map_err(|e| anyhow::Error::new(e.clone()))?;
    let mutant = mutate(program, *kind, *site);
    if mutant.text == program.text() {
        return Ok(Some("gen: the mutant equals the program".to_owned()));
    }
    let file = write(dir, "mutant.si", &mutant.text)?;
    let agreed = match outcome(tools, "elab", &file, &program.top(), &[])? {
        Ok(agreed) => agreed,
        Err(message) => return Ok(Some(message)),
    };
    let code = if agreed.code == 0 {
        ACCEPTED.to_owned()
    } else {
        parse_report(&String::from_utf8_lossy(&agreed.report))
            .ok_or_else(|| anyhow!("the agreed rejection has no report"))?
            .code
    };
    if let Some(expect) = mutant.expect
        && expect != code
    {
        return Ok(Some(format!(
            "gen: predicted {expect} for `{}`, both front ends gave {code}",
            mutant.what
        )));
    }
    *tally.entry(code).or_default() += 1;
    Ok(None)
}

/// Prints the failure of seed `seed`: the message, the shrunk mutant as a
/// `tests/source/check` file, and the repeat command. The expected error
/// comes from `silicon-check`, the reference elaborator. A spawn error is
/// an `Err`.
pub(super) fn report(
    tools: &Tools,
    dir: &Path,
    seed: u64,
    case: &Case,
    message: &str,
) -> Result<()> {
    println!("FAIL seed {seed} (mutation): {message}");
    // A failure has a program: a builder fault is an error, not a failure.
    let (Ok(program), kind, site) = case else {
        return Ok(());
    };
    let mutant = mutate(program, *kind, *site);
    let top = program.top();
    let file = write(dir, "report.si", &mutant.text)?;
    let lean = lean_report(tools, &file, &top)?;
    print!(
        "{}",
        check_file(&mutant.text, &top, &mutant.what, lean.as_ref())
    );
    println!("Run `{}` to repeat it.", repeat(Mode::Mutation, seed));
    Ok(())
}

/// The report of `silicon-check elab` on `file`, or why it has none. A
/// spawn error is an `Err`.
fn lean_report(
    tools: &Tools,
    file: &Path,
    top: &str,
) -> Result<std::result::Result<Report, String>> {
    let out = testkit::spawn::spawn(
        std::process::Command::new(&tools.lean)
            .arg("elab")
            .arg(file)
            .args(["--top", top]),
        "",
    )
    .with_context(|| format!("cannot run {}", tools.lean.display()))?;
    let code = out.status.code();
    Ok(match parse_report(&String::from_utf8_lossy(&out.stdout)) {
        Some(report) if code == Some(1) => Ok(report),
        _ if code == Some(0) => Err("silicon-check accepts the mutant".to_owned()),
        _ => Err(format!("silicon-check gave no report, exit {code:?}")),
    })
}

/// The text of a `tests/source/check` file for the mutant `text`. The
/// directive is on line 3, so mutant line `L` is file line `3 + L` and the
/// offset is `L`. Without a Lean report, line 3 is a comment that says
/// why, and the file expects success.
fn check_file(
    text: &str,
    top: &str,
    what: &str,
    lean: std::result::Result<&Report, &String>,
) -> String {
    let line3 = match lean {
        Ok(r) => format!("// expected-error {} @+{}\n", r.code, r.line),
        Err(why) => format!("// {why}: no expected-error\n"),
    };
    format!("// TOP {top}\n// mutation: {what}\n{line3}{text}")
}

/// The success line for `count` mutants of the seeds `seed` to `last`.
pub(super) fn summary(count: u64, seed: u64, last: u64, tally: &Tally) -> String {
    let accepted = tally.get(ACCEPTED).copied().unwrap_or(0);
    let rejected: Vec<(&String, &u64)> = tally
        .iter()
        .filter(|(code, _)| code.as_str() != ACCEPTED)
        .collect();
    let total: u64 = rejected.iter().map(|(_, n)| **n).sum();
    let codes = if rejected.is_empty() {
        String::new()
    } else {
        let codes: Vec<String> = rejected
            .iter()
            .map(|(code, n)| format!("{code} {n}"))
            .collect();
        format!(" ({})", codes.join(", "))
    };
    format!(
        "diff-si: {count} mutants agree (seeds {seed} to {last}): {total} rejected{codes}, {accepted} accepted"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_check_reproducer_points_at_the_lean_error() {
        let text = "module M0() domains() {\n    output o0: Bool;\n}\n";
        let lean = Report {
            code: "S018".into(),
            line: 1,
            col: 1,
        };
        assert_eq!(
            check_file(text, "M0()", "delete statement 2 of M0", Ok(&lean)),
            format!(
                "// TOP M0()\n// mutation: delete statement 2 of M0\n// expected-error S018 @+1\n{text}"
            )
        );
        let accepted = "silicon-check accepts the mutant".to_owned();
        assert_eq!(
            check_file(text, "M0()", "delete statement 2 of M0", Err(&accepted)),
            format!(
                "// TOP M0()\n// mutation: delete statement 2 of M0\n// silicon-check accepts the mutant: no expected-error\n{text}"
            )
        );
    }

    #[test]
    fn the_tally_names_each_code() {
        let tally: Tally = [("S003", 2), ("S007", 1), ("accepted", 1)]
            .into_iter()
            .map(|(code, n)| (code.to_owned(), n))
            .collect();
        assert_eq!(
            summary(4, 1, 4, &tally),
            "diff-si: 4 mutants agree (seeds 1 to 4): 3 rejected (S003 2, S007 1), 1 accepted"
        );
    }
}
