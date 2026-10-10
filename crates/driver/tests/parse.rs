//! The `tests/source/parse` suite (frontend spec sections 8 and 11.3): the Lean
//! `silicon-check parse` and the Rust `silicon parse` run on each `.si` file.
//! They must agree on the exit code. On success they must print the same dump.
//! On an error they must print the same code and the same line and column. The
//! message text can differ (section 6.2).

mod checker;
mod common;

use std::path::Path;
use std::process::{Command, Output};

use common::spawn;

/// What the two front ends must share for one file.
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    code: Option<i32>,
    /// The full dump on success, else the prefix `error[CODE]: LINE:COL:`.
    report: String,
}

/// The part of the stdout that the two front ends must share.
fn outcome(out: &Output) -> Outcome {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let code = out.status.code();
    let report = if code == Some(0) {
        stdout.into_owned()
    } else {
        error_prefix(&stdout).unwrap_or(&stdout).to_owned()
    };
    Outcome { code, report }
}

/// The `error[CODE]: LINE:COL:` prefix of an error line.
fn error_prefix(stdout: &str) -> Option<&str> {
    let rest = stdout.strip_prefix("error[")?;
    let (_, rest) = rest.split_once("]: ")?;
    let (_, rest) = rest.split_once(':')?;
    let (_, rest) = rest.split_once(':')?;
    Some(&stdout[..stdout.len() - rest.len()])
}

fn compare(path: &Path) -> datatest_stable::Result<()> {
    let lean = outcome(&spawn(
        Command::new(checker::path()).arg("parse").arg(path),
        "",
    )?);
    let rust = outcome(&spawn(checker::silicon().arg("parse").arg(path), "")?);
    if lean == rust {
        return Ok(());
    }
    Err(format!("the front ends disagree\nLean: {lean:?}\nRust: {rust:?}").into())
}

datatest_stable::harness! {
    { test = compare, root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/source/parse"), pattern = r"\.si$" },
}
