//! The `tests/source/parse` suite (frontend spec sections 8 and 11.3): the Lean
//! `silicon-check parse` and the Rust `silicon parse` run on each `.si` file.
//! They must agree on the exit code. On success they must print the same dump.
//! On an error they must print the same code and the same line and column. The
//! message text can differ (section 6.2).

mod checker;
mod common;
mod outcome;

use std::path::Path;
use std::process::Command;

use common::spawn;
use outcome::classify;

fn compare(path: &Path) -> datatest_stable::Result<()> {
    let lean = classify(&spawn(
        Command::new(checker::path()).arg("parse").arg(path),
        "",
    )?)
    .map_err(|e| format!("Lean `silicon-check parse` failed: {e}"))?;
    let rust = classify(&spawn(checker::silicon().arg("parse").arg(path), "")?)
        .map_err(|e| format!("Rust `silicon parse` failed: {e}"))?;
    if lean == rust {
        return Ok(());
    }
    Err(format!("the front ends disagree\nLean: {lean:?}\nRust: {rust:?}").into())
}

datatest_stable::harness! {
    { test = compare, root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/source/parse"), pattern = r"\.si$" },
}
