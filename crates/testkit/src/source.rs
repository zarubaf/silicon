//! The runner of the `tests/source` suites.

use std::path::Path;
use std::process::Command;

use crate::bins::{self, silicon_check};
use crate::outcome::classify;
use crate::spawn::spawn;

/// The `parse` suite (frontend spec sections 8 and 11.3): the Lean
/// `silicon-check parse` and the Rust `silicon parse` run on each `.si` file.
/// They must agree on the exit code. On success they must print the same dump.
/// On an error they must print the same code and the same line and column. The
/// message text can differ (section 6.2).
///
/// # Errors
///
/// Returns an error when a front end misbehaves or the two disagree.
pub fn parse(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let lean = classify(&spawn(
        Command::new(silicon_check()).arg("parse").arg(file),
        "",
    )?)
    .map_err(|e| format!("Lean `silicon-check parse` failed: {e}"))?;
    let rust = classify(&spawn(bins::silicon(binary).arg("parse").arg(file), "")?)
        .map_err(|e| format!("Rust `silicon parse` failed: {e}"))?;
    if lean == rust {
        return Ok(());
    }
    Err(format!("the front ends disagree\nLean: {lean:?}\nRust: {rust:?}").into())
}
