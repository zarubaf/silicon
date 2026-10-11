// SPDX-License-Identifier: Apache-2.0
//! The runners of the `tests/core` suites (spec section 9).

use std::io::ErrorKind;
use std::path::Path;
use std::process::{Command, Output};

use crate::bins::{silicon, under_test};
use crate::directive::{Expectation, Expected, Marker, expectation, expected_error, has_check};
use crate::report::parse_report;
use crate::spawn::spawn;

/// True when `stdout` reports the error `want`: the code and the line only.
fn reports(stdout: &str, want: &Expected) -> bool {
    parse_report(stdout).is_some_and(|got| got.code == want.code && got.line == want.line)
}

fn wrong_error(want: &Expected, code: Option<i32>, stdout: &str) -> String {
    format!(
        "expected error[{}] on line {}, got exit {code:?}: {stdout}",
        want.code, want.line
    )
}

/// The `check` suite: the `check` command of the binary under test (`silicon`,
/// or `silicon-check` through `cargo xtask lean-check`) runs on each `.sil`
/// file. A file with `; expected-error EXXX @+N` (or `@-N`) expects that code
/// on the line `N` lines after (or before) the comment. A file without it
/// expects `ok`. The suite compares the code and the line only.
///
/// # Errors
///
/// Returns an error when the output differs from the expectation.
pub fn check(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let bytes = std::fs::read(file)?;
    let source = String::from_utf8_lossy(&bytes);
    let expected =
        expected_error(&source, Marker::Sil).map_err(|e| format!("{}: {e}", file.display()))?;
    let out = spawn(Command::new(under_test(binary)).arg("check").arg(file), "")?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let code = out.status.code();
    match expected {
        None if code == Some(0) && stdout == "ok\n" => Ok(()),
        None => Err(format!("expected `ok`, got exit {code:?}: {stdout}").into()),
        Some(want) if code == Some(1) && reports(&stdout, &want) => Ok(()),
        Some(want) => Err(wrong_error(&want, code, &stdout).into()),
    }
}

/// The `run` suite: the `run` command of the binary under test runs on each
/// `.sil` file. Each `; STEP in=(...) out=(...)` line is one clock cycle: the
/// suite feeds the `in=` parts to stdin, one per line, and compares stdout with
/// the `out=` parts byte for byte. A file without STEP lines holds one
/// `; expected-error EXXX @+N` instead (for `E014`), and the suite compares the
/// code and the line only.
///
/// # Errors
///
/// Returns an error when the output differs from the expectation.
pub fn run(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let bytes = std::fs::read(file)?;
    let source = String::from_utf8_lossy(&bytes);
    let expected =
        expectation(&source, Marker::Sil).map_err(|e| format!("{}: {e}", file.display()))?;
    let stdin = match &expected {
        Expectation::Steps { stdin, .. } => stdin.as_str(),
        Expectation::Error(_) => "",
    };
    let out = spawn(Command::new(under_test(binary)).arg("run").arg(file), stdin)?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let code = out.status.code();
    match expected {
        Expectation::Steps { stdout: want, .. } if code == Some(0) && stdout == want => Ok(()),
        Expectation::Steps { stdout: want, .. } => Err(format!(
            "expected exit 0 and\n{want}got exit {code:?} and\n{stdout}{}",
            String::from_utf8_lossy(&out.stderr)
        )
        .into()),
        Expectation::Error(want) if code == Some(1) && reports(&stdout, &want) => Ok(()),
        Expectation::Error(want) => Err(wrong_error(&want, code, &stdout).into()),
    }
}

/// Runs the tool `name`, or says that it is not on `PATH`.
pub(crate) fn run_tool(name: &str, args: &[&Path], stdin: &str) -> datatest_stable::Result<Output> {
    match spawn(Command::new(name).args(args), stdin) {
        Err(e) if e.kind() == ErrorKind::NotFound => {
            Err(format!("{name} is not on PATH: run the tests in the dev shell").into())
        }
        other => Ok(other?),
    }
}

/// The `lower` suite: `silicon lower` prints the MLIR of each `.sil` file, and
/// LLVM `FileCheck` checks it against the `; CHECK:` lines of the same file.
///
/// # Errors
///
/// Returns an error when the file has no `CHECK` line, `silicon lower` fails,
/// or `FileCheck` fails.
pub fn lower(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(file)?;
    if !has_check(&source, Marker::Sil) {
        return Err(format!("{}: no `; CHECK:` line", file.display()).into());
    }
    let mlir = spawn(silicon(binary).arg("lower").arg(file), "")?;
    if !mlir.status.success() {
        return Err(failure("silicon lower", &mlir).into());
    }
    let out = run_tool("FileCheck", &[file], &String::from_utf8_lossy(&mlir.stdout))?;
    if out.status.success() {
        Ok(())
    } else {
        Err(format!("FileCheck failed: {}", String::from_utf8_lossy(&out.stderr)).into())
    }
}

fn failure(what: &str, out: &Output) -> String {
    format!(
        "{what} failed: {}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// Runs `silicon` with `args` on `file` and returns its stdout, or the failure.
fn run_silicon(binary: &Path, args: &[&str], file: &Path) -> datatest_stable::Result<String> {
    let out = spawn(silicon(binary).args(args).arg(file), "")?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(failure(&format!("silicon {}", args.join(" ")), &out).into())
    }
}

/// The smoke checks of a corpus file: `silicon check` prints `ok`, the `silicon lower` output
/// parses with `circt-opt`, and `silicon verilog` and `silicon verilog --models` succeed.
pub(crate) fn smoke(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    if run_silicon(binary, &["check"], file)? != "ok\n" {
        return Err("silicon check did not print `ok`".into());
    }
    let mlir = run_silicon(binary, &["lower"], file)?;
    let out = run_tool("circt-opt", &[], &mlir)?;
    if !out.status.success() {
        return Err(failure("circt-opt", &out).into());
    }
    run_silicon(binary, &["verilog"], file)?;
    run_silicon(binary, &["verilog", "--models"], file)?;
    Ok(())
}

/// The `corpus` smoke suite: each `.sil` file passes `silicon check`, its
/// `silicon lower` output parses with `circt-opt`, and `silicon verilog` and
/// `silicon verilog --models` succeed. The files carry no expectations. The LEC
/// and the differential tests of spec section 8 are the oracles of their
/// contents.
///
/// # Errors
///
/// Returns an error when one of the commands fails.
pub fn corpus(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    smoke(binary, file)
}
