// SPDX-License-Identifier: Apache-2.0
//! The equivalence proof that the tests share: `circt-lec` on two modules.

use std::error::Error;

use crate::common;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

/// Runs `circt-opt` with `passes` on `mlir`, and returns its output.
fn opt(mlir: &str, passes: &[&str]) -> Result<String> {
    let out = common::run("circt-opt", passes, mlir)?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{stderr}\n{mlir}");
    Ok(String::from_utf8(out.stdout)?)
}

/// The modules of `mlir` with each register as a port: an input for its
/// value and an output for its next value. `circt-lec` reads no `seq`
/// dialect, so the clock, which then drives nothing, becomes an `i1`.
///
/// # Errors
///
/// `circt-opt` does not start.
pub fn externalized(mlir: &str) -> Result<String> {
    let passes = [
        "--hw-flatten-modules",
        "--externalize-registers",
        "--canonicalize",
    ];
    Ok(opt(mlir, &passes)?.replace("!seq.clock", "i1"))
}

/// Proves that the modules `c1` and `c2` of `mlir`, which has no register,
/// are equal, or reports a counterexample as `false`.
///
/// # Errors
///
/// A tool does not start, or `circt-lec` gives no verdict.
pub fn prove(mlir: &str, c1: &str, c2: &str) -> Result<bool> {
    let flat = opt(mlir, &["--hw-flatten-modules"])?;
    let z3 = std::env::var("SILICON_Z3_LIB").map_err(|_| "SILICON_Z3_LIB is not set")?;
    let out = common::run(
        "circt-lec",
        &[
            "-",
            &format!("--c1={c1}"),
            &format!("--c2={c2}"),
            "--run",
            &format!("--shared-libs={z3}"),
        ],
        &flat,
    )?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    match stdout.trim() {
        "c1 == c2" => Ok(true),
        "c1 != c2" => Ok(false),
        other => Err(format!("unexpected `circt-lec` output: {other}").into()),
    }
}
