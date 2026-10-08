//! The equivalence proof that the tests share: `circt-lec` on two modules.

use std::error::Error;

use crate::common;

/// Proves with `circt-lec` that the modules `c1` and `c2` of `mlir` are
/// equal, or reports a counterexample as `false`. The registers become ports
/// first, because `circt-lec` reads no `seq` dialect. The clock then drives
/// nothing, and its type becomes `i1` for the same reason.
///
/// # Errors
///
/// A tool does not start, or `circt-lec` gives no verdict.
pub fn equivalent(mlir: &str, c1: &str, c2: &str) -> Result<bool, Box<dyn Error>> {
    let flat = common::run(
        "circt-opt",
        &[
            "--hw-flatten-modules",
            "--externalize-registers",
            "--canonicalize",
        ],
        mlir,
    )?;
    let stderr = String::from_utf8_lossy(&flat.stderr);
    assert!(flat.status.success(), "{stderr}\n{mlir}");
    let flat = String::from_utf8(flat.stdout)?.replace("!seq.clock", "i1");
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
