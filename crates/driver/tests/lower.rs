//! The `tests/lower` suite (spec section 9): `silicon lower` prints the MLIR
//! of each `.sil` file, and LLVM `FileCheck` checks it against the `; CHECK:`
//! lines of the same file.

mod checker;
mod common;

use std::io::ErrorKind;
use std::path::Path;
use std::process::Command;

use common::spawn;

/// True for a line that starts with a `FileCheck` directive.
fn is_directive(line: &str) -> bool {
    ["", "-DAG", "-NEXT", "-NOT", "-LABEL"]
        .iter()
        .any(|kind| line.starts_with(&format!("; CHECK{kind}:")))
}

fn lower(path: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(path)?;
    if !source.lines().any(is_directive) {
        return Err(format!("{}: no `; CHECK:` line", path.display()).into());
    }
    let mlir = spawn(checker::silicon().arg("lower").arg(path), "")?;
    if !mlir.status.success() {
        return Err(format!(
            "silicon lower failed: {}{}",
            String::from_utf8_lossy(&mlir.stdout),
            String::from_utf8_lossy(&mlir.stderr)
        )
        .into());
    }
    let mut file_check = Command::new("FileCheck");
    file_check.arg(path);
    let out = match spawn(&mut file_check, &String::from_utf8_lossy(&mlir.stdout)) {
        Err(e) if e.kind() == ErrorKind::NotFound => {
            return Err("FileCheck is not on PATH: run the tests in the dev shell".into());
        }
        other => other?,
    };
    if out.status.success() {
        Ok(())
    } else {
        Err(format!("FileCheck failed: {}", String::from_utf8_lossy(&out.stderr)).into())
    }
}

datatest_stable::harness! {
    { test = lower, root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/lower"), pattern = r"\.sil$" },
}
