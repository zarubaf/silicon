//! The `tests/corpus` smoke suite (spec section 9): each `.sil` file passes
//! `silicon check`, its `silicon lower` output parses with `circt-opt`, and
//! `silicon verilog` and `silicon verilog --models` succeed. The files carry
//! no expectations. The LEC and the differential tests of spec section 8 are
//! the oracles of their contents.

mod checker;
mod common;

use std::io::ErrorKind;
use std::path::Path;
use std::process::{Command, Output};

use common::spawn;

/// Runs `silicon` with `args` and returns its stdout, or the failure.
fn silicon(args: &[&str], path: &Path) -> datatest_stable::Result<String> {
    let out = spawn(checker::silicon().args(args).arg(path), "")?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(failure(&format!("silicon {}", args.join(" ")), &out))
    }
}

fn failure(what: &str, out: &Output) -> Box<dyn std::error::Error + Send + Sync> {
    format!(
        "{what} failed: {}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
    .into()
}

/// Checks that `circt-opt` parses `mlir`.
fn parses(mlir: &str) -> datatest_stable::Result<()> {
    let out = match spawn(&mut Command::new("circt-opt"), mlir) {
        Err(e) if e.kind() == ErrorKind::NotFound => {
            return Err("circt-opt is not on PATH: run the tests in the dev shell".into());
        }
        other => other?,
    };
    if out.status.success() {
        Ok(())
    } else {
        Err(failure("circt-opt", &out))
    }
}

fn smoke(path: &Path) -> datatest_stable::Result<()> {
    if silicon(&["check"], path)? != "ok\n" {
        return Err("silicon check did not print `ok`".into());
    }
    parses(&silicon(&["lower"], path)?)?;
    silicon(&["verilog"], path)?;
    silicon(&["verilog", "--models"], path)?;
    Ok(())
}

datatest_stable::harness! {
    { test = smoke, root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/corpus"), pattern = r"\.sil$" },
}
