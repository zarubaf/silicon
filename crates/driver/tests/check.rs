//! The `tests/check` suite (spec section 9): the `check` command of the binary under test (`silicon`, or `silicon-check`
//! through `cargo xtask lean-check`) runs on each
//! `.sil` file. A file with `; expected-error EXXX @+N` (or `@-N`) expects
//! that code on the line `N` lines after (or before) the comment. A file
//! without it expects `ok`. The suite compares the code and the line only.

mod common;
mod expect;

use std::path::Path;
use std::process::Command;

use common::spawn;
use expect::{expectation, parse_report};

fn check(path: &Path) -> datatest_stable::Result<()> {
    let bytes = std::fs::read(path)?;
    let source = String::from_utf8_lossy(&bytes);
    let expected = expectation(&source).map_err(|e| format!("{}: {e}", path.display()))?;
    let out = spawn(Command::new(expect::binary()).arg("check").arg(path), "")?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let code = out.status.code();
    match expected {
        None if code == Some(0) && stdout == "ok\n" => Ok(()),
        None => Err(format!("expected `ok`, got exit {code:?}: {stdout}").into()),
        Some(want) => match parse_report(&stdout) {
            Some(got) if code == Some(1) && got == want => Ok(()),
            _ => Err(format!(
                "expected error[{}] on line {}, got exit {code:?}: {stdout}",
                want.code, want.line
            )
            .into()),
        },
    }
}

datatest_stable::harness! {
    { test = check, root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/check"), pattern = r"\.sil$" },
}
