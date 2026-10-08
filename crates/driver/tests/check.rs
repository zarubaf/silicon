//! The `tests/check` suite (spec section 9): `silicon check` runs on each
//! `.sil` file. A file with `; expected-error EXXX @+N` (or `@-N`) expects
//! that code on the line `N` lines after (or before) the comment. A file
//! without it expects `ok`. The suite compares the code and the line only.

mod common;

use std::path::Path;
use std::process::Command;

use common::spawn;

const MARKER: &str = "; expected-error ";

/// The expected error of a file: its code and its 1-based line.
#[derive(Debug, PartialEq, Eq)]
struct Expected {
    code: String,
    line: usize,
}

/// Parses `EXXX @+N` or `EXXX @-N` on the 1-based line `at`.
fn parse_expectation(rest: &str, at: usize) -> Result<Expected, String> {
    let bad = || format!("line {at}: malformed expectation `{MARKER}{rest}`");
    let (code, offset) = rest.trim().split_once(" @").ok_or_else(bad)?;
    let valid_code =
        code.len() == 4 && code.starts_with('E') && code[1..].bytes().all(|b| b.is_ascii_digit());
    if !valid_code {
        return Err(bad());
    }
    let (sign, digits) = offset.split_at_checked(1).ok_or_else(bad)?;
    let n: usize = digits.parse().map_err(|_| bad())?;
    let line = match sign {
        "+" if n >= 1 => at.checked_add(n),
        "-" if n >= 1 => at.checked_sub(n).filter(|&l| l >= 1),
        _ => None,
    }
    .ok_or_else(bad)?;
    Ok(Expected {
        code: code.to_owned(),
        line,
    })
}

/// The expectation of a file. `None` means the file must pass.
fn expectation(source: &str) -> Result<Option<Expected>, String> {
    let mut found = None;
    for (index, text) in source.lines().enumerate() {
        let Some(rest) = text.trim_start().strip_prefix(MARKER) else {
            continue;
        };
        if found.is_some() {
            return Err(format!("line {}: a second expectation", index + 1));
        }
        found = Some(parse_expectation(rest, index + 1)?);
    }
    Ok(found)
}

/// Parses the report `error[EXXX]: L:C: message`.
fn parse_report(stdout: &str) -> Option<Expected> {
    let rest = stdout.strip_prefix("error[")?;
    let (code, rest) = rest.split_once("]: ")?;
    let (line, _) = rest.split_once(':')?;
    Some(Expected {
        code: code.to_owned(),
        line: line.parse().ok()?,
    })
}

fn check(path: &Path) -> datatest_stable::Result<()> {
    let bytes = std::fs::read(path)?;
    let source = String::from_utf8_lossy(&bytes);
    let expected = expectation(&source).map_err(|e| format!("{}: {e}", path.display()))?;
    let out = spawn(
        Command::new(env!("CARGO_BIN_EXE_silicon"))
            .arg("check")
            .arg(path),
        "",
    )?;
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
