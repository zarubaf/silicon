//! The `; expected-error EXXX @+N` expectation (spec section 9), the
//! error report `error[EXXX]: L:C: message` (spec 6.4.2), and the binary
//! under test, which the `tests/check` and `tests/run` suites share.

use std::path::PathBuf;

/// The binary that the shared suites `check` and `run` test: `SILICON_BIN`
/// if it is set, else `silicon`. `cargo xtask lean-check` sets `SILICON_BIN`
/// to the absolute path of `silicon-check`. A relative path fails, because
/// the tests run in another folder. A `SILICON_BIN` left in the shell also
/// changes the binary of `just test`.
pub fn binary() -> PathBuf {
    std::env::var_os("SILICON_BIN").map_or_else(
        || PathBuf::from(env!("CARGO_BIN_EXE_silicon")),
        PathBuf::from,
    )
}

const MARKER: &str = "; expected-error ";

/// The expected error of a file: its code and its 1-based line.
#[derive(Debug, PartialEq, Eq)]
pub struct Expected {
    pub code: String,
    pub line: usize,
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
pub fn expectation(source: &str) -> Result<Option<Expected>, String> {
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
pub fn parse_report(stdout: &str) -> Option<Expected> {
    let rest = stdout.strip_prefix("error[")?;
    let (code, rest) = rest.split_once("]: ")?;
    let (line, _) = rest.split_once(':')?;
    Some(Expected {
        code: code.to_owned(),
        line: line.parse().ok()?,
    })
}
