//! The `tests/run` suite (spec section 9): the `run` command of the binary
//! under test (`silicon`, or `silicon-check` through `cargo xtask
//! lean-check`) runs on each `.sil` file. Each `; STEP in=(...) out=(...)` line is one clock cycle: the suite
//! feeds the `in=` parts to stdin, one per line, and compares stdout with the
//! `out=` parts byte for byte. A file without STEP lines holds one
//! `; expected-error EXXX @+N` instead (for `E014`), and the suite compares
//! the code and the line only.

mod common;
mod expect;

use std::path::Path;
use std::process::Command;

use common::spawn;
use expect::{Expected, expectation, parse_report};

const STEP: &str = "; STEP ";

/// What a file expects of `silicon run`.
enum Expectation {
    /// The stdin lines and the expected stdout.
    Steps {
        stdin: String,
        stdout: String,
    },
    Error(Expected),
}

/// Parses the STEP lines of `source`, each with its LF.
fn steps(source: &str) -> Result<(String, String), String> {
    let mut stdin = String::new();
    let mut stdout = String::new();
    for (index, text) in source.lines().enumerate() {
        let Some(rest) = text.trim_start().strip_prefix(STEP) else {
            continue;
        };
        let (input, output) = rest
            .split_once(" out=")
            .filter(|(input, _)| input.starts_with("in="))
            .ok_or_else(|| format!("line {}: malformed STEP line", index + 1))?;
        stdin.push_str(input.trim_end());
        stdin.push('\n');
        stdout.push_str("out=");
        stdout.push_str(output.trim_end());
        stdout.push('\n');
    }
    Ok((stdin, stdout))
}

fn parse(source: &str) -> Result<Expectation, String> {
    let (stdin, stdout) = steps(source)?;
    match (expectation(source)?, stdin.is_empty()) {
        (None, false) => Ok(Expectation::Steps { stdin, stdout }),
        (Some(error), true) => Ok(Expectation::Error(error)),
        (None, true) => Err("no STEP line and no expected-error".to_owned()),
        (Some(_), false) => Err("both STEP lines and an expected-error".to_owned()),
    }
}

fn run(path: &Path) -> datatest_stable::Result<()> {
    let bytes = std::fs::read(path)?;
    let source = String::from_utf8_lossy(&bytes);
    let expected = parse(&source).map_err(|e| format!("{}: {e}", path.display()))?;
    let stdin = match &expected {
        Expectation::Steps { stdin, .. } => stdin.as_str(),
        Expectation::Error(_) => "",
    };
    let out = spawn(Command::new(expect::binary()).arg("run").arg(path), stdin)?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let code = out.status.code();
    match expected {
        Expectation::Steps { stdout: want, .. } if code == Some(0) && stdout == want => Ok(()),
        Expectation::Steps { stdout: want, .. } => Err(format!(
            "expected exit 0 and\n{want}got exit {code:?} and\n{stdout}{}",
            String::from_utf8_lossy(&out.stderr)
        )
        .into()),
        Expectation::Error(want) => match parse_report(&stdout) {
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
    { test = run, root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/run"), pattern = r"\.sil$" },
}
