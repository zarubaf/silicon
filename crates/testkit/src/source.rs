// SPDX-License-Identifier: Apache-2.0
//! The runner of the `tests/source` suites.

use std::path::Path;
use std::process::{Command, Output};

use crate::bins::{self, silicon_check};
use crate::directive::{Expected, Marker, expected_error, top};
use crate::outcome::classify;
use crate::report::parse_report;
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

/// Compares the `elab` runs of the two front ends with the expectation of the file. Both
/// must exit 0 with equal designs, or exit 1 with an equal code, line, and column. With an
/// `expected-error`, the code and the line must also equal the directive.
fn compare_check(rust: &Output, lean: &Output, want: Option<&Expected>) -> Result<(), String> {
    let both = || {
        format!(
            "\nRust stdout:\n{}\nLean stdout:\n{}",
            String::from_utf8_lossy(&rust.stdout),
            String::from_utf8_lossy(&lean.stdout)
        )
    };
    let r = classify(rust).map_err(|e| format!("Rust `silicon elab` failed: {e}{}", both()))?;
    let l =
        classify(lean).map_err(|e| format!("Lean `silicon-check elab` failed: {e}{}", both()))?;
    if r != l {
        return Err(format!("the front ends disagree{}", both()));
    }
    match want {
        None if r.code == 0 => Ok(()),
        None => Err(format!("expected a design{}", both())),
        Some(want) => match parse_report(&String::from_utf8_lossy(&rust.stdout)) {
            Some(got) if got.code == want.code && got.line == want.line => Ok(()),
            _ => Err(format!(
                "expected error[{}] on line {}{}",
                want.code,
                want.line,
                both()
            )),
        },
    }
}

/// The `check` suite (frontend spec section 11.3): the Rust `silicon elab` and the Lean
/// `silicon-check elab` run on each `.si` file with the top selection of its `// TOP` line.
/// A file with `// expected-error SXXX @+N` (or `@-N`) expects that code on that line in
/// both, at the same column. A file without it expects the same design from both.
///
/// # Errors
///
/// Returns an error when a directive is missing or malformed, a front end misbehaves, the
/// two disagree, or the result differs from the expectation.
pub fn check(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(file)?;
    let in_file = |e: String| format!("{}: {e}", file.display());
    let top = top(&source).map_err(in_file)?;
    let want = expected_error(&source, Marker::Si).map_err(in_file)?;
    let elab =
        |mut command: Command| spawn(command.arg("elab").arg(file).arg("--top").arg(&top), "");
    let rust = elab(bins::silicon(binary))?;
    let lean = elab(Command::new(silicon_check()))?;
    Ok(compare_check(&rust, &lean, want.as_ref())?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt;
    use std::process::ExitStatus;

    fn exited(code: i32, stdout: &str) -> Output {
        Output {
            status: ExitStatus::from_raw(code << 8),
            stdout: stdout.as_bytes().to_vec(),
            stderr: Vec::new(),
        }
    }

    fn s010_on(line: usize) -> Expected {
        Expected {
            code: "S010".to_owned(),
            line,
        }
    }

    #[test]
    fn equal_errors_pass() {
        let rust = exited(1, "error[S010]: 4:8: one text\n");
        let lean = exited(1, "error[S010]: 4:8: another text\n");
        assert_eq!(compare_check(&rust, &lean, Some(&s010_on(4))), Ok(()));
    }

    #[test]
    fn a_column_difference_fails() {
        let rust = exited(1, "error[S010]: 4:8: x\n");
        let lean = exited(1, "error[S010]: 4:9: x\n");
        assert!(compare_check(&rust, &lean, Some(&s010_on(4))).is_err());
    }

    #[test]
    fn an_error_on_another_line_fails() {
        let out = exited(1, "error[S010]: 5:8: x\n");
        assert!(compare_check(&out, &out, Some(&s010_on(4))).is_err());
    }

    #[test]
    fn exit_2_fails_with_the_expected_text() {
        let rust = exited(2, "error[S010]: 4:8: x\n");
        let lean = exited(1, "error[S010]: 4:8: x\n");
        assert!(compare_check(&rust, &lean, Some(&s010_on(4))).is_err());
        assert!(compare_check(&lean, &rust, Some(&s010_on(4))).is_err());
    }

    #[test]
    fn different_designs_fail_and_show_both() {
        let rust = exited(0, "(design A)\n");
        let lean = exited(0, "(design B)\n");
        let err = compare_check(&rust, &lean, None).unwrap_err();
        assert!(
            err.contains("(design A)") && err.contains("(design B)"),
            "{err}"
        );
    }

    #[test]
    fn equal_designs_pass_and_an_error_fails_without_a_directive() {
        let ok = exited(0, "(design A)\n");
        assert_eq!(compare_check(&ok, &ok, None), Ok(()));
        let err = exited(1, "error[S010]: 4:8: x\n");
        assert!(compare_check(&err, &err, None).is_err());
    }
}
