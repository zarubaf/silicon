//! Translation validation of the input: the Lean `silicon-check` checks the
//! bytes that the Rust compiler read, before it emits (spec sections 6.4.2
//! and 8.1).

use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::process::{Command, Stdio};

/// The variable that names the checker. Without it, the search path finds
/// `silicon-check`.
pub const VARIABLE: &str = "SILICON_CHECK";

const DEFAULT: &str = "silicon-check";

/// What the Lean checker said about a design.
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    Accepted,
    /// The stdout of the checker: the error line.
    Rejected(Vec<u8>),
}

/// Runs the Lean checker on `source`. The error is a usage error message.
pub fn validate(source: &[u8]) -> Result<Verdict, String> {
    let checker = std::env::var_os(VARIABLE).unwrap_or_else(|| OsString::from(DEFAULT));
    validate_with(&checker, source)
}

/// The checker gets the bytes on stdin, not the path of the file. A file that
/// changes after the read thus cannot reach the output unchecked.
fn validate_with(checker: &OsStr, source: &[u8]) -> Result<Verdict, String> {
    let shown = checker.to_string_lossy();
    let mut child = Command::new(checker)
        // `silicon-check` reads a file, and this path is the pipe.
        .args(["check", "/dev/stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|e| start_error(&shown, &e))?;
    if let Some(mut pipe) = child.stdin.take() {
        // A checker that exits before it reads all input closes the pipe;
        // its exit code then tells the story.
        match pipe.write_all(source) {
            Err(e) if e.kind() != io::ErrorKind::BrokenPipe => {
                return Err(format!("cannot write to the checker `{shown}`: {e}"));
            }
            _ => {}
        }
    }
    let output = child
        .wait_with_output()
        .map_err(|e| format!("the checker `{shown}` did not finish: {e}"))?;
    match output.status.code() {
        Some(0) => Ok(Verdict::Accepted),
        // Only an error line is a rejection of the design (spec section 6.4.2).
        Some(1) if output.stdout.starts_with(b"error[") => Ok(Verdict::Rejected(output.stdout)),
        _ => Err(format!(
            "the checker `{shown}` failed ({}). Use --no-validate to skip the validation.",
            output.status
        )),
    }
}

fn start_error(shown: &str, error: &io::Error) -> String {
    format!(
        "cannot run the checker `{shown}`: {error}. Set {VARIABLE} to its path, or use --no-validate to skip the validation."
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const VALID: &[u8] =
        b"(design d (module d (input a (bits 1)) (output q (bits 1)) (assign q a)))";
    const E004: &[u8] = b"(design d (module d (input a (bits 1)) (input b (bits 2)) (output q (bits 1)) (assign q (add a b))))";

    /// The same rule as `testkit::bins::silicon_check`: `SILICON_CHECK`, else the Lake build.
    fn real() -> OsString {
        std::env::var_os(VARIABLE).unwrap_or_else(|| {
            concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../lean/.lake/build/bin/silicon-check"
            )
            .into()
        })
    }

    #[test]
    fn the_checker_accepts_the_bytes_it_gets() {
        assert_eq!(validate_with(&real(), VALID), Ok(Verdict::Accepted));
    }

    /// The bytes decide, so no file on disk can change the verdict.
    #[test]
    fn the_checker_rejects_bad_bytes_with_its_error_line() {
        let Ok(Verdict::Rejected(line)) = validate_with(&real(), E004) else {
            panic!("the real checker accepted a bad design");
        };
        assert!(line.starts_with(b"error[E004]: "), "{line:?}");
    }

    #[test]
    fn exit_1_without_an_error_line_is_a_checker_failure() {
        let error = validate_with(OsStr::new("false"), VALID).unwrap_err();
        assert!(error.contains("--no-validate"), "{error}");
    }

    /// `ls` exits with 2 for the unknown file `check`.
    #[test]
    fn another_exit_code_is_a_checker_failure() {
        let error = validate_with(OsStr::new("ls"), VALID).unwrap_err();
        assert!(error.contains("failed"), "{error}");
    }
}
