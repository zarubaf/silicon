// SPDX-License-Identifier: Apache-2.0
//! Translation validation of the input: the Lean `silicon-check` checks the
//! bytes that the Rust compiler read, before it emits (spec sections 6.4.2
//! and 8.1).

use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::path::Path;
use std::process::{Command, Output, Stdio};

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
    validate_with(&checker(), source)
}

fn checker() -> OsString {
    std::env::var_os(VARIABLE).unwrap_or_else(|| OsString::from(DEFAULT))
}

/// Runs the checker with `args` and gives it `stdin` as its input. The checker
/// gets the bytes on stdin, not the path of the file. A file that changes
/// after the read thus cannot reach the output unchecked.
fn run_checker_with(checker: &OsStr, args: &[&OsStr], stdin: &[u8]) -> Result<Output, String> {
    let shown = checker.to_string_lossy();
    let mut child = Command::new(checker)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|e| start_error(&shown, &e))?;
    if let Some(mut pipe) = child.stdin.take() {
        // A checker that exits before it reads all input closes the pipe;
        // its exit code then tells the story.
        match pipe.write_all(stdin) {
            Err(e) if e.kind() != io::ErrorKind::BrokenPipe => {
                return Err(format!("cannot write to the checker `{shown}`: {e}"));
            }
            _ => {}
        }
    }
    child
        .wait_with_output()
        .map_err(|e| format!("the checker `{shown}` did not finish: {e}"))
}

/// What the Lean checker said about the elaboration of a source file.
#[derive(Debug, PartialEq, Eq)]
pub enum Elaborated {
    Accepted,
    /// The stdout of the checker. Rust accepted the source, so the Lean rejection or the
    /// mismatch with the core IR of Rust is a defect of the Rust front end.
    Defect(Vec<u8>),
}

/// Runs `silicon-check validate` on `source` and the core IR file `sil`. `budget` holds the
/// budget flags, which the checker reads before the file. The error is a usage error message.
pub fn validate_elaboration(
    source: &[u8],
    top: &str,
    sil: &Path,
    budget: &[String],
) -> Result<Elaborated, String> {
    let args = validate_args(top, sil, budget);
    let checker = checker();
    let output = run_checker_with(&checker, &args, source)?;
    elaborated(&output).map_err(|()| failed(&checker.to_string_lossy(), &output))
}

/// The arguments of `silicon-check validate`: the budget flags come before the file.
fn validate_args<'a>(top: &'a str, sil: &'a Path, budget: &'a [String]) -> Vec<&'a OsStr> {
    let mut args = vec![OsStr::new("validate")];
    args.extend(budget.iter().map(OsStr::new));
    args.extend([
        // `silicon-check` reads a file, and this path is the pipe.
        OsStr::new("/dev/stdin"),
        OsStr::new("--top"),
        OsStr::new(top),
        sil.as_os_str(),
    ]);
    args
}

/// Only `ok`, an error line, or a mismatch line is a verdict (spec section 6.4.2). Any other
/// outcome is a failure of the checker.
fn elaborated(output: &Output) -> Result<Elaborated, ()> {
    match output.status.code() {
        Some(0) if output.stdout == b"ok\n" => Ok(Elaborated::Accepted),
        Some(1)
            if output.stdout.starts_with(b"error[")
                || output.stdout.starts_with(b"mismatch at line") =>
        {
            Ok(Elaborated::Defect(output.stdout.clone()))
        }
        _ => Err(()),
    }
}

fn validate_with(checker: &OsStr, source: &[u8]) -> Result<Verdict, String> {
    // `silicon-check` reads a file, and this path is the pipe.
    let args = [OsStr::new("check"), OsStr::new("/dev/stdin")];
    let output = run_checker_with(checker, &args, source)?;
    match output.status.code() {
        Some(0) => Ok(Verdict::Accepted),
        // Only an error line is a rejection of the design (spec section 6.4.2).
        Some(1) if output.stdout.starts_with(b"error[") => Ok(Verdict::Rejected(output.stdout)),
        _ => Err(failed(&checker.to_string_lossy(), &output)),
    }
}

fn failed(shown: &str, output: &Output) -> String {
    format!(
        "the checker `{shown}` failed ({}). Use --no-validate to skip the validation.",
        output.status
    )
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

    #[test]
    fn the_checker_accepts_the_bytes_it_gets() {
        assert_eq!(
            validate_with(testkit::bins::silicon_check().as_os_str(), VALID),
            Ok(Verdict::Accepted)
        );
    }

    /// The bytes decide, so no file on disk can change the verdict.
    #[test]
    fn the_checker_rejects_bad_bytes_with_its_error_line() {
        let Ok(Verdict::Rejected(line)) =
            validate_with(testkit::bins::silicon_check().as_os_str(), E004)
        else {
            panic!("the real checker accepted a bad design");
        };
        assert!(line.starts_with(b"error[E004]: "), "{line:?}");
    }

    fn exited(code: i32, stdout: &[u8]) -> Output {
        use std::os::unix::process::ExitStatusExt;
        Output {
            status: std::process::ExitStatus::from_raw(code << 8),
            stdout: stdout.to_vec(),
            stderr: Vec::new(),
        }
    }

    #[test]
    fn a_mismatch_line_is_a_defect() {
        let line = b"mismatch at line 3: expected `a`, found `b`\n";
        assert_eq!(
            elaborated(&exited(1, line)),
            Ok(Elaborated::Defect(line.to_vec()))
        );
    }

    #[test]
    fn a_lean_error_line_is_a_defect() {
        let line = b"error[S003]: 1:1: unknown name\n";
        assert_eq!(
            elaborated(&exited(1, line)),
            Ok(Elaborated::Defect(line.to_vec()))
        );
    }

    #[test]
    fn exit_1_with_another_line_is_a_checker_failure() {
        assert_eq!(elaborated(&exited(1, b"other\n")), Err(()));
    }

    #[test]
    fn exit_0_without_ok_is_a_checker_failure() {
        assert_eq!(elaborated(&exited(0, b"")), Err(()));
        assert_eq!(elaborated(&exited(0, b"ok")), Err(()));
    }

    #[test]
    fn the_checker_gets_the_budgets_before_the_file() {
        let budget = ["--syntax-depth", "100", "--fuel", "161", "--depth", "50"].map(String::from);
        let args = validate_args("T(1)", Path::new("x.sil"), &budget);
        let expected = [
            "validate",
            "--syntax-depth",
            "100",
            "--fuel",
            "161",
            "--depth",
            "50",
            "/dev/stdin",
            "--top",
            "T(1)",
            "x.sil",
        ];
        assert_eq!(args, expected.map(OsStr::new));
    }

    #[test]
    fn exit_0_is_accepted() {
        assert_eq!(elaborated(&exited(0, b"ok\n")), Ok(Elaborated::Accepted));
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
