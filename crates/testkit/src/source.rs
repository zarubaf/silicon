// SPDX-License-Identifier: Apache-2.0
//! The runner of the `tests/source` suites.

use std::path::Path;
use std::process::{Command, Output};

use crate::bins::{self, silicon_check};
use crate::core::{run_tool, smoke};
use crate::directive::{
    BudgetKind, Expectation, Expected, Marker, budgets, expectation, expected_error, has_check,
    has_observe, top,
};
use crate::outcome::{Outcome, classify};
use crate::report::{message_matches, parse_report};
use crate::spawn::spawn;

/// Runs `command` of the two front ends on `file` with the further arguments `args` and `stdin`.
/// Returns the Rust output, then the Lean output.
fn run_both(
    binary: &Path,
    command: &str,
    file: &Path,
    args: &[&str],
    stdin: &str,
) -> std::io::Result<(Output, Output)> {
    let run = |mut front_end: Command| spawn(front_end.arg(command).arg(file).args(args), stdin);
    Ok((
        run(bins::silicon(binary))?,
        run(Command::new(silicon_check()))?,
    ))
}

/// Runs `command` of the two front ends on `file` with the arguments `args`. They must give the
/// same exit code, 0 or 1. On success they must print the same stdout. On an error they must print
/// the same code, line, and column; the message can differ (section 6.2). Returns the Rust output.
///
/// # Errors
///
/// Returns the reason when a front end misbehaves or the two disagree.
pub fn agreed(binary: &Path, command: &str, file: &Path, args: &[&str]) -> Result<Output, String> {
    let (rust, lean) = run_both(binary, command, file, args, "").map_err(|e| e.to_string())?;
    agree(command, &rust, &lean)?;
    Ok(rust)
}

/// The agreement rule of the two front ends on one run of `command`: both exit 0 or 1, and they
/// print the same dump or the same code, line, and column. Returns the common outcome.
///
/// # Errors
///
/// Returns the reason when a front end misbehaves or the two disagree.
pub fn agree(command: &str, rust: &Output, lean: &Output) -> Result<Outcome, String> {
    let rust_outcome =
        classify(rust).map_err(|e| format!("Rust `silicon {command}` failed: {e}"))?;
    let lean_outcome =
        classify(lean).map_err(|e| format!("Lean `silicon-check {command}` failed: {e}"))?;
    if rust_outcome == lean_outcome {
        return Ok(rust_outcome);
    }
    Err(format!(
        "the front ends disagree\nRust: {rust_outcome:?}\nLean: {lean_outcome:?}"
    ))
}

/// The suites of `tests/source` whose runner compares `expected-error` and `expected-message`.
/// The `elab`, `budget`, and `corpus` runners do not read them.
pub const MESSAGE_SUITES: [&str; 3] = ["parse", "check", "run"];

/// The `parse` suite (frontend spec sections 8 and 11.3): the Lean
/// `silicon-check parse` and the Rust `silicon parse` run on each `.si` file.
/// They must agree as `agree` says. A file with `// expected-error SXXX @+N` (or `@-N`) expects
/// that code on that line in both, as `check` does. A file without it expects both to succeed
/// with the same dump.
///
/// # Errors
///
/// Returns an error when a directive is malformed, a front end misbehaves, the two disagree,
/// or the result differs from the expectation.
pub fn parse(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(file)?;
    let in_file = |e: String| format!("{}: {e}", file.display());
    let want = expected_error(&source, Marker::Si).map_err(in_file)?;
    let (rust, lean) = run_both(binary, "parse", file, &[], "")?;
    Ok(compare_check("parse", &rust, &lean, want.as_ref()).map_err(in_file)?)
}

/// Compares the runs of the command `name` in the two front ends with the expectation of the
/// file. The two must agree as `agree` says. With an `expected-error`, the code and the line
/// must also equal the directive; with an `expected-message` too, both front ends must print
/// exactly that message. Without an `expected-error`, both must succeed.
fn compare_check(
    name: &str,
    rust: &Output,
    lean: &Output,
    want: Option<&Expected>,
) -> Result<(), String> {
    let outputs = || {
        format!(
            "\nRust stdout:\n{}\nLean stdout:\n{}",
            String::from_utf8_lossy(&rust.stdout),
            String::from_utf8_lossy(&lean.stdout)
        )
    };
    let r = agree(name, rust, lean).map_err(|e| format!("{e}{}", outputs()))?;
    match want {
        None if r.code == 0 => Ok(()),
        None => Err(format!("expected success{}", outputs())),
        Some(want) => match parse_report(&String::from_utf8_lossy(&rust.stdout)) {
            Some(got) if r.code == 1 && got.code == want.code && got.line == want.line => {
                compare_message(want, lean).map_err(|e| format!("{e}{}", outputs()))?;
                compare_message(want, rust).map_err(|e| format!("{e}{}", outputs()))
            }
            _ => Err(format!(
                "expected error[{}] on line {}{}",
                want.code,
                want.line,
                outputs()
            )),
        },
    }
}

/// Checks that the report in `out` holds exactly the message of `want`, if it has one.
fn compare_message(want: &Expected, out: &Output) -> Result<(), String> {
    let Some(message) = &want.message else {
        return Ok(());
    };
    if message_matches(&String::from_utf8_lossy(&out.stdout), Some(message)) {
        Ok(())
    } else {
        Err(format!("expected the message `{message}`"))
    }
}

/// What a front end printed for `observe`: the record lines, as bytes, then the error line, if
/// the exit code is 1.
pub struct Observed {
    pub records: Vec<u8>,
    pub error: Option<String>,
}

/// Splits the output of `observe` into its records and its error line. The records end at the
/// last line when the exit code is 1, and that line is a report `error[XNNN]: L:C: message`.
///
/// # Errors
///
/// Returns the reason if the exit code is neither 0 nor 1, or if the output at exit 1 does not
/// end with a report line.
pub fn split_observed(out: &Output) -> Result<Observed, String> {
    match out.status.code() {
        Some(0) => Ok(Observed {
            records: out.stdout.clone(),
            error: None,
        }),
        Some(1) => {
            let body = out.stdout.strip_suffix(b"\n").unwrap_or(&out.stdout);
            let at = body.iter().rposition(|&b| b == b'\n').map_or(0, |i| i + 1);
            let (records, line) = out.stdout.split_at(at);
            let line = String::from_utf8_lossy(line);
            if parse_report(&line).is_none() {
                return Err(format!(
                    "exit 1 without an error line at the end\nstdout: {}",
                    String::from_utf8_lossy(&out.stdout)
                ));
            }
            Ok(Observed {
                records: records.to_vec(),
                error: Some(line.into_owned()),
            })
        }
        _ => Err(format!(
            "neither exit 0 nor exit 1\nstatus: {}\nstdout: {}\nstderr: {}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )),
    }
}

/// Compares the `observe` runs of the two front ends (section 11.3): the same exit code, the
/// same record lines byte for byte, and, with exit 1, the same code, line, and column in the
/// error line. The message of the error line is compared only when `want` holds an
/// `expected-message`, as `compare_check` does.
///
/// # Errors
///
/// Returns the first difference between the two runs.
pub fn compare_observe(
    rust: &Output,
    lean: &Output,
    want: Option<&Expected>,
) -> Result<(), String> {
    let outputs = || {
        format!(
            "\nRust stdout:\n{}\nLean stdout:\n{}",
            String::from_utf8_lossy(&rust.stdout),
            String::from_utf8_lossy(&lean.stdout)
        )
    };
    let r = split_observed(rust).map_err(|e| format!("Rust `silicon observe` failed: {e}"))?;
    let l =
        split_observed(lean).map_err(|e| format!("Lean `silicon-check observe` failed: {e}"))?;
    if r.records != l.records {
        return Err(format!("the records differ{}", outputs()));
    }
    match (&r.error, &l.error) {
        (None, None) => Ok(()),
        (Some(a), Some(b)) => {
            if parse_report(a) != parse_report(b) {
                return Err(format!("the error lines disagree{}", outputs()));
            }
            let message = want.and_then(|w| w.message.as_deref());
            for (front_end, line) in [("Rust", a), ("Lean", b)] {
                if !message_matches(line, message) {
                    return Err(format!(
                        "{front_end}: expected the message `{}`{}",
                        message.unwrap_or_default(),
                        outputs()
                    ));
                }
            }
            Ok(())
        }
        _ => Err(format!("the exit codes differ{}", outputs())),
    }
}

/// True when the text of a file may call `diagnostic`. A cheap scan is enough: a file without a
/// call has no record, and the compare of `observe` costs two runs.
#[must_use]
pub fn makes_records(source: &str) -> bool {
    source.contains("diagnostic")
}

/// The compare of `compare_observe` on `file` with the top selection `top` and the flags
/// `flags`, if the text of the file makes records or has `OBSERVE` lines. Then each front end
/// must pass `FileCheck` with the prefix `OBSERVE` on its output, if the file has such lines.
fn observed_agree(
    binary: &Path,
    file: &Path,
    source: &str,
    top: &str,
    flags: &[&str],
    want: Option<&Expected>,
) -> Result<(), String> {
    let lines = has_observe(source, Marker::Si);
    if !lines && !makes_records(source) {
        return Ok(());
    }
    let (rust, lean) = both(binary, "observe", file, top, flags, "").map_err(|e| e.to_string())?;
    compare_observe(&rust, &lean, want)?;
    if !lines {
        return Ok(());
    }
    let prefix = Path::new("--check-prefix=OBSERVE");
    for (front_end, out) in [("Rust `silicon", &rust), ("Lean `silicon-check", &lean)] {
        let stdout = String::from_utf8_lossy(&out.stdout);
        let checked = run_tool("FileCheck", &[prefix, file], &stdout).map_err(|e| e.to_string())?;
        if !checked.status.success() {
            return Err(format!(
                "FileCheck failed on the output of {front_end} observe`: {}\n{stdout}",
                String::from_utf8_lossy(&checked.stderr)
            ));
        }
    }
    Ok(())
}

/// Runs `command` of the two front ends on `file` with the top selection `top`, the further
/// arguments `flags`, and `stdin`. Returns the Rust output, then the Lean output.
fn both(
    binary: &Path,
    command: &str,
    file: &Path,
    top: &str,
    flags: &[&str],
    stdin: &str,
) -> std::io::Result<(Output, Output)> {
    let args = [&["--top", top], flags].concat();
    run_both(binary, command, file, &args, stdin)
}

/// The `check` suite (frontend spec section 11.3): the Rust `silicon elab` and the Lean
/// `silicon-check elab` run on each `.si` file with the top selection of its `// TOP` line.
/// A file with `// expected-error SXXX @+N` (or `@-N`) expects that code on that line in
/// both, at the same column; a following `// expected-message: TEXT` pins the exact message.
/// A file without it expects the same design from both. A file that calls `diagnostic` also
/// gets the compare of `observe`.
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
    let (rust, lean) = both(binary, "elab", file, &top, &[], "")?;
    compare_check("elab", &rust, &lean, want.as_ref()).map_err(in_file)?;
    Ok(observed_agree(binary, file, &source, &top, &[], want.as_ref()).map_err(in_file)?)
}

/// Compares the `run` runs of the two front ends with the expectation of the file. With
/// STEP lines, both must exit 0 and print the `out=` lines byte for byte. With an
/// `expected-error`, both must report it as `compare_check` says.
fn compare_run(rust: &Output, lean: &Output, want: &Expectation) -> Result<(), String> {
    match want {
        Expectation::Error(error) => compare_check("run", rust, lean, Some(error)),
        Expectation::Steps { stdout, .. } => {
            compare_check("run", rust, lean, None)?;
            if rust.stdout == stdout.as_bytes() {
                return Ok(());
            }
            Err(format!(
                "expected\n{stdout}got\n{}",
                String::from_utf8_lossy(&rust.stdout)
            ))
        }
    }
}

/// The `run` suite (frontend spec section 11.2): the Rust `silicon run` and the Lean
/// `silicon-check run` run on each `.si` file with the top selection of its `// TOP` line.
/// Each `// STEP in=(...) out=(...)` line is one clock cycle: the suite feeds the `in=`
/// parts to stdin and compares stdout with the `out=` parts byte for byte, in both front
/// ends. A file without STEP lines holds one `// expected-error` instead. A file that calls
/// `diagnostic` also gets the compare of `observe`.
///
/// # Errors
///
/// Returns an error when a directive is missing or malformed, a front end misbehaves, the
/// two disagree, or the result differs from the expectation.
pub fn run(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(file)?;
    let in_file = |e: String| format!("{}: {e}", file.display());
    let top = top(&source).map_err(in_file)?;
    let want = expectation(&source, Marker::Si).map_err(in_file)?;
    let stdin = match &want {
        Expectation::Steps { stdin, .. } => stdin.as_str(),
        Expectation::Error(_) => "",
    };
    let (rust, lean) = both(binary, "run", file, &top, &[], stdin)?;
    compare_run(&rust, &lean, &want).map_err(in_file)?;
    let error = match &want {
        Expectation::Error(error) => Some(error),
        Expectation::Steps { .. } => None,
    };
    Ok(observed_agree(binary, file, &source, &top, &[], error).map_err(in_file)?)
}

/// The `elab` suite (frontend spec section 11.3): the Rust `silicon elab` and the Lean
/// `silicon-check elab` run on each `.si` file with the top selection of its `// TOP` line.
/// LLVM `FileCheck` checks the output of each against the `// CHECK:` lines of the same
/// file, so both front ends must pass the same checks.
///
/// # Errors
///
/// Returns an error when the file has no `CHECK` line, a directive is malformed, a front end
/// fails, or `FileCheck` fails on either output.
pub fn elab(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(file)?;
    let in_file = |e: String| format!("{}: {e}", file.display());
    if !has_check(&source, Marker::Si) {
        return Err(in_file("no `// CHECK:` line".to_owned()).into());
    }
    let top = top(&source).map_err(in_file)?;
    let (rust, lean) = both(binary, "elab", file, &top, &[], "")?;
    filecheck_agreed(file, &rust, &lean).map_err(in_file)?;
    Ok(observed_agree(binary, file, &source, &top, &[], None).map_err(in_file)?)
}

/// Requires that the two outputs of `elab` agree as `agree` says, then runs `FileCheck` with
/// `file` on each. A `CHECK` file can cover a part of the output, so `agree` comes first.
fn filecheck_agreed(file: &Path, rust: &Output, lean: &Output) -> Result<(), String> {
    let agreed = agree("elab", rust, lean)?;
    if agreed.code != 0 {
        return Err(format!(
            "`elab` failed in both front ends: {}",
            String::from_utf8_lossy(&rust.stdout)
        ));
    }
    for (front_end, out) in [("Rust `silicon", rust), ("Lean `silicon-check", lean)] {
        let stdout = String::from_utf8_lossy(&out.stdout);
        let checked = run_tool("FileCheck", &[file], &stdout).map_err(|e| e.to_string())?;
        if !checked.status.success() {
            return Err(format!(
                "FileCheck failed on the output of {front_end} elab`: {}\n{stdout}",
                String::from_utf8_lossy(&checked.stderr)
            ));
        }
    }
    Ok(())
}

/// Compares the `elab` runs of the two front ends one unit below a budget of kind `kind`. Both
/// must exit 1 with the code of `kind`, at the same line and column.
fn compare_below(kind: BudgetKind, rust: &Output, lean: &Output) -> Result<(), String> {
    let code = kind.code();
    match parse_report(&String::from_utf8_lossy(&rust.stdout)) {
        // The budget fixes only the code. `compare_check` makes the Lean report agree with the
        // line and the column of the Rust report.
        Some(got) => compare_check(
            "elab",
            rust,
            lean,
            Some(&Expected {
                code: code.to_owned(),
                line: got.line,
                message: None,
            }),
        ),
        None => compare_check("elab", rust, lean, None)
            .and_then(|()| Err(format!("expected error[{code}], got a success"))),
    }
}

/// The `budget` suite (frontend spec sections 5.4 and 11.3): the Rust `silicon elab` and the
/// Lean `silicon-check elab` run on each `.si` file with the top selection of its `// TOP`
/// line, once for each `// FUEL N`, `// DEPTH N`, or `// SYNTAX-DEPTH N` line. With the
/// budget N, both front ends succeed with the same design; the file has no `expected-error`. With N - 1, both front ends fail
/// with `S015` (`S001` for `SYNTAX-DEPTH`) at the same line and column. Last, `cost` with the
/// default budgets exits 0 in both and prints the same stdout. A file that calls `diagnostic`
/// also gets the compare of `observe` at each limit.
///
/// # Errors
///
/// Returns an error when the file has no budget, a directive is malformed, a front end
/// misbehaves, the two disagree, or a result differs from the expectation.
pub fn budget(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(file)?;
    let in_file = |e: String| format!("{}: {e}", file.display());
    let top = top(&source).map_err(in_file)?;
    if expected_error(&source, Marker::Si)
        .map_err(in_file)?
        .is_some()
    {
        return Err(in_file("a budget file takes no `expected-error`".to_owned()).into());
    }
    let budgets = budgets(&source).map_err(in_file)?;
    if budgets.is_empty() {
        return Err(in_file("no budget line".to_owned()).into());
    }
    for budget in budgets {
        let flag = budget.kind.flag();
        let at = budget.limit.to_string();
        let below = (budget.limit - 1).to_string();
        let (rust, lean) = both(binary, "elab", file, &top, &[flag, &at], "")?;
        compare_check("elab", &rust, &lean, None)
            .map_err(|e| in_file(format!("with `{flag} {at}`: {e}")))?;
        observed_agree(binary, file, &source, &top, &[flag, &at], None)
            .map_err(|e| in_file(format!("with `{flag} {at}`: {e}")))?;
        let (rust, lean) = both(binary, "elab", file, &top, &[flag, &below], "")?;
        compare_below(budget.kind, &rust, &lean)
            .map_err(|e| in_file(format!("with `{flag} {below}`: {e}")))?;
    }
    let (rust, lean) = both(binary, "cost", file, &top, &[], "")?;
    compare_cost(&rust, &lean).map_err(in_file)?;
    Ok(())
}

/// Compares the `cost` runs of the two front ends. Both must exit 0, and print equal stdout.
fn compare_cost(rust: &Output, lean: &Output) -> Result<(), String> {
    let outputs = || {
        format!(
            "\nRust stdout:\n{}\nLean stdout:\n{}",
            String::from_utf8_lossy(&rust.stdout),
            String::from_utf8_lossy(&lean.stdout)
        )
    };
    for (front_end, out) in [("Rust `silicon", rust), ("Lean `silicon-check", lean)] {
        match classify(out) {
            Ok(o) if o.code == 0 => {}
            Ok(_) => return Err(format!("{front_end} cost` did not succeed{}", outputs())),
            Err(e) => return Err(format!("{front_end} cost` failed: {e}{}", outputs())),
        }
    }
    if rust.stdout == lean.stdout {
        return Ok(());
    }
    Err(format!("`cost` differs{}", outputs()))
}

/// The `corpus` suite (frontend spec section 8): the Rust `silicon elab` writes the core IR of
/// each `.si` file, with the top selection of its `// TOP` line, to a temporary `.sil` file.
/// The Lean `silicon-check validate` must accept it. Then the smoke checks of the `corpus`
/// suite of `tests/core` run on it. The files carry no other expectations.
///
/// # Errors
///
/// Returns an error when the `TOP` line is missing or malformed, `elab` fails, `validate`
/// rejects the output, or a smoke check fails.
pub fn corpus(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    let source = std::fs::read_to_string(file)?;
    let in_file = |e: String| format!("{}: {e}", file.display());
    let top = top(&source).map_err(in_file)?;
    let elab = spawn(
        bins::silicon(binary)
            .arg("elab")
            .arg(file)
            .arg("--top")
            .arg(&top),
        "",
    )?;
    if !elab.status.success() {
        return Err(in_file(format!(
            "Rust `silicon elab` failed: {}{}",
            String::from_utf8_lossy(&elab.stdout),
            String::from_utf8_lossy(&elab.stderr)
        ))
        .into());
    }
    let name = file.file_stem().unwrap_or_default().to_string_lossy();
    let sil =
        std::env::temp_dir().join(format!("testkit-corpus-{}-{name}.sil", std::process::id()));
    std::fs::write(&sil, &elab.stdout)?;
    let result = validate_and_smoke(binary, file, &top, &sil);
    // The file is a scratch copy; a failed removal must not hide the result.
    let _ = std::fs::remove_file(&sil);
    Ok(result.map_err(in_file)?)
}

/// Lean `validate` of the core IR `sil` of `file`, then the smoke checks on `sil`.
fn validate_and_smoke(binary: &Path, file: &Path, top: &str, sil: &Path) -> Result<(), String> {
    let validated = spawn(
        Command::new(silicon_check())
            .arg("validate")
            .arg(file)
            .arg(sil)
            .arg("--top")
            .arg(top),
        "",
    )
    .map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&validated.stdout);
    if validated.status.code() != Some(0) || stdout != "ok\n" {
        return Err(format!(
            "Lean `silicon-check validate` did not print `ok`: exit {:?}: {stdout}{}",
            validated.status.code(),
            String::from_utf8_lossy(&validated.stderr)
        ));
    }
    smoke(binary, sil).map_err(|e| e.to_string())
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
            message: None,
        }
    }

    #[test]
    fn agree_takes_equal_errors_with_other_messages() {
        let rust = exited(1, "error[S010]: 4:8: one\n");
        let lean = exited(1, "error[S010]: 4:8: another\n");
        let got = agree("parse", &rust, &lean).unwrap();
        assert_eq!(
            got,
            Outcome {
                code: 1,
                report: b"error[S010]: 4:8:".to_vec()
            }
        );
    }

    #[test]
    fn agree_fails_on_another_column() {
        let rust = exited(1, "error[S010]: 4:8: one\n");
        let lean = exited(1, "error[S010]: 4:9: one\n");
        let err = agree("parse", &rust, &lean).unwrap_err();
        assert!(err.contains("the front ends disagree"), "{err}");
    }

    #[test]
    fn agree_fails_on_exit_3() {
        let rust = exited(3, "");
        let lean = exited(0, "");
        let err = agree("elab", &rust, &lean).unwrap_err();
        assert!(err.starts_with("Rust `silicon elab` failed"), "{err}");
    }

    #[test]
    fn elab_outputs_that_differ_fail_before_filecheck() {
        let rust = exited(0, "(design A)\n");
        let lean = exited(0, "(design A)\n(extra)\n");
        let err = filecheck_agreed(Path::new("/nonexistent"), &rust, &lean).unwrap_err();
        assert!(err.contains("the front ends disagree"), "{err}");
    }

    #[test]
    fn elab_needs_a_check_line() {
        let dir = std::env::temp_dir().join(format!("testkit-elab-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("none.si");
        std::fs::write(&file, "// TOP M()\nmodule M() domains() {}\n").unwrap();
        let err = elab(Path::new("/nonexistent"), &file).unwrap_err();
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(err.to_string().contains("no `// CHECK:` line"), "{err}");
    }

    #[test]
    fn a_budget_file_takes_no_expected_error() {
        let dir = std::env::temp_dir().join(format!("testkit-budget-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("err.si");
        std::fs::write(
            &file,
            "// TOP M()\n// FUEL 5\n// expected-error S010 @+1\nmodule M() domains() {}\n",
        )
        .unwrap();
        let err = budget(Path::new("/nonexistent"), &file).unwrap_err();
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(
            err.to_string().contains("takes no `expected-error`"),
            "{err}"
        );
    }

    #[test]
    fn equal_errors_pass() {
        let rust = exited(1, "error[S010]: 4:8: one text\n");
        let lean = exited(1, "error[S010]: 4:8: another text\n");
        assert_eq!(
            compare_check("elab", &rust, &lean, Some(&s010_on(4))),
            Ok(())
        );
    }

    #[test]
    fn an_equal_message_passes_and_another_fails() {
        let out = exited(1, "error[S010]: 4:8: the text: here\n");
        let want = |text: &str| Expected {
            message: Some(text.to_owned()),
            ..s010_on(4)
        };
        assert_eq!(
            compare_check("elab", &out, &out, Some(&want("the text: here"))),
            Ok(())
        );
        let err = compare_check("elab", &out, &out, Some(&want("other"))).unwrap_err();
        assert!(err.contains("expected the message `other`"), "{err}");
        let lean = exited(1, "error[S010]: 4:8: another\n");
        assert!(compare_check("elab", &out, &lean, Some(&want("the text: here"))).is_err());
    }

    const RECORD: &str = "(record 4 3 M () (string \"a\") (int 1))\n";

    #[test]
    fn equal_records_pass_with_or_without_an_error() {
        let ok = exited(0, RECORD);
        assert_eq!(compare_observe(&ok, &ok, None), Ok(()));
        let none = exited(0, "");
        assert_eq!(compare_observe(&none, &none, None), Ok(()));
        let stop = exited(1, &format!("{RECORD}error[S010]: 5:3: x\n"));
        assert_eq!(compare_observe(&stop, &stop, None), Ok(()));
        let only = exited(1, "error[S001]: 1:1: x\n");
        assert_eq!(compare_observe(&only, &only, None), Ok(()));
    }

    #[test]
    fn records_that_differ_fail_and_show_both() {
        let rust = exited(0, RECORD);
        let lean = exited(0, "(record 4 3 M () (string \"a\") (int 2))\n");
        let err = compare_observe(&rust, &lean, None).unwrap_err();
        assert!(err.contains("the records differ"), "{err}");
        assert!(err.contains("(int 1)") && err.contains("(int 2)"), "{err}");
        let fewer = exited(0, "");
        assert!(compare_observe(&rust, &fewer, None).is_err());
        let before_error = exited(1, &format!("{RECORD}error[S010]: 5:3: x\n"));
        let other = exited(
            1,
            "(record 4 3 M () (string \"b\") (int 1))\nerror[S010]: 5:3: x\n",
        );
        let err = compare_observe(&before_error, &other, None).unwrap_err();
        assert!(err.contains("the records differ"), "{err}");
    }

    #[test]
    fn an_error_line_with_another_message_passes() {
        let rust = exited(1, &format!("{RECORD}error[S010]: 5:3: one\n"));
        let lean = exited(1, &format!("{RECORD}error[S010]: 5:3: another\n"));
        assert_eq!(compare_observe(&rust, &lean, None), Ok(()));
    }

    #[test]
    fn another_column_or_code_in_the_error_line_fails() {
        let rust = exited(1, &format!("{RECORD}error[S010]: 5:3: x\n"));
        let column = exited(1, &format!("{RECORD}error[S010]: 5:4: x\n"));
        let err = compare_observe(&rust, &column, None).unwrap_err();
        assert!(err.contains("the error lines disagree"), "{err}");
        let line = exited(1, &format!("{RECORD}error[S010]: 6:3: x\n"));
        assert!(compare_observe(&rust, &line, None).is_err());
        let code = exited(1, &format!("{RECORD}error[S011]: 5:3: x\n"));
        assert!(compare_observe(&rust, &code, None).is_err());
    }

    #[test]
    fn an_expected_message_is_compared_in_the_error_line() {
        let want = Expected {
            message: Some("the text".to_owned()),
            ..s010_on(5)
        };
        let good = exited(1, &format!("{RECORD}error[S010]: 5:3: the text\n"));
        assert_eq!(compare_observe(&good, &good, Some(&want)), Ok(()));
        let other = exited(1, &format!("{RECORD}error[S010]: 5:3: other\n"));
        let err = compare_observe(&good, &other, Some(&want)).unwrap_err();
        assert!(
            err.contains("Lean: expected the message `the text`"),
            "{err}"
        );
        let err = compare_observe(&other, &good, Some(&want)).unwrap_err();
        assert!(
            err.contains("Rust: expected the message `the text`"),
            "{err}"
        );
        // Without the directive, the message is free.
        assert_eq!(compare_observe(&good, &other, Some(&s010_on(5))), Ok(()));
    }

    #[test]
    fn observe_fails_on_other_exit_codes_and_on_a_missing_error_line() {
        let ok = exited(0, RECORD);
        let stop = exited(1, &format!("{RECORD}error[S010]: 5:3: x\n"));
        let err = compare_observe(&ok, &stop, None).unwrap_err();
        assert!(err.contains("the exit codes differ"), "{err}");
        assert!(compare_observe(&stop, &ok, None).is_err());
        let usage = exited(2, "");
        let err = compare_observe(&usage, &usage, None).unwrap_err();
        assert!(err.starts_with("Rust `silicon observe` failed"), "{err}");
        let defect = exited(3, RECORD);
        assert!(compare_observe(&ok, &defect, None).is_err());
        let bare = exited(1, RECORD);
        let err = compare_observe(&bare, &bare, None).unwrap_err();
        assert!(err.contains("without an error line"), "{err}");
    }

    #[test]
    fn only_a_file_that_makes_records_gets_the_observe_compare() {
        assert!(makes_records("diagnostic(\"a\", 1);"));
        assert!(!makes_records("module M() {}"));
        // No front end runs for a file without records or `OBSERVE` lines.
        assert_eq!(
            observed_agree(
                Path::new("/nonexistent"),
                Path::new("/nonexistent"),
                "module M() {}",
                "M()",
                &[],
                None
            ),
            Ok(())
        );
    }

    #[test]
    fn a_column_difference_fails() {
        let rust = exited(1, "error[S010]: 4:8: x\n");
        let lean = exited(1, "error[S010]: 4:9: x\n");
        assert!(compare_check("elab", &rust, &lean, Some(&s010_on(4))).is_err());
    }

    #[test]
    fn an_error_on_another_line_fails() {
        let out = exited(1, "error[S010]: 5:8: x\n");
        assert!(compare_check("elab", &out, &out, Some(&s010_on(4))).is_err());
    }

    #[test]
    fn an_expected_error_needs_exit_1() {
        let ok = exited(0, "error[S010]: 4:8: x\n");
        assert!(compare_check("elab", &ok, &ok, Some(&s010_on(4))).is_err());
    }

    #[test]
    fn below_a_budget_needs_exit_1() {
        let ok = exited(0, "error[S015]: 4:8: x\n");
        assert!(compare_below(BudgetKind::Fuel, &ok, &ok).is_err());
    }

    #[test]
    fn exit_2_fails_with_the_expected_text() {
        let rust = exited(2, "error[S010]: 4:8: x\n");
        let lean = exited(1, "error[S010]: 4:8: x\n");
        assert!(compare_check("elab", &rust, &lean, Some(&s010_on(4))).is_err());
        assert!(compare_check("elab", &lean, &rust, Some(&s010_on(4))).is_err());
    }

    #[test]
    fn different_designs_fail_and_show_both() {
        let rust = exited(0, "(design A)\n");
        let lean = exited(0, "(design B)\n");
        let err = compare_check("elab", &rust, &lean, None).unwrap_err();
        assert!(
            err.contains("(design A)") && err.contains("(design B)"),
            "{err}"
        );
    }

    #[test]
    fn equal_designs_pass_and_an_error_fails_without_a_directive() {
        let ok = exited(0, "(design A)\n");
        assert_eq!(compare_check("elab", &ok, &ok, None), Ok(()));
        let err = exited(1, "error[S010]: 4:8: x\n");
        assert!(compare_check("elab", &err, &err, None).is_err());
    }

    fn steps_of(stdout: &str) -> Expectation {
        Expectation::Steps {
            stdin: String::new(),
            stdout: stdout.to_owned(),
        }
    }

    #[test]
    fn equal_steps_pass() {
        let ok = exited(0, "out=(q 1)\n");
        assert_eq!(compare_run(&ok, &ok, &steps_of("out=(q 1)\n")), Ok(()));
    }

    #[test]
    fn other_steps_fail_and_show_both() {
        let ok = exited(0, "out=(q 2)\n");
        let err = compare_run(&ok, &ok, &steps_of("out=(q 1)\n")).unwrap_err();
        assert!(
            err.contains("out=(q 1)") && err.contains("out=(q 2)"),
            "{err}"
        );
    }

    #[test]
    fn steps_that_the_front_ends_disagree_on_fail() {
        let rust = exited(0, "out=(q 1)\n");
        let lean = exited(0, "out=(q 2)\n");
        assert!(compare_run(&rust, &lean, &steps_of("out=(q 1)\n")).is_err());
    }

    #[test]
    fn budget_needs_the_exact_code_one_below() {
        let s015 = exited(1, "error[S015]: 4:8: x\n");
        assert_eq!(compare_below(BudgetKind::Fuel, &s015, &s015), Ok(()));
        let s001 = exited(1, "error[S001]: 4:8: x\n");
        assert!(compare_below(BudgetKind::Fuel, &s001, &s001).is_err());
        assert_eq!(compare_below(BudgetKind::SyntaxDepth, &s001, &s001), Ok(()));
        let usage = exited(2, "error[S015]: 4:8: x\n");
        assert!(compare_below(BudgetKind::Fuel, &usage, &s015).is_err());
        assert!(compare_below(BudgetKind::Fuel, &s015, &usage).is_err());
        let ok = exited(0, "(design A)\n");
        assert!(compare_below(BudgetKind::Depth, &ok, &ok).is_err());
        let other_column = exited(1, "error[S015]: 4:9: x\n");
        assert!(compare_below(BudgetKind::Depth, &s015, &other_column).is_err());
    }

    #[test]
    fn cost_needs_success_and_equal_stdout() {
        let a = exited(0, "cost 5\n");
        assert_eq!(compare_cost(&a, &a), Ok(()));
        let b = exited(0, "cost 6\n");
        let err = compare_cost(&a, &b).unwrap_err();
        assert!(err.contains("cost 5") && err.contains("cost 6"), "{err}");
        let signal = Output {
            status: ExitStatus::from_raw(9),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
        assert!(compare_cost(&signal, &signal).is_err());
        let usage = exited(2, "");
        assert!(compare_cost(&usage, &usage).is_err());
        let failed = exited(1, "error[S010]: 4:8: x\n");
        assert!(compare_cost(&failed, &failed).is_err());
        assert!(compare_cost(&a, &failed).is_err());
        assert!(compare_cost(&failed, &a).is_err());
    }

    #[test]
    fn a_run_error_matches_code_and_line() {
        let out = exited(1, "error[S010]: 4:8: x\n");
        assert_eq!(
            compare_run(&out, &out, &Expectation::Error(s010_on(4))),
            Ok(())
        );
        assert!(compare_run(&out, &out, &Expectation::Error(s010_on(5))).is_err());
    }
}
