// SPDX-License-Identifier: Apache-2.0
//! The runner of the `tests/source` suites.

use std::path::Path;
use std::process::{Command, Output};

use crate::bins::{self, silicon_check};
use crate::core::{run_tool, smoke};
use crate::directive::{
    BudgetKind, Expectation, Expected, Marker, budgets, expectation, expected_error, has_check, top,
};
use crate::outcome::classify;
use crate::report::parse_report;
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
    let rust_outcome =
        classify(&rust).map_err(|e| format!("Rust `silicon {command}` failed: {e}"))?;
    let lean_outcome =
        classify(&lean).map_err(|e| format!("Lean `silicon-check {command}` failed: {e}"))?;
    if rust_outcome == lean_outcome {
        return Ok(rust);
    }
    Err(format!(
        "the front ends disagree\nRust: {rust_outcome:?}\nLean: {lean_outcome:?}"
    ))
}

/// The `parse` suite (frontend spec sections 8 and 11.3): the Lean
/// `silicon-check parse` and the Rust `silicon parse` run on each `.si` file.
/// They must agree as `agreed` says.
///
/// # Errors
///
/// Returns an error when a front end misbehaves or the two disagree.
pub fn parse(binary: &Path, file: &Path) -> datatest_stable::Result<()> {
    agreed(binary, "parse", file, &[])?;
    Ok(())
}

/// Compares the runs of the command `name` in the two front ends with the expectation of the
/// file. Both must exit 0 with equal stdout, or exit 1 with an equal code, line, and column.
/// With an `expected-error`, the code and the line must also equal the directive.
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
    let r =
        classify(rust).map_err(|e| format!("Rust `silicon {name}` failed: {e}{}", outputs()))?;
    let l = classify(lean)
        .map_err(|e| format!("Lean `silicon-check {name}` failed: {e}{}", outputs()))?;
    if r != l {
        return Err(format!("the front ends disagree{}", outputs()));
    }
    match want {
        None if r.code == 0 => Ok(()),
        None => Err(format!("expected success{}", outputs())),
        Some(want) => match parse_report(&String::from_utf8_lossy(&rust.stdout)) {
            Some(got) if r.code == 1 && got.code == want.code && got.line == want.line => Ok(()),
            _ => Err(format!(
                "expected error[{}] on line {}{}",
                want.code,
                want.line,
                outputs()
            )),
        },
    }
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
    let (rust, lean) = both(binary, "elab", file, &top, &[], "")?;
    Ok(compare_check("elab", &rust, &lean, want.as_ref())?)
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
/// ends. A file without STEP lines holds one `// expected-error` instead.
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
    Ok(compare_run(&rust, &lean, &want).map_err(in_file)?)
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
    for (front_end, out) in [("Rust `silicon", &rust), ("Lean `silicon-check", &lean)] {
        let stdout = String::from_utf8_lossy(&out.stdout);
        if !out.status.success() {
            return Err(in_file(format!(
                "{front_end} elab` failed: {stdout}{}",
                String::from_utf8_lossy(&out.stderr)
            ))
            .into());
        }
        let checked = run_tool("FileCheck", &[file], &stdout)?;
        if !checked.status.success() {
            return Err(in_file(format!(
                "FileCheck failed on the output of {front_end} elab`: {}\n{stdout}",
                String::from_utf8_lossy(&checked.stderr)
            ))
            .into());
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
/// default budgets prints the same stdout and exits with the same code in both.
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
        let (rust, lean) = both(binary, "elab", file, &top, &[flag, &below], "")?;
        compare_below(budget.kind, &rust, &lean)
            .map_err(|e| in_file(format!("with `{flag} {below}`: {e}")))?;
    }
    let (rust, lean) = both(binary, "cost", file, &top, &[], "")?;
    compare_cost(&rust, &lean).map_err(in_file)?;
    Ok(())
}

/// Compares the `cost` runs of the two front ends: equal exit codes and byte-equal stdout.
fn compare_cost(rust: &Output, lean: &Output) -> Result<(), String> {
    if rust.status.code() == lean.status.code() && rust.stdout == lean.stdout {
        return Ok(());
    }
    Err(format!(
        "`cost` differs\nRust exit {:?}:\n{}\nLean exit {:?}:\n{}",
        rust.status.code(),
        String::from_utf8_lossy(&rust.stdout),
        lean.status.code(),
        String::from_utf8_lossy(&lean.stdout)
    ))
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
        }
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
    fn cost_needs_equal_stdout_and_exit() {
        let a = exited(0, "cost 5\n");
        assert_eq!(compare_cost(&a, &a), Ok(()));
        let b = exited(0, "cost 6\n");
        let err = compare_cost(&a, &b).unwrap_err();
        assert!(err.contains("cost 5") && err.contains("cost 6"), "{err}");
        assert!(compare_cost(&a, &exited(1, "cost 5\n")).is_err());
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
