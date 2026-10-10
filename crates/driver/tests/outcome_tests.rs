//! Tests of the outcome check that the `parse` suite uses.

mod outcome;

use outcome::{Outcome, classify};
use std::os::unix::process::ExitStatusExt;
use std::process::{ExitStatus, Output};

fn output(status: i32, stdout: &str) -> Output {
    Output {
        status: ExitStatus::from_raw(status),
        stdout: stdout.as_bytes().to_vec(),
        stderr: b"boom".to_vec(),
    }
}

fn exited(code: i32, stdout: &str) -> Output {
    output(code << 8, stdout)
}

#[test]
fn exit_0_keeps_the_full_dump() {
    let out = classify(&exited(0, "(const a)\n"));
    assert_eq!(
        out,
        Ok(Outcome {
            code: 0,
            report: b"(const a)\n".to_vec()
        })
    );
}

#[test]
fn exit_1_keeps_the_prefix_without_the_message() {
    let out = classify(&exited(1, "error[S001]: 12:5: any text\n"));
    assert_eq!(
        out,
        Ok(Outcome {
            code: 1,
            report: b"error[S001]: 12:5:".to_vec()
        })
    );
}

#[test]
fn exit_2_fails_and_reports_stderr() {
    let err = classify(&exited(2, "")).unwrap_err();
    assert!(
        err.contains("neither exit 0 nor exit 1") && err.contains("boom"),
        "{err}"
    );
}

#[test]
fn a_signal_fails() {
    assert!(classify(&output(11, "")).unwrap_err().contains("signal"));
}

#[test]
fn exit_1_without_a_diagnostic_fails() {
    for stdout in [
        "",
        "oops\n",
        "error[E001]: 1:1: x\n",
        "error[S01]: 1:1: x\n",
        "error[S001]: 1: x\n",
        "error[S001]: a:1: x\n",
    ] {
        assert!(classify(&exited(1, stdout)).is_err(), "{stdout:?}");
    }
}

#[test]
fn exit_0_compares_bytes_that_are_no_utf8() {
    let mut out = exited(0, "");
    out.stdout = vec![0xff, 0xfe];
    assert_eq!(classify(&out).unwrap().report, [0xff, 0xfe]);
}
