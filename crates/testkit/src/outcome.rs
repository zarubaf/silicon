// SPDX-License-Identifier: Apache-2.0
//! The result of one command that the two front ends must share.

use std::process::Output;

/// What a front end printed for one file: the full dump on success, as bytes (exit 0), or the prefix
/// `error[S0xx]: LINE:COL:` of its diagnostic (exit 1).
#[derive(Debug, PartialEq, Eq)]
pub struct Outcome {
    pub code: i32,
    pub report: Vec<u8>,
}

/// Splits a nonempty run of digits off the front of `s`.
fn number(s: &str) -> Option<(&str, &str)> {
    let n = s.bytes().take_while(u8::is_ascii_digit).count();
    (n > 0).then(|| s.split_at(n))
}

/// The prefix `error[S0xx]: LINE:COL:` of the first line of `stdout`.
fn diagnostic_prefix(stdout: &str) -> Option<&str> {
    let rest = stdout.strip_prefix("error[S")?;
    let (digits, rest) = rest.split_at_checked(3)?;
    if !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let rest = rest.strip_prefix("]: ")?;
    let (_, rest) = number(rest)?;
    let (_, rest) = number(rest.strip_prefix(':')?)?;
    let rest = rest.strip_prefix(':')?;
    Some(&stdout[..stdout.len() - rest.len()])
}

/// The outcome of a command, or why the command did not behave like a source command. Only exit 0 and
/// exit 1 with a valid diagnostic count. A signal and every other exit code fail.
///
/// # Errors
///
/// Returns the reason, with the status and both streams, when the command is not a valid run.
pub fn classify(out: &Output) -> Result<Outcome, String> {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let fail = |why: &str| {
        Err(format!(
            "{why}\nstatus: {}\nstdout: {stdout}\nstderr: {}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        ))
    };
    match out.status.code() {
        Some(0) => Ok(Outcome {
            code: 0,
            report: out.stdout.clone(),
        }),
        Some(1) => match diagnostic_prefix(&stdout) {
            Some(prefix) => Ok(Outcome {
                code: 1,
                report: prefix.as_bytes().to_vec(),
            }),
            None => fail("exit 1 without a diagnostic `error[S0xx]: LINE:COL:`"),
        },
        Some(_) => fail("neither exit 0 nor exit 1"),
        None => fail("the command ended without an exit code (a signal)"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt;
    use std::process::ExitStatus;

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
}
