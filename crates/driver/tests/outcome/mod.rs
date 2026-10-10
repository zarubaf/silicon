//! The result of one `parse` command that the two front ends must share.

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

/// The outcome of a command, or why the command did not behave like `parse`. Only exit 0 and
/// exit 1 with a valid diagnostic count. A signal and every other exit code fail.
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
