// SPDX-License-Identifier: Apache-2.0
//! The helper that the tests share: run a CIRCT tool as a process.

use std::io::Write;
use std::process::{Command, Output, Stdio};

/// Runs `tool` with `args` and `stdin`, and waits for its output.
///
/// # Errors
///
/// The message names the tool if it does not start or the pipe fails.
pub fn run(tool: &str, args: &[&str], stdin: &str) -> Result<Output, String> {
    let fail = |e: std::io::Error| format!("{tool}: {e}");
    let mut child = Command::new(tool)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(fail)?;
    if let Some(mut pipe) = child.stdin.take() {
        pipe.write_all(stdin.as_bytes()).map_err(fail)?;
    }
    child.wait_with_output().map_err(fail)
}
