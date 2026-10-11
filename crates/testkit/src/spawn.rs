// SPDX-License-Identifier: Apache-2.0
//! Runs a command with a given standard input.

use std::io::Write;
use std::process::{Command, Output, Stdio};

/// Runs `command` with `stdin` as input and collects its output.
///
/// # Errors
///
/// Returns an error when the command cannot start or its output cannot be read.
pub fn spawn(command: &mut Command, stdin: &str) -> std::io::Result<Output> {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| {
            let program = command.get_program().to_string_lossy().into_owned();
            std::io::Error::new(e.kind(), format!("cannot run `{program}`: {e}"))
        })?;
    if let Some(mut pipe) = child.stdin.take() {
        // A command that fails before it reads stdin closes the pipe.
        match pipe.write_all(stdin.as_bytes()) {
            Err(e) if e.kind() != std::io::ErrorKind::BrokenPipe => return Err(e),
            _ => {}
        }
    }
    child.wait_with_output()
}
