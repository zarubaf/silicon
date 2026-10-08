//! Helpers that the test binaries of the `silicon` command share.

use std::io::Write;
use std::process::{Command, Output, Stdio};

/// Runs `command` with `stdin` as input and collects its output.
pub fn spawn(command: &mut Command, stdin: &str) -> std::io::Result<Output> {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(mut pipe) = child.stdin.take() {
        // A command that fails before it reads stdin closes the pipe.
        match pipe.write_all(stdin.as_bytes()) {
            Err(e) if e.kind() != std::io::ErrorKind::BrokenPipe => return Err(e),
            _ => {}
        }
    }
    child.wait_with_output()
}
