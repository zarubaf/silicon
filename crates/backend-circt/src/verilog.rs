//! The Verilog of MLIR text through `firtool`, which runs as a process.

use std::error::Error;
use std::fmt;
use std::io::{self, Write};
use std::process::{Command, Stdio};
use std::thread;

/// The tool that exports Verilog.
const FIRTOOL: &str = "firtool";

/// An error of a CIRCT tool.
#[derive(Debug)]
pub enum ToolError {
    /// The tool is not on the `PATH`.
    Missing(&'static str),
    /// The tool failed, or the pipe to it failed, with the message.
    Failed(&'static str, String),
}

impl fmt::Display for ToolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToolError::Missing(tool) => write!(f, "{tool}: the CIRCT tool is not on the PATH"),
            ToolError::Failed(tool, message) => write!(f, "{tool}: {message}"),
        }
    }
}

impl Error for ToolError {}

/// The Verilog of `mlir`, which `firtool` exports without the random
/// initialization of registers and without location comments.
///
/// # Errors
///
/// `firtool` is not on the `PATH`, or it rejects `mlir`.
pub fn verilog(mlir: &str) -> Result<String, ToolError> {
    run(
        FIRTOOL,
        &[
            "--format=mlir",
            "--disable-all-randomization",
            "--lowering-options=locationInfoStyle=none",
            "-",
        ],
        mlir,
    )
}

/// Runs `tool` with `args`, gives it `stdin`, and returns its standard output.
fn run(tool: &'static str, args: &[&str], stdin: &str) -> Result<String, ToolError> {
    let failed = |e: io::Error| ToolError::Failed(tool, e.to_string());
    let mut child = Command::new(tool)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| match e.kind() {
            io::ErrorKind::NotFound => ToolError::Missing(tool),
            _ => failed(e),
        })?;
    let pipe = child.stdin.take();
    // A thread writes the input, so a full output pipe cannot block the write.
    let (written, output) = thread::scope(|scope| {
        let writer =
            scope.spawn(move || pipe.map_or(Ok(()), |mut p| p.write_all(stdin.as_bytes())));
        let output = child.wait_with_output();
        (writer.join(), output)
    });
    let output = output.map_err(failed)?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(ToolError::Failed(tool, stderr.trim_end().to_owned()));
    }
    written
        .map_err(|_| ToolError::Failed(tool, "the input writer panicked".to_owned()))?
        .map_err(failed)?;
    String::from_utf8(output.stdout)
        .map_err(|_| ToolError::Failed(tool, "the output is not valid UTF-8".to_owned()))
}
