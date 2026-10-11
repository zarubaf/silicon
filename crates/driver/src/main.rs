// SPDX-License-Identifier: Apache-2.0
//! The `silicon` command-line tool.

mod cli;
mod validate;

use std::io::{self, Write};
use std::process::ExitCode;

use clap::Parser;

fn main() -> ExitCode {
    let cli = cli::Cli::parse();
    let stdin = io::stdin().lock();
    let mut stdout = io::stdout().lock();
    let exit = cli::execute(&cli.command, stdin, &mut stdout);
    // A failed flush loses output, which is an output error (exit 2).
    if let Err(e) = stdout.flush() {
        // A failed write to stderr has no better channel to report to.
        let _ = writeln!(io::stderr(), "silicon: {e}");
        return cli::Exit::UsageError.into();
    }
    exit.into()
}
