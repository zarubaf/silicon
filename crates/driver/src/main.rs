//! The `silicon` command-line tool.

mod cli;

use std::io;
use std::process::ExitCode;

use clap::Parser;

fn main() -> ExitCode {
    let cli = cli::Cli::parse();
    let stdin = io::stdin().lock();
    let stdout = io::stdout().lock();
    cli::execute(&cli.command, stdin, stdout).into()
}
