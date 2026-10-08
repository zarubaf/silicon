#![allow(clippy::print_stdout)] // xtask is a CLI; stdout is its interface.

mod guidance;
mod repo;
mod tree;
mod violation;
mod workspace;

use std::process::ExitCode;

use anyhow::Result;
use clap::{Parser, Subcommand};

use repo::Repo;
use violation::Violation;

type Check = fn(&Repo) -> Result<Vec<Violation>>;

/// Every registered check. Each check family adds one entry.
const CHECKS: &[Check] = &[tree::check, guidance::check, workspace::check];

#[derive(Parser)]
#[command(about = "Repository tooling for Silicon")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run every repository check.
    Check,
}

fn main() -> Result<ExitCode> {
    match Cli::parse().command {
        Command::Check => run_checks(),
    }
}

fn run_checks() -> Result<ExitCode> {
    let repo = Repo::discover()?;
    let mut failed = false;
    for check in CHECKS {
        for violation in check(&repo)? {
            println!("{violation}");
            failed |= violation.severity.fails_run();
        }
    }
    Ok(if failed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}
