#![allow(clippy::print_stdout)] // xtask is a CLI; stdout is its interface.

mod commit;
mod fmt;
mod guidance;
mod lean;
mod prose;
mod repo;
mod review;
mod tree;
mod violation;
mod vocab;
mod workspace;

use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::Result;
use clap::{Parser, Subcommand};

use repo::Repo;
use violation::Violation;

type Check = fn(&Repo) -> Result<Vec<Violation>>;

/// Every registered check. Each check family adds one entry.
const CHECKS: &[Check] = &[tree::check, guidance::check, workspace::check, lean::check];

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
    /// Format every tracked non-Rust file.
    Fmt {
        /// Report unformatted files instead of rewriting them.
        #[arg(long)]
        check: bool,
    },
    /// Regenerate the vale vocabulary from `CONTEXT.md`.
    ValeVocab,
    /// Regenerate the vale vocabulary, then lint tracked Markdown with vale and lychee.
    Prose,
    /// Check one commit message file. The `commit-msg` hook calls this.
    CommitMsg {
        /// Path of the message file.
        file: PathBuf,
    },
    /// Check every commit in a range against the commit conventions.
    CommitCheck {
        /// Base revision, for example `origin/main`. An empty or all-zeros base checks the whole history.
        #[arg(long)]
        base: String,
    },
    /// Run the Codex adversarial review of the current branch.
    Review {
        /// Git ref to review against.
        #[arg(long, default_value = "main")]
        base: String,
    },
}

fn main() -> Result<ExitCode> {
    match Cli::parse().command {
        Command::Check => run_checks(),
        Command::Fmt { check } => {
            fmt::run(&Repo::discover()?, check)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::ValeVocab => {
            vocab::write(&Repo::discover()?)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::Prose => Ok(if prose::run(&Repo::discover()?)? {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }),
        Command::CommitMsg { file } => Ok(report(&commit::check_message_file(&file)?)),
        Command::Review { base } => {
            review::run(&Repo::discover()?.root, &base)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::CommitCheck { base } => {
            let repo = Repo::discover()?;
            Ok(report(&commit::check_range(
                &repo.root,
                &commit::range_for_base(&base),
                &commit::allowed_scopes()?,
            )?))
        }
    }
}

fn report(problems: &[String]) -> ExitCode {
    for problem in problems {
        println!("{problem}");
    }
    if problems.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
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
