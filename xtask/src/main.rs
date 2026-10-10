#![allow(clippy::print_stdout)] // xtask is a CLI; stdout is its interface.

mod arch;
mod arch_review;
mod commit;
mod corpus;
mod diff;
mod fmt;
mod gitcmd;
mod guidance;
mod lean;
mod lean_check;
mod lean_prose;
mod lec;
mod prose;
mod repo;
mod review;
mod silicon;
mod skips;
#[cfg(test)]
mod testgit;
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
const CHECKS: &[Check] = &[
    tree::check,
    guidance::check,
    workspace::check,
    lean::check,
    arch::check,
];

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
    /// Build `silicon-check` and run the shared `check` and `run` suites with it.
    LeanCheck,
    /// Run the differential tests: random designs through the Lean interpreter, `silicon run`, and `arcilator`.
    Diff {
        /// The seed of the first design. Design `k` uses the seed plus `k`.
        #[arg(long, default_value_t = 1)]
        seed: u64,
        /// The number of random designs.
        #[arg(long, default_value_t = 200, value_parser = clap::value_parser!(u64).range(1..))]
        count: u64,
    },
    /// Run the LEC of the core IR spec, section 8.1, over `tests/corpus`.
    Lec,
    /// List the files of the branch that touch an architecture path of `doc/architecture.md`.
    ///
    /// Exit codes: 0 no architecture path changed, 10 an architecture review is due,
    /// 1 an error (for example an unknown base or a malformed path list).
    ReviewScope {
        /// Git ref that the branch forked from, for example `origin/main`.
        #[arg(long)]
        base: String,
    },
    /// Report whether a drift review is due: 15 merged pull requests or 7 days since the newest `arch-review/<date>` tag.
    ///
    /// Counts pull requests with `gh`, because a rebase merge leaves no merge commit.
    /// Exit codes: 0 no review is due, 10 a review is due (also when no tag exists), 1 an error
    /// (also when a pull request commit is missing from the clone, or a tag `arch-review/*` is not a date).
    ReviewDue {
        /// The base branch of the pull requests. The command fetches it from `origin` first.
        #[arg(long, default_value = "main")]
        base: String,
    },
    /// Print the facts for an architecture reviewer: crate graph, layers, public items, line counts, trust table, and error codes.
    ArchSummary,
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
        Command::LeanCheck => Ok(if lean_check::run(&Repo::discover()?)? {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }),
        Command::Diff { seed, count } => Ok(if diff::run(&Repo::discover()?, seed, count)? {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }),
        Command::Lec => Ok(if lec::run(&Repo::discover()?)? {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }),
        Command::CommitMsg { file } => Ok(report(&commit::check_message_file(&file)?)),
        Command::ReviewScope { base } => arch_review::review_scope(&base),
        Command::ReviewDue { base } => arch_review::review_due(&base),
        Command::ArchSummary => {
            arch_review::arch_summary()?;
            Ok(ExitCode::SUCCESS)
        }
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
