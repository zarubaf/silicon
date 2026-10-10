//! Tooling for the continuous architecture review of ADR 0013.

mod due;
mod paths;
mod scope;
mod summary;

use std::process::ExitCode;

use anyhow::Result;

use crate::repo::Repo;

/// Exit code of `review-scope` and `review-due` when a review is due.
/// `1` is an error and `2` is a usage error, so `10` stays distinct.
const REVIEW_DUE: u8 = 10;

/// Prints the architecture files that the branch changed.
/// Exits `0` when it changed none, and `10` when an architecture review is due.
pub fn review_scope(base: &str) -> Result<ExitCode> {
    let repo = Repo::discover()?;
    let files = scope::changed_architecture_files(&repo.root, base)?;
    for file in &files {
        println!("{file}");
    }
    Ok(if files.is_empty() {
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "architecture review due: the branch changes {} architecture file(s)",
            files.len()
        );
        ExitCode::from(REVIEW_DUE)
    })
}

/// Reports whether a drift review is due on the base branch `base` of `origin`.
/// Exits `0` when none is due, and `10` when one is due.
pub fn review_due(base: &str) -> Result<ExitCode> {
    let repo = Repo::discover()?;
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)?
        .as_secs();
    due::fetch(&repo.root, base)?;
    let remote_ref = format!("origin/{base}");
    let verdict = due::check(&repo.root, &remote_ref, i64::try_from(now)?, |since| {
        due::merged_prs(&repo.root, base, since)
    })?;
    println!("{}", verdict.summary);
    for reason in &verdict.reasons {
        println!("drift review due: {reason}");
    }
    Ok(if verdict.reasons.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(REVIEW_DUE)
    })
}

/// Prints the facts for an architecture reviewer.
pub fn arch_summary() -> Result<()> {
    print!("{}", summary::render(&Repo::discover()?)?);
    Ok(())
}
