//! Tooling for the continuous architecture review of ADR 0013.

mod paths;
mod scope;

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
