// SPDX-License-Identifier: Apache-2.0
//! Runs the shared `check` and `run` suites against the Lean `silicon-check`.

use std::path::PathBuf;
use std::process::Command;

use anyhow::{Context, Result};

use crate::repo::Repo;

/// Where Lake puts the executable, relative to the repository root. The
/// suites (`silicon_check` in `crates/testkit/src/bins.rs`) use the same path.
const BINARY: &str = "lean/.lake/build/bin/silicon-check";

fn lake_build_args() -> Vec<&'static str> {
    vec!["-d", "lean", "build", "silicon-check"]
}

/// The `check` and `run` suites of the target `suites`, by their test names.
fn nextest_args() -> Vec<&'static str> {
    vec![
        "nextest",
        "run",
        "-p",
        "driver",
        "--test",
        "suites",
        "-E",
        "test(/^core::(check|run)::/)",
    ]
}

/// Builds `silicon-check` and returns the absolute path of the executable,
/// or `None` if the build fails.
pub fn build(repo: &Repo) -> Result<Option<PathBuf>> {
    let build = Command::new("lake")
        .args(lake_build_args())
        .current_dir(&repo.root)
        .status()
        .context("cannot run lake")?;
    if !build.success() {
        return Ok(None);
    }
    // The callers run it in other working directories, so the path must be absolute.
    let binary = repo
        .root
        .join(BINARY)
        .canonicalize()
        .with_context(|| format!("cannot find {BINARY} after the build"))?;
    Ok(Some(binary))
}

/// Builds `silicon-check`, then runs the shared suites with it as the binary under test.
/// Returns whether both steps passed. The suites do not run after a failed build.
pub fn run(repo: &Repo) -> Result<bool> {
    let Some(binary) = build(repo)? else {
        return Ok(false);
    };
    let tests = Command::new("cargo")
        .args(nextest_args())
        .env("SILICON_BIN", binary)
        .current_dir(&repo.root)
        .status()
        .context("cannot run cargo nextest")?;
    Ok(tests.success())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lake_builds_the_executable_of_the_lean_package() {
        assert_eq!(lake_build_args(), ["-d", "lean", "build", "silicon-check"]);
    }

    #[test]
    fn nextest_runs_the_two_shared_suites() {
        assert_eq!(
            nextest_args(),
            [
                "nextest",
                "run",
                "-p",
                "driver",
                "--test",
                "suites",
                "-E",
                "test(/^core::(check|run)::/)",
            ]
        );
    }
}
