//! Lints tracked Markdown prose with vale against the STE rules and the glossary.

use std::process::{Command, ExitStatus};

use anyhow::{Context, Result};

use crate::repo::{Repo, TrackedFile};
use crate::vocab;

/// Tracked Markdown files that vale checks. Symlinks are skipped: they repeat their target.
pub fn markdown_files(files: &[TrackedFile]) -> Vec<String> {
    files
        .iter()
        .filter(|f| !f.is_symlink)
        .filter(|f| f.path.extension().is_some_and(|e| e == "md"))
        .map(|f| f.path.to_string_lossy().into_owned())
        .collect()
}

/// Regenerates the vocabulary, then runs vale over the tracked Markdown.
pub fn run(repo: &Repo) -> Result<ExitStatus> {
    vocab::write(repo)?;
    Command::new("vale")
        .arg("--no-wrap")
        .args(markdown_files(&repo.files))
        .current_dir(&repo.root)
        .status()
        .context("running vale")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn file(path: &str, is_symlink: bool) -> TrackedFile {
        TrackedFile {
            path: PathBuf::from(path),
            is_symlink,
        }
    }

    #[test]
    fn selects_markdown_and_skips_symlinks() {
        let files = [
            file("AGENTS.md", false),
            file("CLAUDE.md", true),
            file("doc/design/spec.md", false),
            file("justfile", false),
            file("xtask/src/main.rs", false),
        ];
        assert_eq!(markdown_files(&files), ["AGENTS.md", "doc/design/spec.md"]);
    }
}
