//! Lints tracked Markdown prose with vale against the STE rules and the glossary.

use std::process::Command;

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

/// The vale arguments for these files, or `None` when no Markdown is tracked.
/// Vale without file arguments reads standard input, so it must not run then.
pub fn vale_args(files: &[TrackedFile]) -> Option<Vec<String>> {
    let markdown = markdown_files(files);
    if markdown.is_empty() {
        return None;
    }
    let mut args = vec!["--no-wrap".to_string()];
    args.extend(markdown);
    Some(args)
}

/// Regenerates the vocabulary, then runs vale over the tracked Markdown. Returns `true` on a pass.
pub fn run(repo: &Repo) -> Result<bool> {
    vocab::write(repo)?;
    let Some(args) = vale_args(&repo.files) else {
        return Ok(true);
    };
    let status = Command::new("vale")
        .args(args)
        .current_dir(&repo.root)
        .status()
        .context("running vale")?;
    Ok(status.success())
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

    #[test]
    fn no_markdown_skips_vale() {
        assert_eq!(vale_args(&[]), None);
        assert_eq!(
            vale_args(&[file("CLAUDE.md", true), file("justfile", false)]),
            None
        );
    }

    #[test]
    fn vale_args_list_markdown_files() {
        assert_eq!(
            vale_args(&[file("AGENTS.md", false)]),
            Some(vec!["--no-wrap".to_string(), "AGENTS.md".to_string()])
        );
    }
}
