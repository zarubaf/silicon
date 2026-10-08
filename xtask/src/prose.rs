//! Lints tracked Markdown: vale checks the prose against the STE rules and the glossary,
//! and lychee checks the internal links.

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

/// The lychee arguments for these files, or `None` when no Markdown is tracked.
/// `--offline` limits the run to internal links, so it needs no network.
pub fn lychee_args(files: &[TrackedFile]) -> Option<Vec<String>> {
    let markdown = markdown_files(files);
    if markdown.is_empty() {
        return None;
    }
    let mut args = vec!["--offline".to_string(), "--no-progress".to_string()];
    args.extend(markdown);
    Some(args)
}

/// Regenerates the vocabulary, then runs vale and lychee over the tracked Markdown.
/// Both tools always run. Returns `true` when both pass.
pub fn run(repo: &Repo) -> Result<bool> {
    vocab::write(repo)?;
    let vale = tool(repo, "vale", vale_args(&repo.files))?;
    let lychee = tool(repo, "lychee", lychee_args(&repo.files))?;
    Ok(vale && lychee)
}

/// Runs `program` with `args` at the repository root. `None` skips the run and counts as a pass.
fn tool(repo: &Repo, program: &str, args: Option<Vec<String>>) -> Result<bool> {
    let Some(args) = args else {
        return Ok(true);
    };
    let status = Command::new(program)
        .args(args)
        .current_dir(&repo.root)
        .status()
        .with_context(|| format!("running {program}"))?;
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
            is_executable: false,
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
    fn lychee_args_check_internal_links_offline() {
        assert_eq!(lychee_args(&[file("CLAUDE.md", true)]), None);
        assert_eq!(
            lychee_args(&[file("AGENTS.md", false), file("justfile", false)]),
            Some(vec![
                "--offline".to_string(),
                "--no-progress".to_string(),
                "AGENTS.md".to_string()
            ])
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
