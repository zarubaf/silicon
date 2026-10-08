//! Lints tracked Markdown: vale checks the prose against the STE rules and the glossary,
//! and lychee checks the internal links.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result};

use crate::lean_prose;
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

/// Where the Markdown extracted from Lean files goes. `target/` is git-ignored.
const LEAN_PROSE_DIR: &str = "target/lean-prose";

/// The Markdown extracted from one Lean file, with the map back to its Lean lines.
struct LeanProse {
    markdown_path: String,
    lean_path: String,
    line_map: Vec<usize>,
}

/// Tracked Lean files, without symlinks.
fn lean_files(files: &[TrackedFile]) -> impl Iterator<Item = &TrackedFile> {
    files
        .iter()
        .filter(|f| !f.is_symlink && f.path.extension().is_some_and(|e| e == "lean"))
}

/// Writes the prose of each tracked Lean file as Markdown under `target/lean-prose/`.
/// Files without prose blocks produce nothing.
fn extract_lean_prose(repo: &Repo) -> Result<Vec<LeanProse>> {
    let mut extracted = Vec::new();
    for file in lean_files(&repo.files) {
        let blocks = lean_prose::prose_blocks(&repo.read(&file.path)?);
        if blocks.is_empty() {
            continue;
        }
        let (markdown, line_map) = lean_prose::to_markdown(&blocks);
        let relative = Path::new(LEAN_PROSE_DIR).join(format!("{}.md", file.path.display()));
        let target: PathBuf = repo.root.join(&relative);
        if let Some(dir) = target.parent() {
            std::fs::create_dir_all(dir).with_context(|| format!("creating {}", dir.display()))?;
        }
        std::fs::write(&target, markdown)
            .with_context(|| format!("writing {}", target.display()))?;
        extracted.push(LeanProse {
            markdown_path: relative.to_string_lossy().into_owned(),
            lean_path: file.path.to_string_lossy().into_owned(),
            line_map,
        });
    }
    Ok(extracted)
}

/// Rewrites one vale `--output=line` report (`path:line:col:rule:message`) from the
/// extracted Markdown to the Lean file. Other lines stay unchanged.
fn rewrite_report_line(line: &str, extracted: &[LeanProse]) -> String {
    let mut parts = line.splitn(3, ':');
    let (Some(path), Some(number), Some(rest)) = (parts.next(), parts.next(), parts.next()) else {
        return line.to_string();
    };
    let lean_line = extracted
        .iter()
        .find(|e| e.markdown_path == path)
        .zip(number.parse::<usize>().ok())
        .and_then(|(e, n)| Some((e, e.line_map.get(n.checked_sub(1)?)?)));
    match lean_line {
        Some((e, lean_line)) => format!("{}:{lean_line}:{rest}", e.lean_path),
        None => line.to_string(),
    }
}

/// Regenerates the vocabulary, then runs vale over the tracked Markdown and the prose of the
/// Lean files, and lychee over the tracked Markdown.
/// Both tools always run. Returns `true` when both pass.
pub fn run(repo: &Repo) -> Result<bool> {
    vocab::write(repo)?;
    let extracted = extract_lean_prose(repo)?;
    let vale = run_vale(repo, &extracted)?;
    let lychee = tool(repo, "lychee", lychee_args(&repo.files))?;
    Ok(vale && lychee)
}

/// Vale reports in line format, so that the Lean reports can map back to their source lines.
fn run_vale(repo: &Repo, extracted: &[LeanProse]) -> Result<bool> {
    let mut paths = markdown_files(&repo.files);
    paths.extend(extracted.iter().map(|e| e.markdown_path.clone()));
    if paths.is_empty() {
        return Ok(true);
    }
    let output = Command::new("vale")
        .args(["--no-wrap", "--output=line"])
        .args(paths)
        .current_dir(&repo.root)
        .output()
        .context("running vale")?;
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        println!("{}", rewrite_report_line(line, extracted));
    }
    eprint!("{}", String::from_utf8_lossy(&output.stderr));
    Ok(output.status.success())
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
    fn rewrites_vale_report_to_lean_lines() {
        let extracted = [LeanProse {
            markdown_path: "target/lean-prose/lean/A.lean.md".to_string(),
            lean_path: "lean/A.lean".to_string(),
            line_map: vec![2, 3, 4],
        }];
        assert_eq!(
            rewrite_report_line(
                "target/lean-prose/lean/A.lean.md:2:5:Silicon.SentenceLength:Too long",
                &extracted
            ),
            "lean/A.lean:3:5:Silicon.SentenceLength:Too long"
        );
        assert_eq!(
            rewrite_report_line("AGENTS.md:1:1:R:m", &extracted),
            "AGENTS.md:1:1:R:m"
        );
    }
}
