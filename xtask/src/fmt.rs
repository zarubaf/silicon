//! Drives every non-Rust formatter from the tracked file list.

use std::path::Path;
use std::process::Command;

use anyhow::{Context, Result, bail};

use crate::repo::{Repo, TrackedFile};

/// One formatter call: a program and its arguments, files last.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Invocation {
    pub program: &'static str,
    pub args: Vec<String>,
}

/// A formatter, the extensions it owns, and its leading arguments.
struct Tool {
    program: &'static str,
    extensions: &'static [&'static str],
    base: &'static [&'static str],
    check_flag: &'static str,
}

const TOOLS: &[Tool] = &[
    Tool {
        program: "mdformat",
        extensions: &["md"],
        base: &[],
        check_flag: "--check",
    },
    Tool {
        program: "taplo",
        extensions: &["toml"],
        base: &["fmt"],
        check_flag: "--check",
    },
    Tool {
        program: "yamlfmt",
        extensions: &["yml", "yaml"],
        base: &[],
        check_flag: "-lint",
    },
    Tool {
        program: "nixfmt",
        extensions: &["nix"],
        base: &[],
        check_flag: "--check",
    },
];

/// Plans one invocation per tool that has files. Symlinks are skipped.
pub fn plan(files: &[TrackedFile], check: bool) -> Vec<Invocation> {
    TOOLS
        .iter()
        .filter_map(|tool| {
            let paths: Vec<String> = files
                .iter()
                .filter(|f| !f.is_symlink)
                .filter(|f| {
                    f.path
                        .extension()
                        .and_then(|e| e.to_str())
                        .is_some_and(|e| tool.extensions.contains(&e))
                })
                .map(|f| f.path.to_string_lossy().into_owned())
                .collect();
            if paths.is_empty() {
                return None;
            }
            let mut args: Vec<String> = tool.base.iter().map(|a| (*a).to_string()).collect();
            if check {
                args.push(tool.check_flag.to_string());
            }
            args.extend(paths);
            Some(Invocation {
                program: tool.program,
                args,
            })
        })
        .collect()
}

/// Runs every planned formatter from the repository root. Fails on the first nonzero exit.
pub fn run(repo: &Repo, check: bool) -> Result<()> {
    for inv in plan(&repo.files, check) {
        run_one(&repo.root, &inv)?;
    }
    Ok(())
}

fn run_one(root: &Path, inv: &Invocation) -> Result<()> {
    let status = Command::new(inv.program)
        .args(&inv.args)
        .current_dir(root)
        .status()
        .with_context(|| format!("running {}", inv.program))?;
    if !status.success() {
        bail!("{} failed: {status}", inv.program);
    }
    Ok(())
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

    fn inv(program: &'static str, args: &[&str]) -> Invocation {
        Invocation {
            program,
            args: args.iter().map(|a| (*a).to_string()).collect(),
        }
    }

    #[test]
    fn plan_groups_by_extension() {
        let files = [
            file("a.md", false),
            file("b.toml", false),
            file("c.yml", false),
            file("d.nix", false),
        ];
        assert_eq!(
            plan(&files, false),
            [
                inv("mdformat", &["a.md"]),
                inv("taplo", &["fmt", "b.toml"]),
                inv("yamlfmt", &["c.yml"]),
                inv("nixfmt", &["d.nix"]),
            ]
        );
    }

    #[test]
    fn check_mode_flags() {
        let files = [
            file("a.md", false),
            file("b.toml", false),
            file("c.yaml", false),
            file("d.nix", false),
        ];
        assert_eq!(
            plan(&files, true),
            [
                inv("mdformat", &["--check", "a.md"]),
                inv("taplo", &["fmt", "--check", "b.toml"]),
                inv("yamlfmt", &["-lint", "c.yaml"]),
                inv("nixfmt", &["--check", "d.nix"]),
            ]
        );
    }

    #[test]
    fn no_files_no_invocation() {
        assert!(plan(&[], false).is_empty());
        assert!(plan(&[file("main.rs", false)], true).is_empty());
    }

    #[test]
    fn symlinks_skipped() {
        let files = [file("CLAUDE.md", true), file("AGENTS.md", false)];
        assert_eq!(plan(&files, false), [inv("mdformat", &["AGENTS.md"])]);
    }
}
