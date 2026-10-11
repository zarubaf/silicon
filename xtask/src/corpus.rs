// SPDX-License-Identifier: Apache-2.0
//! The designs of the corpus, which LEC and the differential tests share:
//! the core files of `tests/core/corpus`, then the source files of
//! `tests/source/corpus` through `silicon elab`.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail};

use crate::paths;
use crate::repo::Repo;

/// One design of the corpus.
pub struct Design {
    /// The tracked file, relative to the root. Reports and inventories use it.
    pub name: PathBuf,
    /// The core IR file that the checks read.
    pub sil: PathBuf,
}

/// The tracked files below `dir` with the extension `ext`, sorted, relative
/// to the root.
fn tracked(repo: &Repo, dir: &Path, ext: &str) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = repo
        .files
        .iter()
        .map(|f| f.path.clone())
        .filter(|p| p.starts_with(dir) && p.extension().is_some_and(|e| e == ext))
        .collect();
    files.sort();
    files
}

/// The designs of both corpora. `silicon` elaborates each source file into
/// `dir`. The corpus must elaborate, so a rejection is an error.
pub fn designs(repo: &Repo, silicon: &Path, dir: &Path) -> Result<Vec<Design>> {
    let core = tracked(repo, &paths::corpus_dir(), "sil")
        .into_iter()
        .map(|name| Design {
            sil: repo.root.join(&name),
            name,
        });
    let source = tracked(repo, &paths::source_corpus_dir(), "si")
        .into_iter()
        .map(|name| {
            let sil = elaborate(silicon, &repo.root, &name, dir)?;
            Ok(Design { name, sil })
        });
    core.map(Ok).chain(source).collect()
}

/// Writes the core IR of the source file `name` (relative to `root`), with
/// the top selection of its `// TOP` line, to a file in `dir`. Returns that
/// file. The Rust front end is the shipped path, and the `corpus` suite
/// proves its output equal to the Lean output.
fn elaborate(silicon: &Path, root: &Path, name: &Path, dir: &Path) -> Result<PathBuf> {
    let shown = name.display();
    let file = root.join(name);
    let source = std::fs::read_to_string(&file).with_context(|| format!("cannot read {shown}"))?;
    let top = testkit::top(&source).map_err(|e| anyhow!("{shown}: {e}"))?;
    let out = Command::new(silicon)
        .arg("elab")
        .arg(&file)
        .arg("--top")
        .arg(&top)
        .output()
        .with_context(|| format!("{shown}: cannot run {}", silicon.display()))?;
    if !out.status.success() {
        bail!(
            "{shown}: `silicon elab --top {top}` failed ({}):\n{}{}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let stem = name.file_stem().context("a source file has no name")?;
    let sil = dir.join(stem).with_extension("sil");
    std::fs::write(&sil, &out.stdout).with_context(|| format!("cannot write {}", sil.display()))?;
    Ok(sil)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::TrackedFile;

    /// A repository in a new directory with the tracked files `files`.
    fn repo(files: &[(&str, &str)]) -> (tempfile::TempDir, Repo) {
        let tmp = tempfile::tempdir().unwrap();
        let mut tracked = Vec::new();
        for (path, text) in files {
            let full = tmp.path().join(path);
            std::fs::create_dir_all(full.parent().unwrap()).unwrap();
            std::fs::write(&full, text).unwrap();
            tracked.push(TrackedFile {
                path: PathBuf::from(path),
                is_symlink: false,
                is_executable: false,
            });
        }
        let repo = Repo::from_parts(tmp.path().to_owned(), tracked);
        (tmp, repo)
    }

    /// `echo` stands in for `silicon`: its output is its arguments.
    #[test]
    fn a_source_design_is_its_elaboration_under_its_name() {
        let (tmp, repo) = repo(&[
            ("tests/source/corpus/b.si", "// TOP B(2)\n"),
            ("tests/core/corpus/a.sil", "(design a)\n"),
            ("tests/core/corpus/notes.txt", ""),
            ("tests/source/check/c.si", "// TOP C()\n"),
        ]);
        let out = tempfile::tempdir().unwrap();
        let designs = designs(&repo, Path::new("echo"), out.path()).unwrap();
        let names: Vec<_> = designs.iter().map(|d| d.name.to_str().unwrap()).collect();
        assert_eq!(
            names,
            ["tests/core/corpus/a.sil", "tests/source/corpus/b.si"]
        );
        assert_eq!(designs[0].sil, tmp.path().join("tests/core/corpus/a.sil"));
        assert_eq!(designs[1].sil, out.path().join("b.sil"));
        let elab = std::fs::read_to_string(&designs[1].sil).unwrap();
        let file = tmp.path().join("tests/source/corpus/b.si");
        assert_eq!(elab, format!("elab {} --top B(2)\n", file.display()));
    }

    #[test]
    fn a_rejected_source_design_is_an_error_with_its_name() {
        let (_tmp, repo) = repo(&[("tests/source/corpus/b.si", "// TOP B()\n")]);
        let out = tempfile::tempdir().unwrap();
        let error = designs(&repo, Path::new("false"), out.path())
            .err()
            .unwrap();
        assert!(
            format!("{error:#}").starts_with("tests/source/corpus/b.si: `silicon elab"),
            "{error:#}"
        );
    }

    #[test]
    fn a_source_design_without_a_top_is_an_error_with_its_name() {
        let (_tmp, repo) = repo(&[("tests/source/corpus/b.si", "module B() {}\n")]);
        let out = tempfile::tempdir().unwrap();
        let error = designs(&repo, Path::new("echo"), out.path()).err().unwrap();
        assert_eq!(
            format!("{error:#}"),
            "tests/source/corpus/b.si: no TOP line"
        );
    }
}
