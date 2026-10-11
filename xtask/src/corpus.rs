// SPDX-License-Identifier: Apache-2.0
//! The designs of the corpus, which LEC and the differential tests share.

use std::path::{Path, PathBuf};

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

/// The designs of the core corpus.
pub fn designs(repo: &Repo) -> Vec<Design> {
    tracked(repo, &paths::corpus_dir(), "sil")
        .into_iter()
        .map(|name| Design {
            sil: repo.root.join(&name),
            name,
        })
        .collect()
}
