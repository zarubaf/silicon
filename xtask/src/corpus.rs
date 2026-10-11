//! The designs of the corpus, which LEC and the differential tests share.

use std::path::PathBuf;

use crate::paths;
use crate::repo::Repo;

/// The tracked `.sil` files of the corpus, sorted, relative to the root.
pub fn files(repo: &Repo) -> Vec<PathBuf> {
    let dir = paths::corpus_dir(repo);
    let mut files: Vec<PathBuf> = repo
        .files
        .iter()
        .map(|f| f.path.clone())
        .filter(|p| p.starts_with(&dir) && p.extension().is_some_and(|e| e == "sil"))
        .collect();
    files.sort();
    files
}
