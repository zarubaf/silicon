//! The designs of `tests/corpus`, which LEC and the differential tests share.

use std::path::PathBuf;

use crate::repo::Repo;

const DIR: &str = "tests/corpus";

/// The tracked `.sil` files of the corpus, sorted, relative to the root.
pub fn files(repo: &Repo) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = repo
        .files
        .iter()
        .map(|f| f.path.clone())
        .filter(|p| p.starts_with(DIR) && p.extension().is_some_and(|e| e == "sil"))
        .collect();
    files.sort();
    files
}
