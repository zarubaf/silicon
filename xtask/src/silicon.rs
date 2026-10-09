//! The build of `silicon`, the Rust binary that the Lean oracles check.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result};
use cargo_metadata::MetadataCommand;

/// Builds `silicon` and returns its path, or `None` if the build fails.
/// Cargo prints the build errors.
pub fn build(root: &Path) -> Result<Option<PathBuf>> {
    let build = Command::new("cargo")
        .args(["build", "--quiet", "-p", "driver", "--bin", "silicon"])
        .current_dir(root)
        .status()
        .context("cannot run cargo build")?;
    if !build.success() {
        return Ok(None);
    }
    let metadata = MetadataCommand::new()
        .current_dir(root)
        .no_deps()
        .exec()
        .context("cannot read the cargo metadata")?;
    Ok(Some(metadata.target_directory.join("debug/silicon").into()))
}
