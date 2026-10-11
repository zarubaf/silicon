// SPDX-License-Identifier: Apache-2.0
//! Runs the Codex adversarial review: the cross-vendor review required before merge.

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail};

/// The newest `codex-companion.mjs` under `plugins_root`.
/// Version directories are ordered by `major.minor.patch`; other names are skipped.
pub fn find_companion(plugins_root: &Path) -> Result<PathBuf> {
    let versions = plugins_root.join("openai-codex/codex");
    let missing = || {
        anyhow!(
            "Codex plugin not found under {}; run /plugin install codex@openai-codex",
            versions.display()
        )
    };
    let entries = std::fs::read_dir(&versions).map_err(|_| missing())?;
    entries
        .filter_map(Result::ok)
        .filter_map(|entry| {
            let version = parse_semver(&entry.file_name().to_string_lossy())?;
            let script = entry.path().join("scripts/codex-companion.mjs");
            script.is_file().then_some((version, script))
        })
        .max()
        .map(|(_, script)| script)
        .ok_or_else(missing)
}

/// Parses `major.minor.patch` as integers. Any other shape gives `None`.
fn parse_semver(name: &str) -> Option<(u64, u64, u64)> {
    let mut parts = name.split('.').map(|part| part.parse::<u64>().ok());
    let version = (parts.next()??, parts.next()??, parts.next()??);
    parts.next().is_none().then_some(version)
}

/// Runs the adversarial review of the current branch against `base`.
/// Fails when the Codex companion exits with a nonzero status.
pub fn run(root: &Path, base: &str) -> Result<()> {
    let home = std::env::var_os("HOME").context("HOME is not set; cannot find the Codex plugin")?;
    let plugins_root = Path::new(&home).join(".claude/plugins/cache");
    let companion = find_companion(&plugins_root)?;
    let status = Command::new("node")
        .arg(&companion)
        .args(["adversarial-review", "--wait", "--base", base])
        .current_dir(root)
        .status()
        .with_context(|| format!("cannot run node {}", companion.display()))?;
    if !status.success() {
        bail!("the Codex review failed: {status}");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    fn install(root: &Path, version: &str) -> PathBuf {
        let script = root
            .join("openai-codex/codex")
            .join(version)
            .join("scripts/codex-companion.mjs");
        fs::create_dir_all(script.parent().unwrap()).unwrap();
        fs::write(&script, "").unwrap();
        script
    }

    #[test]
    fn picks_highest_semver() {
        let dir = tempfile::tempdir().unwrap();
        install(dir.path(), "1.0.6");
        let newest = install(dir.path(), "1.0.10");
        install(dir.path(), "0.9.99");
        assert_eq!(find_companion(dir.path()).unwrap(), newest);
    }

    #[test]
    fn skips_names_that_are_not_semver() {
        let dir = tempfile::tempdir().unwrap();
        let only = install(dir.path(), "1.2.3");
        install(dir.path(), "latest");
        assert_eq!(find_companion(dir.path()).unwrap(), only);
    }

    #[test]
    fn missing_plugin_is_error() {
        let dir = tempfile::tempdir().unwrap();
        let message = format!("{:#}", find_companion(dir.path()).unwrap_err());
        assert!(
            message.contains("/plugin install codex@openai-codex"),
            "{message}"
        );
    }
}
