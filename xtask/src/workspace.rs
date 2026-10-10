use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use cargo_metadata::MetadataCommand;

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

/// The one crate that sits outside the pipeline layers.
pub const EXEMPT: &str = "xtask";

/// Returns one message per dependency `(from, to)` on a later stage.
///
/// Crates absent from `order` are skipped here; [`unplaced_crates`] reports them.
pub fn layer_violations(order: &[String], deps: &[(String, String)]) -> Vec<String> {
    let position = |name: &str| order.iter().position(|n| n == name);
    deps.iter()
        .filter_map(|(from, to)| {
            let (from_at, to_at) = (position(from)?, position(to)?);
            (to_at > from_at).then(|| format!("`{from}` depends on later stage `{to}`"))
        })
        .collect()
}

/// Returns the workspace crates missing from `order`, except the exempt tool crate.
pub fn unplaced_crates<'a>(order: &[String], members: &'a [String]) -> Vec<&'a str> {
    members
        .iter()
        .map(String::as_str)
        .filter(|m| *m != EXEMPT && !order.iter().any(|o| o == m))
        .collect()
}

/// True when the manifest declares `[lints] workspace = true`.
pub fn inherits_lints(manifest: &str) -> bool {
    manifest
        .parse::<toml::Table>()
        .ok()
        .and_then(|doc| doc.get("lints")?.get("workspace")?.as_bool())
        .unwrap_or(false)
}

/// Returns each tracked `crates/*/Cargo.toml` that is not among the workspace `members`.
pub fn non_member_crates<'a>(tracked: &[&'a Path], members: &[PathBuf]) -> Vec<&'a Path> {
    tracked
        .iter()
        .copied()
        .filter(|p| is_crate_manifest(p) && !members.iter().any(|m| m == p))
        .collect()
}

/// True for a path of the form `crates/<name>/Cargo.toml`.
fn is_crate_manifest(path: &Path) -> bool {
    let parts: Vec<_> = path
        .components()
        .map(std::path::Component::as_os_str)
        .collect();
    matches!(parts.as_slice(), [c, _, m] if *c == "crates" && *m == "Cargo.toml")
}

fn violation(path: &Path, rule: &'static str, message: String) -> Violation {
    Violation {
        path: path.to_path_buf(),
        line: None,
        rule,
        severity: Severity::Error,
        message,
    }
}

/// The crate names of `[workspace.metadata.layers] order`, empty when absent.
pub fn layer_order(metadata: &cargo_metadata::Metadata) -> Vec<String> {
    metadata
        .workspace_metadata
        .get("layers")
        .and_then(|l| l.get("order"))
        .and_then(|o| o.as_array())
        .map(|a| {
            a.iter()
                .filter_map(|n| n.as_str().map(str::to_owned))
                .collect()
        })
        .unwrap_or_default()
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let metadata = MetadataCommand::new()
        .manifest_path(repo.root.join("Cargo.toml"))
        .no_deps()
        .exec()
        .context("reading cargo metadata")?;
    let order = layer_order(&metadata);

    let members: Vec<String> = metadata
        .packages
        .iter()
        .map(|p| p.name.to_string())
        .collect();
    let manifests: Vec<PathBuf> = metadata
        .packages
        .iter()
        .map(|p| {
            p.manifest_path
                .as_std_path()
                .strip_prefix(&repo.root)
                .map_or_else(|_| p.manifest_path.clone().into(), Path::to_path_buf)
        })
        .collect();
    let tracked: Vec<&Path> = repo.files.iter().map(|f| f.path.as_path()).collect();
    let mut out = Vec::new();
    for path in non_member_crates(&tracked, &manifests) {
        out.push(violation(
            path,
            "workspace-member",
            "crate is not in `[workspace] members`, so no Rust gate checks it".into(),
        ));
    }
    for (package, manifest) in metadata.packages.iter().zip(&manifests) {
        let name = package.name.to_string();

        if unplaced_crates(&order, std::slice::from_ref(&name)).len() == 1 {
            out.push(violation(
                manifest,
                "workspace-layers",
                format!("crate `{name}` not placed in workspace.metadata.layers"),
            ));
        }
        let deps: Vec<(String, String)> = package
            .dependencies
            .iter()
            .filter(|d| d.path.is_some() && members.contains(&d.name))
            .map(|d| (name.clone(), d.name.clone()))
            .collect();
        for message in layer_violations(&order, &deps) {
            out.push(violation(manifest, "workspace-layers", message));
        }

        let text = std::fs::read_to_string(&package.manifest_path)
            .with_context(|| format!("reading {}", package.manifest_path))?;
        if !inherits_lints(&text) {
            out.push(violation(
                manifest,
                "workspace-lints",
                "crate must set `[lints] workspace = true`".into(),
            ));
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::TrackedFile;

    fn names(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|s| (*s).to_owned()).collect()
    }

    fn dep(from: &str, to: &str) -> (String, String) {
        (from.to_owned(), to.to_owned())
    }

    #[test]
    fn later_stage_dependency_rejected() {
        let got = layer_violations(&names(&["syntax", "parse"]), &[dep("syntax", "parse")]);
        assert_eq!(got.len(), 1);
    }

    #[test]
    fn earlier_stage_dependency_allowed() {
        let got = layer_violations(&names(&["syntax", "parse"]), &[dep("parse", "syntax")]);
        assert!(got.is_empty());
    }

    #[test]
    fn unlisted_crate_rejected() {
        let members = names(&["syntax", "extra", "xtask"]);
        assert_eq!(unplaced_crates(&names(&["syntax"]), &members), ["extra"]);
    }

    #[test]
    fn crate_manifest_outside_workspace_reported() {
        let tracked = [
            Path::new("crates/a/Cargo.toml"),
            Path::new("crates/b/Cargo.toml"),
            Path::new("crates/a/src/lib.rs"),
            Path::new("crates/a/fuzz/Cargo.toml"),
            Path::new("xtask/Cargo.toml"),
        ];
        let members = [PathBuf::from("crates/a/Cargo.toml")];
        assert_eq!(
            non_member_crates(&tracked, &members),
            [Path::new("crates/b/Cargo.toml")]
        );
    }

    #[test]
    fn check_reports_crate_missing_from_members() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(
            root,
            "Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/syntax\"]\n\
             [workspace.metadata.layers]\norder = [\"syntax\"]\n\n[workspace.lints.rust]\nunused = \"warn\"\n",
        );
        write(
            root,
            "crates/syntax/Cargo.toml",
            &crate_manifest("syntax", "", true),
        );
        write(root, "crates/syntax/src/lib.rs", "");
        write(
            root,
            "crates/orphan/Cargo.toml",
            &crate_manifest("orphan", "", true),
        );
        write(root, "crates/orphan/src/lib.rs", "");
        let tracked = |p: &str| TrackedFile {
            path: p.into(),
            is_symlink: false,
            is_executable: false,
        };
        let files = vec![
            tracked("Cargo.toml"),
            tracked("crates/syntax/Cargo.toml"),
            tracked("crates/orphan/Cargo.toml"),
        ];
        let repo = Repo::from_parts(root.to_path_buf(), files);
        let got: Vec<_> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.path.display().to_string(), v.rule))
            .collect();
        assert_eq!(
            got,
            [("crates/orphan/Cargo.toml".to_owned(), "workspace-member")]
        );
    }

    #[test]
    fn lints_workspace_required() {
        assert!(!inherits_lints("[package]\nname='a'\n"));
        assert!(!inherits_lints("[lints]\nworkspace = false\n"));
        assert!(inherits_lints(
            "[package]\nname='a'\n[lints]\nworkspace = true\n"
        ));
    }

    fn write(root: &Path, rel: &str, body: &str) {
        let full = root.join(rel);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, body).unwrap();
    }

    fn crate_manifest(name: &str, deps: &str, lints: bool) -> String {
        let lints = if lints {
            "[lints]\nworkspace = true\n"
        } else {
            ""
        };
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\n{lints}\n[dependencies]\n{deps}"
        )
    }

    #[test]
    fn check_reports_layers_and_lints() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(
            root,
            "Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\"]\n\
             [workspace.metadata.layers]\norder = [\"syntax\", \"parse\"]\n\n[workspace.lints.rust]\nunused = \"warn\"\n",
        );
        write(
            root,
            "crates/syntax/Cargo.toml",
            &crate_manifest("syntax", "parse = { path = \"../parse\" }\n", true),
        );
        write(root, "crates/syntax/src/lib.rs", "");
        write(
            root,
            "crates/parse/Cargo.toml",
            &crate_manifest("parse", "", false),
        );
        write(root, "crates/parse/src/lib.rs", "");
        write(
            root,
            "crates/stray/Cargo.toml",
            &crate_manifest("stray", "", true),
        );
        write(root, "crates/stray/src/lib.rs", "");
        let repo = Repo::from_parts(root.to_path_buf(), Vec::<TrackedFile>::new());

        let mut got: Vec<_> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.path.display().to_string(), v.rule))
            .collect();
        got.sort();
        assert_eq!(
            got,
            [
                ("crates/parse/Cargo.toml".to_owned(), "workspace-lints"),
                ("crates/stray/Cargo.toml".to_owned(), "workspace-layers"),
                ("crates/syntax/Cargo.toml".to_owned(), "workspace-layers"),
            ]
        );
    }
}
