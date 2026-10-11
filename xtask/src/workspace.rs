// SPDX-License-Identifier: Apache-2.0
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use cargo_metadata::{DependencyKind, MetadataCommand};

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

/// Returns one message per shipped dependency `(from, to)` on a dev-only crate.
///
/// `deps` holds only the normal and build dependencies; a dev-dependency may
/// name a dev-only crate. The exempt tool crate may name one in any kind.
pub fn dev_only_violations(dev_only: &[String], deps: &[(String, String)]) -> Vec<String> {
    deps.iter()
        .filter(|(from, to)| from != EXEMPT && dev_only.contains(to))
        .map(|(from, to)| format!("`{from}` has a normal or build dependency on dev-only `{to}`"))
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
    layers_list(metadata, "order")
}

/// Reads `[workspace.metadata.layers] dev-only` from the root manifest.
///
/// Returns the crate names and one message per defect. A missing key, a
/// value that is not an array, an entry that is not a string, and a name
/// that is not a workspace member are defects, so a bad list cannot turn
/// the rule off.
fn dev_only_list(root_manifest: &str, members: &[String]) -> (Vec<String>, Vec<String>) {
    const KEY: &str = "`[workspace.metadata.layers] dev-only`";
    let doc = root_manifest.parse::<toml::Table>().ok();
    let value = doc.as_ref().and_then(|d| {
        d.get("workspace")?
            .get("metadata")?
            .get("layers")?
            .get("dev-only")
    });
    let Some(value) = value else {
        return (Vec::new(), vec![format!("{KEY} is missing")]);
    };
    let Some(entries) = value.as_array() else {
        return (Vec::new(), vec![format!("{KEY} is not an array")]);
    };
    let mut names = Vec::new();
    let mut problems = Vec::new();
    for entry in entries {
        match entry.as_str() {
            Some(name) if members.iter().any(|m| m == name) => names.push(name.to_owned()),
            Some(name) => problems.push(format!(
                "{KEY} names `{name}`, which is not a workspace member"
            )),
            None => problems.push(format!(
                "{KEY} has the entry `{entry}`, which is not a string"
            )),
        }
    }
    (names, problems)
}

fn layers_list(metadata: &cargo_metadata::Metadata, key: &str) -> Vec<String> {
    metadata
        .workspace_metadata
        .get("layers")
        .and_then(|l| l.get(key))
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
    let root_manifest = std::fs::read_to_string(repo.root.join("Cargo.toml"))
        .context("reading the root Cargo.toml")?;
    let (dev_only, dev_only_problems) = dev_only_list(&root_manifest, &members);
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
    let mut out: Vec<Violation> = dev_only_problems
        .into_iter()
        .map(|m| violation(Path::new("Cargo.toml"), "workspace-dev-only", m))
        .collect();
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
        let shipped: Vec<(String, String)> = package
            .dependencies
            .iter()
            .filter(|d| matches!(d.kind, DependencyKind::Normal | DependencyKind::Build))
            .map(|d| (name.clone(), d.name.clone()))
            .collect();
        for message in dev_only_violations(&dev_only, &shipped) {
            out.push(violation(manifest, "workspace-dev-only", message));
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
    fn normal_dependency_on_dev_only_crate_rejected() {
        let dev_only = names(&["testkit"]);
        let got = dev_only_violations(&dev_only, &[dep("driver", "testkit")]);
        assert_eq!(got.len(), 1);
    }

    #[test]
    fn exempt_tool_may_name_dev_only_crate() {
        let dev_only = names(&["testkit"]);
        assert!(dev_only_violations(&dev_only, &[dep(EXEMPT, "testkit")]).is_empty());
    }

    fn dev_only_of(layers: &str) -> (Vec<String>, Vec<String>) {
        let manifest = format!("[workspace]\n[workspace.metadata.layers]\n{layers}");
        dev_only_list(&manifest, &names(&["testkit", "srcgen"]))
    }

    #[test]
    fn dev_only_list_of_members_accepted() {
        let (got, problems) = dev_only_of("dev-only = [\"srcgen\", \"testkit\"]\n");
        assert_eq!(got, ["srcgen", "testkit"]);
        assert!(problems.is_empty());
    }

    #[test]
    fn missing_dev_only_list_rejected() {
        let (got, problems) = dev_only_of("order = []\n");
        assert!(got.is_empty());
        assert_eq!(problems.len(), 1);
        assert!(problems[0].contains("is missing"), "{problems:?}");
    }

    #[test]
    fn dev_only_list_that_is_no_array_rejected() {
        let (_, problems) = dev_only_of("dev-only = \"testkit\"\n");
        assert_eq!(problems.len(), 1);
        assert!(problems[0].contains("not an array"), "{problems:?}");
    }

    #[test]
    fn dev_only_entry_that_is_no_string_rejected() {
        let (got, problems) = dev_only_of("dev-only = [\"testkit\", 7]\n");
        assert_eq!(got, ["testkit"]);
        assert_eq!(problems.len(), 1);
        assert!(problems[0].contains("not a string"), "{problems:?}");
    }

    #[test]
    fn dev_only_entry_that_is_no_member_rejected() {
        let (got, problems) = dev_only_of("dev-only = [\"testkit\", \"tsetkit\"]\n");
        assert_eq!(got, ["testkit"]);
        assert_eq!(problems.len(), 1);
        assert!(problems[0].contains("`tsetkit`"), "{problems:?}");
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
             [workspace.metadata.layers]\norder = [\"syntax\"]\ndev-only = []\n\n[workspace.lints.rust]\nunused = \"warn\"\n",
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
             [workspace.metadata.layers]\norder = [\"syntax\", \"parse\"]\ndev-only = []\n\n[workspace.lints.rust]\nunused = \"warn\"\n",
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

    #[test]
    fn check_reports_normal_dependency_on_dev_only_crate() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(
            root,
            "Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"crates/*\"]\n\
             [workspace.metadata.layers]\norder = [\"testkit\", \"parse\", \"driver\"]\n\
             dev-only = [\"testkit\"]\n\n[workspace.lints.rust]\nunused = \"warn\"\n",
        );
        write(
            root,
            "crates/testkit/Cargo.toml",
            &crate_manifest("testkit", "", true),
        );
        write(root, "crates/testkit/src/lib.rs", "");
        write(
            root,
            "crates/parse/Cargo.toml",
            &crate_manifest(
                "parse",
                "\n[dev-dependencies]\ntestkit = { path = \"../testkit\" }\n",
                true,
            ),
        );
        write(root, "crates/parse/src/lib.rs", "");
        write(
            root,
            "crates/driver/Cargo.toml",
            &crate_manifest("driver", "testkit = { path = \"../testkit\" }\n", true),
        );
        write(root, "crates/driver/src/lib.rs", "");
        let repo = Repo::from_parts(root.to_path_buf(), Vec::<TrackedFile>::new());

        let got: Vec<_> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.path.display().to_string(), v.rule))
            .collect();
        assert_eq!(
            got,
            [("crates/driver/Cargo.toml".to_owned(), "workspace-dev-only")]
        );
    }

    #[test]
    fn check_reports_missing_dev_only_list() {
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
        let repo = Repo::from_parts(root.to_path_buf(), Vec::<TrackedFile>::new());

        let got: Vec<_> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| (v.path.display().to_string(), v.rule))
            .collect();
        assert_eq!(got, [("Cargo.toml".to_owned(), "workspace-dev-only")]);
    }
}
