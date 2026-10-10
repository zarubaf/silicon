//! `arch-summary`: the facts for an architecture reviewer, as Markdown.
//!
//! The output holds facts only, with no judgment. The order is fixed, so
//! two runs on one tree print the same text.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::path::Path;

use anyhow::{Context, Result, bail};
use cargo_metadata::{DependencyKind, MetadataCommand};
use regex::Regex;

use crate::repo::Repo;

const SPEC: &str = "doc/design/2026-10-08-core-ir.md";
const TRUST: &str = "doc/trust.md";
const TRUST_HEADING: &str = "## Parts";
/// The tool crate has no pipeline stage and no public API.
const TOOL_CRATE: &str = "xtask";

/// A workspace crate with the facts that the summary reports.
struct Krate {
    name: String,
    /// The crate directory relative to the repository root.
    dir: String,
    /// Workspace dependencies as `(name, kind)` with kind `normal`, `dev`, or `build`, sorted.
    deps: Vec<(String, &'static str)>,
}

pub fn render(repo: &Repo) -> Result<String> {
    let metadata = MetadataCommand::new()
        .manifest_path(repo.root.join("Cargo.toml"))
        .no_deps()
        .exec()
        .context("reading cargo metadata")?;
    let order = crate::workspace::layer_order(&metadata);
    let names: BTreeSet<String> = metadata
        .packages
        .iter()
        .map(|p| p.name.to_string())
        .collect();
    let mut crates = Vec::new();
    for package in &metadata.packages {
        let dir = package
            .manifest_path
            .as_std_path()
            .parent()
            .and_then(|d| d.strip_prefix(&repo.root).ok())
            .with_context(|| format!("{} is outside the repository", package.manifest_path))?;
        let mut deps: Vec<(String, &'static str)> = package
            .dependencies
            .iter()
            .filter(|d| names.contains(&d.name))
            .map(|d| (d.name.clone(), kind_label(d.kind)))
            .collect();
        deps.sort();
        deps.dedup();
        crates.push(Krate {
            name: package.name.to_string(),
            dir: dir.to_string_lossy().into_owned(),
            deps,
        });
    }
    crates.sort_by_key(|c| {
        (
            order
                .iter()
                .position(|n| *n == c.name)
                .unwrap_or(order.len()),
            c.name.clone(),
        )
    });

    let mut out = String::from("# Architecture summary\n\nFacts only. Order is fixed.\n");
    out.push_str(&graph_section(&order, &crates));
    out.push_str(&public_section(repo, &crates)?);
    out.push_str(&lines_section(repo, &crates)?);
    out.push_str("\n## Trust table\n\n");
    out.push_str(&trust_table(&repo.read(Path::new(TRUST))?)?);
    out.push_str("\n## Error codes\n\n");
    out.push_str(&error_codes(&repo.read(Path::new(SPEC))?)?);
    Ok(out)
}

fn kind_label(kind: DependencyKind) -> &'static str {
    match kind {
        DependencyKind::Development => "dev",
        DependencyKind::Build => "build",
        _ => "normal",
    }
}

fn graph_section(order: &[String], crates: &[Krate]) -> String {
    let mut out = format!("\n## Layers\n\nOrder: {}\n", order.join(" < "));
    out.push_str("\n## Crate graph\n\nWorkspace dependencies, by crate. A dependency of another kind has its kind in parentheses.\n\n");
    for krate in crates {
        let deps: Vec<String> = krate
            .deps
            .iter()
            .map(|(n, kind)| {
                if *kind == "normal" {
                    n.clone()
                } else {
                    format!("{n} ({kind})")
                }
            })
            .collect();
        let deps = if deps.is_empty() {
            "none".to_owned()
        } else {
            deps.join(", ")
        };
        let _ = writeln!(out, "- {} -> {deps}", krate.name);
    }
    out
}

fn public_section(repo: &Repo, crates: &[Krate]) -> Result<String> {
    let mut out = String::from(
        "\n## Public items\n\nItems declared `pub`, by file, with `pub use` re-exports. This is not a computed public API: it includes methods and items in private modules.\n",
    );
    for krate in crates.iter().filter(|c| c.name != TOOL_CRATE) {
        let _ = write!(out, "\n### {}\n\n", krate.name);
        let prefix = format!("{}/src/", krate.dir);
        let mut files: Vec<_> = repo
            .files
            .iter()
            .filter(|f| f.path.extension().is_some_and(|e| e == "rs"))
            .filter(|f| f.path.starts_with(&prefix))
            .collect();
        files.sort_by(|a, b| a.path.cmp(&b.path));
        for file in files {
            let items = public_items(&repo.read(&file.path)?);
            if !items.is_empty() {
                let _ = writeln!(out, "- {}: {}", file.path.display(), items.join(", "));
            }
        }
    }
    Ok(out)
}

fn lines_section(repo: &Repo, crates: &[Krate]) -> Result<String> {
    let mut out = String::from(
        "\n## Line counts\n\nAll lines of the tracked files, with tests and comments.\n\n",
    );
    for krate in crates {
        let rust = count_lines(repo, &format!("{}/", krate.dir), "rs")?;
        let _ = writeln!(out, "- {}: {rust} Rust lines", krate.name);
    }
    let lean = count_lines(repo, "lean/", "lean")?;
    let _ = writeln!(out, "- lean: {lean} Lean lines");
    Ok(out)
}

fn count_lines(repo: &Repo, prefix: &str, extension: &str) -> Result<usize> {
    let mut total = 0;
    for file in &repo.files {
        if file.path.starts_with(prefix) && file.path.extension().is_some_and(|e| e == extension) {
            total += repo.read(&file.path)?.lines().count();
        }
    }
    Ok(total)
}

/// The `kind name` of each `pub` item declaration in `source`, in file order.
/// `pub(crate)` and other restricted forms do not match.
pub fn public_items(source: &str) -> Vec<String> {
    #[allow(clippy::unwrap_used)] // the patterns are constants
    let (item, reexport) = (
        Regex::new(
            r"^\s*pub\s+(?:(?:const|async|unsafe)\s+)*(fn|struct|enum|trait|type|const|static|mod|union)\s+((?:r#)?[A-Za-z_][A-Za-z0-9_]*)",
        )
        .unwrap(),
        Regex::new(r"^\s*pub\s+use\s+(.*?);?\s*$").unwrap(),
    );
    source
        .lines()
        .filter_map(|line| {
            item.captures(line)
                .map(|c| format!("{} {}", &c[1], &c[2]))
                .or_else(|| reexport.captures(line).map(|c| format!("use {}", &c[1])))
        })
        .collect()
}

/// The table under `## Parts` of the trust document, verbatim.
pub fn trust_table(markdown: &str) -> Result<String> {
    let table: Vec<&str> = markdown
        .lines()
        .skip_while(|line| line.trim_end() != TRUST_HEADING)
        .skip(1)
        .skip_while(|line| !line.starts_with('|'))
        .take_while(|line| line.starts_with('|'))
        .collect();
    if table.is_empty() {
        bail!("`{TRUST}` has no table under `{TRUST_HEADING}`");
    }
    Ok(table.join("\n") + "\n")
}

/// Every error code of the spec, one per line, with the rule text when the
/// table of the rules has a row for it. `E014` has no row: only `run` reports it.
pub fn error_codes(spec: &str) -> Result<String> {
    #[allow(clippy::unwrap_used)] // the patterns are constants
    let (code, row) = (
        Regex::new(r"\bE\d{3}\b").unwrap(),
        Regex::new(r"^\| `(E\d{3})` \| (.*?) +\|$").unwrap(),
    );
    let codes: BTreeSet<&str> = code.find_iter(spec).map(|m| m.as_str()).collect();
    if codes.is_empty() {
        bail!("`{SPEC}` names no error code");
    }
    let mut out = String::new();
    for name in codes {
        let rule = spec
            .lines()
            .find_map(|line| row.captures(line).filter(|c| &c[1] == name))
            .map_or("no rule row", |c| c.get(2).map_or("", |m| m.as_str()));
        let _ = writeln!(out, "- {name}: {rule}");
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_public_items_only() {
        let source = "pub fn a() {}\npub(crate) fn b() {}\n    pub const fn c() {}\npub struct D;\n\
                      pub const E: u8 = 1;\npub use a::b;\nfn f() {}\n    pub async unsafe fn g() {}\n// pub fn h\n";
        assert_eq!(
            public_items(source),
            ["fn a", "fn c", "struct D", "const E", "use a::b", "fn g"]
        );
    }

    #[test]
    fn trust_table_is_copied_verbatim() {
        let md = "# T\n\n## Statuses\n\n| not | this |\n\n## Parts\n\ntext\n\n| A | B |\n| - | - |\n| 1 | 2 |\n\n## Gaps\n";
        assert_eq!(
            trust_table(md).unwrap(),
            "| A | B |\n| - | - |\n| 1 | 2 |\n"
        );
        assert!(trust_table("## Parts\n\nnone\n").is_err());
    }

    #[test]
    fn error_codes_are_sorted_with_rules() {
        let spec = "| `E002` | A name is unique. |\n| `E001` | Syntax is valid.   |\nText E014 and E001.\n";
        assert_eq!(
            error_codes(spec).unwrap(),
            "- E001: Syntax is valid.\n- E002: A name is unique.\n- E014: no rule row\n"
        );
        assert!(error_codes("none").is_err());
    }

    #[test]
    fn real_tree_summary_is_deterministic_and_complete() {
        let repo = Repo::discover_in(Path::new(env!("CARGO_MANIFEST_DIR"))).unwrap();
        let first = render(&repo).unwrap();
        assert_eq!(first, render(&repo).unwrap());
        for needle in [
            "Order: core-ir < syntax < parse < backend-circt < driver",
            "- driver -> ",
            "### core-ir",
            "- xtask: ",
            "- lean: ",
            "| Part ",
            "- E001: ",
            "- E014: ",
        ] {
            assert!(first.contains(needle), "missing {needle:?} in\n{first}");
        }
    }
}
