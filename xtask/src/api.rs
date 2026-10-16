// SPDX-License-Identifier: Apache-2.0
//! The rule `api-allowlist`: each library crate lists its public items in `crates/<crate>/api.txt`,
//! and the check fails on an item that is not in the list and on a list entry that has no item.
//!
//! The scan reads the crate from `src/lib.rs` with `syn` and follows the `mod` declarations. An
//! item is public when it is `pub`, and every module on its path is `pub` or the item is the
//! target of a `pub use` in a public module. The scan also lists the `pub` methods of inherent
//! `impl` blocks. It skips every item with `#[cfg(test)]`. It does not list fields, variants, or
//! trait items, and it does not follow a `pub use` of another crate: such a re-export is one entry.
//! `cargo xtask api-list` rewrites the lists.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use syn::{Attribute, Item, Meta, Visibility};

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

/// The most `pub use` hops that the scan follows for one name.
const MAX_HOPS: usize = 8;

/// A public item or method found in a module.
#[derive(Debug, Clone)]
struct Decl {
    kind: &'static str,
    public: bool,
}

/// A `use` declaration: the path of the module of the target, the name of the target (`*` for a
/// glob), and the name that the declaration brings in.
#[derive(Debug, Clone)]
struct Use {
    public: bool,
    path: Vec<String>,
    name: String,
    alias: String,
}

#[derive(Debug, Default)]
struct Module {
    public: bool,
    decls: BTreeMap<String, Decl>,
    uses: Vec<Use>,
    children: BTreeMap<String, Module>,
}

/// Inherent methods by the name of the type, over the whole crate.
type Methods = BTreeMap<String, BTreeSet<String>>;

fn is_test_only(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| match &a.meta {
        Meta::List(l) => l.path.is_ident("cfg") && l.tokens.to_string() == "test",
        _ => false,
    })
}

fn is_pub(vis: &Visibility) -> bool {
    matches!(vis, Visibility::Public(_))
}

fn name_of(ident: &syn::Ident) -> String {
    ident.to_string().trim_start_matches("r#").to_owned()
}

fn use_leaves(tree: &syn::UseTree, prefix: &mut Vec<String>, public: bool, out: &mut Vec<Use>) {
    match tree {
        syn::UseTree::Path(p) => {
            prefix.push(name_of(&p.ident));
            use_leaves(&p.tree, prefix, public, out);
            prefix.pop();
        }
        syn::UseTree::Name(n) => {
            let name = name_of(&n.ident);
            let mut path = prefix.clone();
            if name == "self" {
                let Some(last) = path.pop() else { return };
                out.push(Use {
                    public,
                    path,
                    alias: last.clone(),
                    name: last,
                });
            } else {
                out.push(Use {
                    public,
                    path,
                    alias: name.clone(),
                    name,
                });
            }
        }
        syn::UseTree::Rename(r) => out.push(Use {
            public,
            path: prefix.clone(),
            name: name_of(&r.ident),
            alias: name_of(&r.rename),
        }),
        syn::UseTree::Glob(_) => out.push(Use {
            public,
            path: prefix.clone(),
            name: "*".to_owned(),
            alias: "*".to_owned(),
        }),
        syn::UseTree::Group(g) => {
            for t in &g.items {
                use_leaves(t, prefix, public, out);
            }
        }
    }
}

/// Loads the module of `items` and, through `load`, the files of its `mod x;` declarations.
fn read_module(
    items: &[Item],
    dir: &Path,
    path: &[String],
    load: &dyn Fn(&Path) -> Result<Option<String>>,
    methods: &mut Methods,
) -> Result<Module> {
    let mut module = Module::default();
    for item in items {
        match item {
            Item::Fn(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.sig.ident, "fn", &i.vis);
            }
            Item::Struct(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "struct", &i.vis);
            }
            Item::Enum(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "enum", &i.vis);
            }
            Item::Union(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "union", &i.vis);
            }
            Item::Trait(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "trait", &i.vis);
            }
            Item::Type(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "type", &i.vis);
            }
            Item::Const(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "const", &i.vis);
            }
            Item::Static(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "static", &i.vis);
            }
            Item::Macro(i) if !is_test_only(&i.attrs) => {
                let exported = i.attrs.iter().any(|a| a.path().is_ident("macro_export"));
                if let (true, Some(ident)) = (exported, &i.ident) {
                    // An exported macro lives at the root of the crate.
                    module.decls.insert(
                        name_of(ident),
                        Decl {
                            kind: "macro",
                            public: true,
                        },
                    );
                }
            }
            Item::Use(i) if !is_test_only(&i.attrs) => {
                use_leaves(&i.tree, &mut Vec::new(), is_pub(&i.vis), &mut module.uses);
            }
            Item::Impl(i) if !is_test_only(&i.attrs) && i.trait_.is_none() => {
                if let syn::Type::Path(t) = &*i.self_ty
                    && let Some(seg) = t.path.segments.last()
                {
                    let entry = methods.entry(name_of(&seg.ident)).or_default();
                    for member in &i.items {
                        if let syn::ImplItem::Fn(f) = member
                            && is_pub(&f.vis)
                            && !is_test_only(&f.attrs)
                        {
                            entry.insert(name_of(&f.sig.ident));
                        }
                    }
                }
            }
            Item::Mod(m) if !is_test_only(&m.attrs) => {
                if m.attrs.iter().any(|a| a.path().is_ident("path")) {
                    bail!(
                        "the module `{}` uses #[path], which the scan does not follow",
                        m.ident
                    );
                }
                let name = name_of(&m.ident);
                let mut child_path = path.to_vec();
                child_path.push(name.clone());
                let mut child = if let Some((_, inner)) = &m.content {
                    read_module(inner, &dir.join(&name), &child_path, load, methods)?
                } else {
                    read_module_file(dir, &name, &child_path, load, methods)?
                };
                child.public = is_pub(&m.vis);
                module.children.insert(name, child);
            }
            _ => {}
        }
    }
    Ok(module)
}

fn declare(module: &mut Module, ident: &syn::Ident, kind: &'static str, vis: &Visibility) {
    module.decls.insert(
        name_of(ident),
        Decl {
            kind,
            public: is_pub(vis),
        },
    );
}

/// Loads the file of the module `name` declared in a file whose children live in `dir`.
fn read_module_file(
    dir: &Path,
    name: &str,
    path: &[String],
    load: &dyn Fn(&Path) -> Result<Option<String>>,
    methods: &mut Methods,
) -> Result<Module> {
    let flat = dir.join(format!("{name}.rs"));
    let nested = dir.join(name).join("mod.rs");
    for (file, child_dir) in [(flat, dir.join(name)), (nested, dir.join(name))] {
        if let Some(text) = load(&file)? {
            let parsed =
                syn::parse_file(&text).with_context(|| format!("parsing {}", file.display()))?;
            return read_module(&parsed.items, &child_dir, path, load, methods);
        }
    }
    bail!(
        "the file of the module `{}` is not in the repository",
        path.join("::")
    )
}

fn find<'a>(root: &'a Module, path: &[String]) -> Option<&'a Module> {
    path.iter().try_fold(root, |m, seg| m.children.get(seg))
}

/// Resolves the path of a `use` that sits in the module `at` to an absolute path in the crate.
/// `None` means the path leaves the crate.
fn absolute(root: &Module, at: &[String], path: &[String]) -> Option<Vec<String>> {
    let (first, rest) = path.split_first()?;
    let mut base: Vec<String> = match first.as_str() {
        "crate" => Vec::new(),
        "self" => at.to_vec(),
        "super" => at[..at.len().checked_sub(1)?].to_vec(),
        name => {
            let here = find(root, at)?;
            if here.children.contains_key(name) || here.decls.contains_key(name) {
                at.to_vec()
            } else {
                return None;
            }
        }
    };
    if matches!(first.as_str(), "crate" | "self" | "super") {
        base.extend(rest.iter().cloned());
    } else {
        base.extend(path.iter().cloned());
    }
    Some(base)
}

struct Scan<'a> {
    root: &'a Module,
    methods: &'a Methods,
    crate_name: &'a str,
    out: BTreeSet<String>,
}

impl Scan<'_> {
    fn entry(&mut self, kind: &str, at: &[String], name: &str) {
        let mut full = vec![self.crate_name.to_owned()];
        full.extend(at.iter().cloned());
        full.push(name.to_owned());
        self.out.insert(format!("{kind} {}", full.join("::")));
    }

    /// Lists the item `orig` as `name` in the module `at`, with its methods.
    fn item(&mut self, kind: &str, at: &[String], name: &str, orig: &str) {
        self.entry(kind, at, name);
        if let Some(ms) = self.methods.get(orig) {
            let mut owner = at.to_vec();
            owner.push(name.to_owned());
            for m in ms {
                self.entry("method", &owner, m);
            }
        }
    }

    /// Lists the public contents of the module at `source` as if it sat at `alias`.
    fn export_module(&mut self, source: &[String], alias: &[String], hops: usize) {
        let Some(module) = find(self.root, source) else {
            return;
        };
        let decls = module.decls.clone();
        let children: Vec<(String, bool)> = module
            .children
            .iter()
            .map(|(n, m)| (n.clone(), m.public))
            .collect();
        let uses = module.uses.clone();
        for (name, decl) in decls {
            if decl.public || decl.kind == "macro" {
                self.item(decl.kind, alias, &name, &name);
            }
        }
        for (name, public) in children {
            if public {
                self.entry("mod", alias, &name);
                let (mut s, mut a) = (source.to_vec(), alias.to_vec());
                s.push(name.clone());
                a.push(name);
                self.export_module(&s, &a, hops);
            }
        }
        self.reexports(source, alias, &uses, hops);
    }

    /// Lists the targets of the public `use` declarations `uses` of the module `source`.
    fn reexports(&mut self, source: &[String], alias: &[String], uses: &[Use], hops: usize) {
        for u in uses.iter().filter(|u| u.public) {
            let Some(target) = absolute(self.root, source, &u.path) else {
                if u.name != "*" {
                    let from = u.path.join("::");
                    self.entry(&format!("use {from}::{} as", u.name), alias, &u.alias);
                }
                continue;
            };
            if hops == 0 {
                continue;
            }
            if u.name == "*" {
                self.export_module(&target, alias, hops - 1);
            } else {
                self.export_name(&target, &u.name, alias, &u.alias, hops - 1);
            }
        }
    }

    /// Lists the name `name` of the module `target` as `as_name` in the module `alias`.
    fn export_name(
        &mut self,
        target: &[String],
        name: &str,
        alias: &[String],
        as_name: &str,
        hops: usize,
    ) {
        let Some(module) = find(self.root, target) else {
            return;
        };
        if let Some(decl) = module.decls.get(name) {
            let kind = decl.kind;
            self.item(kind, alias, as_name, name);
        } else if module.children.contains_key(name) {
            let mut s = target.to_vec();
            s.push(name.to_owned());
            let mut a = alias.to_vec();
            a.push(as_name.to_owned());
            self.entry("mod", alias, as_name);
            self.export_module(&s, &a, hops);
        } else {
            let chained: Vec<Use> = module
                .uses
                .iter()
                .filter(|u| u.alias == name || u.name == "*")
                .map(|u| {
                    if u.name == "*" {
                        Use {
                            public: true,
                            path: u.path.clone(),
                            name: name.to_owned(),
                            alias: as_name.to_owned(),
                        }
                    } else {
                        Use {
                            public: true,
                            alias: as_name.to_owned(),
                            ..u.clone()
                        }
                    }
                })
                .collect();
            self.reexports(target, alias, &chained, hops);
        }
    }
}

/// The sorted lines of the public API of the crate `crate_name` whose root file is `root_file`.
/// `load` returns the text of a file or `None` for a file that does not exist.
pub fn scan_crate(
    crate_name: &str,
    root_file: &Path,
    load: &dyn Fn(&Path) -> Result<Option<String>>,
) -> Result<Vec<String>> {
    let text = load(root_file)?.with_context(|| format!("{} is missing", root_file.display()))?;
    let parsed =
        syn::parse_file(&text).with_context(|| format!("parsing {}", root_file.display()))?;
    let dir = root_file.parent().unwrap_or(Path::new("")).to_path_buf();
    let mut methods = Methods::new();
    let root = read_module(&parsed.items, &dir, &[], load, &mut methods)?;
    let mut scan = Scan {
        root: &root,
        methods: &methods,
        crate_name,
        out: BTreeSet::new(),
    };
    scan.export_module(&[], &[], MAX_HOPS);
    Ok(scan.out.into_iter().collect())
}

/// The library crates of the repository: the name and the root file of each `crates/*/src/lib.rs`.
fn library_crates(repo: &Repo) -> Vec<(String, PathBuf)> {
    let mut out: Vec<(String, PathBuf)> = repo
        .files
        .iter()
        .filter_map(|f| {
            let parts: Vec<_> = f.path.iter().filter_map(|c| c.to_str()).collect();
            match parts.as_slice() {
                ["crates", name, "src", "lib.rs"] => Some(((*name).to_owned(), f.path.clone())),
                _ => None,
            }
        })
        .collect();
    out.sort();
    out
}

fn list_path(name: &str) -> PathBuf {
    PathBuf::from("crates").join(name).join("api.txt")
}

fn loader(repo: &Repo) -> impl Fn(&Path) -> Result<Option<String>> + '_ {
    move |p| {
        if repo.files.iter().any(|f| f.path == p && !f.is_symlink) {
            repo.read(p).map(Some)
        } else {
            Ok(None)
        }
    }
}

/// The current public API of each library crate: the crate name and its lines.
fn current(repo: &Repo) -> Result<Vec<(String, Vec<String>)>> {
    let load = loader(repo);
    library_crates(repo)
        .into_iter()
        .map(|(name, root)| {
            let lines = scan_crate(&name.replace('-', "_"), &root, &load)?;
            Ok((name, lines))
        })
        .collect()
}

/// The problems of one crate: the lines of `now` that `listed` lacks, and the reverse.
pub fn diff(listed: &str, now: &[String]) -> Vec<String> {
    let listed: BTreeSet<&str> = listed.lines().filter(|l| !l.trim().is_empty()).collect();
    let now: BTreeSet<&str> = now.iter().map(String::as_str).collect();
    let new = now
        .difference(&listed)
        .map(|l| format!("`{l}` is public but not in the list"));
    let stale = listed
        .difference(&now)
        .map(|l| format!("`{l}` is in the list but not public"));
    new.chain(stale).collect()
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    for (name, lines) in current(repo)? {
        let path = list_path(&name);
        let listed = repo.read(&path).unwrap_or_default();
        for message in diff(&listed, &lines) {
            out.push(Violation {
                path: path.clone(),
                line: None,
                rule: "api-allowlist",
                severity: Severity::Error,
                message: format!(
                    "{message}; hide the item, or review the change and run `cargo xtask api-list`"
                ),
            });
        }
    }
    Ok(out)
}

/// Rewrites the list of each library crate.
pub fn write(repo: &Repo) -> Result<()> {
    for (name, lines) in current(repo)? {
        let mut text = lines.join("\n");
        text.push('\n');
        let path = repo.root.join(list_path(&name));
        std::fs::write(&path, text).with_context(|| format!("writing {}", path.display()))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(files: &[(&str, &str)]) -> Vec<String> {
        let load = |p: &Path| {
            Ok(files
                .iter()
                .find(|(n, _)| Path::new(n) == p)
                .map(|(_, t)| (*t).to_owned()))
        };
        scan_crate("c", Path::new("src/lib.rs"), &load).unwrap()
    }

    #[test]
    fn lists_public_items_and_methods() {
        let lines = scan(&[(
            "src/lib.rs",
            "pub struct A; impl A { pub fn new() {} fn hidden() {} }\nfn private() {}\n\
             pub(crate) fn limited() {}\n#[cfg(test)] pub fn test_only() {}\n",
        )]);
        assert_eq!(lines, ["method c::A::new", "struct c::A"]);
    }

    #[test]
    fn private_module_hides_its_items() {
        let lines = scan(&[
            ("src/lib.rs", "mod inner;\npub mod open;\n"),
            ("src/inner.rs", "pub fn hidden() {}\n"),
            ("src/open.rs", "pub fn shown() {}\n"),
        ]);
        assert_eq!(lines, ["fn c::open::shown", "mod c::open"]);
    }

    #[test]
    fn reexport_exposes_an_item_of_a_private_module() {
        let lines = scan(&[
            (
                "src/lib.rs",
                "mod inner;\npub use inner::{Shown, deep::Deep as Renamed};\n",
            ),
            (
                "src/inner.rs",
                "pub struct Shown; impl Shown { pub fn m(&self) {} }\npub struct Other;\npub mod deep;\n",
            ),
            ("src/inner/deep.rs", "pub struct Deep;\n"),
        ]);
        assert_eq!(
            lines,
            ["method c::Shown::m", "struct c::Renamed", "struct c::Shown"]
        );
    }

    #[test]
    fn glob_reexport_lists_the_public_items() {
        let lines = scan(&[
            ("src/lib.rs", "mod inner;\npub use inner::*;\n"),
            ("src/inner.rs", "pub fn a() {}\nfn b() {}\n"),
        ]);
        assert_eq!(lines, ["fn c::a"]);
    }

    #[test]
    fn reexport_of_another_crate_is_one_entry() {
        let lines = scan(&[("src/lib.rs", "pub use other::thing::X;\n")]);
        assert_eq!(lines, ["use other::thing::X as c::X"]);
    }

    #[test]
    fn diff_reports_new_and_stale_entries() {
        let problems = diff(
            "fn c::a\nfn c::gone\n",
            &["fn c::a".to_owned(), "fn c::b".to_owned()],
        );
        assert_eq!(problems.len(), 2);
        assert!(problems[0].contains("c::b"));
        assert!(problems[1].contains("c::gone"));
    }
}
