// SPDX-License-Identifier: Apache-2.0
//! The rule `api-allowlist`: each library crate lists its public items in `crates/<crate>/api.txt`,
//! and the check fails on an item that is not in the list and on a list entry that has no item.
//!
//! The scan reads the crate from `src/lib.rs` with `syn` and follows the `mod` declarations. An
//! item is public when it is `pub`, and every module on its path is `pub` or the item is the
//! target of a `pub use` in a public module. The scan also lists the `pub` methods of inherent
//! `impl` blocks, keyed by the module path of the type, and the methods of the target of a
//! `pub type` alias. An exported macro sits at the crate root. The scan skips every item with
//! `#[cfg(test)]`. It does not list fields, variants, or trait items, and a `pub use` of another
//! crate is one entry.
//!
//! The scan fails, and does not skip, when it meets a form that it cannot resolve: a `#[path]`
//! module, two items of one name in one module (for example under different `cfg(feature)`), a
//! `use` chain that is too long, or a path that it cannot follow.
//! `cargo xtask api-list` rewrites the lists.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use syn::{Attribute, Item, Meta, Visibility};

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

/// The most `use` hops that the scan follows for one name.
const MAX_HOPS: usize = 8;

/// An item of a module. `alias_of` holds the target path of a `pub type`.
#[derive(Debug, Clone)]
struct Decl {
    kind: &'static str,
    public: bool,
    alias_of: Option<Vec<String>>,
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

/// An inherent `impl` with public methods, before the type is resolved.
#[derive(Debug)]
struct PendingImpl {
    at: Vec<String>,
    ty: Vec<String>,
    methods: Vec<String>,
}

/// What the read of the files collects besides the module tree.
#[derive(Debug, Default)]
struct Collected {
    impls: Vec<PendingImpl>,
    macros: BTreeSet<String>,
    /// The tokens of each `macro_rules!` definition, by name.
    definitions: BTreeMap<String, proc_macro2::TokenStream>,
}

/// Inherent methods by the full module path of the type, joined with `::`.
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

/// The segments of a path type without their generics, or `None` for another type.
fn type_segments(ty: &syn::Type) -> Option<Vec<String>> {
    match ty {
        syn::Type::Path(t) if t.qself.is_none() => {
            Some(t.path.segments.iter().map(|s| name_of(&s.ident)).collect())
        }
        syn::Type::Group(g) => type_segments(&g.elem),
        syn::Type::Paren(p) => type_segments(&p.elem),
        _ => None,
    }
}

/// Loads the module of `items` and, through `load`, the files of its `mod x;` declarations.
fn read_module(
    items: &[Item],
    dir: &Path,
    path: &[String],
    load: &dyn Fn(&Path) -> Result<Option<String>>,
    col: &mut Collected,
) -> Result<Module> {
    let mut module = Module::default();
    for item in items {
        match item {
            Item::Fn(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.sig.ident, "fn", &i.vis, None)?;
            }
            Item::Struct(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "struct", &i.vis, None)?;
            }
            Item::Enum(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "enum", &i.vis, None)?;
            }
            Item::Union(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "union", &i.vis, None)?;
            }
            Item::Trait(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "trait", &i.vis, None)?;
            }
            Item::Type(i) if !is_test_only(&i.attrs) => {
                let target = type_segments(&i.ty);
                declare(&mut module, &i.ident, "type", &i.vis, target)?;
            }
            Item::Const(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "const", &i.vis, None)?;
            }
            Item::Static(i) if !is_test_only(&i.attrs) => {
                declare(&mut module, &i.ident, "static", &i.vis, None)?;
            }
            Item::Macro(i) if !is_test_only(&i.attrs) => {
                if let Some(ident) = &i.ident {
                    if i.attrs.iter().any(|a| a.path().is_ident("macro_export")) {
                        col.macros.insert(name_of(ident));
                    }
                    col.definitions.insert(name_of(ident), i.mac.tokens.clone());
                } else {
                    declare_from_macro(&mut module, path, &i.mac, col)?;
                }
            }
            Item::Use(i) if !is_test_only(&i.attrs) => {
                use_leaves(&i.tree, &mut Vec::new(), is_pub(&i.vis), &mut module.uses);
            }
            Item::Impl(i) if !is_test_only(&i.attrs) && i.trait_.is_none() => {
                let methods: Vec<String> = i
                    .items
                    .iter()
                    .filter_map(|member| match member {
                        syn::ImplItem::Fn(f) if is_pub(&f.vis) && !is_test_only(&f.attrs) => {
                            Some(name_of(&f.sig.ident))
                        }
                        _ => None,
                    })
                    .collect();
                if !methods.is_empty() {
                    let Some(ty) = type_segments(&i.self_ty) else {
                        bail!(
                            "an inherent impl in `{}` has a type that the scan cannot resolve",
                            path.join("::")
                        );
                    };
                    col.impls.push(PendingImpl {
                        at: path.to_vec(),
                        ty,
                        methods,
                    });
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
                    read_module(inner, &dir.join(&name), &child_path, load, col)?
                } else {
                    read_module_file(dir, &name, &child_path, load, col)?
                };
                child.public = is_pub(&m.vis);
                if module.children.insert(name, child).is_some() {
                    bail!(
                        "the module `{}` is declared twice in `{}`",
                        m.ident,
                        path.join("::")
                    );
                }
            }
            _ => {}
        }
    }
    Ok(module)
}

/// Declares the `pub` items that the definition of the macro of an item-position call writes. A
/// literal name is the item. A name from a macro variable (`pub struct $name`) stands for each
/// identifier of the call outside attributes, and a `pub fn` of the same definition is a method of
/// each of them. This reads the text of the definition and does not expand it.
fn declare_from_macro(
    module: &mut Module,
    at: &[String],
    call: &syn::Macro,
    col: &mut Collected,
) -> Result<()> {
    let name = call
        .path
        .segments
        .last()
        .map(|s| name_of(&s.ident))
        .unwrap_or_default();
    let Some(definition) = col.definitions.get(&name) else {
        bail!("the scan does not know the macro `{name}!`, which may declare items");
    };
    let mut flat = Vec::new();
    flatten(definition.clone(), &mut flat);
    let word = |i: usize| flat.get(i).and_then(|t| t.as_deref());
    let computed = call_names(call.tokens.clone());
    let mut uses_computed = false;
    for i in 0..flat.len() {
        if word(i) != Some("pub") {
            continue;
        }
        let kind: &'static str = match word(i + 1) {
            Some("struct") => "struct",
            Some("enum") => "enum",
            Some("union") => "union",
            Some("trait") => "trait",
            Some("type") => "type",
            Some("static") => "static",
            Some("const") if word(i + 2) != Some("fn") => "const",
            Some("fn" | "const" | "unsafe" | "async") => {
                let fn_at = (i + 1..i + 4).find(|&k| word(k) == Some("fn"));
                let Some(method) = fn_at.and_then(|k| word(k + 1)) else {
                    continue;
                };
                if !uses_computed {
                    bail!("the macro `{name}!` declares a `pub fn` that the scan cannot place");
                }
                for ty in &computed {
                    col.impls.push(PendingImpl {
                        at: at.to_vec(),
                        ty: vec![ty.clone()],
                        methods: vec![method.to_owned()],
                    });
                }
                continue;
            }
            _ => continue,
        };
        match word(i + 2) {
            Some("$") => {
                uses_computed = true;
                for item in &computed {
                    let ident = syn::Ident::new(item, proc_macro2::Span::call_site());
                    declare(module, &ident, kind, &syn::parse_quote!(pub), None)?;
                }
            }
            Some(item) => {
                let ident = syn::Ident::new(item, proc_macro2::Span::call_site());
                declare(module, &ident, kind, &syn::parse_quote!(pub), None)?;
            }
            None => bail!("the macro `{name}!` declares a `pub {kind}` that the scan cannot read"),
        }
    }
    Ok(())
}

/// The identifiers of the tokens of a macro call, without the attributes.
fn call_names(stream: proc_macro2::TokenStream) -> Vec<String> {
    let mut names = Vec::new();
    let mut after_hash = false;
    for tree in stream {
        match tree {
            proc_macro2::TokenTree::Punct(p) if p.as_char() == '#' => after_hash = true,
            proc_macro2::TokenTree::Group(_) if after_hash => after_hash = false,
            proc_macro2::TokenTree::Ident(i) => {
                after_hash = false;
                names.push(name_of(&i));
            }
            _ => after_hash = false,
        }
    }
    names
}

/// The identifiers of a token stream in order, `$` as a word, and `None` for any other token.
fn flatten(stream: proc_macro2::TokenStream, out: &mut Vec<Option<String>>) {
    for tree in stream {
        match tree {
            proc_macro2::TokenTree::Group(g) => flatten(g.stream(), out),
            proc_macro2::TokenTree::Ident(i) => out.push(Some(name_of(&i))),
            proc_macro2::TokenTree::Punct(p) if p.as_char() == '$' => {
                out.push(Some("$".to_owned()));
            }
            _ => out.push(None),
        }
    }
}

fn declare(
    module: &mut Module,
    ident: &syn::Ident,
    kind: &'static str,
    vis: &Visibility,
    alias_of: Option<Vec<String>>,
) -> Result<()> {
    let decl = Decl {
        kind,
        public: is_pub(vis),
        alias_of,
    };
    if module.decls.insert(name_of(ident), decl).is_some() {
        bail!(
            "two items named `{ident}` in one module (for example under different `cfg`); \
             the scan cannot tell them apart, so rename one"
        );
    }
    Ok(())
}

/// Loads the file of the module `name` declared in a file whose children live in `dir`.
fn read_module_file(
    dir: &Path,
    name: &str,
    path: &[String],
    load: &dyn Fn(&Path) -> Result<Option<String>>,
    col: &mut Collected,
) -> Result<Module> {
    let flat = dir.join(format!("{name}.rs"));
    let nested = dir.join(name).join("mod.rs");
    for (file, child_dir) in [(flat, dir.join(name)), (nested, dir.join(name))] {
        if let Some(text) = load(&file)? {
            let parsed =
                syn::parse_file(&text).with_context(|| format!("parsing {}", file.display()))?;
            return read_module(&parsed.items, &child_dir, path, load, col);
        }
    }
    bail!(
        "the file of the module `{}` is not in the repository",
        path.join("::")
    )
}

fn find<'a>(root: &'a Module, path: &[String]) -> Result<&'a Module> {
    path.iter()
        .try_fold(root, |m, seg| m.children.get(seg))
        .with_context(|| format!("the scan cannot find the module `{}`", path.join("::")))
}

/// The full path of the entity that `name` means in the module `at`, through `use` aliases and
/// globs. `None` means that the module does not know the name, so the name is another crate.
fn lookup_local(
    root: &Module,
    at: &[String],
    name: &str,
    depth: usize,
) -> Result<Option<Vec<String>>> {
    if depth == 0 {
        bail!(
            "a `use` chain at `{}` is too long for the scan",
            at.join("::")
        );
    }
    let here = find(root, at)?;
    let mut own = at.to_vec();
    own.push(name.to_owned());
    if here.decls.contains_key(name) || here.children.contains_key(name) {
        return Ok(Some(own));
    }
    for u in &here.uses {
        if u.name != "*" && u.alias == name {
            let mut full = u.path.clone();
            full.push(u.name.clone());
            return absolute(root, at, &full, depth - 1);
        }
    }
    for u in here.uses.iter().filter(|u| u.name == "*") {
        if let Some(module) = absolute(root, at, &u.path, depth - 1)?
            && let Some(found) = lookup_local(root, &module, name, depth - 1)?
        {
            return Ok(Some(found));
        }
    }
    Ok(None)
}

/// Resolves a path of the module `at` to the full path in the crate. `None` means that the path
/// leaves the crate.
fn absolute(
    root: &Module,
    at: &[String],
    path: &[String],
    depth: usize,
) -> Result<Option<Vec<String>>> {
    let Some((first, rest)) = path.split_first() else {
        return Ok(Some(at.to_vec()));
    };
    let mut base = match first.as_str() {
        "crate" => Vec::new(),
        "self" => at.to_vec(),
        "super" => match at.split_last() {
            Some((_, parent)) => parent.to_vec(),
            None => bail!("`super` above the root of the crate"),
        },
        name => match lookup_local(root, at, name, depth)? {
            Some(found) => found,
            None => return Ok(None),
        },
    };
    base.extend(rest.iter().cloned());
    Ok(Some(base))
}

/// The full path of the item that the type path `ty`, written in the module `at`, names. `None`
/// means a type of another crate.
fn resolve_type(root: &Module, at: &[String], ty: &[String]) -> Result<Option<Vec<String>>> {
    let Some(mut full) = absolute(root, at, ty, MAX_HOPS)? else {
        return Ok(None);
    };
    for _ in 0..MAX_HOPS {
        let Some((name, module)) = full.split_last() else {
            break;
        };
        if find(root, module)?.decls.contains_key(name) {
            return Ok(Some(full));
        }
        match lookup_local(root, module, name, MAX_HOPS)? {
            Some(next) if next != full => full = next,
            _ => break,
        }
    }
    bail!("the scan cannot resolve the type `{}`", ty.join("::"))
}

fn methods_of(root: &Module, col: &Collected) -> Result<Methods> {
    let mut methods = Methods::new();
    for imp in &col.impls {
        if let Some(full) = resolve_type(root, &imp.at, &imp.ty)? {
            methods
                .entry(full.join("::"))
                .or_default()
                .extend(imp.methods.iter().cloned());
        }
    }
    Ok(methods)
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

    /// Lists the item `orig` of the module `home` as `name` in the module `at`, with its methods,
    /// and with the methods of the target of a type alias.
    fn item(&mut self, at: &[String], name: &str, home: &[String], orig: &str) -> Result<()> {
        let decl = find(self.root, home)?
            .decls
            .get(orig)
            .with_context(|| format!("no item `{orig}` in `{}`", home.join("::")))?
            .clone();
        self.entry(decl.kind, at, name);
        let mut owner = at.to_vec();
        owner.push(name.to_owned());
        let mut key = home.to_vec();
        key.push(orig.to_owned());
        let mut keys = vec![key.join("::")];
        if let Some(target) = &decl.alias_of
            && let Some(full) = resolve_type(self.root, home, target)?
        {
            keys.push(full.join("::"));
        }
        for key in keys {
            if let Some(ms) = self.methods.get(&key) {
                for m in ms {
                    self.entry("method", &owner, m);
                }
            }
        }
        Ok(())
    }

    /// Lists the public contents of the module at `source` as if it sat at `alias`.
    fn export_module(&mut self, source: &[String], alias: &[String], hops: usize) -> Result<()> {
        let module = find(self.root, source)?;
        let decls: Vec<(String, bool)> = module
            .decls
            .iter()
            .map(|(n, d)| (n.clone(), d.public))
            .collect();
        let children: Vec<(String, bool)> = module
            .children
            .iter()
            .map(|(n, m)| (n.clone(), m.public))
            .collect();
        let uses = module.uses.clone();
        for (name, public) in decls {
            if public {
                self.item(alias, &name, source, &name)?;
            }
        }
        for (name, public) in children {
            if public {
                self.entry("mod", alias, &name);
                let (mut s, mut a) = (source.to_vec(), alias.to_vec());
                s.push(name.clone());
                a.push(name);
                self.export_module(&s, &a, hops)?;
            }
        }
        self.reexports(source, alias, &uses, hops)
    }

    /// Lists the targets of the public `use` declarations `uses` of the module `source`.
    fn reexports(
        &mut self,
        source: &[String],
        alias: &[String],
        uses: &[Use],
        hops: usize,
    ) -> Result<()> {
        for u in uses.iter().filter(|u| u.public) {
            let mut full = u.path.clone();
            if u.name != "*" {
                full.push(u.name.clone());
            }
            let Some(abs) = absolute(self.root, source, &full, MAX_HOPS)? else {
                if u.name == "*" {
                    bail!(
                        "unsupported re-export: a glob of `{}`, which is not in this crate",
                        u.path.join("::")
                    );
                }
                let from = u.path.join("::");
                self.entry(&format!("use {from}::{} as", u.name), alias, &u.alias);
                continue;
            };
            if hops == 0 {
                bail!(
                    "unsupported re-export: the chain of `{}` in `{}` is too long",
                    full.join("::"),
                    source.join("::")
                );
            }
            if u.name == "*" {
                self.export_module(&abs, alias, hops - 1)?;
            } else if let Some((name, target)) = abs.split_last() {
                self.export_name(target, name, alias, &u.alias, hops - 1)?;
            }
        }
        Ok(())
    }

    /// Lists the name `name` of the module `target` as `as_name` in the module `alias`.
    fn export_name(
        &mut self,
        target: &[String],
        name: &str,
        alias: &[String],
        as_name: &str,
        hops: usize,
    ) -> Result<()> {
        let module = find(self.root, target)?;
        if module.decls.contains_key(name) {
            return self.item(alias, as_name, target, name);
        }
        if module.children.contains_key(name) {
            let mut s = target.to_vec();
            s.push(name.to_owned());
            let mut a = alias.to_vec();
            a.push(as_name.to_owned());
            self.entry("mod", alias, as_name);
            return self.export_module(&s, &a, hops);
        }
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
        // A glob that lacks the name fails; the export is right when one candidate resolves.
        let mut resolved = false;
        for candidate in chained {
            let saved = self.out.clone();
            if self.reexports(target, alias, &[candidate], hops).is_ok() {
                resolved = true;
            } else {
                self.out = saved;
            }
        }
        if !resolved {
            bail!(
                "unsupported re-export: the scan cannot resolve `{name}` in `{}`",
                target.join("::")
            );
        }
        Ok(())
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
    let mut col = Collected::default();
    let root = read_module(&parsed.items, &dir, &[], load, &mut col)?;
    let methods = methods_of(&root, &col)?;
    let mut scan = Scan {
        root: &root,
        methods: &methods,
        crate_name,
        out: BTreeSet::new(),
    };
    scan.export_module(&[], &[], MAX_HOPS)?;
    for name in &col.macros {
        scan.entry("macro", &[], name);
    }
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

    fn scan_err(files: &[(&str, &str)]) -> String {
        let load = |p: &Path| {
            Ok(files
                .iter()
                .find(|(n, _)| Path::new(n) == p)
                .map(|(_, t)| (*t).to_owned()))
        };
        format!(
            "{:#}",
            scan_crate("c", Path::new("src/lib.rs"), &load).unwrap_err()
        )
    }

    #[test]
    fn exported_macro_sits_at_the_crate_root() {
        let lines = scan(&[
            ("src/lib.rs", "mod inner;\n"),
            (
                "src/inner.rs",
                "#[macro_export]\nmacro_rules! m { () => {} }\nmacro_rules! hidden { () => {} }\n",
            ),
        ]);
        assert_eq!(lines, ["macro c::m"]);
    }

    #[test]
    fn methods_belong_to_the_type_of_their_module() {
        let lines = scan(&[
            ("src/lib.rs", "pub mod a;\npub mod b;\n"),
            (
                "src/a.rs",
                "pub struct T; impl T { pub fn only_a(&self) {} }\n",
            ),
            (
                "src/b.rs",
                "pub struct T; impl T { pub fn only_b(&self) {} }\n",
            ),
        ]);
        assert!(lines.contains(&"method c::a::T::only_a".to_owned()));
        assert!(!lines.contains(&"method c::a::T::only_b".to_owned()));
        assert!(lines.contains(&"method c::b::T::only_b".to_owned()));
    }

    #[test]
    fn reexport_through_a_module_alias_resolves() {
        let lines = scan(&[
            (
                "src/lib.rs",
                "mod hidden;\nuse hidden::inner as exposed;\npub use exposed::*;\n",
            ),
            ("src/hidden.rs", "pub mod inner;\n"),
            ("src/hidden/inner.rs", "pub fn f() {}\n"),
        ]);
        assert_eq!(lines, ["fn c::f"]);
    }

    #[test]
    fn unresolved_reexport_fails() {
        let text = scan_err(&[
            ("src/lib.rs", "mod inner;\npub use inner::Missing;\n"),
            ("src/inner.rs", "pub fn f() {}\n"),
        ]);
        assert!(text.contains("unsupported re-export"), "{text}");
    }

    #[test]
    fn type_alias_lists_the_methods_of_a_private_target() {
        let lines = scan(&[
            (
                "src/lib.rs",
                "mod inner;\npub type Shown = inner::Hidden;\n",
            ),
            (
                "src/inner.rs",
                "pub struct Hidden; impl Hidden { pub fn m(&self) {} }\n",
            ),
        ]);
        assert_eq!(lines, ["method c::Shown::m", "type c::Shown"]);
    }

    #[test]
    fn same_name_under_different_cfg_fails() {
        let text = scan_err(&[(
            "src/lib.rs",
            "#[cfg(feature = \"a\")]\npub fn f() {}\n#[cfg(not(feature = \"a\"))]\npub fn f() {}\n",
        )]);
        assert!(text.contains("two items named `f`"), "{text}");
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
