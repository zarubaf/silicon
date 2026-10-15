// SPDX-License-Identifier: Apache-2.0
//! The Rust subset of the elaborator core (front-end spec, section 4.5). The check parses each
//! module of `crates/elab` that `lib.rs` reaches and looks for the constructs that Aeneas cannot
//! translate. It skips each item whose attribute is exactly `#[cfg(test)]`.
//!
//! The check works on the syntax tree, so it sees a banned type by its name and not by its use.
//! It cannot see a closure that captures a mutable value without the word `FnMut`, and it does
//! not follow an external crate.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use proc_macro2::{TokenStream, TokenTree};
use syn::visit::{self, Visit};
use syn::{Attribute, Meta, StaticMutability};

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

const ROOT_FILE: &str = "crates/elab/src/lib.rs";

/// A banned construct that the code may still use: the file, the construct, and the reason.
/// An entry needs an issue that removes it.
const ALLOWED: &[(&str, &str, &str)] = &[];

/// The names of the banned types, traits, and macros. A name that starts with `Atomic` is banned
/// too.
const BANNED_NAMES: &[&str] = &[
    "Cell",
    "RefCell",
    "OnceCell",
    "LazyCell",
    "UnsafeCell",
    "Rc",
    "Arc",
    "Weak",
    "Mutex",
    "RwLock",
    "OnceLock",
    "LazyLock",
    "FnMut",
    "HashMap",
    "HashSet",
];

fn is_banned_name(name: &str) -> bool {
    BANNED_NAMES.contains(&name) || name.starts_with("Atomic")
}

/// What the scan of one file found.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Found {
    /// The line and the banned construct of each use in production code.
    pub constructs: Vec<(usize, String)>,
    /// The modules that the file declares in files, outermost inline module first.
    pub modules: Vec<Vec<String>>,
}

/// True for `#[cfg(test)]`, and for no other attribute.
fn is_cfg_test(attr: &Attribute) -> bool {
    match &attr.meta {
        Meta::List(list) => list.path.is_ident("cfg") && list.tokens.to_string() == "test",
        _ => false,
    }
}

fn test_only(attrs: &[Attribute]) -> bool {
    attrs.iter().any(is_cfg_test)
}

struct Scan {
    found: Found,
    inline: Vec<String>,
}

impl Scan {
    fn hit(&mut self, line: usize, construct: &str) {
        self.found.constructs.push((line, construct.to_owned()));
    }

    /// The banned constructs in the tokens of a macro call, which the parser does not read.
    fn tokens(&mut self, stream: TokenStream) {
        let mut flat = Vec::new();
        flatten(stream, &mut flat);
        for (i, tree) in flat.iter().enumerate() {
            let Flat::Ident(name, line) = tree else {
                continue;
            };
            let after = |n: usize| flat.get(i + n);
            if is_banned_name(name) || name == "dyn" || name == "unsafe" || name == "thread_local" {
                self.hit(*line, name);
            } else if name == "static" && matches!(after(1), Some(Flat::Ident(m, _)) if m == "mut")
            {
                self.hit(*line, "static mut");
            } else if (name == "std" || name == "core")
                && matches!(after(1), Some(Flat::Colon))
                && matches!(after(2), Some(Flat::Colon))
                && matches!(after(3), Some(Flat::Ident(t, _)) if t == "thread")
            {
                self.hit(*line, "std::thread");
            }
        }
    }

    /// The banned constructs in the tree of a `use`, where `prefix` is the path before it.
    fn use_tree(&mut self, tree: &syn::UseTree, prefix: &mut Vec<String>) {
        match tree {
            syn::UseTree::Path(p) => {
                self.use_name(&p.ident, prefix);
                prefix.push(p.ident.to_string());
                self.use_tree(&p.tree, prefix);
                prefix.pop();
            }
            syn::UseTree::Name(n) => self.use_name(&n.ident, prefix),
            syn::UseTree::Rename(r) => self.use_name(&r.ident, prefix),
            syn::UseTree::Group(g) => {
                for t in &g.items {
                    self.use_tree(t, prefix);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }

    fn use_name(&mut self, ident: &syn::Ident, prefix: &[String]) {
        let name = ident.to_string();
        let line = ident.span().start().line;
        if is_banned_name(&name) {
            self.hit(line, &name);
        } else if name == "thread" && prefix.last().is_some_and(|p| p == "std" || p == "core") {
            self.hit(line, "std::thread");
        }
    }
}

/// A token of a macro call without its groups.
enum Flat {
    Ident(String, usize),
    Colon,
    Other,
}

fn flatten(stream: TokenStream, out: &mut Vec<Flat>) {
    for tree in stream {
        match tree {
            TokenTree::Group(g) => flatten(g.stream(), out),
            TokenTree::Ident(i) => out.push(Flat::Ident(i.to_string(), i.span().start().line)),
            TokenTree::Punct(p) if p.as_char() == ':' => out.push(Flat::Colon),
            _ => out.push(Flat::Other),
        }
    }
}

/// Overrides of `visit_*` that skip the nodes with `#[cfg(test)]`.
macro_rules! gated {
    ($($method:ident($ty:ty) => $walk:path),* $(,)?) => {
        $(fn $method(&mut self, node: &'ast $ty) {
            if !test_only(&node.attrs) {
                $walk(self, node);
            }
        })*
    };
}

impl<'ast> Visit<'ast> for Scan {
    gated! {
        visit_item_fn(syn::ItemFn) => visit::visit_item_fn,
        visit_item_struct(syn::ItemStruct) => visit::visit_item_struct,
        visit_item_enum(syn::ItemEnum) => visit::visit_item_enum,
        visit_item_union(syn::ItemUnion) => visit::visit_item_union,
        visit_item_impl(syn::ItemImpl) => visit::visit_item_impl,
        visit_item_trait(syn::ItemTrait) => visit::visit_item_trait,
        visit_item_const(syn::ItemConst) => visit::visit_item_const,
        visit_item_type(syn::ItemType) => visit::visit_item_type,
        visit_item_macro(syn::ItemMacro) => visit::visit_item_macro,
        visit_item_foreign_mod(syn::ItemForeignMod) => visit::visit_item_foreign_mod,
        visit_impl_item_fn(syn::ImplItemFn) => visit::visit_impl_item_fn,
        visit_impl_item_const(syn::ImplItemConst) => visit::visit_impl_item_const,
        visit_impl_item_type(syn::ImplItemType) => visit::visit_impl_item_type,
        visit_trait_item_fn(syn::TraitItemFn) => visit::visit_trait_item_fn,
        visit_trait_item_const(syn::TraitItemConst) => visit::visit_trait_item_const,
        visit_trait_item_type(syn::TraitItemType) => visit::visit_trait_item_type,
        visit_field(syn::Field) => visit::visit_field,
        visit_variant(syn::Variant) => visit::visit_variant,
        visit_arm(syn::Arm) => visit::visit_arm,
        visit_field_value(syn::FieldValue) => visit::visit_field_value,
        visit_local(syn::Local) => visit::visit_local,
        visit_expr_block(syn::ExprBlock) => visit::visit_expr_block,
        visit_expr_call(syn::ExprCall) => visit::visit_expr_call,
        visit_expr_method_call(syn::ExprMethodCall) => visit::visit_expr_method_call,
        visit_expr_macro(syn::ExprMacro) => visit::visit_expr_macro,
        visit_expr_assign(syn::ExprAssign) => visit::visit_expr_assign,
        visit_expr_if(syn::ExprIf) => visit::visit_expr_if,
        visit_expr_match(syn::ExprMatch) => visit::visit_expr_match,
        visit_expr_for_loop(syn::ExprForLoop) => visit::visit_expr_for_loop,
    }

    fn visit_attribute(&mut self, _: &'ast Attribute) {}

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        if test_only(&node.attrs) {
            return;
        }
        let name = node.ident.to_string();
        if let Some((_, items)) = &node.content {
            self.inline.push(name);
            for item in items {
                self.visit_item(item);
            }
            self.inline.pop();
        } else {
            let mut path = self.inline.clone();
            path.push(name);
            self.found.modules.push(path);
        }
    }

    fn visit_item_use(&mut self, node: &'ast syn::ItemUse) {
        if !test_only(&node.attrs) {
            self.use_tree(&node.tree, &mut Vec::new());
        }
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        let names: Vec<&syn::Ident> = path.segments.iter().map(|s| &s.ident).collect();
        for pair in names.windows(2) {
            if (pair[0] == "std" || pair[0] == "core") && pair[1] == "thread" {
                self.hit(pair[1].span().start().line, "std::thread");
            }
        }
        for segment in &path.segments {
            let name = segment.ident.to_string();
            if is_banned_name(&name) {
                self.hit(segment.ident.span().start().line, &name);
            }
        }
        visit::visit_path(self, path);
    }

    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        if node.path.is_ident("thread_local") {
            self.hit(
                node.path.segments[0].ident.span().start().line,
                "thread_local!",
            );
        } else {
            self.visit_path(&node.path);
            self.tokens(node.tokens.clone());
        }
    }

    fn visit_type_trait_object(&mut self, node: &'ast syn::TypeTraitObject) {
        if let Some(dyn_token) = &node.dyn_token {
            self.hit(dyn_token.span.start().line, "dyn");
        }
        visit::visit_type_trait_object(self, node);
    }

    fn visit_expr_unsafe(&mut self, node: &'ast syn::ExprUnsafe) {
        self.hit(node.unsafe_token.span.start().line, "unsafe");
        visit::visit_expr_unsafe(self, node);
    }

    fn visit_signature(&mut self, node: &'ast syn::Signature) {
        if let Some(token) = &node.unsafety {
            self.hit(token.span.start().line, "unsafe");
        }
        visit::visit_signature(self, node);
    }

    fn visit_item_static(&mut self, node: &'ast syn::ItemStatic) {
        if test_only(&node.attrs) {
            return;
        }
        if let StaticMutability::Mut(token) = &node.mutability {
            self.hit(token.span.start().line, "static mut");
        }
        visit::visit_item_static(self, node);
    }
}

/// The banned constructs and the file modules of the Rust source `text`.
pub fn scan_source(text: &str) -> Result<Found> {
    let file = syn::parse_file(text).context("parsing Rust source")?;
    let mut scan = Scan {
        found: Found::default(),
        inline: Vec::new(),
    };
    if !test_only(&file.attrs) {
        scan.visit_file(&file);
    }
    Ok(scan.found)
}

/// The directory that holds the files of the modules that `file` declares.
fn module_dir(file: &Path) -> PathBuf {
    let dir = file.parent().unwrap_or(Path::new(""));
    match file.file_stem().and_then(|s| s.to_str()) {
        Some("lib" | "main" | "mod") | None => dir.to_path_buf(),
        Some(stem) => dir.join(stem),
    }
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    let tracked = |p: &Path| repo.files.iter().any(|f| f.path == p && !f.is_symlink);
    let mut work = vec![PathBuf::from(ROOT_FILE)];
    while let Some(file) = work.pop() {
        let name = file.to_string_lossy().into_owned();
        let found = scan_source(&repo.read(&file)?)
            .with_context(|| format!("scanning {}", file.display()))?;
        for (line, construct) in found.constructs {
            if ALLOWED
                .iter()
                .any(|(path, token, _)| *path == name && *token == construct)
            {
                continue;
            }
            out.push(Violation {
                path: file.clone(),
                line: Some(line),
                rule: "elab-subset",
                severity: Severity::Error,
                message: format!(
                    "`{construct}` is outside the Rust subset of the elaborator core \
                     (front-end spec, section 4.5); pass state as a parameter and use owned data"
                ),
            });
        }
        let dir = module_dir(&file);
        for module in found.modules.into_iter().rev() {
            let Some((last, inline)) = module.split_last() else {
                continue;
            };
            let base = inline.iter().fold(dir.clone(), |d, m| d.join(m));
            let flat = base.join(format!("{last}.rs"));
            let nested = base.join(last).join("mod.rs");
            if let Some(child) = [flat, nested].into_iter().find(|p| tracked(p)) {
                work.push(child);
            } else {
                out.push(Violation {
                    path: file.clone(),
                    line: None,
                    rule: "elab-subset",
                    severity: Severity::Error,
                    message: format!("the file of the module `{last}` is not in the repository"),
                });
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo::TrackedFile;

    fn found(text: &str) -> Vec<(usize, String)> {
        scan_source(text).unwrap().constructs
    }

    fn names(text: &str) -> Vec<String> {
        found(text).into_iter().map(|(_, c)| c).collect()
    }

    #[test]
    fn finds_each_banned_construct() {
        for construct in [
            "Cell",
            "RefCell",
            "OnceCell",
            "LazyCell",
            "UnsafeCell",
            "Rc",
            "Arc",
            "Weak",
            "Mutex",
            "RwLock",
            "OnceLock",
            "LazyLock",
            "FnMut",
            "HashMap",
            "HashSet",
            "AtomicU64",
            "AtomicBool",
        ] {
            let text = format!("fn f(x: &{construct}<u8>) {{}}\n");
            assert_eq!(found(&text), [(1, construct.to_owned())], "{construct}");
        }
        assert_eq!(found("fn f(x: &dyn T) {}\n"), [(1, "dyn".to_owned())]);
        assert_eq!(names("fn f() { unsafe { g() } }\n"), ["unsafe"],);
        assert_eq!(names("unsafe fn f() {}\n"), ["unsafe"]);
        assert_eq!(names("static mut N: u8 = 0;\n"), ["static mut"]);
        assert_eq!(
            names("thread_local! { static N: u8 = 0; }\n"),
            ["thread_local!"]
        );
        assert_eq!(
            names("fn f() { std::thread::spawn(g); }\n"),
            ["std::thread"]
        );
    }

    #[test]
    fn finds_each_use_form() {
        assert_eq!(names("use std::thread;\n"), ["std::thread"]);
        assert_eq!(names("use std::{thread, mem};\n"), ["std::thread"]);
        assert_eq!(names("use std::sync::atomic::AtomicU64;\n"), ["AtomicU64"]);
        assert_eq!(
            names("use std::cell::{Cell, RefCell as R};\n"),
            ["Cell", "RefCell"]
        );
        assert!(names("use std::mem;\nuse a::thread;\n").is_empty());
    }

    #[test]
    fn a_banned_name_in_a_macro_call_is_found() {
        assert_eq!(names("fn f() { let v = vec![Rc::new(1)]; }\n"), ["Rc"]);
        assert_eq!(
            names("fn f() { m!(std :: thread :: spawn); }\n"),
            ["std::thread"]
        );
        assert_eq!(names("fn f() { m!(static mut X); }\n"), ["static mut"]);
    }

    #[test]
    fn spacing_does_not_hide_a_construct() {
        assert_eq!(
            names("fn f() { std :: thread :: spawn(g); }\n"),
            ["std::thread"]
        );
        assert_eq!(
            names("thread_local ! { static N: u8 = 0; }\n"),
            ["thread_local!"]
        );
        assert_eq!(names("static\nmut N: u8 = 0;\n"), ["static mut"]);
        assert_eq!(names("use std :: thread ;\n"), ["std::thread"]);
    }

    #[test]
    fn a_longer_name_is_not_a_construct() {
        assert!(names("fn f(a: OnceCellar, b: Weakness, c: Arcs) {}\nstruct Cell;\n").is_empty());
        assert!(names("fn f() { let unsafe_code = 1; }\n").is_empty());
    }

    #[test]
    fn a_comment_and_a_string_are_not_code() {
        let text = "// a Cell\n/// an Arc<str>\n/* a Mutex\n   dyn */\n\
                    fn f() { let m = \"a Mutex and dyn\"; let r = r#\"Cell \" HashMap\"#; }\n\
                    #[doc = \"Rc\"]\nfn g() {}\n";
        assert!(names(text).is_empty());
    }

    #[test]
    fn a_test_item_is_skipped() {
        let text = "#[cfg(test)]\nmod tests {\n    use std::cell::Cell;\n    fn f() { let c = Cell::new(0); }\n}\nfn g(x: Rc<u8>) {}\n";
        assert_eq!(found(text), [(6, "Rc".to_owned())]);
    }

    #[test]
    fn an_item_after_a_one_line_test_item_is_scanned() {
        let text = "#[cfg(test)] fn t(c: Cell<u8>) {}\nfn g(x: Rc<u8>) {}\n#[cfg(test)] const C: Mutex<u8> = M;\nfn h(x: Arc<u8>) {}\n";
        assert_eq!(names(text), ["Rc", "Arc"]);
    }

    #[test]
    fn a_split_test_attribute_is_skipped() {
        let text = "#[cfg(\n    test\n)]\nfn t(c: Cell<u8>) {}\n#[ cfg ( test ) ]\nstruct S { x: Rc<u8> }\n";
        assert!(names(text).is_empty());
    }

    #[test]
    fn only_the_exact_test_attribute_skips() {
        assert_eq!(names("#[cfg(not(test))]\nfn f(c: Cell<u8>) {}\n"), ["Cell"]);
        assert_eq!(
            names("#[cfg(any(test, debug_assertions))]\nfn f(c: Cell<u8>) {}\n"),
            ["Cell"]
        );
        assert_eq!(
            names("#[cfg(all(test, unix))]\nfn f(c: Cell<u8>) {}\n"),
            ["Cell"]
        );
        assert_eq!(
            names("#[cfg_attr(test, derive(Debug))]\nfn f(c: Cell<u8>) {}\n"),
            ["Cell"]
        );
    }

    #[test]
    fn a_test_field_statement_and_block_are_skipped() {
        let text = "struct S {\n    #[cfg(test)]\n    steps: Cell<u64>,\n    x: Rc<u8>,\n}\n\
                    fn f() {\n    #[cfg(test)]\n    let c: Cell<u8> = g();\n    #[cfg(test)]\n    {\n        let d: Cell<u8>;\n    }\n    #[cfg(test)]\n    crate::counters::add(Cell::new(1));\n    let e: Arc<u8>;\n}\n";
        assert_eq!(found(text), [(4, "Rc".to_owned()), (15, "Arc".to_owned())]);
    }

    #[test]
    fn an_inner_test_attribute_skips_the_file() {
        assert!(names("#![cfg(test)]\nfn f(c: Cell<u8>) {}\n").is_empty());
    }

    #[test]
    fn a_file_module_is_reported_unless_it_is_test_only() {
        let text = "mod a;\n#[cfg(test)]\nmod tests_a;\nmod b {\n    mod c;\n}\n";
        let modules = scan_source(text).unwrap().modules;
        assert_eq!(
            modules,
            [vec!["a".to_owned()], vec!["b".to_owned(), "c".to_owned()]]
        );
    }

    #[test]
    fn check_follows_the_modules_of_the_root() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        let files = [
            (
                "crates/elab/src/lib.rs",
                "mod eval;\nmod tests_prod;\n#[cfg(test)]\nmod tests;\n",
            ),
            (
                "crates/elab/src/eval.rs",
                "mod inst;\nfn f(c: Cell<u8>) {}\n",
            ),
            ("crates/elab/src/eval/inst.rs", "fn f(c: Rc<u8>) {}\n"),
            ("crates/elab/src/tests_prod.rs", "fn f(c: Arc<u8>) {}\n"),
            ("crates/elab/src/tests.rs", "fn f(c: Mutex<u8>) {}\n"),
            ("crates/elab/src/orphan.rs", "fn f(c: RwLock<u8>) {}\n"),
        ];
        for (name, text) in files {
            let path = root.join(name);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        }
        let tracked = |p: &str| TrackedFile {
            path: p.into(),
            is_symlink: false,
            is_executable: false,
        };
        let repo = Repo::from_parts(root.to_path_buf(), files.map(|(p, _)| tracked(p)).to_vec());
        let mut got: Vec<String> = check(&repo)
            .unwrap()
            .iter()
            .map(|v| format!("{}:{:?}:{}", v.path.display(), v.line, v.rule))
            .collect();
        got.sort();
        assert_eq!(
            got,
            [
                "crates/elab/src/eval.rs:Some(2):elab-subset",
                "crates/elab/src/eval/inst.rs:Some(1):elab-subset",
                "crates/elab/src/tests_prod.rs:Some(1):elab-subset",
            ]
        );
    }

    #[test]
    fn check_reports_a_module_without_a_file() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        let path = root.join("crates/elab/src/lib.rs");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, "mod gone;\n").unwrap();
        let repo = Repo::from_parts(
            root.to_path_buf(),
            vec![TrackedFile {
                path: "crates/elab/src/lib.rs".into(),
                is_symlink: false,
                is_executable: false,
            }],
        );
        let got = check(&repo).unwrap();
        assert_eq!(got.len(), 1);
        assert!(got[0].message.contains("gone"));
    }
}
