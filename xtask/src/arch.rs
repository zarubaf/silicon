// SPDX-License-Identifier: Apache-2.0
//! Architecture rules: invariants that span the spec, Lean, Rust, and the trust document.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::Path;

use anyhow::{Context, Result, bail};
use cargo_metadata::MetadataCommand;
use regex::Regex;

use crate::lean::strip_comments_and_strings;
use crate::paths;
use crate::repo::Repo;
use crate::violation::{Severity, Violation};
use crate::workspace::EXEMPT;

const TRUST: &str = "doc/trust.md";
const LAKEFILE: &str = "lean/lakefile.toml";
const EXE: &str = "silicon-check";

fn error(path: &str, line: Option<usize>, rule: &'static str, message: String) -> Violation {
    Violation {
        path: Path::new(path).to_path_buf(),
        line,
        rule,
        severity: Severity::Error,
        message,
    }
}

/// Each error code with the 1-based line of its first mention.
type Codes = BTreeMap<String, usize>;

/// Every error code with the prefix `letter` that `lines` name, for example `E001`.
/// `first_line` numbers the first line.
fn codes_in<'a>(
    lines: impl Iterator<Item = &'a str>,
    first_line: usize,
    letter: char,
) -> Result<Codes> {
    let code = Regex::new(&format!(r"\b{letter}\d{{3}}\b"))?;
    let mut out = Codes::new();
    for (offset, line) in lines.enumerate() {
        for m in code.find_iter(line) {
            out.entry(m.as_str().to_owned())
                .or_insert(first_line + offset);
        }
    }
    Ok(out)
}

/// The 1-based line and text of the first item that matches `header`, up to the first `end`.
fn block<'a>(src: &'a str, header: &str, end: &str, what: &str) -> Result<(usize, &'a str)> {
    let start = Regex::new(header)?
        .find(src)
        .with_context(|| format!("no `{header}` in {what}"))?
        .start();
    let rest = &src[start..];
    let len = rest
        .find(end)
        .with_context(|| format!("no `{end}` after `{header}` in {what}"))?;
    let line = src[..start].matches('\n').count() + 1;
    Ok((line, &rest[..len]))
}

/// The error codes of the Lean `ErrorCode` inductive type in `src`, the text of `path`.
pub fn lean_codes(src: &str, path: &str, letter: char) -> Result<Codes> {
    let stripped = strip_comments_and_strings(src);
    let (line, body) = block(&stripped, r"\binductive\s+ErrorCode\b", "deriving", path)?;
    nonempty(codes_in(body.lines(), line, letter)?, path)
}

/// Blanks Rust comments and string and char literals, keeping every line break.
///
/// A hand-written scan avoids a `syn` dependency for one enum. It handles `//` and doc
/// comments, nested `/* */`, escaped strings, raw strings, and char literals against lifetimes.
fn strip_rust(src: &str) -> String {
    let chars: Vec<char> = src.chars().collect();
    let mut out = String::with_capacity(src.len());
    let blank = |c: char| if c == '\n' { '\n' } else { ' ' };
    let mut i = 0;
    while i < chars.len() {
        let rest = &chars[i..];
        let len = match rest {
            ['/', '/', ..] => rest.iter().take_while(|c| **c != '\n').count(),
            ['/', '*', ..] => block_comment_len(rest),
            ['r', '"' | '#', ..] if !prev_is_ident(&chars, i) => raw_string_len(rest),
            ['"', ..] => quoted_len(rest, '"'),
            ['\'', ..] => char_literal_len(rest),
            _ => 0,
        };
        if len == 0 {
            out.push(chars[i]);
            i += 1;
        } else {
            out.extend(rest[..len].iter().map(|c| blank(*c)));
            i += len;
        }
    }
    out
}

fn prev_is_ident(chars: &[char], i: usize) -> bool {
    i > 0 && (chars[i - 1].is_alphanumeric() || chars[i - 1] == '_')
}

/// Length of a possibly nested block comment at the start of `rest`; the rest if unclosed.
fn block_comment_len(rest: &[char]) -> usize {
    let mut depth = 0_usize;
    let mut i = 0;
    while i < rest.len() {
        match rest[i..] {
            ['/', '*', ..] => {
                depth += 1;
                i += 2;
            }
            ['*', '/', ..] => {
                depth -= 1;
                i += 2;
                if depth == 0 {
                    return i;
                }
            }
            _ => i += 1,
        }
    }
    rest.len()
}

/// Length of a literal that `rest` opens with `quote`, with `\` escapes; the rest if unclosed.
fn quoted_len(rest: &[char], quote: char) -> usize {
    let mut i = 1;
    while i < rest.len() {
        match rest[i] {
            '\\' => i += 2,
            c if c == quote => return i + 1,
            _ => i += 1,
        }
    }
    rest.len()
}

/// Length of a raw string such as `r#"..."#`, or 0 when `rest` is an identifier that starts with `r`.
fn raw_string_len(rest: &[char]) -> usize {
    let hashes = rest[1..].iter().take_while(|c| **c == '#').count();
    if rest.get(1 + hashes) != Some(&'"') {
        return 0;
    }
    let close: Vec<char> = std::iter::once('"')
        .chain(std::iter::repeat_n('#', hashes))
        .collect();
    (2 + hashes..rest.len())
        .find(|&at| rest[at..].starts_with(&close))
        .map_or(rest.len(), |at| at + close.len())
}

/// Length of a char literal such as `'x'` or `'\n'`; 0 for a lifetime.
fn char_literal_len(rest: &[char]) -> usize {
    match rest {
        ['\'', '\\', ..] => quoted_len(rest, '\''),
        ['\'', _, '\'', ..] => 3,
        _ => 0,
    }
}

/// The error codes of the Rust enum `name` in `src`, the text of `path`. Comments and
/// literals do not count.
pub fn rust_codes(src: &str, path: &str, name: &str, letter: char) -> Result<Codes> {
    let stripped = strip_rust(src);
    let header = format!(r"\bpub\s+enum\s+{name}\b");
    let (line, body) = block(&stripped, &header, "\n}", path)?;
    nonempty(codes_in(body.lines(), line, letter)?, path)
}

/// The error codes in the first cell of each row of the table of spec section `number`, which
/// `text` holds as the file `path`.
///
/// This includes `E014`, which only `run` reports. Codes in prose do not count.
pub fn spec_codes(text: &str, path: &str, number: &str, letter: char) -> Result<Codes> {
    let header = format!(r"(?m)^### {} ", regex::escape(number));
    let (line, section) = block(text, &header, "\n### ", path)?;
    let rows = section
        .lines()
        .enumerate()
        .skip_while(|(_, l)| !l.starts_with('|'))
        .take_while(|(_, l)| l.starts_with('|'))
        .skip(2);
    let mut out = Codes::new();
    for (offset, row) in rows {
        let cell = row.trim_start_matches('|').split('|').next().unwrap_or("");
        if let Some(code) = cell
            .trim()
            .strip_prefix('`')
            .and_then(|c| c.strip_suffix('`'))
        {
            out.extend(codes_in(std::iter::once(code), line + offset, letter)?);
        }
    }
    nonempty(out, path)
}

fn nonempty(codes: Codes, what: &str) -> Result<Codes> {
    if codes.is_empty() {
        bail!("{what} defines no error code; the parser needs an update");
    }
    Ok(codes)
}

/// The Lean and Rust sources that define one family of error codes, with the spec section
/// that lists them.
struct Family {
    letter: char,
    spec: &'static str,
    spec_section: &'static str,
    lean: &'static str,
    /// Each Rust file with the name of its enum.
    rust: &'static [(&'static str, &'static str)],
}

const FAMILIES: &[Family] = &[Family {
    letter: 'E',
    spec: "doc/design/2026-10-08-core-ir.md",
    spec_section: "4.2",
    lean: "lean/Silicon/Core/Syntax.lean",
    rust: &[("crates/core-ir/src/diag.rs", "ErrorCode")],
}];

/// The codes one implementation defines, by file.
struct Side {
    name: &'static str,
    files: Vec<(&'static str, Codes)>,
}

/// Rule `arch-codes`: the spec and an implementation define the same set of error codes.
fn codes_violations(spec_path: &str, spec: &Codes, side: &Side) -> Vec<Violation> {
    let mut out = Vec::new();
    let name = side.name;
    let defined = |code: &String| side.files.iter().any(|(_, set)| set.contains_key(code));
    for (code, line) in spec.iter().filter(|(c, _)| !defined(c)) {
        out.push(error(
            spec_path,
            Some(*line),
            "arch-codes",
            format!("`{code}` is in the spec but not in {name}"),
        ));
    }
    for (path, set) in &side.files {
        for (code, line) in set.iter().filter(|(c, _)| !spec.contains_key(*c)) {
            out.push(error(
                path,
                Some(*line),
                "arch-codes",
                format!("`{code}` is in {name} but not in the spec"),
            ));
        }
    }
    out
}

fn family_violations(repo: &Repo, family: &Family) -> Result<Vec<Violation>> {
    let letter = family.letter;
    let spec = spec_codes(
        &repo.read(Path::new(family.spec))?,
        family.spec,
        family.spec_section,
        letter,
    )?;
    let lean = Side {
        name: "Lean",
        files: vec![(
            family.lean,
            lean_codes(&repo.read(Path::new(family.lean))?, family.lean, letter)?,
        )],
    };
    let mut rust = Side {
        name: "Rust",
        files: Vec::new(),
    };
    for (path, name) in family.rust {
        let codes = rust_codes(&repo.read(Path::new(path))?, path, name, letter)?;
        rust.files.push((path, codes));
    }
    let mut out = codes_violations(family.spec, &spec, &lean);
    out.extend(codes_violations(family.spec, &spec, &rust));
    Ok(out)
}

/// The `silicon-check` commands: the first string of each `| ["name", ...] =>` or
/// `| "name" :: rest =>` arm.
///
/// A comment can hold an arm, so the stripped text finds the arm lines and the original
/// text gives the name, because stripping blanks strings.
pub fn commands(main: &str) -> Result<BTreeSet<String>> {
    let arm = Regex::new(r#"^\s*\|\s*(?:\[\s*|)"([a-z][a-z-]*)"\s*(?:,|\]|::)"#)?;
    let live = Regex::new(r"^\s*\|")?;
    let stripped = strip_comments_and_strings(main);
    let found: BTreeSet<String> = main
        .lines()
        .zip(stripped.lines())
        .filter(|(_, code)| live.is_match(code))
        .filter_map(|(line, _)| arm.captures(line).map(|c| c[1].to_owned()))
        .collect();
    if found.is_empty() {
        bail!(
            "the `{EXE}` root has no command arm `| [\"name\", ...] =>` or `| \"name\" :: rest =>`; the parser needs an update"
        );
    }
    Ok(found)
}

/// The names in backticks in the Part column (first cell) of each row of the trust table.
/// The second value is the line of the `## Parts` heading.
///
/// A row covers a crate when its Part cell holds the crate name in backticks, for example
/// `core-ir`. A row covers a command when its Part cell holds `silicon-check <command>`
/// in backticks.
pub fn trust_names(trust: &str) -> Result<(HashSet<String>, usize)> {
    let ticks = Regex::new(r"`([^`]+)`")?;
    let (line, section) = block(trust, r"(?m)^## Parts$", "\n## ", TRUST)?;
    let rows: Vec<&str> = section
        .lines()
        .filter(|l| l.starts_with('|'))
        .skip(2)
        .collect();
    if rows.is_empty() {
        bail!("{TRUST} has no table under `## Parts`");
    }
    let names = rows
        .iter()
        .filter_map(|row| row.trim_start_matches('|').split('|').next())
        .flat_map(|cell| {
            ticks
                .captures_iter(cell)
                .map(|c| c[1].to_owned())
                .collect::<Vec<_>>()
        })
        .collect();
    Ok((names, line))
}

/// Rule `arch-trust`: each workspace crate and each `silicon-check` command has a trust row.
fn trust_violations(
    crates: &[String],
    commands: &BTreeSet<String>,
    (names, line): &(HashSet<String>, usize),
) -> Vec<Violation> {
    let wanted = crates
        .iter()
        .filter(|c| *c != EXEMPT)
        .map(|c| (c.clone(), format!("crate `{c}`")))
        .chain(commands.iter().map(|c| {
            let full = format!("{EXE} {c}");
            (full.clone(), format!("`{full}`"))
        }));
    wanted
        .filter(|(key, _)| !names.contains(key))
        .map(|(_, what)| {
            error(
                TRUST,
                Some(*line),
                "arch-trust",
                format!("no row names {what} in backticks in the Part column"),
            )
        })
        .collect()
}

/// The tags that `doc/trust.md` documents: the issue numbers of the Issue
/// column, and each rule code in the table.
pub fn trust_tags(trust: &str) -> Result<HashSet<String>> {
    let (_, section) = block(trust, r"(?m)^## Parts$", "\n## ", TRUST)?;
    let issue = Regex::new(r"#\d+")?;
    let code = Regex::new(r"\bE\d+\b")?;
    let mut tags = HashSet::new();
    for row in section.lines().filter(|l| l.starts_with('|')).skip(2) {
        let cells: Vec<&str> = row.trim_matches('|').split('|').collect();
        if let Some(last) = cells.last() {
            tags.extend(issue.find_iter(last).map(|m| m.as_str().to_owned()));
        }
        tags.extend(code.find_iter(row).map(|m| m.as_str().to_owned()));
    }
    Ok(tags)
}

/// Rule `arch-skips`: the tag of each SKIP of an inventory names a gap of
/// `doc/trust.md`.
fn skips_violations(path: &str, inventory: &str, tags: &HashSet<String>) -> Result<Vec<Violation>> {
    Ok(crate::skips::parse(inventory)?
        .into_iter()
        .filter_map(|(line, entry)| match entry.verdict {
            crate::skips::Verdict::Skip(tag) if !tags.contains(&tag) => Some(error(
                path,
                Some(line),
                "arch-skips",
                format!("the tag `{tag}` is no gap of {TRUST}"),
            )),
            _ => None,
        })
        .collect())
}

/// The path of a Lean module name, relative to `lean/`.
fn module_path(module: &str) -> String {
    format!("lean/{}.lean", module.replace('.', "/"))
}

/// The modules in the header of `src`. The header is a token stream, so an `import` can span
/// lines. Lean 4.34 allows `public` and `meta` before `import`, and `all` after it. One
/// `import` names one module. The header ends at the first token that no header rule accepts.
///
/// This avoids `lake env lean --deps`: `just check` then needs no Lean toolchain.
fn imports(src: &str) -> Vec<String> {
    let stripped = strip_comments_and_strings(src);
    let mut tokens = stripped.split_whitespace().peekable();
    let mut out = Vec::new();
    while let Some(&token) = tokens.peek() {
        match token {
            "module" | "prelude" | "public" | "meta" => {
                tokens.next();
            }
            "import" => {
                tokens.next();
                while tokens.peek() == Some(&"all") {
                    tokens.next();
                }
                if let Some(module) = tokens.next() {
                    out.push(module.to_owned());
                }
            }
            _ => break,
        }
    }
    out
}

/// Rule `lean-exe-imports`: no module under a `Proof` directory is a transitive import of `root`.
///
/// `read` gives the source of a module, or `None` for a module outside `lean/Silicon`.
pub fn exe_import_violations(
    root: &str,
    read: &dyn Fn(&str) -> Result<Option<String>>,
) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![(root.to_owned(), vec![root.to_owned()])];
    while let Some((module, chain)) = stack.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        if module.split('.').any(|part| part == "Proof") {
            out.push(error(
                &module_path(&module),
                None,
                "lean-exe-imports",
                format!("`{EXE}` imports a proof module: {}", chain.join(" -> ")),
            ));
            continue;
        }
        let Some(src) = read(&module)? else { continue };
        for import in imports(&src) {
            let mut next = chain.clone();
            next.push(import.clone());
            stack.push((import, next));
        }
    }
    Ok(out)
}

/// The root module of the `silicon-check` executable.
pub fn exe_root(lakefile: &str) -> Result<String> {
    let doc: toml::Table = lakefile
        .parse()
        .with_context(|| format!("parsing {LAKEFILE}"))?;
    doc.get("lean_exe")
        .and_then(|v| v.as_array())
        .into_iter()
        .flatten()
        .find(|e| e.get("name").and_then(|n| n.as_str()) == Some(EXE))
        .and_then(|e| e.get("root")?.as_str())
        .map(str::to_owned)
        .with_context(|| format!("{LAKEFILE} has no `lean_exe` `{EXE}` with a `root`"))
}

fn workspace_crates(repo: &Repo) -> Result<Vec<String>> {
    let metadata = MetadataCommand::new()
        .manifest_path(repo.root.join("Cargo.toml"))
        .no_deps()
        .exec()
        .context("reading cargo metadata")?;
    Ok(metadata
        .packages
        .iter()
        .map(|p| p.name.to_string())
        .collect())
}

pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    for family in FAMILIES {
        out.extend(family_violations(repo, family)?);
    }
    let root = exe_root(&repo.read(Path::new(LAKEFILE))?)?;
    out.extend(trust_violations(
        &workspace_crates(repo)?,
        &commands(&repo.read(Path::new(&module_path(&root)))?)?,
        &trust_names(&repo.read(Path::new(TRUST))?)?,
    ));
    let tags = trust_tags(&repo.read(Path::new(TRUST))?)?;
    for path in [paths::lec_inventory(), paths::diff_inventory()] {
        let name = path.to_string_lossy();
        out.extend(skips_violations(&name, &repo.read(&path)?, &tags)?);
    }
    out.extend(exe_import_violations(&root, &|module| {
        let path = module_path(module);
        if repo.root.join(&path).exists() {
            repo.read(Path::new(&path)).map(Some)
        } else if module.starts_with("Silicon") {
            bail!("module `{module}` has no file {path}")
        } else {
            Ok(None)
        }
    })?);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn codes(xs: &[&str]) -> Codes {
        xs.iter().map(|s| ((*s).to_owned(), 1)).collect()
    }

    fn side(name: &'static str, files: Vec<(&'static str, Codes)>) -> Side {
        Side { name, files }
    }

    fn lean_e(src: &str) -> Result<Codes> {
        lean_codes(src, "x.lean", 'E')
    }

    fn rust_e(src: &str) -> Result<Codes> {
        rust_codes(src, "x.rs", "ErrorCode", 'E')
    }

    fn spec_e(text: &str) -> Result<Codes> {
        spec_codes(text, "x.md", "4.2", 'E')
    }

    fn keys(c: &Codes) -> Vec<&str> {
        c.keys().map(String::as_str).collect()
    }

    fn set(xs: &[&str]) -> BTreeSet<String> {
        xs.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn codes_equal_sets_pass() {
        let s = codes(&["E001", "E002"]);
        assert!(codes_violations("s.md", &s, &side("Lean", vec![("l", s.clone())])).is_empty());
    }

    #[test]
    fn codes_differing_sets_fail() {
        let spec = codes(&["E001", "E002"]);
        let mut got = codes_violations("s.md", &spec, &side("Lean", vec![("l", codes(&["E001"]))]));
        got.extend(codes_violations(
            "s.md",
            &spec,
            &side("Rust", vec![("r", codes(&["E001", "E002", "E003"]))]),
        ));
        let rules: Vec<_> = got.iter().map(|v| v.message.as_str()).collect();
        assert_eq!(
            rules,
            [
                "`E002` is in the spec but not in Lean",
                "`E003` is in Rust but not in the spec"
            ]
        );
        assert_eq!(got[0].line, Some(1));
    }

    #[test]
    fn lean_and_rust_codes_parse() {
        let lean = "/-! E099 -/\ninductive ErrorCode where\n  | E001 | E002\n  | E003\n  deriving Repr\n\ndef x := \"E004\"\n";
        let got = lean_e(lean).unwrap();
        assert_eq!(keys(&got), ["E001", "E002", "E003"]);
        assert_eq!(got["E003"], 4);
        let rust = "/// E099\npub enum ErrorCode {\n    E001,\n    E002, // E005\n    // E006\n}\nconst X: &str = \"E004\";\n";
        assert_eq!(keys(&rust_e(rust).unwrap()), ["E001", "E002"]);
    }

    #[test]
    fn commented_or_quoted_codes_are_missing() {
        let rust = "pub enum ErrorCode {\n    E001,\n    /* E002, */\n    /* a /* E003, */ E004, */\n    #[doc = \"E005\"]\n    E006, // E007\n    /** E008 */\n}\n";
        assert_eq!(keys(&rust_e(rust).unwrap()), ["E001", "E006"]);
        let lean = "inductive ErrorCode where\n  | E001\n  /- E014 -/\n  /-- E015 -/\n  | E002 -- E016\n  deriving Repr\n";
        assert_eq!(keys(&lean_e(lean).unwrap()), ["E001", "E002"]);
        let spec = codes(&["E001", "E002", "E014"]);
        for (name, found) in [
            ("Lean", lean_e(lean).unwrap()),
            ("Rust", rust_e(rust).unwrap()),
        ] {
            let got = codes_violations("s.md", &spec, &side(name, vec![("f", found)]));
            let want = format!("`E014` is in the spec but not in {name}");
            assert!(got.iter().any(|v| v.message == want));
        }
    }

    #[test]
    fn rust_stripper_keeps_lifetimes_and_raw_strings_apart() {
        let src = "fn f<'a>(x: &'a str) { let _ = r#\"E009 \" /*\"#; let c = '\"'; } // E010\npub enum ErrorCode {\n    E001,\n}\n";
        assert_eq!(keys(&rust_e(src).unwrap()), ["E001"]);
        assert_eq!(strip_rust(src).lines().count(), src.lines().count());
    }

    #[test]
    fn commented_command_arms_do_not_count() {
        let main = "match args with\n  | [\"check\", f] => a\n  -- | [\"old\", f] => b\n  /- | [\"older\", f] => c -/\n  | _ => d\n";
        assert_eq!(commands(main).unwrap(), set(&["check"]));
    }

    #[test]
    fn commands_parse_list_and_cons_arms() {
        let main = "match args with\n  | [\"check\", file] => a\n  | \"parse\" :: rest => b\n  -- | \"ghost\" :: rest => c\n  | _ => d\n";
        assert_eq!(commands(main).unwrap(), set(&["check", "parse"]));
    }

    #[test]
    fn enum_names_need_a_word_boundary() {
        assert!(lean_e("inductive ErrorCodeKind where\n | E001\n deriving Repr").is_err());
        assert!(rust_e("pub enum ErrorCodes {\n    E001,\n}\n").is_err());
    }

    const SPEC_DOC: &str = "### 4.2 Rules\n\n| Code | Rule |\n| --- | --- |\n| `E001` | Syntax. |\n| `E002` | Names, not `E009`. |\n\nProse names `E014`.\n\n### 4.3 Next\n| `E077` | x |\n";

    #[test]
    fn spec_codes_come_from_the_first_cell_of_the_table() {
        let got = spec_e(SPEC_DOC).unwrap();
        assert_eq!(keys(&got), ["E001", "E002"]);
        assert_eq!(got["E002"], 6);
        let without_row = SPEC_DOC.replace("| `E002` | Names, not `E009`. |\n", "");
        let lean = codes(&["E001", "E002"]);
        let got = spec_e(&without_row).unwrap();
        let both = side("Lean", vec![("l", lean)]);
        assert_eq!(codes_violations("s.md", &got, &both).len(), 1);
    }

    #[test]
    fn unreadable_code_sources_fail_clearly() {
        assert!(lean_e("def x := 1").is_err());
        assert!(lean_e("inductive ErrorCode where\n deriving Repr").is_err());
        assert!(rust_e("pub enum Other {\n}\n").is_err());
        assert!(spec_e("no codes").is_err());
    }

    const TRUST_DOC: &str = "# T\n\n## Parts\n\n| Part | Status |\n| --- | --- |\n| The `core-ir` crate and `silicon-check check` | Proven |\n| Prose with `x` | Trusted |\n\n## Gaps\n\n| `other` |\n";

    #[test]
    fn commands_parse_from_main() {
        let main = "match args with\n  | [\"check\", file] => a\n  | [\"lower\", \"--models\", file] => b\n  | _ => c\n";
        assert_eq!(commands(main).unwrap(), set(&["check", "lower"]));
        assert!(commands("def main := 1").is_err());
    }

    #[test]
    fn trust_row_covers_crate_and_command() {
        let names = trust_names(TRUST_DOC).unwrap();
        assert_eq!(names.1, 3);
        assert!(
            !names.0.contains("other"),
            "rows outside `## Parts` do not count"
        );
        let crates = vec!["core-ir".to_owned(), "xtask".to_owned()];
        assert!(trust_violations(&crates, &set(&["check"]), &names).is_empty());
    }

    const TRUST_TABLE: &str = "## Parts\n\n| Part | Oracle | Issue |\n| --- | --- | --- |\n\
        | A | None. It rejects an extern (`E014`). | #20, #21 |\n| B | #99 in prose | |\n\n## Gaps\n";

    #[test]
    fn trust_tags_are_issue_cells_and_rule_codes() {
        let tags = trust_tags(TRUST_TABLE).unwrap();
        assert_eq!(tags, set(&["#20", "#21", "E014"]).into_iter().collect());
    }

    #[test]
    fn a_skip_tag_outside_the_trust_table_fails() {
        let tags = trust_tags(TRUST_TABLE).unwrap();
        let inventory =
            "a.sil main SKIP #20\na.sil lowering SKIP #22\na.sil run SKIP E014\na.sil x PASS\n";
        let found = skips_violations("inv.txt", inventory, &tags).unwrap();
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].line, Some(2));
        assert_eq!(found[0].rule, "arch-skips");
    }

    #[test]
    fn missing_trust_row_fails() {
        let names = trust_names(TRUST_DOC).unwrap();
        let crates = vec!["core-ir".to_owned(), "driver".to_owned()];
        let got = trust_violations(&crates, &set(&["check", "run"]), &names);
        let messages: Vec<_> = got.iter().map(|v| v.message.as_str()).collect();
        assert_eq!(messages.len(), 2);
        assert_eq!(got[0].line, Some(3));
        assert!(messages[0].contains("`driver`") && messages[1].contains("`silicon-check run`"));
        assert!(trust_names("# no table").is_err());
    }

    fn reader(files: &[(&str, &str)]) -> impl Fn(&str) -> Result<Option<String>> {
        let map: HashMap<String, String> = files
            .iter()
            .map(|(k, v)| ((*k).to_owned(), (*v).to_owned()))
            .collect();
        move |m| Ok(map.get(m).cloned())
    }

    #[test]
    fn exe_without_proof_imports_passes() {
        let read = reader(&[
            ("A.Main", "import A.B\nimport Std\n"),
            ("A.B", "import A.C\n"),
            ("A.C", ""),
        ]);
        assert!(exe_import_violations("A.Main", &read).unwrap().is_empty());
    }

    #[test]
    fn exe_with_transitive_proof_import_fails() {
        let read = reader(&[
            ("A.Main", "import A.B\n"),
            ("A.B", "-- import A.Proof.X\nimport A.Proof.Y\n"),
            ("A.Proof.Y", "import A.B\n"),
        ]);
        let got = exe_import_violations("A.Main", &read).unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].path, Path::new("lean/A/Proof/Y.lean"));
        assert!(got[0].message.contains("A.Main -> A.B -> A.Proof.Y"));
    }

    #[test]
    fn exe_with_a_second_import_or_all_modifier_fails() {
        let read = reader(&[
            ("A.Main", "import A.B\nimport A.Proof.X\n"),
            ("A.B", ""),
            ("A.Proof.X", ""),
        ]);
        assert_eq!(exe_import_violations("A.Main", &read).unwrap().len(), 1);
        let read = reader(&[
            ("A.Main", "import A.B\n"),
            ("A.B", "import all A.Proof.X\n"),
            ("A.Proof.X", ""),
        ]);
        let got = exe_import_violations("A.Main", &read).unwrap();
        assert!(got[0].message.contains("A.Main -> A.B -> A.Proof.X"));
    }

    #[test]
    fn exe_with_multiline_or_modified_proof_import_fails() {
        let proof = [("A.Proof.X", "")];
        for header in [
            "import\n  A.Proof.X\n",
            "module\nimport A.B\npublic meta import\n  all A.Proof.X\n",
            "import A.B\nimport all\nA.Proof.X\n",
        ] {
            let mut files = vec![("A.Main", header), ("A.B", "")];
            files.extend(proof);
            let read = reader(&files);
            assert_eq!(
                exe_import_violations("A.Main", &read).unwrap().len(),
                1,
                "{header}"
            );
        }
        let nested = reader(&[
            ("A.Main", "import A.B\n"),
            ("A.B", "import\n  A.C\n"),
            ("A.C", "import\n  A.Proof.X\n"),
            ("A.Proof.X", ""),
        ]);
        let got = exe_import_violations("A.Main", &nested).unwrap();
        assert!(got[0].message.contains("A.Main -> A.B -> A.C -> A.Proof.X"));
    }

    #[test]
    fn exe_ignores_imports_in_comments_and_after_the_header() {
        let read = reader(&[
            (
                "A.Main",
                "/- import A.Proof.X\n  /- nested -/ import A.Proof.Y -/\nimport A.B\n-- import A.Proof.Z\ndef x := 1\nimport A.Proof.W\n",
            ),
            ("A.B", ""),
        ]);
        assert!(exe_import_violations("A.Main", &read).unwrap().is_empty());
    }

    #[test]
    fn exe_root_reads_lakefile() {
        let lake = "[[lean_exe]]\nname = \"other\"\nroot = \"X\"\n[[lean_exe]]\nname = \"silicon-check\"\nroot = \"S.Main\"\n";
        assert_eq!(exe_root(lake).unwrap(), "S.Main");
        assert!(exe_root("name = \"x\"").is_err());
    }
}
