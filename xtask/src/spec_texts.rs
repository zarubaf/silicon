// SPDX-License-Identifier: Apache-2.0
//! Rule `spec-texts`: each normative message text of the front-end spec names its fix, and both
//! front ends and the `expected-message` files carry it (ADR 0022).
//!
//! A text is a row of a table with the columns `Code`, `Case`, and `Message` in section 6.2. The
//! slice 3 table is the first such table, and a later slice adds rows or tables of the same form.
//! The older bullet texts of slices 1 and 2 are outside this rule.
//!
//! Matching is explicit. A placeholder such as `{T}` becomes `{}` in the spec and in the code. A
//! text is in a front end when it is a substring of the string literals that the code joins with
//! `++` or `\` at the end of a line. A pin is an `expected-message` line that matches the text with
//! each placeholder as a wildcard. A text that the code builds in pieces needs an entry in `ALLOW_FILE`.

use std::path::Path;

use anyhow::{Result, bail};
use regex::Regex;
use testkit::source::MESSAGE_SUITES;
use testkit::{Marker, expected_error};

use crate::repo::Repo;
use crate::violation::{Severity, Violation};

const ALLOW_FILE: &str = "tests/inventory/spec-texts.txt";
const SPEC: &str = "doc/design/2026-10-09-frontend.md";
const SECTION: &str = "### 6.2 ";
const RULE: &str = "spec-texts";
const LEAN_DIR: &str = "lean/Silicon/Source/";
const RUST_DIR: &str = "crates/";
const PIN_DIR: &str = "tests/source/";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Part {
    Fix,
    Lean,
    Rust,
    Pin,
}

impl Part {
    fn name(self) -> &'static str {
        match self {
            Self::Fix => "fix clause",
            Self::Lean => "Lean literal",
            Self::Rust => "Rust literal",
            Self::Pin => "`expected-message` pin",
        }
    }
}

/// A known gap. `row` is the code and the case of a row, as in `S021 Uncovered value`.
struct Gap {
    row: String,
    part: Part,
    issue: u32,
}

/// Reads the known gaps from the inventory, which `ALLOW_FILE` names and documents.
fn parse_allow(text: &str) -> Result<Vec<Gap>> {
    let mut gaps = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let at = i + 1;
        let cells: Vec<&str> = line.split(" | ").map(str::trim).collect();
        let [part, row, issue] = cells[..] else {
            bail!("{ALLOW_FILE}:{at}: write `<part> | <row> | <issue>`");
        };
        let part = match part {
            "fix" => Part::Fix,
            "lean" => Part::Lean,
            "rust" => Part::Rust,
            "pin" => Part::Pin,
            other => bail!("{ALLOW_FILE}:{at}: the part `{other}` is not fix, lean, rust, or pin"),
        };
        let Ok(issue) = issue.parse() else {
            bail!(
                "{ALLOW_FILE}:{at}: `{issue}` is not an issue number; name the issue that closes the gap"
            );
        };
        gaps.push(Gap {
            row: row.to_owned(),
            part,
            issue,
        });
    }
    Ok(gaps)
}

#[derive(Debug, PartialEq, Eq)]
struct Row {
    line: usize,
    code: String,
    case: String,
    text: String,
}

impl Row {
    fn id(&self) -> String {
        format!("{} {}", self.code, self.case)
    }
}

fn cells(line: &str) -> Vec<&str> {
    line.trim()
        .trim_matches('|')
        .split('|')
        .map(str::trim)
        .collect()
}

/// The rows of each `Code | Case | Message` table in section 6.2.
fn spec_rows(spec: &str) -> Result<Vec<Row>> {
    let mut rows = Vec::new();
    let mut in_section = false;
    let mut in_table = false;
    for (i, line) in spec.lines().enumerate() {
        if line.starts_with("### ") || line.starts_with("## ") {
            in_section = line.starts_with(SECTION);
        }
        if !in_section || !line.starts_with('|') {
            in_table = false;
            continue;
        }
        let c = cells(line);
        if c == ["Code", "Case", "Message"] {
            in_table = true;
        } else if in_table && !c[0].starts_with('-') {
            if c.len() != 3 {
                bail!("{SPEC}:{}: a row of a message table has 3 cells", i + 1);
            }
            rows.push(Row {
                line: i + 1,
                code: c[0].trim_matches('`').to_owned(),
                case: c[1].to_owned(),
                text: c[2].to_owned(),
            });
        }
    }
    if rows.is_empty() {
        bail!("{SPEC} has no `Code | Case | Message` table in section 6.2");
    }
    Ok(rows)
}

/// The clause after the last `; `, when the text has one with at least two words.
fn fix(text: &str) -> Option<&str> {
    let (_, fix) = text.rsplit_once("; ")?;
    (fix.split_whitespace().count() >= 2).then_some(fix)
}

/// The text with each placeholder `{x}` as `{}`. `X and Y` in the `S011` texts are two
/// placeholders too.
fn normalize(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(open) = rest.find('{') {
        out.push_str(&rest[..open]);
        let inner = &rest[open + 1..];
        match inner.split_once('}') {
            Some((name, tail))
                if !name.is_empty() && name.chars().all(|c| c.is_ascii_alphabetic()) =>
            {
                out.push_str("{}");
                rest = tail;
            }
            _ => {
                out.push('{');
                rest = inner;
            }
        }
    }
    out.push_str(rest);
    out.replace(": X and Y;", ": {} and {};")
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Lang {
    Rust,
    Lean,
}

struct Scan<'a> {
    c: &'a [char],
    i: usize,
}

impl Scan<'_> {
    fn starts(&self, s: &str) -> bool {
        s.chars()
            .enumerate()
            .all(|(k, ch)| self.c.get(self.i + k) == Some(&ch))
    }

    fn skip_to(&mut self, end: &str) {
        while self.i < self.c.len() && !self.starts(end) {
            self.i += 1;
        }
        self.i = (self.i + end.len()).min(self.c.len());
    }

    fn skip_space(&mut self) {
        while self.c.get(self.i).is_some_and(|c| c.is_whitespace()) {
            self.i += 1;
        }
    }
}

/// The text of the string literal that starts at the opening quote `s.i`. A `{...}` hole of an
/// interpolated string is `{}`.
fn literal(s: &mut Scan, lang: Lang, holes: bool) -> String {
    let mut out = String::new();
    s.i += 1;
    while let Some(&ch) = s.c.get(s.i) {
        s.i += 1;
        match ch {
            '"' => break,
            '\\' => {
                let Some(&e) = s.c.get(s.i) else { break };
                s.i += 1;
                match e {
                    'n' => out.push('\n'),
                    '\n' => s.skip_space(),
                    other => out.push(other),
                }
            }
            '{' if lang == Lang::Rust && s.c.get(s.i) == Some(&'{') => {
                s.i += 1;
                out.push('{');
            }
            '}' if lang == Lang::Rust && s.c.get(s.i) == Some(&'}') => {
                s.i += 1;
                out.push('}');
            }
            '{' if lang == Lang::Rust => {
                let hole = s.c[s.i..]
                    .iter()
                    .position(|c| !(c.is_alphanumeric() || "_:?.#".contains(*c)));
                match hole {
                    Some(n) if s.c[s.i + n] == '}' => {
                        s.i += n + 1;
                        out.push_str("{}");
                    }
                    _ => out.push('{'),
                }
            }
            '{' if holes => {
                let mut depth = 1;
                while depth > 0 && s.i < s.c.len() {
                    match s.c[s.i] {
                        '{' => depth += 1,
                        '}' => depth -= 1,
                        _ => {}
                    }
                    s.i += 1;
                }
                out.push_str("{}");
            }
            other => out.push(other),
        }
    }
    out
}

/// The string literals of `src`. A literal that a `++` joins to the next one is one entry. The
/// holes of format strings and of `s!` strings are `{}`.
fn runs(src: &str, lang: Lang) -> Vec<String> {
    let c: Vec<char> = src.chars().collect();
    let mut s = Scan { c: &c, i: 0 };
    let line_comment = if lang == Lang::Rust { "//" } else { "--" };
    let (open, close) = if lang == Lang::Rust {
        ("/*", "*/")
    } else {
        ("/-", "-/")
    };
    let mut out = Vec::new();
    let mut run: Option<String> = None;
    while s.i < c.len() {
        if s.starts(line_comment) {
            s.skip_to("\n");
        } else if s.starts(open) {
            s.skip_to(close);
        } else if s.starts("'\"'") {
            s.i += 3;
        } else if s.starts("s!\"") || s.starts("\"") {
            let holes = s.starts("s!\"");
            s.i += if holes { 2 } else { 0 };
            let text = literal(&mut s, lang, holes);
            run.get_or_insert_with(String::new).push_str(&text);
            let end = s.i;
            s.skip_space();
            let joined = lang == Lang::Lean && s.starts("++") && {
                s.i += 2;
                s.skip_space();
                s.starts("\"") || s.starts("s!\"")
            };
            if !joined {
                out.extend(run.take());
                s.i = end;
            }
        } else {
            s.i += 1;
        }
    }
    out.iter().map(|r| r.replace("{}:{}", "{}")).collect()
}

/// A Rust file without its test module and without a test file.
fn rust_non_test(path: &str, src: &str) -> Option<String> {
    let p = Path::new(path);
    let test_file = p.components().any(|c| c.as_os_str() == "tests")
        || p.file_stem()
            .and_then(|s| s.to_str())
            .is_some_and(|s| s.starts_with("tests"))
        || path.starts_with("crates/testkit/");
    if test_file || p.extension() != Some("rs".as_ref()) {
        return None;
    }
    let cut = src
        .match_indices("\n#[cfg(test)]\nmod ")
        .find(|(i, m)| {
            src[i + m.len()..]
                .lines()
                .next()
                .is_some_and(|l| l.ends_with(" {"))
        })
        .map_or(src.len(), |(i, _)| i);
    Some(src[..cut].to_owned())
}

fn lean_non_test(path: &str) -> bool {
    Path::new(path).extension() == Some("lean".as_ref())
        && !path.contains("/Test/")
        && !path.contains("/Proof/")
}

/// The regex that matches a message of the spec text, with each placeholder as a wildcard.
fn pin_regex(normal: &str) -> Result<Regex> {
    let parts: Vec<String> = normal.split("{}").map(regex::escape).collect();
    Ok(Regex::new(&format!("^{}$", parts.join(".*")))?)
}

fn violation(row: &Row, message: String) -> Violation {
    Violation {
        path: Path::new(SPEC).to_path_buf(),
        line: Some(row.line),
        rule: RULE,
        severity: Severity::Error,
        message,
    }
}

/// What the rule reads from the tree.
struct Sources {
    lean: Vec<String>,
    rust: Vec<String>,
    /// The code and the message of each `expected-error` and `expected-message` pair.
    pins: Vec<(String, String)>,
}

/// `strict` makes a stale entry of the inventory an error. Otherwise it is a warning, so a commit
/// that closes a gap passes `just check`. `just ci` runs the strict mode.
fn violations(rows: &[Row], src: &Sources, allow: &[Gap], strict: bool) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    for row in rows {
        let normal = normalize(&row.text);
        let pin = pin_regex(&normal)?;
        let checks = [
            (Part::Fix, fix(&row.text).is_some()),
            (Part::Lean, src.lean.iter().any(|r| r.contains(&normal))),
            (Part::Rust, src.rust.iter().any(|r| r.contains(&normal))),
            (
                Part::Pin,
                src.pins
                    .iter()
                    .any(|(c, m)| *c == row.code && pin.is_match(m)),
            ),
        ];
        for (part, ok) in checks {
            let id = row.id();
            let gap = allow.iter().find(|g| g.row == id && g.part == part);
            match (ok, gap) {
                (true, Some(g)) => out.push(Violation {
                    severity: if strict {
                        Severity::Error
                    } else {
                        Severity::Warning
                    },
                    ..violation(
                        row,
                        format!(
                            "`{id}` now has a {}: remove its line from `{ALLOW_FILE}` (#{})",
                            part.name(),
                            g.issue
                        ),
                    )
                }),
                (true, None) | (false, Some(_)) => {}
                (false, None) => out.push(violation(row, missing(&id, part))),
            }
        }
    }
    for g in allow {
        if !rows.iter().any(|r| r.id() == g.row) {
            out.push(Violation {
                path: Path::new(SPEC).to_path_buf(),
                line: None,
                rule: RULE,
                severity: Severity::Error,
                message: format!(
                    "`{ALLOW_FILE}` names `{}`, which is not a row: remove its line",
                    g.row
                ),
            });
        }
    }
    Ok(out)
}

fn missing(id: &str, part: Part) -> String {
    let how = match part {
        Part::Fix => "end the text with a clause after `; ` that tells the user what to do",
        Part::Lean => "print the text exactly in `lean/Silicon/Source`",
        Part::Rust => "print the text exactly in `crates/`",
        Part::Pin => "add a file under `tests/source` with `// expected-message:` for the text",
    };
    format!(
        "the text `{id}` has no {}; {how}",
        part.name().trim_start_matches("a ")
    )
}

/// True for a `.si` file in a suite whose runner compares the directives.
fn pin_file(path: &str) -> bool {
    path.strip_prefix(PIN_DIR)
        .and_then(|rest| rest.split_once('/'))
        .is_some_and(|(dir, file)| {
            MESSAGE_SUITES.contains(&dir) && Path::new(file).extension() == Some("si".as_ref())
        })
}

/// The code and the message of a file, read with the parser of the harness. A malformed file has
/// no pin, and the harness reports it.
fn pin_of(text: &str) -> Option<(String, String)> {
    let expected = expected_error(text, Marker::Si).ok()??;
    Some((expected.code, expected.message?))
}

/// The rule in `cargo xtask check`: a stale entry of the inventory is a warning.
pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    run(repo, false)
}

/// The rule in `cargo xtask spec-texts --strict`, which `just ci` runs.
pub fn run(repo: &Repo, strict: bool) -> Result<Vec<Violation>> {
    let rows = spec_rows(&repo.read(Path::new(SPEC))?)?;
    let mut src = Sources {
        lean: Vec::new(),
        rust: Vec::new(),
        pins: Vec::new(),
    };
    for f in &repo.files {
        let Some(path) = f.path.to_str() else {
            continue;
        };
        if path.starts_with(LEAN_DIR) && lean_non_test(path) {
            src.lean.extend(runs(&repo.read(&f.path)?, Lang::Lean));
        } else if path.starts_with(RUST_DIR) {
            if let Some(text) = rust_non_test(path, &repo.read(&f.path).unwrap_or_default()) {
                src.rust.extend(runs(&text, Lang::Rust));
            }
        } else if let Some(text) = pin_file(path).then(|| repo.read(&f.path)) {
            src.pins.extend(pin_of(&text?));
        }
    }
    violations(
        &rows,
        &src,
        &parse_allow(&repo.read(Path::new(ALLOW_FILE))?)?,
        strict,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const TABLE: &str = "### 6.2 Report order\n\n| Code | Case | Message |\n| --- | --- | --- |\n| `S021` | Uncovered | the `match` does not cover `{v}` of `{T}`; add an arm for it |\n| `S010` | Kind | a pattern of `{T}` is {k}, not `{p}`; write {k}, or `_` |\n\n### 6.3 Next\n\n| Code | Case | Message |\n| --- | --- | --- |\n| `S001` | Other | no fix here |\n";

    fn src(lean: &[&str], rust: &[&str], pins: &[(&str, &str)]) -> Sources {
        let own = |xs: &[&str]| xs.iter().map(|s| (*s).to_owned()).collect();
        Sources {
            lean: own(lean),
            rust: own(rust),
            pins: pins
                .iter()
                .map(|(c, m)| ((*c).to_owned(), (*m).to_owned()))
                .collect(),
        }
    }

    const UNCOVERED: &str = "the `match` does not cover `{}` of `{}`; add an arm for it";
    const KIND: &str = "a pattern of `{}` is {}, not `{}`; write {}, or `_`";

    fn complete() -> Sources {
        src(
            &[UNCOVERED, KIND],
            &[KIND, UNCOVERED],
            &[
                (
                    "S021",
                    "the `match` does not cover `3` of `UInt[2]`; add an arm for it",
                ),
                (
                    "S010",
                    "a pattern of `Op` is an integer, not `true`; write an integer, or `_`",
                ),
            ],
        )
    }

    fn messages(rows: &[Row], s: &Sources, allow: &[Gap]) -> Vec<String> {
        violations(rows, s, allow, true)
            .unwrap()
            .into_iter()
            .map(|v| v.message)
            .collect()
    }

    #[test]
    fn rows_come_from_the_tables_of_section_6_2_only() {
        let rows = spec_rows(TABLE).unwrap();
        let ids: Vec<String> = rows.iter().map(Row::id).collect();
        assert_eq!(ids, ["S021 Uncovered", "S010 Kind"]);
        assert_eq!(rows[0].line, 5);
        assert!(spec_rows("### 6.2 x\n").is_err());
    }

    #[test]
    fn a_complete_text_passes() {
        let rows = spec_rows(TABLE).unwrap();
        assert_eq!(messages(&rows, &complete(), &[]), Vec::<String>::new());
    }

    #[test]
    fn a_text_without_a_fix_fails() {
        let rows = spec_rows(&TABLE.replace("; add an arm for it", "")).unwrap();
        let s = src(
            &["the `match` does not cover `{}` of `{}`", KIND],
            &["the `match` does not cover `{}` of `{}`", KIND],
            &[
                ("S021", "the `match` does not cover `3` of `UInt[2]`"),
                (
                    "S010",
                    "a pattern of `Op` is an integer, not `true`; write an integer, or `_`",
                ),
            ],
        );
        let got = messages(&rows, &s, &[]);
        assert_eq!(got.len(), 1, "{got:?}");
        assert!(got[0].contains("S021 Uncovered") && got[0].contains("fix clause"));
        assert_eq!(fix("one; two"), None);
        assert_eq!(fix("a; b; do the thing"), Some("do the thing"));
    }

    #[test]
    fn a_text_in_only_lean_or_only_rust_fails() {
        let rows = spec_rows(TABLE).unwrap();
        let mut s = complete();
        s.rust.remove(1);
        let got = messages(&rows, &s, &[]);
        assert_eq!(got.len(), 1, "{got:?}");
        assert!(got[0].contains("Rust literal"));
        let mut s = complete();
        s.lean.remove(0);
        assert!(messages(&rows, &s, &[])[0].contains("Lean literal"));
    }

    #[test]
    fn a_text_with_no_pin_fails() {
        let rows = spec_rows(TABLE).unwrap();
        let mut s = complete();
        s.pins.remove(1);
        let got = messages(&rows, &s, &[]);
        assert_eq!(got.len(), 1, "{got:?}");
        assert!(got[0].contains("S010 Kind") && got[0].contains("pin"));
        s.pins[0].1 = "the `match` does not cover".to_owned();
        assert_eq!(messages(&rows, &s, &[]).len(), 2);
    }

    const PIN_FILE: &str = "// expected-error S010 @+2\n// expected-message: a pattern of `Op` is an integer, not `true`; write an integer, or `_`\nx\n";

    #[test]
    fn a_disabled_directive_is_no_pin() {
        let pin = pin_of(PIN_FILE).unwrap();
        assert_eq!(pin.0, "S010");
        let disabled = PIN_FILE.replace("// expected-message:", "// disabled expected-message:");
        assert_eq!(pin_of(&disabled), None);
        let orphan = PIN_FILE.replace("// expected-error S010 @+2\n", "");
        assert_eq!(pin_of(&orphan), None);
    }

    #[test]
    fn a_file_outside_the_message_suites_is_no_pin() {
        assert!(pin_file("tests/source/check/a.si"));
        assert!(pin_file("tests/source/parse/a.si"));
        assert!(pin_file("tests/source/run/a.si"));
        assert!(!pin_file("tests/source/elab/a.si"));
        assert!(!pin_file("tests/source/corpus/a.si"));
        assert!(!pin_file("tests/source/budget/a.si"));
        assert!(!pin_file("tests/source/scaling/a.si"));
        assert!(!pin_file("tests/source/check/a.txt"));
        assert!(!pin_file("doc/a.si"));
    }

    #[test]
    fn a_pin_with_another_code_fails() {
        let rows = spec_rows(TABLE).unwrap();
        let mut s = complete();
        s.pins[1].0 = "S011".to_owned();
        let got = messages(&rows, &s, &[]);
        assert_eq!(got.len(), 1, "{got:?}");
        assert!(got[0].contains("S010 Kind") && got[0].contains("pin"));
    }

    #[test]
    fn the_allowlist_excuses_a_gap_and_goes_stale_when_it_closes() {
        let rows = spec_rows(TABLE).unwrap();
        let mut s = complete();
        s.pins.remove(1);
        let gap = [Gap {
            row: "S010 Kind".to_owned(),
            part: Part::Pin,
            issue: 1,
        }];
        assert!(messages(&rows, &s, &gap).is_empty());
        let stale = messages(&rows, &complete(), &gap);
        assert_eq!(stale.len(), 1);
        assert!(stale[0].contains("remove its line from `tests/inventory/spec-texts.txt` (#1)"));
        let lax = violations(&rows, &complete(), &gap, false).unwrap();
        assert_eq!((lax.len(), lax[0].severity), (1, Severity::Warning));
        let strict = violations(&rows, &complete(), &gap, true).unwrap();
        assert_eq!((strict.len(), strict[0].severity), (1, Severity::Error));
        let mut missing = complete();
        missing.pins.remove(1);
        let lax = violations(&rows, &missing, &[], false).unwrap();
        assert_eq!((lax.len(), lax[0].severity), (1, Severity::Error));
        let unknown = [Gap {
            row: "S999 Gone".to_owned(),
            part: Part::Pin,
            issue: 1,
        }];
        assert!(messages(&rows, &complete(), &unknown)[0].contains("not a row"));
    }

    #[test]
    fn the_allow_file_parses_and_rejects_a_bad_line() {
        let ok =
            parse_allow("# c\n\nlean | S021 Uncovered value | 12\npin | S011 A `b` | 3\n").unwrap();
        assert_eq!(ok.len(), 2);
        assert_eq!(
            (ok[1].row.as_str(), ok[1].part, ok[1].issue),
            ("S011 A `b`", Part::Pin, 3)
        );
        for bad in [
            "lean | S021 X",
            "lean | S021 X | ",
            "lean | S021 X | #3",
            "text | S021 X | 3",
        ] {
            assert!(parse_allow(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn placeholders_normalize_and_literals_join() {
        assert_eq!(normalize("a `{T}` b {k}; X and Y"), "a `{}` b {}; X and Y");
        assert_eq!(normalize("differ: X and Y; fix"), "differ: {} and {}; fix");
        let lean = "def f := fail .S021 p (s!\"at {b.line}:{b.col} \\{ {if a then \"x\" else \"y\"} \" ++\n  \"tail\") -- \"no\"\n";
        assert_eq!(runs(lean, Lang::Lean), ["at {} { {} tail"]);
        let rust = "let m = format!(\"`{}` has {{ {text:?}; \\\n    next\"); // \"no\"\n";
        assert_eq!(runs(rust, Lang::Rust), ["`{}` has { {}; next"]);
    }

    #[test]
    fn rust_tests_are_not_code() {
        assert!(rust_non_test("crates/a/src/tests_x.rs", "x").is_none());
        assert!(rust_non_test("crates/testkit/src/lib.rs", "x").is_none());
        let src = "a\n#[cfg(test)]\nmod tests {\n b\n}\n";
        assert_eq!(rust_non_test("crates/a/src/lib.rs", src).unwrap(), "a");
        assert!(lean_non_test("lean/Silicon/Source/Eval.lean"));
        assert!(!lean_non_test("lean/Silicon/Source/Test/Eval.lean"));
    }

    #[test]
    fn the_checked_in_tree_passes() {
        let repo = Repo::discover().unwrap();
        assert_eq!(check(&repo).unwrap(), Vec::new());
    }
}
