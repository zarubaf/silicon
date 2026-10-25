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
//! A string literal of `CLI_PINS` that is a whole `error[Sxxx]: LINE:COL: MESSAGE` line is a pin too.
//!
//! A note of section 6.2 can close a placeholder with a sentence `Values of `{p}`: `a`, `b`.` after
//! the quoted case names of the rows it applies to. The rule then expands such a row over the
//! values, and a front end holds the row when, for each value, a literal matches the text with the
//! value filled in, where a hole `{}` of the literal may stand for the value, or for the value
//! without its leading `@`. So `` `@{}` `` and `` `{}` `` both hold `{g}` = `@TypeOf`, but a hole in
//! another place of the literal does not. A closed placeholder that ends the text is a fix clause
//! when each value has two words or more. The rule does not check that a hole holds the values.
//!
//! The rule also reads the other direction. Each message literal at an error site of a front end
//! (see `sites`) must be in a row, or `ALLOW_FILE` lists it as `unlisted`. A site that builds its
//! message in a helper is unscannable, and `ALLOW_FILE` lists it by its file.

mod scan;
mod sites;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::{Result, bail};
use regex::Regex;
use testkit::source::MESSAGE_SUITES;
use testkit::{Marker, expected_error};

use crate::repo::Repo;
use crate::violation::{Severity, Violation};
use scan::{Lang, lean_non_test, runs, rust_non_test};
use sites::{Site, lean_sites, rust_sites};

const ALLOW_FILE: &str = "tests/inventory/spec-texts.txt";
const SPEC: &str = "doc/design/2026-10-09-frontend.md";
const SECTION: &str = "### 6.2 ";
const RULE: &str = "spec-texts";
const LEAN_DIR: &str = "lean/Silicon/Source/";
const RUST_DIR: &str = "crates/";
/// The crates of the Rust front end, whose error sites the rule reads.
const FRONT_END_CRATES: [&str; 5] = ["parse", "syntax", "resolve", "typeck", "elab"];
const PIN_DIR: &str = "tests/source/";
/// The test of the driver that asserts the full text of a message.
const CLI_PINS: &str = "crates/driver/tests/cli.rs";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Part {
    Fix,
    Lean,
    Rust,
    Pin,
    /// An error text of a front end that has no row. The gap names it, not a row.
    Unlisted,
}

impl Part {
    fn name(self) -> &'static str {
        match self {
            Self::Fix => "fix clause",
            Self::Lean => "Lean literal",
            Self::Rust => "Rust literal",
            Self::Pin => "`expected-message` pin",
            Self::Unlisted => "row in section 6.2",
        }
    }
}

/// A known gap. `row` is the code and the case of a row, as in `S021 Uncovered value`.
struct Gap {
    row: String,
    part: Part,
    issue: u32,
}

/// Reads the known gaps from the inventory, which `ALLOW_FILE` names and documents. A malformed
/// line is a problem in the second value and has no gap.
fn parse_allow(text: &str) -> (Vec<Gap>, Vec<String>) {
    let mut gaps = Vec::new();
    let mut problems = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let at = i + 1;
        let cells: Vec<&str> = line.split(" | ").map(str::trim).collect();
        let [part, row, issue] = cells[..] else {
            problems.push(format!(
                "{ALLOW_FILE}:{at}: write `<part> | <row> | <issue>`"
            ));
            continue;
        };
        let part = match part {
            "fix" => Part::Fix,
            "lean" => Part::Lean,
            "rust" => Part::Rust,
            "pin" => Part::Pin,
            "unlisted" => Part::Unlisted,
            other => {
                problems.push(format!(
                    "{ALLOW_FILE}:{at}: the part `{other}` is not fix, lean, rust, pin, or unlisted"
                ));
                continue;
            }
        };
        let Ok(issue) = issue.parse() else {
            problems.push(format!(
                "{ALLOW_FILE}:{at}: `{issue}` is not an issue number; name the issue that closes the gap"
            ));
            continue;
        };
        gaps.push(Gap {
            row: row.to_owned(),
            part,
            issue,
        });
    }
    (gaps, problems)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    line: usize,
    code: String,
    case: String,
    text: String,
    /// The values of each closed placeholder of the text, by its name.
    closed: BTreeMap<String, Vec<String>>,
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
                closed: BTreeMap::new(),
            });
        }
    }
    if rows.is_empty() {
        bail!("{SPEC} has no `Code | Case | Message` table in section 6.2");
    }
    close_placeholders(spec, &mut rows)?;
    Ok(rows)
}

/// The length of the backtick run that starts at byte `at`.
fn ticks(line: &str, at: usize) -> usize {
    line[at..].bytes().take_while(|b| *b == b'`').count()
}

/// The code spans of a line: the text between two backtick runs of one length.
fn code_spans(line: &str) -> Vec<String> {
    let mut spans = Vec::new();
    let mut from = 0;
    while let Some(open) = line[from..].find('`').map(|off| off + from) {
        let width = ticks(line, open);
        let body = open + width;
        let mut scan = body;
        let mut close = None;
        while let Some(at) = line[scan..].find('`').map(|off| off + scan) {
            let run = ticks(line, at);
            if run == width {
                close = Some(at);
                break;
            }
            scan = at + run;
        }
        match close {
            Some(at) => {
                spans.push(line[body..at].trim().to_owned());
                from = at + width;
            }
            None => from = body,
        }
    }
    spans
}

const VALUES: &str = "Values of `{";

/// Gives each row a closed placeholder from the sentence `Values of `{p}`: `a`, `b`.` of a note in
/// section 6.2. The quoted strings before the sentence name the rows, by case.
fn close_placeholders(spec: &str, rows: &mut [Row]) -> Result<()> {
    let mut in_section = false;
    for (i, line) in spec.lines().enumerate() {
        if line.starts_with("### ") || line.starts_with("## ") {
            in_section = line.starts_with(SECTION);
        }
        let Some(at) = line.find(VALUES).filter(|_| in_section) else {
            continue;
        };
        let here = i + 1;
        let tail = &line[at + VALUES.len()..];
        let Some((name, tail)) = tail.split_once("}`:") else {
            bail!("{SPEC}:{here}: write `Values of `{{p}}`: `a`, `b`.`");
        };
        let values = code_spans(tail);
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphabetic()) || values.is_empty() {
            bail!("{SPEC}:{here}: write `Values of `{{p}}`: `a`, `b`.` with one or more values");
        }
        let mut found = false;
        for case in line[..at].split('"').skip(1).step_by(2) {
            for row in rows.iter_mut().filter(|r| r.case == case) {
                row.closed.insert(name.to_owned(), values.clone());
                found = true;
            }
        }
        if !found {
            bail!("{SPEC}:{here}: the values of `{{{name}}}` follow no quoted case of a row");
        }
    }
    Ok(())
}

/// A hole of the code stands for a closed value, or for the value without its `@`.
fn value_pattern(value: &str) -> String {
    let mut alts = vec![regex::escape(&normalize(value)), r"\{\}".to_owned()];
    if value.starts_with('@') {
        alts.push(r"@\{\}".to_owned());
    }
    format!("(?:{})", alts.join("|"))
}

/// The text of a row with one choice of a value for each closed placeholder, or the text itself
/// when the row has none.
struct Expansion {
    /// Matches a literal that holds the text, where a hole stands for a value.
    whole: Regex,
    /// The text with the values filled in and the other placeholders as `{}`.
    text: String,
}
fn expansions(row: &Row) -> Result<Vec<Expansion>> {
    let mut raw = row.text.clone();
    for name in row.closed.keys() {
        raw = raw.replace(&format!("{{{name}}}"), &format!("\u{1}{name}\u{1}"));
    }
    let normal = normalize(&raw);
    let pieces: Vec<&str> = normal.split('\u{1}').collect();
    let mut picks: Vec<BTreeMap<&str, &str>> = vec![BTreeMap::new()];
    for (name, values) in &row.closed {
        picks = picks
            .into_iter()
            .flat_map(|pick| {
                values.iter().map(move |v| {
                    let mut next = pick.clone();
                    next.insert(name.as_str(), v.as_str());
                    next
                })
            })
            .collect();
    }
    picks
        .iter()
        .map(|pick| {
            let text: String = pieces
                .iter()
                .enumerate()
                .map(|(k, piece)| {
                    if k % 2 == 0 {
                        (*piece).to_owned()
                    } else {
                        normalize(pick[piece])
                    }
                })
                .collect();
            let src: String = pieces
                .iter()
                .enumerate()
                .map(|(k, piece)| {
                    if k % 2 == 0 {
                        regex::escape(piece)
                    } else {
                        value_pattern(pick[piece])
                    }
                })
                .collect();
            Ok(Expansion {
                whole: Regex::new(&src)?,
                text,
            })
        })
        .collect()
}

/// Whether some literal of `runs` holds the text of the row. A row with a closed placeholder needs
/// a literal for each value.
fn holds(forms: &[Expansion], runs: &[String]) -> bool {
    forms
        .iter()
        .all(|form| runs.iter().any(|r| form.whole.is_match(r)))
}

/// Whether the literal of an error site belongs to the row: it holds the text of a value, or it is
/// a part of that text. A hole of the literal stands for a value only where the row is closed.
fn belongs(row: &Row, forms: &[Expansion], literal: &str) -> bool {
    // A hole after an `@` of the literal stands for the value without its `@`.
    let hole = |after_at: bool| {
        let mut alts = vec![r"\{\}".to_owned()];
        for value in row.closed.values().flatten() {
            match (after_at, value.strip_prefix('@')) {
                (true, Some(bare)) => alts.push(regex::escape(&normalize(bare))),
                (true, None) => {}
                (false, _) => alts.push(regex::escape(&normalize(value))),
            }
        }
        format!("(?:{})", alts.join("|"))
    };
    let pieces: Vec<&str> = literal.split("{}").collect();
    let mut part = String::new();
    for (k, piece) in pieces.iter().enumerate() {
        part.push_str(&regex::escape(piece));
        if k + 1 < pieces.len() {
            part.push_str(&hole(piece.ends_with('@')));
        }
    }
    let part = Regex::new(&part).ok();
    forms.iter().any(|form| {
        form.whole.is_match(literal) || part.as_ref().is_some_and(|re| re.is_match(&form.text))
    })
}

/// Whether the text ends with a clause that tells the user what to do. The clause can be a closed
/// placeholder, whose values are each such a clause.
fn has_fix(row: &Row) -> bool {
    let words = |t: &str| t.split_whitespace().count() >= 2;
    if fix(&row.text).is_some() {
        return true;
    }
    let Some((_, last)) = row.text.rsplit_once("; ") else {
        return false;
    };
    last.trim()
        .strip_prefix('{')
        .and_then(|l| l.strip_suffix('}'))
        .and_then(|name| row.closed.get(name))
        .is_some_and(|values| values.iter().all(|v| words(v)))
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

/// The regex that matches a message of the spec text, with each placeholder as a wildcard.
fn pin_regex(normal: &str) -> Result<Regex> {
    let parts: Vec<String> = normal.split("{}").map(regex::escape).collect();
    Ok(Regex::new(&format!("^{}$", parts.join(".*")))?)
}

/// A finding of the rule. Every finding is a warning in `cargo xtask check`, so a commit that
/// adds a row without its gap lines can pass. `--strict`, which `just ci` runs, makes it an error.
fn finding(strict: bool, path: &str, line: Option<usize>, message: String) -> Violation {
    Violation {
        path: Path::new(path).to_path_buf(),
        line,
        rule: RULE,
        severity: if strict {
            Severity::Error
        } else {
            Severity::Warning
        },
        message,
    }
}

/// What the rule reads from the tree.
struct Sources {
    lean: Vec<String>,
    rust: Vec<String>,
    /// The code and the message of each `expected-error` and `expected-message` pair, and of
    /// each full message in `CLI_PINS`.
    pins: Vec<(String, String)>,
    /// The error sites of the Lean and of the Rust front end.
    lean_sites: Vec<Site>,
    rust_sites: Vec<Site>,
}

/// Whether each part of a row is present. The fix is in the spec text, the rest is in `src`.
fn row_checks(row: &Row, forms: &[Expansion], src: &Sources) -> Result<[(Part, bool); 4]> {
    let normal = normalize(&row.text);
    let pin = pin_regex(&normal)?;
    Ok([
        (Part::Fix, has_fix(row)),
        (Part::Lean, holds(forms, &src.lean)),
        (Part::Rust, holds(forms, &src.rust)),
        (
            Part::Pin,
            src.pins
                .iter()
                .any(|(c, m)| *c == row.code && pin.is_match(m)),
        ),
    ])
}

fn violations(
    rows: &[Row],
    src: &Sources,
    allow: &[Gap],
    problems: &[String],
    strict: bool,
) -> Result<Vec<Violation>> {
    let mut out = Vec::new();
    for problem in problems {
        out.push(finding(strict, ALLOW_FILE, None, problem.clone()));
    }
    for row in rows {
        let checks = row_checks(row, &expansions(row)?, src)?;
        for (part, ok) in checks {
            let id = row.id();
            let gap = allow.iter().find(|g| g.row == id && g.part == part);
            match (ok, gap) {
                (true, Some(g)) => out.push(finding(
                    strict,
                    SPEC,
                    Some(row.line),
                    format!(
                        "`{id}` now has a {}: remove its line from `{ALLOW_FILE}` (#{})",
                        part.name(),
                        g.issue
                    ),
                )),
                (true, None) | (false, Some(_)) => {}
                (false, None) => {
                    out.push(finding(strict, SPEC, Some(row.line), missing(&id, part)));
                }
            }
        }
    }
    unlisted(rows, src, allow, strict, &mut out)?;
    for g in allow.iter().filter(|g| g.part != Part::Unlisted) {
        if !rows.iter().any(|r| r.id() == g.row) {
            out.push(finding(
                strict,
                SPEC,
                None,
                format!(
                    "`{ALLOW_FILE}` names `{}`, which is not a row: remove its line",
                    g.row
                ),
            ));
        }
    }
    Ok(out)
}

/// The first characters of a text, which name it in the inventory.
const KEY_CHARS: usize = 48;

/// The inventory name of a finding: the code and the start of the text, or the file of a site
/// that has no literal.
fn unlisted_key(site: &Site) -> String {
    match &site.text {
        Some(t) => format!(
            "{} {}",
            site.code,
            t.chars().take(KEY_CHARS).collect::<String>().trim_end()
        ),
        None => format!("{} unscannable {}", site.code, site.path),
    }
}

/// The findings for the error sites with a text that no row of section 6.2 holds, and for the
/// lines of `unlisted` that no site needs any more.
fn unlisted(
    rows: &[Row],
    src: &Sources,
    allow: &[Gap],
    strict: bool,
    out: &mut Vec<Violation>,
) -> Result<()> {
    let forms: Vec<Vec<Expansion>> = rows.iter().map(expansions).collect::<Result<_>>()?;
    let listed = |t: &str| {
        rows.iter()
            .zip(&forms)
            .any(|(row, form)| belongs(row, form, t))
    };
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let sides = [("Lean", &src.lean_sites), ("Rust", &src.rust_sites)];
    for (side, sites) in sides {
        for site in sites {
            if site.text.as_deref().is_some_and(listed) {
                continue;
            }
            let key = unlisted_key(site);
            seen.insert(key.clone());
            let gap = allow
                .iter()
                .any(|g| g.part == Part::Unlisted && g.row == key);
            if !gap {
                let what = match site.text {
                    Some(_) => "has no row in section 6.2; add a row, or list it".to_owned(),
                    None => "builds its message in a helper that the scanner cannot see; \
                             write the text as a literal at the site, or list it"
                        .to_owned(),
                };
                out.push(finding(
                    strict,
                    &site.path,
                    Some(site.line),
                    format!("the {side} error text `{key}` {what} in `{ALLOW_FILE}` as `unlisted | {key} | <issue>`"),
                ));
            }
        }
    }
    for g in allow.iter().filter(|g| g.part == Part::Unlisted) {
        if !seen.contains(&g.row) {
            out.push(finding(
                strict,
                ALLOW_FILE,
                None,
                format!(
                    "`{ALLOW_FILE}` lists `{}` (#{}), which no error site has now: remove its line",
                    g.row, g.issue
                ),
            ));
        }
    }
    Ok(())
}

fn missing(id: &str, part: Part) -> String {
    let how = match part {
        Part::Fix => "end the text with a clause after `; ` that tells the user what to do",
        Part::Lean => "print the text exactly in `lean/Silicon/Source`",
        Part::Rust => "print the text exactly in `crates/`",
        Part::Pin => "add a file under `tests/source` with `// expected-message:` for the text",
        Part::Unlisted => "add a row to the table of section 6.2",
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

/// The code and the message of a string literal of `CLI_PINS` that is a whole diagnostic line,
/// `error[Sxxx]: LINE:COL: MESSAGE`. The position may be holes or digits.
fn cli_pin(run: &str) -> Option<(String, String)> {
    let re = Regex::new(r"^error\[(S\d{3})\]: (?:\{\}|\d+):(?:\{\}|\d+): (.*?)\n?$").ok()?;
    let m = re.captures(run)?;
    Some((m[1].to_owned(), m[2].to_owned()))
}

/// The codes with a row in the message tables of section 6.2. A front end prints the same text
/// for each of them (front-end spec 11.4).
pub fn normative_codes(repo: &Repo) -> Result<BTreeSet<String>> {
    let rows = spec_rows(&repo.read(Path::new(SPEC))?)?;
    Ok(rows.into_iter().map(|row| row.code).collect())
}

/// The rule in `cargo xtask check`: every finding is a warning.
pub fn check(repo: &Repo) -> Result<Vec<Violation>> {
    run(repo, false)
}

/// The rule in `cargo xtask spec-texts --strict`, which `just ci` runs: every finding is an error.
pub fn run(repo: &Repo, strict: bool) -> Result<Vec<Violation>> {
    let rows = spec_rows(&repo.read(Path::new(SPEC))?)?;
    let mut src = Sources {
        lean: Vec::new(),
        rust: Vec::new(),
        pins: Vec::new(),
        lean_sites: Vec::new(),
        rust_sites: Vec::new(),
    };
    for f in &repo.files {
        let Some(path) = f.path.to_str() else {
            continue;
        };
        if path.starts_with(LEAN_DIR) && lean_non_test(path) {
            let text = repo.read(&f.path)?;
            src.lean.extend(runs(&text, Lang::Lean));
            src.lean_sites.extend(lean_sites(path, &text)?);
        } else if path.starts_with(RUST_DIR) {
            if let Some(text) = rust_non_test(path, &repo.read(&f.path).unwrap_or_default()) {
                src.rust.extend(runs(&text, Lang::Rust));
                if FRONT_END_CRATES
                    .iter()
                    .any(|c| path.starts_with(&format!("{RUST_DIR}{c}/")))
                {
                    src.rust_sites.extend(rust_sites(path, &text));
                }
            }
            if path == CLI_PINS {
                src.pins.extend(
                    runs(&repo.read(&f.path)?, Lang::Rust)
                        .iter()
                        .filter_map(|r| cli_pin(r)),
                );
            }
        } else if let Some(text) = pin_file(path).then(|| repo.read(&f.path)) {
            src.pins.extend(pin_of(&text?));
        }
    }
    let (allow, problems) = parse_allow(&repo.read(Path::new(ALLOW_FILE))?);
    violations(&rows, &src, &allow, &problems, strict)
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
            lean_sites: Vec::new(),
            rust_sites: Vec::new(),
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
        violations(rows, s, allow, &[], true)
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
        let lax = violations(&rows, &complete(), &gap, &[], false).unwrap();
        assert_eq!((lax.len(), lax[0].severity), (1, Severity::Warning));
        let strict = violations(&rows, &complete(), &gap, &[], true).unwrap();
        assert_eq!((strict.len(), strict[0].severity), (1, Severity::Error));
        let unknown = [Gap {
            row: "S999 Gone".to_owned(),
            part: Part::Pin,
            issue: 1,
        }];
        assert!(messages(&rows, &complete(), &unknown)[0].contains("not a row"));
    }

    #[test]
    fn every_finding_is_a_warning_unless_strict() {
        let rows = spec_rows(TABLE).unwrap();
        let mut missing = complete();
        missing.pins.remove(1);
        missing.rust.remove(1);
        let unknown = [Gap {
            row: "S999 Gone".to_owned(),
            part: Part::Pin,
            issue: 1,
        }];
        let bad = ["ALLOW:1: malformed".to_owned()];
        for strict in [false, true] {
            let want = if strict {
                Severity::Error
            } else {
                Severity::Warning
            };
            let got = violations(&rows, &missing, &unknown, &bad, strict).unwrap();
            assert_eq!(got.len(), 4, "{got:?}");
            assert!(got.iter().all(|v| v.severity == want), "{got:?}");
        }
    }

    #[test]
    fn the_allow_file_parses_and_reports_a_bad_line() {
        let (ok, problems) =
            parse_allow("# c\n\nlean | S021 Uncovered value | 12\npin | S011 A `b` | 3\n");
        assert!(problems.is_empty());
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
            let (gaps, problems) = parse_allow(bad);
            assert!(gaps.is_empty() && problems.len() == 1, "{bad}");
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

    fn site(path: &str, code: &str, text: Option<&str>) -> Site {
        Site {
            path: path.to_owned(),
            line: 7,
            code: code.to_owned(),
            text: text.map(str::to_owned),
        }
    }

    #[test]
    fn an_error_text_with_no_row_is_unlisted_and_a_listed_one_is_not() {
        let rows = spec_rows(TABLE).unwrap();
        let mut s = complete();
        s.lean_sites = vec![
            site("a.lean", "S021", Some(UNCOVERED)),
            site("a.lean", "S010", Some("the `{}` has no part")),
        ];
        s.rust_sites = vec![site("a.rs", "S021", Some(UNCOVERED))];
        let got = messages(&rows, &s, &[]);
        assert_eq!(got.len(), 1, "{got:?}");
        assert!(
            got[0].starts_with("the Lean error text `S010 the `{}` has no part` has no row"),
            "{got:?}"
        );
        assert!(got[0].contains("unlisted | S010 the `{}` has no part | <issue>"));
    }

    #[test]
    fn a_site_with_no_literal_is_unscannable() {
        let rows = spec_rows(TABLE).unwrap();
        let mut s = complete();
        s.rust_sites = vec![site("crates/elab/src/a.rs", "S017", None)];
        let got = messages(&rows, &s, &[]);
        assert_eq!(got.len(), 1, "{got:?}");
        assert!(got[0].contains("`S017 unscannable crates/elab/src/a.rs`"));
        assert!(got[0].contains("scanner cannot see"));
    }

    #[test]
    fn the_inventory_excuses_an_unlisted_text_and_goes_stale() {
        let rows = spec_rows(TABLE).unwrap();
        let mut s = complete();
        s.rust_sites = vec![site("a.rs", "S010", Some("the part does not exist"))];
        let gap = |row: &str| Gap {
            row: row.to_owned(),
            part: Part::Unlisted,
            issue: 9,
        };
        assert!(messages(&rows, &s, &[gap("S010 the part does not exist")]).is_empty());
        let stale = messages(&rows, &complete(), &[gap("S010 the part does not exist")]);
        assert_eq!(stale.len(), 1, "{stale:?}");
        assert!(stale[0].contains("which no error site has now"));
        let (gaps, problems) = parse_allow("unlisted | S010 the part | 9\n");
        assert!(problems.is_empty() && gaps[0].part == Part::Unlisted);
    }

    #[test]
    fn a_full_message_in_the_driver_test_is_a_pin() {
        let run = "error[S011]: {line}:5: the `eval` command makes no hardware, but its expression reaches this {hw} in `mk`; fix\n";
        let literal = runs(
            &format!("let t = format!(\"{}\");", run.replace('\n', "\\n")),
            Lang::Rust,
        );
        let pin = cli_pin(&literal[0]).unwrap();
        assert_eq!(pin.0, "S011");
        assert_eq!(
            pin.1,
            "the `eval` command makes no hardware, but its expression reaches this {} in `mk`; fix"
        );
        let rows = vec![Row {
            line: 1,
            code: "S011".to_owned(),
            case: "Hardware".to_owned(),
            text: "the `eval` command makes no hardware, but its expression reaches this {s} in `{h}`; fix".to_owned(),
            closed: BTreeMap::new(),
        }];
        let mut s = src(&[], &[], &[]);
        s.pins.push(pin);
        assert!(messages(&rows, &s, &[]).iter().all(|m| !m.contains("pin")),);
        assert_eq!(cli_pin("error[S011]: text"), None);
    }

    const CLOSED: &str = "### 6.2 Closed\n\n| Code | Case | Message |\n| --- | --- | --- |\n| `S001` | Operand | `{g}` takes a name; bind it with `let` |\n| `S010` | Place | no place for `{k}`; {h} |\n\n- In \"Operand\", `{g}` is the builtin. Values of `{g}`: `@TypeOf`, `@ports`.\n- In \"Place\", `{h}` is the fix. Values of `{h}`: `` bind it with `:=`, for example `u.{k} := e` ``, `read it as a value`.\n";

    fn closed_rows() -> Vec<Row> {
        spec_rows(CLOSED).unwrap()
    }

    fn holds_in(row: &Row, runs: &[&str]) -> bool {
        let runs: Vec<String> = runs.iter().map(|r| (*r).to_owned()).collect();
        holds(&expansions(row).unwrap(), &runs)
    }

    #[test]
    fn a_note_closes_a_placeholder_of_the_quoted_rows() {
        let rows = closed_rows();
        assert_eq!(rows[0].closed["g"], ["@TypeOf", "@ports"]);
        assert_eq!(
            rows[1].closed["h"],
            [
                "bind it with `:=`, for example `u.{k} := e`",
                "read it as a value"
            ]
        );
        assert!(!rows[0].closed.contains_key("h") && !rows[1].closed.contains_key("g"));
        assert_eq!(code_spans("a `b` `` c`d `` e"), ["b", "c`d"]);
        for bad in [
            "- In \"Operand\", Values of `{g}`: none.\n",
            "- In \"Operand\", Values of `{g}` `@a`.\n",
            "- In \"Gone\", Values of `{g}`: `@a`.\n",
            "- Values of `{g}`: `@a`.\n",
        ] {
            let spec = CLOSED.replace(CLOSED.lines().nth(7).unwrap(), bad.trim_end());
            assert!(spec_rows(&spec).is_err(), "{bad}");
        }
    }

    #[test]
    fn a_hole_at_a_closed_placeholder_holds_every_value() {
        let row = &closed_rows()[0];
        let tail = " takes a name; bind it with `let`";
        assert!(holds_in(row, &[&format!("`@{{}}`{tail}")]));
        assert!(holds_in(row, &[&format!("`{{}}`{tail}")]));
        assert!(holds_in(row, &[&format!("x `@{{}}`{tail} y")]));
    }

    #[test]
    fn a_literal_needs_each_value_when_it_has_no_hole() {
        let row = &closed_rows()[0];
        let one = "`@TypeOf` takes a name; bind it with `let`";
        let two = "`@ports` takes a name; bind it with `let`";
        assert!(holds_in(row, &[one, two]));
        assert!(!holds_in(row, &[one]));
        assert!(!holds_in(
            row,
            &["`@typeInfo` takes a name; bind it with `let`", two]
        ));
    }

    #[test]
    fn a_near_miss_does_not_hold() {
        let row = &closed_rows()[0];
        for run in [
            "`@{}` takes a name; bind it with `var`",
            "`@{}` takes a type; bind it with `let`",
            "`@@{}` takes a name; bind it with `let`",
            "{} takes a name; bind it with `let`",
            "`{}`takes a name; bind it with `let`",
            "",
        ] {
            assert!(!holds_in(row, &[run]), "{run}");
        }
        let place = &closed_rows()[1];
        assert!(!holds_in(place, &["no place for `{}`"]));
        assert!(holds_in(place, &["no place for `{}`; {}"]));
    }

    #[test]
    fn a_hole_stands_only_at_the_closed_placeholder() {
        let rows = spec_rows(
            &CLOSED
                .replace("no place for `{k}`", "no place for {k} of `{g}`")
                .replace("In \"Operand\"", "In \"Operand\" and \"Place\""),
        )
        .unwrap();
        let place = &rows[1];
        assert!(holds_in(place, &["no place for {} of `@{}`; {}"]));
        assert!(!holds_in(place, &["no place for `{}` of `@{}`; {}"]));
        assert!(!holds_in(place, &["no place for {} of `@{}` in {}; {}"]));
    }

    #[test]
    fn a_closed_placeholder_at_the_end_is_a_fix_when_each_value_is() {
        let rows = closed_rows();
        assert!(has_fix(&rows[0]) && has_fix(&rows[1]));
        let mut short = rows[1].clone();
        short.closed.insert(
            "h".to_owned(),
            vec!["bind it".to_owned(), "stop".to_owned()],
        );
        assert!(!has_fix(&short));
        let mut open = rows[1].clone();
        open.closed.clear();
        assert!(!has_fix(&open));
        let mut mid = rows[0].clone();
        mid.text = "`{g}` takes a name".to_owned();
        assert!(!has_fix(&mid));
    }

    #[test]
    fn a_site_with_a_value_of_a_closed_placeholder_has_a_row() {
        let rows = closed_rows();
        let one = "`@TypeOf` takes a name; bind it with `let`";
        let two = "`@ports` takes a name; bind it with `let`";
        let fix = "no place for `{}`; {}";
        let mut s = src(
            &[one, two, fix],
            &[one, two, fix],
            &[("S001", "x"), ("S010", "y")],
        );
        for side in [&mut s.lean_sites, &mut s.rust_sites] {
            *side = vec![
                site("a", "S001", Some(one)),
                site("a", "S001", Some(two)),
                site("a", "S001", Some("`@{}` takes a name; bind it with `let`")),
                site("a", "S001", Some("`@ports` takes a name")),
                site("a", "S010", Some(fix)),
            ];
        }
        let got = messages(&rows, &s, &[]);
        assert!(got.iter().all(|m| !m.contains("error text")), "{got:?}");
        s.rust_sites.push(site(
            "a",
            "S001",
            Some("`@typeInfo` takes a name; bind it with `let`"),
        ));
        let got: Vec<String> = messages(&rows, &s, &[])
            .into_iter()
            .filter(|m| m.contains("error text"))
            .collect();
        assert_eq!(got.len(), 1, "{got:?}");
        assert!(
            got[0].starts_with("the Rust error text `S001 `@typeInfo` takes"),
            "{got:?}"
        );
    }

    #[test]
    fn the_checked_in_tree_passes() {
        let repo = Repo::discover().unwrap();
        assert_eq!(check(&repo).unwrap(), Vec::new());
    }
}
