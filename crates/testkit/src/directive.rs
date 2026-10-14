// SPDX-License-Identifier: Apache-2.0
//! The directives of a test file: `expected-error XNNN @+N` (spec section 9), `TOP`, and the
//! budgets `FUEL`, `DEPTH`, and `SYNTAX-DEPTH`.

/// The comment marker of a source language.
#[derive(Clone, Copy)]
pub enum Marker {
    /// A `.sil` file: `; expected-error`.
    Sil,
    /// A `.si` file: `// expected-error`.
    Si,
}

impl Marker {
    /// The comment prefix.
    #[must_use]
    pub fn prefix(self) -> &'static str {
        match self {
            Marker::Sil => ";",
            Marker::Si => "//",
        }
    }
}

/// True when a line of `source` holds a `FileCheck` directive: `<marker> CHECK`, then `:` or one
/// of the suffixes `-NEXT`, `-NOT`, `-DAG`, `-LABEL`, `-SAME`, `-EMPTY`, and `-COUNT-<n>`, then `:`.
pub(crate) fn has_check(source: &str, marker: Marker) -> bool {
    has_prefix(source, marker, "CHECK")
}

/// True when a line of `source` holds a `FileCheck` directive of the prefix `OBSERVE`, which
/// checks the output of `observe` (section 11.3).
pub(crate) fn has_observe(source: &str, marker: Marker) -> bool {
    has_prefix(source, marker, "OBSERVE")
}

/// True when a line of `source` holds a `FileCheck` directive of the prefix `prefix`.
fn has_prefix(source: &str, marker: Marker, prefix: &str) -> bool {
    let head = format!("{} {prefix}", marker.prefix());
    source.lines().any(|line| {
        line.match_indices(&head).any(|(at, _)| {
            let rest = &line[at + head.len()..];
            let suffix = rest.split(':').next().unwrap_or_default();
            rest.contains(':') && is_check_suffix(suffix)
        })
    })
}

fn is_check_suffix(suffix: &str) -> bool {
    match suffix.strip_prefix("-COUNT-") {
        Some(n) => !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()),
        None => ["", "-NEXT", "-NOT", "-DAG", "-LABEL", "-SAME", "-EMPTY"].contains(&suffix),
    }
}

const KEYWORD: &str = " expected-error ";
const MESSAGE_KEYWORD: &str = " expected-message: ";

/// The expected error of a file: its code, its 1-based line, and the exact message when the file
/// has an `expected-message` directive.
#[derive(Debug, PartialEq, Eq)]
pub struct Expected {
    pub code: String,
    pub line: usize,
    pub message: Option<String>,
}

/// Parses `XNNN @+N` or `XNNN @-N` on the 1-based line `at`.
fn parse_directive(rest: &str, at: usize, marker: &str) -> Result<Expected, String> {
    let bad = || format!("line {at}: malformed directive `{marker}{KEYWORD}{rest}`");
    let (code, offset) = rest.trim().split_once(" @").ok_or_else(bad)?;
    let valid_code = code.len() == 4
        && code.starts_with(|c: char| c.is_ascii_uppercase())
        && code[1..].bytes().all(|b| b.is_ascii_digit());
    if !valid_code {
        return Err(bad());
    }
    let (sign, digits) = offset.split_at_checked(1).ok_or_else(bad)?;
    let n: usize = digits.parse().map_err(|_| bad())?;
    let line = match sign {
        "+" if n >= 1 => at.checked_add(n),
        "-" if n >= 1 => at.checked_sub(n).filter(|&l| l >= 1),
        _ => None,
    }
    .ok_or_else(bad)?;
    Ok(Expected {
        code: code.to_owned(),
        line,
        message: None,
    })
}

/// The directive of a file. `None` means the file must pass. The line `<marker> expected-message:
/// <text>` directly after the `expected-error` line sets the exact message.
///
/// # Errors
///
/// Returns a message when a directive is malformed, a file has more than one of either kind, or
/// an `expected-message` does not follow an `expected-error` line directly.
pub fn expected_error(source: &str, marker: Marker) -> Result<Option<Expected>, String> {
    let prefix = marker.prefix();
    let mut found = None;
    let mut message = None;
    for (index, text) in source.lines().enumerate() {
        let text = text.trim_start().strip_prefix(prefix);
        if let Some(rest) = text.and_then(|r| r.strip_prefix(MESSAGE_KEYWORD)) {
            if message.is_some() {
                return Err(format!("line {}: a second expected-message", index + 1));
            }
            let rest = rest.trim_end();
            if rest.is_empty() {
                return Err(format!("line {}: an empty expected-message", index + 1));
            }
            message = Some((index, rest.to_owned()));
        } else if let Some(rest) = text.and_then(|r| r.strip_prefix(KEYWORD)) {
            if found.is_some() {
                return Err(format!("line {}: a second directive", index + 1));
            }
            found = Some((index, parse_directive(rest, index + 1, prefix)?));
        }
    }
    match (found, message) {
        (None, None) => Ok(None),
        (None, Some((at, _))) => Err(format!(
            "line {}: an expected-message without an expected-error",
            at + 1
        )),
        (Some((_, expected)), None) => Ok(Some(expected)),
        (Some((error_at, expected)), Some((at, text))) if at == error_at + 1 => {
            Ok(Some(Expected {
                message: Some(text),
                ..expected
            }))
        }
        (Some(_), Some((at, _))) => Err(format!(
            "line {}: an expected-message not directly after the expected-error",
            at + 1
        )),
    }
}

/// What a file expects of `run`.
pub(crate) enum Expectation {
    /// The stdin lines and the expected stdout.
    Steps {
        stdin: String,
        stdout: String,
    },
    Error(Expected),
}

/// Parses the `STEP in=(...) out=(...)` lines of `source`, each with its LF.
///
/// # Errors
///
/// Returns a message when a STEP line is malformed.
pub(crate) fn steps(source: &str, marker: Marker) -> Result<(String, String), String> {
    let prefix = format!("{} STEP ", marker.prefix());
    let mut stdin = String::new();
    let mut stdout = String::new();
    for (index, text) in source.lines().enumerate() {
        let Some(rest) = text.trim_start().strip_prefix(prefix.as_str()) else {
            continue;
        };
        let (input, output) = rest
            .split_once(" out=")
            .filter(|(input, _)| input.starts_with("in="))
            .ok_or_else(|| format!("line {}: malformed STEP line", index + 1))?;
        stdin.push_str(input.trim_end());
        stdin.push('\n');
        stdout.push_str("out=");
        stdout.push_str(output.trim_end());
        stdout.push('\n');
    }
    Ok((stdin, stdout))
}

/// The expectation of a `run` file: STEP lines or one `expected-error`, never both and never
/// neither.
///
/// # Errors
///
/// Returns a message when a directive is malformed or the file has both kinds or neither.
pub(crate) fn expectation(source: &str, marker: Marker) -> Result<Expectation, String> {
    let (stdin, stdout) = steps(source, marker)?;
    match (expected_error(source, marker)?, stdin.is_empty()) {
        (None, false) => Ok(Expectation::Steps { stdin, stdout }),
        (Some(error), true) => Ok(Expectation::Error(error)),
        (None, true) => Err("no STEP line and no expected-error".to_owned()),
        (Some(_), false) => Err("both STEP lines and an expected-error".to_owned()),
    }
}

const TOP: &str = "// TOP ";

/// The top selection of a `.si` file: the text after `// TOP `.
///
/// # Errors
///
/// Returns a message when the file has no `TOP` line or more than one.
pub fn top(source: &str) -> Result<String, String> {
    let mut found = None;
    for (index, text) in source.lines().enumerate() {
        let Some(rest) = text.trim_start().strip_prefix(TOP) else {
            continue;
        };
        if found.is_some() {
            return Err(format!("line {}: a second TOP line", index + 1));
        }
        found = Some(rest.trim().to_owned());
    }
    found.ok_or_else(|| "no TOP line".to_owned())
}

/// The kind of a budget directive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BudgetKind {
    Fuel,
    Depth,
    SyntaxDepth,
}

impl BudgetKind {
    const ALL: [(BudgetKind, &'static str); 3] = [
        (BudgetKind::Fuel, "// FUEL "),
        (BudgetKind::Depth, "// DEPTH "),
        (BudgetKind::SyntaxDepth, "// SYNTAX-DEPTH "),
    ];

    /// The `elab` flag that sets the budget.
    pub(crate) fn flag(self) -> &'static str {
        match self {
            BudgetKind::Fuel => "--fuel",
            BudgetKind::Depth => "--depth",
            BudgetKind::SyntaxDepth => "--syntax-depth",
        }
    }

    /// The error code when the budget runs out.
    pub(crate) fn code(self) -> &'static str {
        match self {
            BudgetKind::Fuel | BudgetKind::Depth => "S015",
            BudgetKind::SyntaxDepth => "S001",
        }
    }
}

/// A budget directive: the file passes with `limit` and fails with `limit - 1`.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Budget {
    pub kind: BudgetKind,
    pub limit: u64,
}

/// The budget directives of a `.si` file, in file order.
///
/// # Errors
///
/// Returns a message when a limit is not a number of at least 1, or a kind occurs twice.
pub(crate) fn budgets(source: &str) -> Result<Vec<Budget>, String> {
    let mut found: Vec<Budget> = Vec::new();
    for (index, text) in source.lines().enumerate() {
        let text = text.trim_start();
        let Some((kind, rest)) = BudgetKind::ALL
            .iter()
            .find_map(|&(kind, prefix)| Some((kind, text.strip_prefix(prefix)?)))
        else {
            continue;
        };
        let limit = rest
            .trim()
            .parse::<u64>()
            .ok()
            .filter(|&limit| limit >= 1)
            .ok_or_else(|| format!("line {}: malformed budget `{text}`", index + 1))?;
        if found.iter().any(|budget| budget.kind == kind) {
            return Err(format!("line {}: a second {kind:?} budget", index + 1));
        }
        found.push(Budget { kind, limit });
    }
    Ok(found)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn has_check_accepts_every_form() {
        for form in [
            "CHECK:",
            "CHECK-NEXT:",
            "CHECK-NOT:",
            "CHECK-DAG:",
            "CHECK-LABEL:",
            "CHECK-SAME:",
            "CHECK-EMPTY:",
            "CHECK-COUNT-2:",
        ] {
            let source = format!("// {form} x\n");
            assert!(has_check(&source, Marker::Si), "{form}");
        }
        assert!(has_check("; CHECK-COUNT-2: x\n", Marker::Sil));
    }

    #[test]
    fn has_observe_takes_its_own_prefix_only() {
        for form in [
            "OBSERVE:",
            "OBSERVE-NEXT:",
            "OBSERVE-NOT:",
            "OBSERVE-COUNT-31:",
        ] {
            let source = format!("// {form} x\n");
            assert!(has_observe(&source, Marker::Si), "{form}");
            assert!(!has_check(&source, Marker::Si), "{form}");
        }
        assert!(!has_observe("// CHECK: x\n", Marker::Si));
        assert!(!has_observe("// OBSERVED: x\n", Marker::Si));
        assert!(!has_observe("// OBSERVE x\n", Marker::Si));
    }

    #[test]
    fn has_check_rejects_other_text() {
        for line in [
            "// CHECK",
            "// CHECK-COUNT-: x",
            "// CHECK-COUNT-a: x",
            "// CHECKED: x",
        ] {
            assert!(!has_check(line, Marker::Si), "{line}");
        }
        assert!(!has_check("// CHECK: x\n", Marker::Sil));
    }

    #[test]
    fn expected_error_reads_both_markers() {
        assert_eq!(
            expected_error("; expected-error E004 @+1\nx", Marker::Sil),
            Ok(Some(Expected {
                code: "E004".to_owned(),
                line: 2,
                message: None
            }))
        );
        assert_eq!(
            expected_error("a\nb\n// expected-error S010 @-1", Marker::Si),
            Ok(Some(Expected {
                code: "S010".to_owned(),
                line: 2,
                message: None
            }))
        );
    }

    #[test]
    fn a_file_without_a_directive_must_pass() {
        assert_eq!(expected_error("x\n", Marker::Sil), Ok(None));
        assert_eq!(
            expected_error("; expected-error E004 @+1", Marker::Si),
            Ok(None)
        );
    }

    #[test]
    fn a_second_directive_is_an_error() {
        let source = "; expected-error E004 @+2\n; expected-error E005 @+1\nx";
        assert_eq!(
            expected_error(source, Marker::Sil),
            Err("line 2: a second directive".to_owned())
        );
    }

    #[test]
    fn expected_message_follows_the_error_line() {
        let source = "// expected-error S016 @+2\n// expected-message: a: b c \nx";
        let got = expected_error(source, Marker::Si).unwrap().unwrap();
        assert_eq!(got.message.as_deref(), Some("a: b c"));
        let sil = "; expected-error S016 @+2\n; expected-message: m\nx";
        let got = expected_error(sil, Marker::Sil).unwrap().unwrap();
        assert_eq!(got.message.as_deref(), Some("m"));
    }

    #[test]
    fn a_bad_expected_message_is_an_error() {
        let error = "// expected-error S016 @+2\n";
        for source in [
            format!("{error}// expected-message: a\n// expected-message: b\n"),
            "// expected-message: a\n".to_owned(),
            format!("{error}\n// expected-message: a\n"),
            format!("// expected-message: a\n{error}"),
            format!("{error}// expected-message: \n"),
        ] {
            assert!(expected_error(&source, Marker::Si).is_err(), "{source:?}");
        }
    }

    #[test]
    fn top_reads_one_line() {
        assert_eq!(
            top("// TOP Counter(8, true)\nmodule ..."),
            Ok("Counter(8, true)".to_owned())
        );
    }

    #[test]
    fn top_needs_exactly_one() {
        assert!(top("module M() {}\n").unwrap_err().contains("no TOP"));
        assert!(
            top("// TOP M()\n// TOP N()\n")
                .unwrap_err()
                .contains("line 2")
        );
    }

    #[test]
    fn budgets_reads_each_kind() {
        assert_eq!(
            budgets("// FUEL 161\n// DEPTH 301\n// SYNTAX-DEPTH 10"),
            Ok(vec![
                Budget {
                    kind: BudgetKind::Fuel,
                    limit: 161
                },
                Budget {
                    kind: BudgetKind::Depth,
                    limit: 301
                },
                Budget {
                    kind: BudgetKind::SyntaxDepth,
                    limit: 10
                },
            ])
        );
    }

    #[test]
    fn budgets_rejects_bad_lines() {
        for source in ["// FUEL 0", "// FUEL x", "// FUEL 1\n// FUEL 2"] {
            assert!(budgets(source).is_err(), "{source:?}");
        }
    }

    #[test]
    fn a_malformed_directive_is_an_error() {
        for source in [
            "; expected-error E004",
            "; expected-error E04 @+1",
            "; expected-error 1004 @+1",
            "; expected-error E004 @+0",
            "; expected-error E004 @*1",
            "; expected-error E004 @-1",
            "; expected-error E004 @+x",
        ] {
            assert!(expected_error(source, Marker::Sil).is_err(), "{source:?}");
        }
    }

    #[test]
    fn steps_reads_both_markers() {
        assert_eq!(
            steps("; STEP in=(a 1) out=(b 2)", Marker::Sil),
            Ok(("in=(a 1)\n".to_owned(), "out=(b 2)\n".to_owned()))
        );
        assert_eq!(
            steps("// STEP in=(a 1) out=(b 2)", Marker::Si),
            Ok(("in=(a 1)\n".to_owned(), "out=(b 2)\n".to_owned()))
        );
    }

    #[test]
    fn run_needs_steps_or_an_error() {
        let steps = "// STEP in=(a 1) out=(b 2)\n";
        let error = "// expected-error S010 @+1\nx\n";
        assert!(matches!(
            expectation(steps, Marker::Si),
            Ok(Expectation::Steps { .. })
        ));
        assert!(matches!(
            expectation(error, Marker::Si),
            Ok(Expectation::Error(_))
        ));
        assert!(expectation("x\n", Marker::Si).is_err());
        assert!(expectation(&format!("{steps}{error}"), Marker::Si).is_err());
    }
}
