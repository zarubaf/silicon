// SPDX-License-Identifier: Apache-2.0
//! The architecture paths: the one list in `doc/architecture.md`.

use anyhow::{Result, bail};

const HEADING: &str = "## Architecture review";
const LIST_INTRO: &str = "These are the architecture paths.";

/// One pattern of the list. A directory pattern ends in `/` and matches
/// every file below it. Other patterns match one file. `*` matches part
/// of one path segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern {
    segments: Vec<String>,
    directory: bool,
}

impl Pattern {
    pub fn parse(text: &str) -> Result<Self> {
        let directory = text.ends_with('/');
        let body = text.strip_suffix('/').unwrap_or(text);
        if body.is_empty() {
            bail!("empty architecture path `{text}`");
        }
        let valid = |c: char| c.is_ascii_alphanumeric() || "_.-*".contains(c);
        let segments: Vec<String> = body.split('/').map(str::to_owned).collect();
        for segment in &segments {
            if segment.is_empty() || segment == "." || segment == ".." {
                bail!("architecture path `{text}` has an empty, `.`, or `..` segment");
            }
            if let Some(bad) = segment.chars().find(|c| !valid(*c)) {
                bail!("architecture path `{text}` has the character `{bad}`");
            }
            if segment.contains("**") {
                bail!("architecture path `{text}` has `**`; `*` covers one segment only");
            }
        }
        Ok(Self {
            segments,
            directory,
        })
    }

    pub fn matches(&self, path: &str) -> bool {
        let parts: Vec<&str> = path.split('/').collect();
        let length_ok = if self.directory {
            parts.len() > self.segments.len()
        } else {
            parts.len() == self.segments.len()
        };
        length_ok
            && self
                .segments
                .iter()
                .zip(&parts)
                .all(|(pattern, part)| glob(pattern, part))
    }
}

/// Matches `text` against a segment where `*` stands for any run of characters.
fn glob(pattern: &str, text: &str) -> bool {
    let mut pieces = pattern.split('*');
    let first = pieces.next().unwrap_or_default();
    let Some(mut rest) = text.strip_prefix(first) else {
        return false;
    };
    let mut pieces: Vec<&str> = pieces.collect();
    let Some(last) = pieces.pop() else {
        return rest.is_empty();
    };
    for piece in pieces {
        let Some(at) = rest.find(piece) else {
            return false;
        };
        rest = &rest[at + piece.len()..];
    }
    rest.ends_with(last)
}

/// Reads the pattern list from the text of `doc/architecture.md`.
/// Every backtick span of a list item is a pattern.
pub fn parse(markdown: &str) -> Result<Vec<Pattern>> {
    let mut lines = markdown.lines();
    if !lines.any(|line| line.trim_end() == HEADING) {
        bail!("`doc/architecture.md` has no section `{HEADING}`");
    }
    let section = lines.take_while(|line| !line.starts_with("## "));
    let mut items = section
        .skip_while(|line| !line.contains(LIST_INTRO))
        .skip(1)
        .skip_while(|line| line.trim().is_empty())
        .take_while(|line| line.starts_with("- "))
        .peekable();
    if items.peek().is_none() {
        bail!("the section `{HEADING}` has no list after \"{LIST_INTRO}\"");
    }
    let mut patterns = Vec::new();
    for item in items {
        let spans: Vec<&str> = item.split('`').skip(1).step_by(2).collect();
        if spans.is_empty() {
            bail!("the architecture path item has no path in backticks: {item}");
        }
        for span in spans {
            patterns.push(Pattern::parse(span)?);
        }
    }
    Ok(patterns)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn doc(items: &str) -> String {
        format!(
            "# T\n\n{HEADING}\n\ntext\n\n{LIST_INTRO} More.\n\n{items}\n\n## Next\n\n- `other`\n"
        )
    }

    fn pattern(text: &str) -> Pattern {
        Pattern::parse(text).unwrap()
    }

    #[test]
    fn file_pattern_matches_only_that_file() {
        assert!(pattern("Cargo.toml").matches("Cargo.toml"));
        assert!(!pattern("Cargo.toml").matches("crates/a/Cargo.toml"));
    }

    #[test]
    fn star_covers_one_segment() {
        let p = pattern("crates/*/Cargo.toml");
        assert!(p.matches("crates/core-ir/Cargo.toml"));
        assert!(!p.matches("crates/a/b/Cargo.toml"));
        assert!(!p.matches("crates/Cargo.toml"));
    }

    #[test]
    fn star_inside_a_segment() {
        let p = pattern("lean/Silicon/*/Syntax.lean");
        assert!(p.matches("lean/Silicon/Core/Syntax.lean"));
        assert!(pattern("a/x*z").matches("a/xyz"));
        assert!(pattern("a/x*z").matches("a/xz"));
        assert!(!pattern("a/x*z").matches("a/xy"));
    }

    #[test]
    fn directory_matches_files_below_it() {
        let p = pattern("doc/adr/");
        assert!(p.matches("doc/adr/0013.md"));
        assert!(p.matches("doc/adr/sub/x.md"));
        assert!(!p.matches("doc/adr"));
        assert!(!p.matches("doc/adrift/x.md"));
    }

    #[test]
    fn malformed_patterns_fail() {
        for bad in [
            "", "/", "/abs", "a//b", "a/../b", "a/**/b", "a b", "a?", "./a",
        ] {
            assert!(Pattern::parse(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn reads_every_span_of_the_list_only() {
        let text = doc("- `a` and each `b/c`\n- The rest: `d/`, and `e*`");
        let got = parse(&text).unwrap();
        assert_eq!(got, ["a", "b/c", "d/", "e*"].map(pattern));
    }

    #[test]
    fn missing_section_fails() {
        let message = parse("# T\n").unwrap_err().to_string();
        assert!(message.contains("no section"), "{message}");
    }

    #[test]
    fn missing_list_fails() {
        let message = parse(&format!("{HEADING}\n\nnothing\n"))
            .unwrap_err()
            .to_string();
        assert!(message.contains("no list"), "{message}");
    }

    #[test]
    fn item_without_span_fails() {
        let message = parse(&doc("- `a`\n- prose only")).unwrap_err().to_string();
        assert!(message.contains("no path in backticks"), "{message}");
    }

    #[test]
    fn malformed_pattern_in_list_fails() {
        assert!(parse(&doc("- `a/**`")).is_err());
    }

    #[test]
    fn the_real_list_parses() {
        let text = include_str!("../../../doc/architecture.md");
        let patterns = parse(text).unwrap();
        assert!(patterns.iter().any(|p| p.matches("xtask/src/main.rs")));
        assert!(
            patterns
                .iter()
                .any(|p| p.matches("crates/core-ir/AGENTS.md"))
        );
        assert!(
            patterns
                .iter()
                .any(|p| p.matches("lean/Silicon/Core/Mlir/Print.lean"))
        );
        assert!(
            !patterns
                .iter()
                .any(|p| p.matches("crates/core-ir/src/ast.rs"))
        );
    }
}
