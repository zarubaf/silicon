//! Builds the vale vocabulary from the `CONTEXT.md` glossary.

use std::collections::BTreeSet;
use std::path::Path;

use anyhow::{Context, Result};

use crate::repo::Repo;

/// The glossary, relative to the repository root.
pub const GLOSSARY: &str = "CONTEXT.md";
/// The vale vocabulary directory that `.vale.ini` names with `Vocab = Silicon`.
const VOCAB_DIR: &str = ".vale/styles/config/vocabularies/Silicon";

/// The accepted terms and the rejected synonyms of the glossary.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Vocab {
    pub accept: Vec<String>,
    pub reject: Vec<String>,
}

/// Reads each `### <term>` heading as an accepted term and each `_Avoid_:` line as rejected words.
pub fn parse(context_md: &str) -> Vocab {
    let mut accept = BTreeSet::new();
    let mut reject = BTreeSet::new();
    for line in context_md.lines() {
        if let Some(term) = line.strip_prefix("### ") {
            accept.insert(term.trim().to_string());
        } else if let Some(words) = line.strip_prefix("_Avoid_:") {
            reject.extend(
                words
                    .split(',')
                    .map(str::trim)
                    .filter(|w| !w.is_empty())
                    .map(str::to_string),
            );
        }
    }
    Vocab {
        accept: accept.into_iter().collect(),
        reject: reject.into_iter().collect(),
    }
}

/// Regenerates `accept.txt` and `reject.txt` from the glossary.
pub fn write(repo: &Repo) -> Result<()> {
    let vocab = parse(&repo.read(Path::new(GLOSSARY))?);
    let dir = repo.root.join(VOCAB_DIR);
    std::fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;
    for (name, entries) in [("accept.txt", &vocab.accept), ("reject.txt", &vocab.reject)] {
        let path = dir.join(name);
        std::fs::write(&path, lines(entries))
            .with_context(|| format!("writing {}", path.display()))?;
    }
    Ok(())
}

/// Writes one vale entry per line. Vale reads each entry as a regular expression.
fn lines(entries: &[String]) -> String {
    let mut out = String::new();
    for entry in entries {
        out.push_str(&pattern(entry));
        out.push('\n');
    }
    out
}

/// Escapes a term. A lowercase term also matches with a capital first letter at the start of a sentence.
fn pattern(term: &str) -> String {
    let mut chars = term.chars();
    match chars.next() {
        Some(first) if first.is_lowercase() => {
            let upper: String = first.to_uppercase().collect();
            format!("[{upper}{first}]{}", regex::escape(chars.as_str()))
        }
        _ => regex::escape(term),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(items: &[&str]) -> Vec<String> {
        items.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn parses_terms_and_avoid_lines() {
        let md = "# Glossary\n\n### register\n\nA state element.\n\n_Avoid_: flop, flip-flop\n";
        assert_eq!(
            parse(md),
            Vocab {
                accept: strings(&["register"]),
                reject: strings(&["flip-flop", "flop"]),
            }
        );
    }

    #[test]
    fn avoid_line_optional() {
        let md = "### core IR\n\nThe central representation.\n\n### module\n\nA unit.\n";
        assert_eq!(
            parse(md),
            Vocab {
                accept: strings(&["core IR", "module"]),
                reject: Vec::new(),
            }
        );
    }

    #[test]
    fn terms_sorted_and_deduplicated() {
        let md =
            "### memory\n\n_Avoid_: RAM, array\n\n### design\n\n_Avoid_: array\n\n### memory\n";
        assert_eq!(
            parse(md),
            Vocab {
                accept: strings(&["design", "memory"]),
                reject: strings(&["RAM", "array"]),
            }
        );
    }

    #[test]
    fn lowercase_terms_match_a_capital_first_letter() {
        assert_eq!(
            lines(&strings(&["core IR", "LEC", "flip-flop"])),
            "[Cc]ore IR\nLEC\n[Ff]lip\\-flop\n"
        );
    }

    #[test]
    fn heading_levels_other_than_3_ignored() {
        let md = "# Title\n\n## Section\n\n#### Detail\n\n### edition\n";
        assert_eq!(
            parse(md),
            Vocab {
                accept: strings(&["edition"]),
                reject: Vec::new(),
            }
        );
    }
}
