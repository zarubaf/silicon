//! The reviewed inventory of what `lec` and `diff` run on the corpus. A SKIP
//! hides a check, and a vanished check hides a bug. Thus the inventory lists
//! every check with its outcome, and a run must match it exactly.

use std::collections::BTreeMap;

use anyhow::{Result, bail};

/// The key of a model check in the inventory. The check belongs to a memory
/// configuration, not to the first corpus file that uses it.
pub const MODEL_FILE: &str = "-";

/// What a check did without failing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    Pass,
    /// The tag is `#ISSUE` or an error code `ECODE`, and it names a gap of
    /// `doc/trust.md`.
    Skip(String),
}

/// One check: the corpus file (or [`MODEL_FILE`]), its name, and its verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    pub file: String,
    pub check: String,
    pub verdict: Verdict,
}

type Key = (String, String);

/// The inventory in `text`. Each line is `FILE CHECK PASS` or
/// `FILE CHECK SKIP TAG`. `CHECK` may hold spaces. Blank lines are ignored.
pub fn parse(text: &str) -> Result<Vec<(usize, Entry)>> {
    let mut entries = Vec::new();
    for (n, line) in text.lines().enumerate().map(|(n, l)| (n + 1, l)) {
        let words: Vec<&str> = line.split_whitespace().collect();
        let (file, check, verdict) = match words.as_slice() {
            [] => continue,
            [file, check @ .., "SKIP", tag] if !check.is_empty() => {
                if !is_tag(tag) {
                    bail!("line {n}: the tag `{tag}` is neither `#ISSUE` nor `ECODE`");
                }
                (file, check, Verdict::Skip((*tag).to_owned()))
            }
            [file, check @ .., "PASS"] if !check.is_empty() => (file, check, Verdict::Pass),
            _ => bail!("line {n}: expected `FILE CHECK PASS` or `FILE CHECK SKIP TAG`"),
        };
        entries.push((
            n,
            Entry {
                file: (*file).to_owned(),
                check: check.join(" "),
                verdict,
            },
        ));
    }
    Ok(entries)
}

/// Whether `tag` is `#` and digits, or `E` and digits.
fn is_tag(tag: &str) -> bool {
    let digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    tag.strip_prefix('#')
        .or_else(|| tag.strip_prefix('E'))
        .is_some_and(digits)
}

fn index(entries: impl IntoIterator<Item = Entry>) -> BTreeMap<Key, Verdict> {
    entries
        .into_iter()
        .map(|e| ((e.file, e.check), e.verdict))
        .collect()
}

/// The problems of a run against the inventory `text`. An empty result means
/// that the run is sound. Each check of `actual` must have exactly one line
/// with its verdict, and a run needs at least one PASS.
pub fn audit(text: &str, actual: &[Entry]) -> Result<Vec<String>> {
    let mut listed = BTreeMap::new();
    for (n, entry) in parse(text)? {
        let key = (entry.file, entry.check);
        if listed.insert(key.clone(), entry.verdict).is_some() {
            bail!("line {n}: duplicate entry for `{} {}`", key.0, key.1);
        }
    }
    let actual = index(actual.iter().cloned());
    let mut problems = Vec::new();
    if !actual.values().any(|v| *v == Verdict::Pass) {
        problems.push("no comparison ran".to_owned());
    }
    for (key, verdict) in &actual {
        match listed.get(key) {
            None => problems.push(format!("unlisted check: {} {} ({verdict:?})", key.0, key.1)),
            Some(want) if want != verdict => problems.push(format!(
                "changed check: {} {} is {verdict:?}, the inventory says {want:?}",
                key.0, key.1
            )),
            Some(_) => {}
        }
    }
    for key in listed.keys().filter(|k| !actual.contains_key(*k)) {
        problems.push(format!("listed check did not run: {} {}", key.0, key.1));
    }
    Ok(problems)
}

/// Prints each problem of [`audit`] against the inventory file `path`.
/// Returns whether the run is sound.
pub fn report(path: &str, problems: &[String]) -> bool {
    for problem in problems {
        println!("FAIL {problem} (inventory: {path})");
    }
    problems.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(file: &str, check: &str, verdict: Verdict) -> Entry {
        Entry {
            file: file.to_owned(),
            check: check.to_owned(),
            verdict,
        }
    }

    fn skip(tag: &str) -> Verdict {
        Verdict::Skip(tag.to_owned())
    }

    const INVENTORY: &str = "a.sil main SKIP #20\n\n- model silicon_mem PASS\nb.sil main PASS\n";

    fn run() -> Vec<Entry> {
        vec![
            entry("a.sil", "main", skip("#20")),
            entry("-", "model silicon_mem", Verdict::Pass),
            entry("b.sil", "main", Verdict::Pass),
        ]
    }

    #[test]
    fn the_checked_in_inventories_parse() {
        for text in [
            include_str!("../../tests/lec-checks.txt"),
            include_str!("../../tests/diff-checks.txt"),
        ] {
            assert!(!parse(text).unwrap().is_empty());
            audit(text, &[]).unwrap();
        }
    }

    #[test]
    fn a_matching_run_is_sound() {
        assert_eq!(audit(INVENTORY, &run()).unwrap(), Vec::<String>::new());
    }

    #[test]
    fn zero_comparisons_fail() {
        let only_skips = [entry("a.sil", "main", skip("#20"))];
        assert_eq!(
            audit("a.sil main SKIP #20", &only_skips).unwrap(),
            ["no comparison ran"]
        );
        assert_eq!(audit("", &[]).unwrap(), ["no comparison ran"]);
    }

    #[test]
    fn an_unlisted_check_fails() {
        let mut actual = run();
        actual.push(entry("c.sil", "main", skip("#20")));
        assert_eq!(
            audit(INVENTORY, &actual).unwrap(),
            ["unlisted check: c.sil main (Skip(\"#20\"))"]
        );
    }

    #[test]
    fn a_listed_check_that_did_not_run_fails() {
        let actual = &run()[..2];
        assert_eq!(
            audit(INVENTORY, actual).unwrap(),
            ["listed check did not run: b.sil main"]
        );
    }

    #[test]
    fn a_changed_verdict_or_tag_fails() {
        let mut actual = run();
        actual[0].verdict = Verdict::Pass;
        assert_eq!(audit(INVENTORY, &actual).unwrap().len(), 1);
        actual[0].verdict = skip("#21");
        assert_eq!(audit(INVENTORY, &actual).unwrap().len(), 1);
    }

    #[test]
    fn a_malformed_inventory_is_an_error() {
        for bad in [
            "a.sil PASS",
            "a.sil main",
            "a.sil main SKIP",
            "a.sil main SKIP 20",
            "a.sil main SKIP E",
            "a.sil main PASS\na.sil main SKIP #1",
        ] {
            assert!(audit(bad, &[]).is_err(), "{bad}");
        }
    }
}
