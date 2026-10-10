//! `review-due`: is a drift review due?
//!
//! Rule: a review is due when the branch has no `arch-review/<date>` tag,
//! or when 15 pull requests merged since the newest tag, or when the tag is
//! at least 7 days old. Git alone cannot count rebase-merged pull requests:
//! the merge keeps no merge commit and no pull request number. So `gh`
//! lists the merged pull requests with the commit that each one landed, and
//! git decides which of those commits come after the tag.

use std::collections::HashSet;
use std::path::Path;

use anyhow::{Context, Result, bail};

use crate::repo::git;

pub const MAX_PULL_REQUESTS: usize = 15;
/// The most pull requests that one `gh` query returns.
const GH_LIMIT: usize = 1000;
const MAX_AGE_SECONDS: i64 = 7 * 24 * 60 * 60;
const TAG_PREFIX: &str = "arch-review/";

/// The review tag that `branch` contains and that has the newest date in its name.
#[derive(Debug, PartialEq, Eq)]
pub struct Baseline {
    pub tag: String,
    /// Creation time in seconds since the epoch.
    pub created: i64,
    /// Committer time of the tagged commit. A review can end days after it.
    pub commit_time: i64,
}

/// A merged pull request and the commit at its tip on the target branch.
#[derive(Debug, PartialEq, Eq)]
pub struct MergedPr {
    pub number: u64,
    pub commit: String,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Verdict {
    /// Why a review is due. Empty when none is due.
    pub reasons: Vec<String>,
    pub summary: String,
}

/// The sort key of `arch-review/YYYY-MM-DD` or `arch-review/YYYY-MM-DD.N`.
/// N starts at 2 for a second review on one day; a tag without N is 1.
fn review_key(name: &str) -> Option<(String, u32)> {
    let rest = name.strip_prefix(TAG_PREFIX)?;
    let (date, seq) = match rest.split_once('.') {
        Some((date, n)) => {
            let ok = !n.is_empty() && !n.starts_with('0') && n.bytes().all(|b| b.is_ascii_digit());
            let n: u32 = if ok { n.parse().ok()? } else { return None };
            if n < 2 {
                return None;
            }
            (date, n)
        }
        None => (rest, 1),
    };
    let shape = |i: usize, c: char| {
        if matches!(i, 4 | 7) {
            c == '-'
        } else {
            c.is_ascii_digit()
        }
    };
    (date.len() == 10 && date.chars().enumerate().all(|(i, c)| shape(i, c)))
        .then(|| (date.to_owned(), seq))
}

fn is_review_tag(name: &str) -> bool {
    review_key(name).is_some()
}

fn tags(root: &Path, merged: Option<&str>) -> Result<Vec<(String, String)>> {
    let mut args = vec!["for-each-ref"];
    if let Some(branch) = merged {
        args.extend(["--merged", branch]);
    }
    args.extend([
        "--format=%(refname:short) %(creatordate:unix)",
        "refs/tags/arch-review/",
    ]);
    let text = String::from_utf8(git(root, &args)?)?;
    text.lines()
        .map(|line| {
            let (tag, created) = line
                .split_once(' ')
                .with_context(|| format!("malformed tag line {line:?}"))?;
            Ok((tag.to_owned(), created.to_owned()))
        })
        .collect()
}

/// Fails on a tag `arch-review/*` whose name is not a date.
pub fn latest_review_tag(root: &Path, branch: &str) -> Result<Option<Baseline>> {
    for (tag, _) in tags(root, None)? {
        if !is_review_tag(&tag) {
            bail!(
                "the tag `{tag}` is not named `{TAG_PREFIX}YYYY-MM-DD` or `{TAG_PREFIX}YYYY-MM-DD.N`"
            );
        }
    }
    let Some((tag, created)) = tags(root, Some(branch))?
        .into_iter()
        .max_by_key(|(tag, _)| review_key(tag))
    else {
        return Ok(None);
    };
    let created = created
        .parse()
        .with_context(|| format!("malformed tag time {created:?}"))?;
    let spec = format!("{tag}^{{commit}}");
    let commit_time = String::from_utf8(git(root, &["log", "-1", "--format=%ct", &spec])?)?;
    let commit_time = commit_time
        .trim()
        .parse()
        .with_context(|| format!("malformed commit time {commit_time:?}"))?;
    Ok(Some(Baseline {
        tag,
        created,
        commit_time,
    }))
}

/// The commits of `branch` after the tag, or all of them without a tag.
fn commits_since(root: &Path, branch: &str, tag: Option<&str>) -> Result<HashSet<String>> {
    let range = tag.map_or_else(|| branch.to_owned(), |t| format!("{t}..{branch}"));
    let out = git(root, &["rev-list", &range])?;
    Ok(String::from_utf8(out)?.lines().map(str::to_owned).collect())
}

/// Parses the lines `<number> <commit>` that [`merged_prs`] asks `gh` for.
pub fn parse_prs(text: &str) -> Result<Vec<MergedPr>> {
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let (number, commit) = line
                .split_once(' ')
                .with_context(|| format!("malformed pull request line {line:?}"))?;
            Ok(MergedPr {
                number: number
                    .parse()
                    .with_context(|| format!("malformed pull request number {number:?}"))?,
                commit: commit.to_owned(),
            })
        })
        .collect()
}

/// Asks GitHub for the pull requests merged into `base`.
///
/// `merged_since` is a UTC date `YYYY-MM-DD`. The server filters by merge
/// time, so an old pull request that merged late is not cut off by the limit.
pub fn merged_prs(root: &Path, base: &str, merged_since: &str) -> Result<Vec<MergedPr>> {
    let search = format!("merged:>={merged_since}");
    let out = std::process::Command::new("gh")
        .args([
            "pr",
            "list",
            "--state",
            "merged",
            "--base",
            base,
            "--search",
            &search,
            "--limit",
            &GH_LIMIT.to_string(),
            "--json",
            "number,mergeCommit",
            "--jq",
            r#".[] | select(.mergeCommit != null) | "\(.number) \(.mergeCommit.oid)""#,
        ])
        .current_dir(root)
        .output()
        .context("running gh; review-due needs it to count merged pull requests")?;
    if !out.status.success() {
        bail!(
            "gh pr list failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    parse_prs(&String::from_utf8(out.stdout)?)
}

/// Applies the rule. `since` holds the commits after the baseline.
pub fn evaluate(
    baseline: Option<&Baseline>,
    now: i64,
    prs: &[MergedPr],
    since: &HashSet<String>,
) -> Verdict {
    let count = prs.iter().filter(|pr| since.contains(&pr.commit)).count();
    let mut reasons = Vec::new();
    let summary = match baseline {
        None => {
            reasons.push("no arch-review tag exists yet".to_owned());
            "no review tag".to_owned()
        }
        Some(base) => {
            let days = (now - base.created).max(0) / (24 * 60 * 60);
            if count >= MAX_PULL_REQUESTS {
                reasons.push(format!(
                    "{count} pull requests merged, limit {MAX_PULL_REQUESTS}"
                ));
            }
            if now - base.created >= MAX_AGE_SECONDS {
                reasons.push(format!("{days} days since {}, limit 7", base.tag));
            }
            format!(
                "{count} merged pull request(s) and {days} day(s) since {}",
                base.tag
            )
        }
    };
    Verdict { reasons, summary }
}

/// Fetches the base branch and the tags, so a stale local ref cannot hide merged pull requests.
pub fn fetch(root: &Path, base: &str) -> Result<()> {
    git(root, &["fetch", "--quiet", "--tags", "origin", base]).map(drop)
}

/// Fails when a pull request commit is not a local object: git could not
/// then tell whether it came after the tag, and the count would be too low.
fn require_local(root: &Path, prs: &[MergedPr]) -> Result<()> {
    for pr in prs {
        let spec = format!("{}^{{commit}}", pr.commit);
        if git(root, &["cat-file", "-e", &spec]).is_err() {
            bail!(
                "the commit {} of pull request #{} is not in this clone; fetch the full history",
                pr.commit,
                pr.number
            );
        }
    }
    Ok(())
}

/// The UTC date one day before `seconds`. The caller passes the committer
/// time of the tagged commit: every pull request merged after that commit
/// has a later merge time, so the window holds all of them even when the
/// review ended days later. The extra day covers clock skew and time zones;
/// git still decides which commits count.
fn search_date(seconds: i64) -> String {
    let days = seconds.div_euclid(86_400) - 1;
    // Civil date from days since 1970-01-01 (Howard Hinnant's algorithm).
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!("{year:04}-{month:02}-{day:02}")
}

/// Decides whether a review is due on `remote_ref` (for example `origin/main`).
/// `list_prs` returns the pull requests merged into the base branch. It does
/// not run when no tag exists, because the answer is "due" either way.
pub fn check(
    root: &Path,
    remote_ref: &str,
    now: i64,
    list_prs: impl FnOnce(&str) -> Result<Vec<MergedPr>>,
) -> Result<Verdict> {
    let baseline = latest_review_tag(root, remote_ref)?;
    let since = commits_since(root, remote_ref, baseline.as_ref().map(|b| b.tag.as_str()))?;
    if baseline.is_none() {
        return Ok(evaluate(None, now, &[], &since));
    }
    let prs = list_prs(&search_date(baseline.as_ref().map_or(0, |b| b.commit_time)))?;
    if prs.len() >= GH_LIMIT {
        bail!("gh returned {GH_LIMIT} pull requests, the query limit; the count may be incomplete");
    }
    if prs.is_empty() && !since.is_empty() {
        bail!(
            "gh lists no merged pull request, but `{remote_ref}` has {} new commit(s)",
            since.len()
        );
    }
    require_local(root, &prs)?;
    Ok(evaluate(baseline.as_ref(), now, &prs, &since))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testgit::{output, run};

    const DAY: i64 = 24 * 60 * 60;

    fn base(created: i64) -> Baseline {
        Baseline {
            tag: "arch-review/2026-10-01".into(),
            created,
            commit_time: created,
        }
    }

    fn prs(n: usize) -> (Vec<MergedPr>, HashSet<String>) {
        let list: Vec<MergedPr> = (0..n)
            .map(|i| MergedPr {
                number: i as u64,
                commit: format!("c{i}"),
            })
            .collect();
        let since = list.iter().map(|p| p.commit.clone()).collect();
        (list, since)
    }

    #[test]
    fn fresh_review_is_not_due() {
        let (list, since) = prs(14);
        let v = evaluate(Some(&base(0)), 7 * DAY - 1, &list, &since);
        assert!(v.reasons.is_empty(), "{v:?}");
    }

    #[test]
    fn fifteen_pull_requests_make_it_due() {
        let (list, since) = prs(15);
        let v = evaluate(Some(&base(0)), DAY, &list, &since);
        assert_eq!(v.reasons.len(), 1);
        assert!(v.reasons[0].contains("15 pull requests"));
    }

    #[test]
    fn seven_days_make_it_due() {
        let v = evaluate(Some(&base(0)), 7 * DAY, &[], &HashSet::new());
        assert_eq!(v.reasons.len(), 1);
        assert!(v.reasons[0].contains("7 days"));
    }

    #[test]
    fn both_limits_give_both_reasons() {
        let (list, since) = prs(20);
        assert_eq!(
            evaluate(Some(&base(0)), 9 * DAY, &list, &since)
                .reasons
                .len(),
            2
        );
    }

    #[test]
    fn pull_requests_before_the_tag_do_not_count() {
        let (list, _) = prs(20);
        let v = evaluate(Some(&base(0)), DAY, &list, &HashSet::new());
        assert!(v.reasons.is_empty());
    }

    #[test]
    fn no_tag_means_due() {
        let v = evaluate(None, 0, &[], &HashSet::new());
        assert_eq!(v.reasons, ["no arch-review tag exists yet"]);
    }

    #[test]
    fn parses_pull_request_lines() {
        let got = parse_prs("12 abc\n\n7 def\n").unwrap();
        assert_eq!(
            got,
            [
                MergedPr {
                    number: 12,
                    commit: "abc".into()
                },
                MergedPr {
                    number: 7,
                    commit: "def".into()
                },
            ]
        );
        assert!(parse_prs("x abc").is_err());
        assert!(parse_prs("12").is_err());
    }

    fn repo() -> tempfile::TempDir {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path();
        crate::testgit::init(dir);
        tmp
    }

    fn commit(dir: &Path, name: &str) -> String {
        run(dir, &["commit", "--quiet", "--allow-empty", "-m", name]);
        output(dir, &["rev-parse", "HEAD"])
    }

    #[test]
    fn newest_contained_tag_is_the_baseline() {
        let tmp = repo();
        let dir = tmp.path();
        commit(dir, "a");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-09-01"]);
        commit(dir, "b");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-10-01"]);
        commit(dir, "c");
        run(dir, &["switch", "--quiet", "-c", "side", "HEAD~1"]);
        commit(dir, "d");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-10-09"]);
        run(dir, &["switch", "--quiet", "main"]);
        let got = latest_review_tag(dir, "main").unwrap().unwrap();
        assert_eq!(got.tag, "arch-review/2026-10-01");
    }

    #[test]
    fn no_tag_gives_none() {
        let tmp = repo();
        commit(tmp.path(), "a");
        run(tmp.path(), &["tag", "other"]);
        assert_eq!(latest_review_tag(tmp.path(), "main").unwrap(), None);
    }

    #[test]
    fn only_commits_after_the_tag_count() {
        let tmp = repo();
        let dir = tmp.path();
        let before = commit(dir, "a");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-10-01"]);
        let after = commit(dir, "b");
        let got = commits_since(dir, "main", Some("arch-review/2026-10-01")).unwrap();
        assert!(got.contains(&after) && !got.contains(&before));
        assert_eq!(commits_since(dir, "main", None).unwrap().len(), 2);
    }

    #[test]
    fn a_tag_that_is_not_a_date_is_an_error() {
        let tmp = repo();
        let dir = tmp.path();
        commit(dir, "a");
        run(dir, &["tag", "arch-review/2026-10-01"]);
        run(dir, &["tag", "arch-review/latest"]);
        let message = latest_review_tag(dir, "main").unwrap_err().to_string();
        assert!(message.contains("arch-review/latest"), "{message}");
        for bad in [
            "arch-review/2026-1-01",
            "arch-review/2026-10-011",
            "arch-review/x026-10-01",
        ] {
            assert!(!is_review_tag(bad), "{bad}");
        }
        assert!(is_review_tag("arch-review/2026-10-01"));
    }

    #[test]
    fn a_second_review_on_one_day_has_a_sequence_number() {
        for good in ["arch-review/2026-10-10.2", "arch-review/2026-10-10.10"] {
            assert!(is_review_tag(good), "{good}");
        }
        for bad in [
            "arch-review/2026-10-10.",
            "arch-review/2026-10-10.0",
            "arch-review/2026-10-10.1",
            "arch-review/2026-10-10.02",
            "arch-review/2026-10-10.x",
        ] {
            assert!(!is_review_tag(bad), "{bad}");
        }
        let tmp = repo();
        let dir = tmp.path();
        commit(dir, "a");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-10-10"]);
        commit(dir, "b");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-10-10.2"]);
        commit(dir, "c");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-10-10.10"]);
        let got = latest_review_tag(dir, "main").unwrap().unwrap();
        assert_eq!(got.tag, "arch-review/2026-10-10.10");
    }

    fn tagged_repo() -> (tempfile::TempDir, String) {
        let tmp = repo();
        let dir = tmp.path();
        commit(dir, "a");
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-10-01"]);
        let landed = commit(dir, "b");
        (tmp, landed)
    }

    fn pr(number: u64, commit: &str) -> MergedPr {
        MergedPr {
            number,
            commit: commit.into(),
        }
    }

    #[test]
    fn counts_pull_requests_that_landed_after_the_tag() {
        let (tmp, landed) = tagged_repo();
        let v = check(tmp.path(), "main", 0, |_| Ok(vec![pr(1, &landed)])).unwrap();
        assert!(v.reasons.is_empty());
        assert!(v.summary.starts_with("1 merged"), "{}", v.summary);
    }

    #[test]
    fn a_pull_request_commit_missing_locally_is_an_error() {
        let (tmp, landed) = tagged_repo();
        let unknown = "0123456789012345678901234567890123456789";
        let result = check(tmp.path(), "main", 0, |_| {
            Ok(vec![pr(1, &landed), pr(2, unknown)])
        });
        let message = format!("{:#}", result.unwrap_err());
        assert!(
            message.contains("#2") && message.contains("not in this clone"),
            "{message}"
        );
    }

    #[test]
    fn no_pull_requests_for_new_commits_is_an_error() {
        let (tmp, _) = tagged_repo();
        assert!(check(tmp.path(), "main", 0, |_| Ok(Vec::new())).is_err());
    }

    #[test]
    fn without_a_tag_gh_is_not_called() {
        let tmp = repo();
        commit(tmp.path(), "a");
        let v = check(tmp.path(), "main", 0, |_| panic!("gh must not run")).unwrap();
        assert_eq!(v.reasons, ["no arch-review tag exists yet"]);
    }

    #[test]
    fn a_result_at_the_gh_limit_is_an_error() {
        let (tmp, landed) = tagged_repo();
        let full = (0..GH_LIMIT as u64).map(|n| pr(n, &landed)).collect();
        let message = check(tmp.path(), "main", 0, |_| Ok(full))
            .unwrap_err()
            .to_string();
        assert!(message.contains("incomplete"), "{message}");
    }

    #[test]
    fn the_search_date_is_one_utc_day_before_the_tag() {
        assert_eq!(search_date(0), "1969-12-31");
        // 2026-10-01T12:00:00Z
        assert_eq!(search_date(1_790_856_000), "2026-09-30");
        // 2024-03-01T00:00:00Z, after a leap day
        assert_eq!(search_date(1_709_251_200), "2024-02-29");
    }

    #[test]
    fn the_search_window_starts_at_the_tagged_commit() {
        let tmp = repo();
        let dir = tmp.path();
        let mut old = crate::gitcmd::git();
        old.args(["commit", "--quiet", "--allow-empty", "-m", "a"])
            .current_dir(dir)
            .env("GIT_COMMITTER_DATE", "2026-01-10T12:00:00Z");
        assert!(old.status().unwrap().success());
        run(dir, &["tag", "-a", "-m", "r", "arch-review/2026-01-20"]);
        let landed = commit(dir, "b");
        let mut asked = String::new();
        let v = check(dir, "main", i64::MAX / 2, |since| {
            since.clone_into(&mut asked);
            Ok((0..15).map(|n| pr(n, &landed)).collect())
        })
        .unwrap();
        assert_eq!(asked, "2026-01-09");
        assert!(
            v.reasons.iter().any(|r| r.contains("15 pull requests")),
            "{v:?}"
        );
    }
}
