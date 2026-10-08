# Commits

This guide gives the branch, commit, and merge conventions. [The foundation spec](../design/2026-10-08-repo-foundation.md), section 7, is the source.

## Task lifecycle

1. **Issue.** The issue template has three fields: Goal, Done criteria (mechanical), and Area.
2. **Worktree.** Claude Code creates it at `.claude/worktrees/<branch>`. The branch name is `<type>/<issue>-<slug>`, for example `feat/42-core-ir-memories`.
3. **Work.** Hand-off notes and plans go to `.scratch/`. Git ignores this directory, and it dies with the worktree.
4. **Pull request.** The pull request must pass `just ci` and the cross-vendor review. The orchestrator then rebase-merges it. History stays linear, and each commit stays separate.
5. **Cleanup.** The worktree and the branch are deleted.

The repository has no merge queue. The orchestrator merges only after CI passes on the pull request.

## Commit rules

1. The format is Conventional Commits: `type(scope): subject`.
2. The type is one of `feat`, `fix`, `refactor`, `perf`, `test`, `docs`, `build`, `ci`, `chore`, `style`, `revert`.
3. The scope is a crate name or one of `lean`, `doc`, `adr`, `ci`, `xtask`, `design`. A commit can have no scope.
4. The subject is imperative and has 72 characters or fewer.
5. The body states why and what the change means. It does not list files.
6. One commit holds one logical change.
7. A breaking change uses `!` and a `BREAKING CHANGE:` footer. No check enforces the footer. This rule is advisory.
8. No AI attribution: no `Co-Authored-By` trailer for an agent, no "Generated with" line.

Refactor first, then change behavior. Put the refactor in its own commit before the behavior change.

## Reverts and fixups

`commit-check` rejects the subjects that git writes for `git revert`, `git commit --fixup`, and `git commit --squash`:

- `Revert "<subject>"`
- `fixup! <subject>`
- `squash! <subject>`

Write a revert as `revert: <subject>`. Squash the fixup commits before the push.

## Checks

`cargo xtask commit-check` checks each commit in a range. CI runs it on each commit of a pull request. `just ci` runs it through `just commit-check`. Each violation prints its rule id:

| Rule id                        | Rejects                                                                       |
| ------------------------------ | ----------------------------------------------------------------------------- |
| `commit-subject`               | A subject that is not a Conventional Commit, including revert and fixup forms |
| `commit-scope`                 | A scope that is not in the allowed list                                       |
| `commit-length`                | A subject with more than 72 characters                                        |
| `commit-attribution`           | An agent `Co-Authored-By` trailer or a "Generated with" line                  |
| `commit-refactor-expectations` | A `refactor` commit that changes test expectations                            |
| `commit-spec-impl`             | A commit that changes `lean/` and `crates/` together                          |
| `commit-expectations-code`     | A commit that changes test expectations and non-test code together            |

Test expectations are the files under `snapshots/` directories and the `expected/` files of `tests/corpus/`.

## Hooks

`lefthook` runs the git hooks. Nix pins it. `lefthook.yml` calls `just` recipes only:

| Hook         | Recipe            |
| ------------ | ----------------- |
| `pre-commit` | `just fmt-check`  |
| `commit-msg` | `just commit-msg` |
| `pre-push`   | `just ci main`    |

The `commit-msg` hook runs the message rules: `commit-subject`, `commit-scope`, `commit-length`, and `commit-attribution`. The rules for changed paths run in `commit-check` only.
