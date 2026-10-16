# Agents

This guide is the authority for orchestration and model choice.

## Orchestrator

The orchestrator is the main Claude Code session, the lead. The user chooses its model for each session. It does these tasks:

- It reads issues and splits the work.
- It creates worktrees and dispatches subagents.
- It reads the results of the subagents and merges.

The orchestrator does not write product code. It does not read large file dumps. A search goes to the `@explorer` subagent.

## Workflow

The workflow is the Superpowers workflow:

1. `brainstorming`
2. `writing-plans`
3. `subagent-driven-development` in a worktree
4. `finishing-a-development-branch`

The repository defines no custom agent roles at the start. A role file in `.claude/agents/` comes into existence only when the same need shows up twice.

## Rules

The repository adds three rules to the Superpowers workflow:

1. **Lean goes to a fresh Opus subagent.** The orchestrator dispatches all Lean work to a new Opus subagent, one bounded task at a time. The subagent does not get the chat history of the orchestrator. The reason: on a long proof, a Codex run ends after 5 to 20 minutes with partial work.
2. **Cross-vendor review before merge.** A Codex adversarial review (`adversarial-review --base main`) must pass on a branch that Claude wrote. It challenges the design, the assumptions, and the tradeoffs. Superpowers' own review covers defects. An Opus review must pass on a branch that Codex wrote. The reviewer gets the diff and the spec, not the reasoning of the author. See [ADR 0009](../adr/0009-cross-vendor-review-before-merge.md).
3. **Superpowers paths are overridden.** Specs go to `doc/design/`. Plans go to `.scratch/` in the worktree.

## Model choice

Model choice is advisory. The lead dispatches each subagent with the cheapest model that can do the job:

- Haiku for search and mechanical edits.
- Sonnet for Rust and integration work.
- Opus for Lean, design, and review.

`@code-reviewer` (Opus, read-only) audits plans and diffs. `@explorer` (Haiku, read-only) searches the code. Codex does the cross-vendor reviews.

`.codex/config.toml` pins the Codex model to `gpt-6-astra`. A change of the Codex model is a one-line change in that file. Codex reads this file for a trusted project.

## Subagents

A subagent gets the task, the root `AGENTS.md`, and the L1 file of its area. It gets no chat history.

A subagent returns a report of 20 lines or fewer. The report has three parts:

1. Changed: what the subagent changed.
2. Verified: how the subagent verified the change.
3. Open questions: what the subagent did not resolve.

## Codex and the development shell

Codex runs inside the development shell:

- Start Claude Code from a direnv-enabled shell in the repository. Codex then inherits the pinned toolchain.
- Codex never runs `nix develop`. Its sandbox cannot reach the Nix daemon.
- Codex cannot commit inside a git worktree. The orchestrator commits the Codex output after `just ci` passes.

Environment requirement: the tools of the development shell must come first on `PATH`. A login-shell profile can put another Rust toolchain before the Nix toolchain. Codex runs then fail.

## Plugins

`.claude/settings.json` pins the plugins through `extraKnownMarketplaces` and `enabledPlugins`. A fresh clone thus gets Superpowers and the Codex plugin. The same file disables commit attribution. It also makes the ASD-STE100 output style the default.
