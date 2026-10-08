# 9. Agents merge after a review by a model from a different vendor

- Status: accepted
- Date: 2026-10-08

## Context

Agents have merge authority at the start. A reviewer from the same model family as the author can share its blind spots. The repository is private on a personal GitHub account. It has no merge queue, and branch rules on a private repository need GitHub Pro.

## Decision

- A Codex adversarial review must pass on a branch that Claude wrote. It challenges the design, the assumptions, and the tradeoffs.
- An Opus review must pass on a branch that Codex wrote.
- The reviewer gets the diff and the spec. It does not get the reasoning of the author.
- The orchestrator rebase-merges a pull request only after CI passes and the review passes.

## Consequences

- The cross-vendor review is advisory until a GitHub check exists. The pull request template has a checkbox for it.
- A merge queue replaces the manual merge step when the repository moves to an organization.
- A later ADR adds human approval gates. The handoff note gives three areas for the human: the core IR semantics, the language design decisions, and the trust boundary.
