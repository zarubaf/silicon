# 13. Continuous architecture review

- Status: accepted
- Date: 2026-10-10

## Context

Many agents write code in parallel. [ADR 0009](0009-cross-vendor-review-before-merge.md) reviews each diff for defects. A review of one diff does not see slow drift. Examples are a stage that gets a second responsibility, an interface that grows, and a Lean definition and a Rust function that move apart.

The project rule is that a rule without a check is advisory.

## Decision

Continuous architecture review is a project goal. It has these triggers:

- **Pull request.** A pull request that touches an architecture path needs an architecture review in addition to the diff review. `doc/architecture.md` lists the architecture paths. `cargo xtask review-scope` classifies the diff.
- **Drift.** A drift review runs after 15 merged pull requests or after one week, whichever comes first. `cargo xtask review-due` reports a due review. The orchestrator runs it before each merge. `just ci` does not run it, because a time limit would make an old commit fail.
- **Milestone.** A full review runs at each milestone, for example at the end of a build step. Codex and Opus each do it independently. The orchestrator joins the two reports.

The reviewer is from a different vendor than the author and has fresh context. It gets `doc/architecture.md`, `doc/trust.md`, the ADRs, the specs, the diff since the last review, and the output of `cargo xtask arch-summary`. It never gets the reasoning of the author. It returns a report of at most 20 lines.

A finding goes to one of these places:

- A decision becomes an ADR.
- Work becomes an issue with the label `architecture`.
- A finding in a human gate area blocks the merge until the user decides. The areas are the core IR semantics, the language design, and the trust boundary.

A periodic review ends with an annotated tag `arch-review/<date>` on the reviewed commit. The tag message holds the report. The drift count starts again from that tag.

Each finding that a machine can check becomes an `xtask` rule. A checklist item that fails twice gets an issue for such a rule.

## Consequences

- The architecture docs stay true, because a reviewer compares them with the code on a fixed schedule.
- Until `review-scope` and `review-due` exist, the triggers are advisory. The follow-up issues add them.
- A merge waits for the user when a finding is in a human gate area.
- The review adds cost to each pull request that touches an architecture path.
