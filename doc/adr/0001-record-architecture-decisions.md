# 1. Record architecture decisions

- Status: accepted
- Date: 2026-10-08

## Context

Two notes held the first decisions of the project: a handoff note and an ecosystem design note. Each note mixed decisions, architecture, and open questions in one text. An agent needs the reason for a decision without a long chat history.

## Decision

Record each architecture decision as an ADR in `doc/adr/NNNN-title.md`. An ADR has a metadata list with its status and its date. The headings Context, Decision, and Consequences follow it. An accepted ADR does not change. A new ADR supersedes it.

The architecture moves to [`doc/architecture.md`](../architecture.md). The ecosystem note moves to [`doc/design/2026-10-05-ecosystem.md`](../design/2026-10-05-ecosystem.md). The owner deletes the handoff note after the move.

## Consequences

- An agent reads one short file for one decision.
- A change of a decision makes a new ADR. The history of decisions stays visible.
- The root `AGENTS.md` points to `doc/adr/` for the question "Why did we decide this?".
