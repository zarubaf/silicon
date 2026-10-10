# 17. The column of the first error is normative

- Status: accepted
- Date: 2026-10-10

## Context

[ADR 0011](0011-lean-reference-elaborator.md) makes the first error of a rejected design normative: the same code and line in both front ends. [ADR 0014](0014-structured-diagnostics.md) keeps this contract for the diagnostics. Section 6.2 of the front-end spec defines each error position exactly, with a line and a column. The comparison of the two parsers (#93) agrees on the column for each of its files.

A contract that ignores the column misses a class of defects: an error on the right line at the wrong token. The architecture review of #93 also found that the spec named the column in one section and excluded it in another.

## Decision

- The first error of a rejected design has the same code, line, and column in both front ends.
- The message text stays outside the contract.
- This replaces only the error contract of ADR 0011 and ADR 0014. The rest of both ADRs stays.

## Consequences

- Each harness that compares a rejection compares the column too.
- A disagreement on the column is a defect in one of the front ends, and Lean decides which.
- The structured diagnostics of ADR 0014 keep their primary span at the position of section 6.2.
