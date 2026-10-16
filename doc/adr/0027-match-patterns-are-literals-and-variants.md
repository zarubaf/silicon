# 27. A match pattern is a literal, a variant, or `_`

- Status: accepted
- Date: 2026-10-17

## Context

[ADR 0021](0021-enums-and-a-pure-match.md) says that a pattern is a static integer, an enum variant with binders for its payload, or `_`. A "static integer" can be any static expression, for example a constant. The ADR gives no pattern for a `Bool` scrutinee.

Issue #268 asked which patterns slice 3 accepts (Q4). A constant as a pattern makes a bare name either a constant or a binder. Rust has this trap. A range adds a second form of coverage. The user accepted the option without constants and ranges on 2026-10-17.

## Decision

- A pattern is one of these forms:
  - An integer literal, also with `-`.
  - `true` or `false`.
  - A variant path with one binder or `_` for each payload value.
  - `_`.
- A constant, a static expression, and a range are not patterns. This replaces the point "a pattern is a static integer" of ADR 0021. The other points of ADR 0021 stay.
- In a pattern, `_` never binds.

## Consequences

- A name in a pattern is always a binder, and only a variant pattern has binders.
- A `match` on `Bool` needs no conversion to an integer.
- The front-end spec records this in decision row F25. A later slice can add constants or ranges with a new ADR.
