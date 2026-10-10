# 16. A review tag can have a sequence number

- Status: accepted
- Date: 2026-10-10

## Context

[ADR 0013](0013-continuous-architecture-review.md) ends each periodic review with an annotated tag `arch-review/<date>`. The drift count starts again from the newest tag. On 2026-10-10, 15 pull requests merged after the first drift review of the day. A second drift review thus became due on the same day. A tag name with only a date cannot hold a second review.

## Decision

- A review tag is `arch-review/YYYY-MM-DD` or `arch-review/YYYY-MM-DD.N`. N starts at 2 for the second review on one day and has no leading zero.
- A tag without N counts as N = 1. `cargo xtask review-due` takes the newest tag by the date, then by N.
- This replaces only the tag rule of ADR 0013. The rest of ADR 0013 stays.

## Consequences

- Each review has its own tag and report, also when two reviews fall on one day.
- The order of the tags is total, because a date and a number give a unique key.
- `review-due` rejects any other tag under `arch-review/`, as before.
