# 22. The spec can make a message text normative

- Status: accepted
- Date: 2026-10-16

## Context

[ADR 0017](0017-error-column-is-normative.md) makes the code, the line, and the column of the first error normative. It keeps the message text outside the contract. Since then, the user made a rule. When a language rule rejects code, the message tells the user how to fix it. Lean and Rust print the same text. Section 6.2 of the front-end spec now makes some texts normative. Examples are `S016` (#178), `S018` for a child input (#200), and the budget messages with their fix (#250, #252). The harnesses pin them with `expected-message`. The drift review of 2026-10-16 found that this practice contradicts ADR 0017.

## Decision

- A message text is normative when section 6.2 of the front-end spec gives it. Both front ends print it exactly.
- A normative text that rejects code names its fix. Examples are the flag of a budget to raise and a short example of the fixed code.
- A file with `expected-message` pins each normative text in both front ends.
- Each other message text stays outside the contract, as ADR 0017 says.
- This replaces only the second point of the decision of ADR 0017. The rest of ADR 0017 stays.

## Consequences

- A change of a normative text goes spec, Lean, the expectations, then Rust, as a change of behavior does.
- `doc/trust.md` names the normative texts in the row of the rejections.
- A message family in section 6.2 with no `expected-message` file is a gap in the tests.
