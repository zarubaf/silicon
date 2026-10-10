# 14. The front end returns structured diagnostics, and only the first error is normative

- Status: accepted, partly superseded by ADR 0017
- Date: 2026-10-10

## Context

Humans and LLM agents write Silicon. An agent reads the errors of the compiler and tries to fix the design in the next turn. The quality of the errors thus sets the cost of each design change. A line such as `error[S010]: 12:5: <message>` gives the code and the position, but it does not show related positions or a fix.

[ADR 0011](0011-lean-reference-elaborator.md) makes the first error of a rejected design normative: Rust and Lean must give the same code and line. A model of help text, notes, and edits in Lean would make each of them part of the spec. Each change of a help text would then need a change of the spec.

rustc shows a good model. Its diagnostics are values with spans, notes, help, and edits with an applicability. Its renderers make a human form and a JSON form from the same value.

## Decision

- The front end returns structured diagnostics: a code, a primary span, labelled secondary spans, notes, help, and suggested edits. Each edit has an applicability: machine-applicable or maybe-incorrect.
- The `driver` renders them. `--error-format` selects `human` (the default, as rustc), `short` (the line of section 6.2 of the front-end spec), or `json` (for LLM agents and the LSP).
- `silicon explain S0xx` prints a long text with a failing and a fixed example. A test elaborates both examples.
- An error of pass 5 has an instantiation backtrace, as the "required by" notes of rustc.
- The front end reports more than one error. Only the first error is normative and validated against Lean.
- Lean models only the accept or reject decision and the first code and line. A diagnostic does not change them.
- Snapshot tests, a corpus of typical LLM mistakes, and a one-turn-fix metric keep the diagnostics useful. The metric is a CI gate.

Section 6.3 of [the front-end spec](../design/2026-10-09-frontend.md) gives the details.

## Consequences

- The `short` form stays the contract of the harnesses. A change of the `human` form changes no oracle.
- The fields of the `json` form are a contract for agents and the LSP. A change of a field is a breaking change.
- A wrong help text or edit can mislead a user, but it cannot make a wrong design pass. [The trust document](../trust.md) records these parts as trusted.
- The one-turn-fix gate calls an LLM, so its result can vary. A pinned model, pinned settings, and a recorded baseline limit this.
- Each new error code needs an explanation with two examples.
