# 2. Lean 4 is the normative spec, Rust is the compiler language

- Status: accepted
- Date: 2026-10-08

## Context

Silicon needs a functional spec that is executable and provable. The spec must not drift from its prose. The compiler needs a good ecosystem, good tools, and good performance.

## Decision

- Lean 4 holds the normative spec in a functional style. The step function has the form `step : State → Input → State × Output`.
- Verso keeps the prose and the checked Lean code in one source.
- Rust is the language of the compiler.
- The Lean project lives in `lean/` at the top level. It is not a part of the compiler.

## Consequences

- The spec is executable by default and compiles to native code. Proofs use the same definitions.
- The text of the spec cannot drift from the model, because Verso checks each code block.
- A commit does not change `lean/` and `crates/` together. `cargo xtask commit-check` enforces this rule (rule `commit-spec-impl`).
- The project needs a bridge between the Rust compiler and the Lean semantics. [ADR 0003](0003-translation-validation.md) gives it.
- No Lean work merges with `sorry`, a new `axiom`, or `native_decide` outside `lean/allowlist.toml`.
