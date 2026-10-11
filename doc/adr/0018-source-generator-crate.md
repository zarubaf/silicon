# 18. The source generator is a dev-only crate with a bounded evaluator

- Status: accepted
- Date: 2026-10-11

## Context

The generator of `just diff-si` ([front-end spec](../design/2026-10-09-frontend.md), section 11.4) is the module `gen` of the lexer crate `syntax`, behind the feature `gen`. It has about 6,000 lines with its tests. It holds the lift, the map from core vectors to source vectors, and the typed program. It also holds the static evaluator, the builder, the twin, and the mutations. The milestone review of slice 1 (tag `arch-review/2026-10-11.2`) found two problems. A lexer crate holds a test tool that has no relation to the lexer. The static rules have three implementations: Lean, `elab`, and the generator. Slice 2 adds the most code to the generator. Without a limit, its evaluator can grow into a second elaborator.

## Decision

- The generator moves to the new crate `srcgen`. Its place in the layer order is directly after `syntax`. It depends on `syntax`, on `core-ir` with the feature `gen`, on `num-bigint`, and on `proptest`.
- `srcgen` is a dev-only crate, as `testkit` is. Only `xtask` and `[dev-dependencies]` name it. A new list `[workspace.metadata.layers] dev-only` names both crates. The new rule `workspace-dev-only` of `cargo xtask check` rejects a normal or build dependency on a crate of this list.
- The rule `workspace-layers` keeps `srcgen` independent of `parse`, `resolve`, `typeck`, and `elab`. The generator is an oracle for these stages, so it must not use their code.
- `syntax` keeps the lexer, the kinds, and the numbers. It loses the feature `gen` and its optional dependencies.
- The evaluator of the generator models only the static semantics of the programs that the builder makes. It works on the typed program of the generator, never on source text or on a syntax tree. Each construct that it evaluates has a builder that emits it.
- It can be stricter than the language: it can reject a program that the language accepts, and the builder then does not emit that program. It must never give a value that differs from the language.
- In slice 2, it can model the static values that the builder emits: aggregates, `List`, strings, and the width of `data_bits(T)`. It can also model the leaves of the ports that the builder declares.
- It does not resolve names, infer or check types, compute `cost` or fuel, make instantiation identities or emitted names, or lower to core IR. It predicts an error code only where the pass order makes the code certain. A need outside these limits needs a new ADR.

## Consequences

- A change to the generator does not rebuild or retest the lexer.
- The evaluator stays a third implementation on purpose. The probe `eval` compares it with both front ends, so a shared misreading of Lean and `elab` can show.
- The size of the evaluator grows with the forms of the builder, not with the language.
- These texts name the new crate: `doc/architecture.md`, the sections 4.4 and 11.4 of the front-end spec, `doc/trust.md`, and the `AGENTS.md` files of `syntax` and `srcgen`.
- `testkit` gets the check that its `AGENTS.md` only states now.
