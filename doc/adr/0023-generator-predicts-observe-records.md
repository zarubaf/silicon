# 23. The source generator predicts the observe records

- Status: accepted
- Date: 2026-10-16

## Context

[ADR 0018](0018-source-generator-crate.md) limits the evaluator of the source generator. It must not make instantiation identities or emitted names. A need outside these limits needs a new ADR. Two later changes went past this limit: the prediction of the `diagnostic` records (#185) and the full record lines of `observe` (#232). Each one edited ADR 0018 instead of a new ADR. [ADR 0001](0001-record-architecture-decisions.md) says that an accepted ADR does not change. The drift review of 2026-10-16 found both edits. This ADR records them, and ADR 0018 goes back to its accepted text.

## Decision

- The generator predicts the static value of each `diagnostic` record from the contexts of its builder (`Builder.contexts` in `crates/srcgen/src/build/inst.rs`). It uses the dedupe of contexts that the builder does, and adds no second identity rule.
- The generator predicts each full record line of `observe` (#232). It makes the emitted name of the argument tuples that its builder emits: integers, Booleans, and function values. It takes the line and the column of a record from its printed text.
- The digest form of an emitted name uses the crate `sha2`, a normal dependency of the dev-only crate `srcgen`. An own SHA-256 was the other choice. The crate keeps the oracle independent of `elab` and is shorter.
- No other emitted name or identity belongs to the generator. A need outside these limits needs a new ADR.

## Consequences

- The oracle of the `observe` records is independent of both front ends for the shapes that the builder makes. #244 tracks the other shapes.
- The generator holds a second rule for the readable and the digest form of an emitted name. A change of section 7.1 of the front-end spec must change the generator too, or `just diff-si` fails.
