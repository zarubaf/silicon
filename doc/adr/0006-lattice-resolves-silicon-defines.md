# 6. Lattice resolves packages, Silicon defines their meaning

- Status: accepted
- Date: 2026-10-08

## Context

The Silicon ecosystem needs versioned packages, incremental compilation, reproducible builds, Lean proofs, and controlled language evolution. These concerns become hard to change when one tool owns all of them. [The ecosystem design](../design/2026-10-05-ecosystem.md) gives the full model.

## Decision

Lattice resolves package identities. Silicon defines their meaning. A build backend executes the required actions. Lean checks formal claims over semantics with an explicit identity.

The ecosystem design raises these invariants (section 11, items 1 and 5 to 9):

1. Lattice resolves a package once. All consumers use that exact dependency map.
2. Compiler semantics and package identity do not depend on a build backend.
3. Cache keys include every declared input that is relevant to the meaning of the artifact.
4. Interface reuse does not bypass the proof obligations of an implementation.
5. Edition migration is explicit, and each package can do it separately.
6. A proof result names its model, its assumptions, its inputs, and its trusted bridges.

## Consequences

- Silicon does not fetch packages or resolve version constraints during compilation. It receives a resolved dependency map.
- Lean does not select versions of Silicon packages.
- Bazel is one possible build backend. It is not necessary.
- [ADR 0007](0007-mandatory-uniquification.md) covers the identity invariants (section 11, items 2 to 4).
