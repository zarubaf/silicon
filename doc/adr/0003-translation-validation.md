# 3. Translation validation instead of a verified compiler

- Status: accepted
- Date: 2026-10-08

## Context

The Rust compiler must agree with the Lean semantics. A verified compiler gives a proof for all inputs, but it costs much more to build and to change.

## Decision

Use translation validation. Each compiler run emits the core IR as a Lean term. A checker confirms the term.

## Consequences

- Each compiler run gets its own guarantee. The cost is lower than the cost of a verified compiler.
- The compiler itself stays unproven. A run without validation has no guarantee.
- The translation validator joins `just ci` in build step 2, with differential testing and LEC. See [the build order](../architecture.md).
- The serialization format of the core IR is still open. See the open questions in [the architecture](../architecture.md).
