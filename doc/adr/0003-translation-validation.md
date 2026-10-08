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
- The translation validator joins `just ci` when its oracle exists. See the build order in [the architecture](../architecture.md).
- The core IR has an S-expression text format. See [the core IR spec](../design/2026-10-08-core-ir.md), section 3.
- Note of 2026-10-08: the core IR spec, section 6.4, fixes the form of the term. Each compiler run emits the core IR as a `.sil` file, and the Lean checker `silicon-check` confirms it.
