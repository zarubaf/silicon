# 10. The Lean reference lowering replaces the reference emitter

- Status: accepted
- Date: 2026-10-08

## Context

[ADR 0004](0004-circt-backend-only.md) puts a small reference emitter in `backend-verilog` next to the CIRCT backend. LEC needs a reference to compare the CIRCT output against. The emitter in Rust gives that reference.

[The core IR spec](../design/2026-10-08-core-ir.md) adds a reference lowering in Lean. The Lean function `lower` translates the core IR to `hw`, `comb`, and `seq` MLIR. Lean also generates a memory model for each memory configuration.

## Decision

The Lean reference lowering and the Lean memory models replace the Rust reference emitter `backend-verilog`. The project does not make the `backend-verilog` crate.

These are the reasons:

- The Lean lowering is a second path that is independent of the Rust compiler. It is on the spec side.
- The theorem `lower_correct` proves the Lean lowering against `step`. The theorem `mem_model_correct` proves the memory models.
- A reference emitter in Rust is a third path. No oracle checks it, so it adds code without a guarantee.

## Consequences

- LEC compares the output of the CIRCT pipeline with the output of `silicon-check lower`. Section 8.1 of the core IR spec gives the flow.
- The Rust pipeline has one backend: `backend-circt`.
- The Lean lowering has one assumption: the `Mlir` semantics in Lean must match the meaning that CIRCT gives to the same operations. `arcilator` and `circt-lec` check this assumption. [The trust document](../trust.md) records it.
- This ADR supersedes the reference emitter of ADR 0004. The other decisions of ADR 0004 stay.
