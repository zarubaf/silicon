# 4. CIRCT is a backend only, LEC closes the trust gap

- Status: accepted, partly superseded by ADR 0010
- Date: 2026-10-08

## Context

CIRCT has mature tools: the `hw`, `comb`, and `seq` dialects, `ExportVerilog`, `arcilator`, and `circt-lec`. The CIRCT passes have no proof.

## Decision

- CIRCT is a backend only. The `backend-circt` crate lowers the core IR to `hw`, `comb`, and `seq`. It uses `ExportVerilog`, `arcilator`, and `circt-lec`.
- LEC runs between the core IR and the emitted Verilog. The tool is `circt-lec` or the Yosys equivalence tools.
- A small reference emitter in `backend-verilog` exists next to the CIRCT backend.

## Consequences

- Silicon reuses mature tools, but its foundation does not depend on CIRCT.
- LEC closes the trust gap of the CIRCT passes.
- LEC joins `just ci` when its oracle exists. See the build order in [the architecture](../architecture.md).
