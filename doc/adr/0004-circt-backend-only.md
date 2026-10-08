# 4. CIRCT is a backend only, LEC closes the trust gap

- Status: accepted
- Date: 2026-10-08

## Context

CIRCT has mature tools: the `hw`, `comb`, and `seq` dialects, `ExportVerilog`, `arcilator`, and `circt-lec`. The CIRCT passes have no proof.

## Decision

- CIRCT is a backend only. The `backend-circt` crate lowers the core IR to `hw`, `comb`, and `seq`. It uses `ExportVerilog`, `arcilator`, and `circt-lec`.
- LEC runs between the core IR and the emitted Verilog. The tool is `circt-lec` or the Yosys equivalence tools.
- A small reference emitter in `backend-verilog` exists next to the CIRCT backend.

## Consequences

- Silicon reuses mature tools, but its foundation does not depend on CIRCT.
- The trust gap of the CIRCT passes moves to the LEC tool. [The trust boundary](../architecture.md) lists the LEC tool as trusted.
- LEC joins `just ci` in build step 2.
