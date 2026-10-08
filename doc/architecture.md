# Architecture

This file describes the compiler pipeline, the crates and their order, the trust boundary, and the build order. The decisions behind it are in [the ADRs](adr/). The package ecosystem is in [the ecosystem design](design/2026-10-05-ecosystem.md).

## Goal

Silicon is a standalone hardware description language. It is not a domain-specific language (DSL) inside another language. It has these properties:

- Registers are first-class primitives. The semantics is synchronous only.
- A small core IR has a formal semantics in Lean 4.
- A compiler in Rust produces the core IR. Translation validation checks each compiler run against the Lean semantics.
- A Lean model is the normative functional spec. Verso keeps prose and checked Lean code in one source.
- The implementation (RTL) stays separate from the spec.

4-state logic, clock domain crossing (CDC) verification, and timing are out of scope. Existing dedicated tools cover them. See [ADR 0005](adr/0005-synchronous-two-state-semantics.md).

## Semantics

- The core IR contains registers, memories, pure combinational logic, and module instances.
- The semantics of a design is a Mealy machine. The step function has the form `step : State → Input → State × Output`.
- Elaboration evaluates parameters, generics, and loops of a rich, pure source language. These constructs do not exist in the core IR. The formal core thus stays small, and the source language can grow.
- A black box is a primitive with an assumed contract, for example an SRAM macro, a PLL, vendor IP, or a clock gate. Real designs need them.
- Each clock domain has its own simple semantics. A crossing between clock domains goes through an explicit CDC primitive. The type system rejects a crossing without synchronization.

## Pipeline

```text
source → syntax → parse → resolve → typeck → elab → core-ir ─┬→ backend-circt → Verilog
                                                             ├→ backend-verilog (small reference emitter)
                                                             └→ Lean term → translation validator
```

## Crates

The Rust workspace has one crate per pipeline stage. A crate comes into existence with its first task. The stages, in pipeline order:

1. `syntax`: a lossless syntax tree with `rowan`, from its first commit.
2. `parse`
3. `resolve`
4. `typeck`
5. `elab`
6. `core-ir`
7. `backend-circt`: lowers the core IR to the CIRCT dialects `hw`, `comb`, and `seq`.
8. `backend-verilog`: a small reference emitter.

The crates `diagnostics`, `driver`, and `lsp` support the stages. The names `crates/fmt`, `crates/lint`, and `crates/lsp` are reserved for the Silicon tooling. A crate depends only on earlier pipeline stages. `cargo xtask check` enforces this order (rule `workspace-layers`).

Libraries:

| Library               | Use                                    |
| --------------------- | -------------------------------------- |
| `rowan`               | Lossless syntax trees for the LSP      |
| `salsa`               | Incremental, query-based compilation   |
| `ariadne` or `miette` | Diagnostics                            |
| `insta`               | Snapshot tests for each compiler stage |
| `proptest`            | Property tests                         |

Reference projects:

- Spade: an HDL compiler in Rust. It is the closest match in domain.
- The `architecture.md` of rust-analyzer: a compiler design for an LSP.
- Kôika (MIT, Coq): a rule-based HDL with a formal semantics and a verified Verilog compiler.
- Bluespec, Chisel and FIRRTL, Veryl, and Filament: sources of ideas for the language design.

The handoff note recommends a short review of the crate layout and the core IR by a compiler engineer early in the project.

## Trust boundary

The trust boundary separates the parts that are proven, the parts that are validated, and the parts that are trusted.

| Part                                            | Status            | Oracle or reason                                                             |
| ----------------------------------------------- | ----------------- | ---------------------------------------------------------------------------- |
| Lemmas and theorems about the core IR semantics | Proven            | The Lean kernel                                                              |
| The core IR of each compiler run                | Validated         | The translation validator checks the core IR as a Lean term                  |
| The emitted Verilog against the core IR         | Validated         | LEC with `circt-lec` or Yosys. CIRCT passes have no proof.                   |
| Black boxes                                     | Trusted           | Their contracts are assumed                                                  |
| The Lean kernel and the pinned Lean toolchain   | Proposed: trusted | They are the proof oracle                                                    |
| The LEC tool                                    | Proposed: trusted | It closes the gap behind CIRCT                                               |
| Synthesis and physical implementation           | Proposed: trusted | No validation or proof covers them yet. See the ecosystem design, section 8. |
| 4-state behavior, CDC, and timing               | Out of scope      | Existing dedicated tools cover them                                          |

The owner decides the trust boundary. A row with the status "Proposed" is not a decision. The sources do not classify these parts.

A Lean proof shows that a theorem holds in the encoded model under its assumptions. A proof result names its model, its assumptions, its inputs, and its trusted bridges.

## Verification against existing SystemVerilog

Three methods check the Lean model against SystemVerilog, for example legacy IP or IP from other teams:

1. Co-simulation. Compile the Lean model to a native library. Call it through DPI-C or a Verilator harness as a UVM or cocotb reference model. This method costs the least. Start here.
2. Generate SVA or SMT from the Lean model for JasperGold, VC Formal, or SymbiYosys. Use this method for critical blocks.
3. Import the RTL into Lean (Yosys or slang, then BTOR2 or SMT-LIB, then Lean) and prove refinement. This method is the strongest. It needs custom tools. Related research: Rtl2lean (arXiv 2607.16855) and Vera (Coq).

## Build and environment

- Cargo builds the Rust workspace. Lake builds the Lean project in `lean/`.
- A Nix flake pins the toolchain. See [ADR 0008](adr/0008-nix-pins-toolchain.md).
- The `justfile` is the only entry point.
- The handoff note plans the recipes `just fuzz`, `just lec`, and `just spec`. They do not exist yet.
- The project uses no Bazel for now. Revisit this choice only if builds stay slow with caching.

## Build order

1. The core IR semantics and a reference interpreter in Lean (mostly human).
2. The core IR in Rust, a shared serialization format, the translation validator, and differential testing. Agents scale from this step.
3. The CIRCT backend with LEC.
4. The source language and the elaborator.
5. Tools: the LSP, the simulator user interface, the waveform map, and the Verso spec.

Do not run many agents in parallel before steps 1 and 2 exist. Without an oracle, more agents only make more code without verification.

## Open questions

- The serialization format of the core IR: S-expressions, JSON, or a custom text format.
- Reset semantics: a core primitive or a library construct.
- The memory model in the core IR: ports and read-during-write behavior.
- How the spec shows nondeterminism and implementation-defined behavior: parameters, oracles, or relations.
- The waveform and debug map from the emitted Verilog back to the source.
- The exact claim of the translation validator about the core IR term. The handoff note says only that a checker confirms the term.
- Classify each bridge as trusted, validated, or proven. The trust boundary table marks the classifications that are only proposed.
- When LEC joins `just ci`. The foundation spec, section 9, puts LEC in build step 2. The build order of the handoff note puts the CIRCT backend with LEC in step 3.
