# Architecture

This file describes the compiler pipeline, the crates and their order, the trust boundary, and the build order. The decisions behind it are in [the ADRs](adr/). The package ecosystem is in [the ecosystem design](design/2026-10-05-ecosystem.md).

## Goal

Silicon is a standalone hardware description language. It is not a domain-specific language (DSL) inside another language. It has these properties:

- Registers are first-class primitives. The semantics is synchronous only.
- A small core IR has a formal semantics in Lean 4.
- A compiler in Rust produces the core IR. Translation validation checks each compiler run against the Lean semantics.
- A Lean model is the normative functional spec. Verso keeps prose and checked Lean code in one source.
- The implementation (RTL) stays separate from the spec.
- The architecture stays reviewed. A continuous architecture review compares the code with this file, the ADRs, and the trust document. See [ADR 0013](adr/0013-continuous-architecture-review.md) and the section [Architecture review](#architecture-review).

4-state logic, clock domain crossing (CDC) verification, and timing are out of scope. Existing dedicated tools cover them. See [ADR 0005](adr/0005-synchronous-two-state-semantics.md).

## Semantics

- The core IR contains registers, memories, pure combinational logic, and module instances.
- The semantics of a design is a Mealy machine. The step function has the form `step : State → Input → State × Output`.
- Elaboration evaluates parameters, generics, and loops of a rich, pure source language. These constructs do not exist in the core IR. The formal core thus stays small, and the source language can grow.
- A black box is a primitive with an assumed contract, for example an SRAM macro, a PLL, vendor IP, or a clock gate. Real designs need them.
- Each clock domain has its own simple semantics. A crossing between clock domains goes through an explicit CDC primitive. The type system rejects a crossing without synchronization.

## Pipeline

```text
source → syntax → parse → resolve → typeck → elab → core IR ─┬→ backend-circt → Verilog
                                                             └→ .sil file → silicon-check validate
```

A Lean reference elaborator defines the meaning of a source design. `silicon-check validate` compares the `.sil` file of each Rust elaboration with its output, byte for byte after `canonicalize`. [ADR 0011](adr/0011-lean-reference-elaborator.md) gives the reasons. [The front-end spec](design/2026-10-09-frontend.md) gives the stages and their oracles.

The translation validator `silicon-check` is a Lean executable. It also holds the reference lowering to MLIR. LEC compares the CIRCT output with the output of the reference lowering. [ADR 0010](adr/0010-lean-reference-lowering.md) gives the reasons.

## Crates

The Rust workspace has one crate per pipeline stage. A crate comes into existence with its first task. The layers, in order:

1. `core-ir`: the core IR, its parser, its printer, its checker, and its interpreter. Each later layer uses it.
2. `syntax`: the lexer and the types of the lossless syntax tree, with `rowan` from its first commit.
3. `parse`: the parser with recovery. It makes the lossless syntax tree and the AST.
4. `resolve`: the item table, the scopes, and the resolved AST.
5. `typeck`: the generic pre-check. It needs no static values and checks each item.
6. `elab`: the static evaluator, the checks for each instantiation, and the lowering to core IR.
7. `backend-circt`: lowers the core IR to the CIRCT dialects `hw`, `comb`, and `seq`.
8. `driver`: the `silicon` CLI.

[ADR 0012](adr/0012-front-end-layer-order.md) gives the reasons for this order and for the split of the type checks. The crates `diagnostics` and `lsp` support the stages. `driver` holds the `silicon` command-line interface (CLI). Two dev-only crates are not pipeline stages. `srcgen` is the source generator of `diff-si`, after `syntax` in the layer order. See [ADR 0018](adr/0018-source-generator-crate.md). `testkit` holds the shared test runners, after `backend-circt`. The list `[workspace.metadata.layers] dev-only` names both. Only `[dev-dependencies]` and the tool `xtask` name a dev-only crate. `cargo xtask check` enforces this (rule `workspace-dev-only`). The names `crates/fmt`, `crates/lint`, and `crates/lsp` are reserved for the Silicon tooling. A crate depends only on earlier layers. `cargo xtask check` enforces this order (rule `workspace-layers`).

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

The initial design notes (not in the repository) recommend an early review of the crate layout and the core IR by a compiler engineer.

## Trust boundary

The trust boundary separates the parts that are proven, the parts that are validated, and the parts that are trusted. [The trust document](trust.md) is its authority.

A Lean proof shows that a theorem holds in the encoded model under its assumptions. A proof result names its model, its assumptions, its inputs, and its trusted bridges.

## Architecture review

A continuous architecture review keeps the code and this file in agreement. [ADR 0013](adr/0013-continuous-architecture-review.md) defines the triggers, the reviewers, and the records of the findings:

- A review of each pull request that touches an architecture path.
- A drift review after 15 merged pull requests or after one week.
- A milestone review at each milestone, for example at the end of a build step.

These are the architecture paths. `cargo xtask review-scope` reads this list. Each item in backticks is a path from the repository root. A path that ends in `/` names a directory. A `*` matches part of one path segment:

- `Cargo.toml` and each `crates/*/Cargo.toml`
- `doc/architecture.md`, `doc/trust.md`, `doc/adr/`, and `doc/design/`
- `CONTEXT.md`, `AGENTS.md`, `*/AGENTS.md`, and `crates/*/AGENTS.md`
- `lean/lakefile.toml`, `lean/lake-manifest.json`, `lean/allowlist.toml`, `lean/Silicon/*/Syntax.lean`, `lean/Silicon/*/Main.lean`, and `lean/Silicon/Main.lean`
- The normative Lean definitions: `lean/Silicon/Core/Semantics.lean`, `lean/Silicon/Core/Semantics/`, `lean/Silicon/Core/Check.lean`, `lean/Silicon/Core/Names.lean`, `lean/Silicon/Core/Typed.lean`, `lean/Silicon/Core/Deps.lean`, `lean/Silicon/Core/Text.lean`, `lean/Silicon/Core/MemModel.lean`, `lean/Silicon/Core/Lower.lean`, and `lean/Silicon/Core/Mlir/`. The normative source definitions: `lean/Silicon/Source/*.lean`
- `justfile`, `.github/workflows/`, `xtask/`, and `tests/inventory/`
- The translation validator `crates/driver/src/validate.rs`
- The toolchain pins `flake.nix` and `flake.lock`

## Verification against existing SystemVerilog

Three methods check the Lean model against SystemVerilog, for example legacy IP or IP from other teams:

1. Co-simulation. Compile the Lean model to a native library. Call it through DPI-C or a Verilator harness as a UVM or cocotb reference model. This method costs the least. Start here.
2. Generate SVA or SMT from the Lean model for JasperGold, VC Formal, or SymbiYosys. Use this method for critical blocks.
3. Import the RTL into Lean (Yosys or slang, then BTOR2 or SMT-LIB, then Lean) and prove refinement. This method is the strongest. It needs custom tools. Related research: Rtl2lean (arXiv 2607.16855) and Vera (Coq).

## Build and environment

- Cargo builds the Rust workspace. Lake builds the Lean project in `lean/`.
- A Nix flake pins the toolchain. See [ADR 0008](adr/0008-nix-pins-toolchain.md).
- The `justfile` is the only entry point.
- The project plans the recipes `just fuzz` and `just spec`. They do not exist yet.
- The project uses no Bazel for now. Revisit this choice only if builds stay slow with caching.

## Build order

1. The core IR semantics and a reference interpreter in Lean (mostly human).
2. The core IR in Rust, a shared serialization format, the translation validator, and differential testing. Agents scale from this step.
3. The CIRCT backend with LEC.
4. The source language and the elaborator. See [the front-end spec](design/2026-10-09-frontend.md).
5. Tools: the LSP, the simulator user interface, the waveform map, and the Verso spec.

Do not run many agents in parallel before steps 1 and 2 exist. Without an oracle, more agents only make more code without verification.

## Open questions

- How the spec shows nondeterminism and implementation-defined behavior: parameters, oracles, or relations.
- The waveform and debug map from the emitted Verilog back to the source.
- The trust status of the parts that [the trust document](trust.md) does not list: the Lean kernel, the pinned Lean toolchain, synthesis, and physical implementation.

[The core IR spec](design/2026-10-08-core-ir.md) closes these questions:

- The serialization format of the core IR: an S-expression text format. See section 3.
- Reset semantics: synchronous reset is a primitive. See section 2, decision D3.
- The memory model in the core IR: a combinational read, writes at the edge, and the higher write port wins. See section 2, decision D4.
- The exact claim of the translation validator: `silicon-check check` elaborates the design into typed terms, and `check_sound` and `check_complete` prove the checker. See section 6.4.
- When LEC joins `just ci`: in this iteration, together with the differential tests. See section 9.
