# 11. A Lean reference elaborator defines the meaning of source

- Status: accepted
- Date: 2026-10-09

## Context

The front end is the largest compiler part, and it changes the most. [ADR 0003](0003-translation-validation.md) validates the core IR of each run, but `silicon-check check` only shows that the output is a well-formed design. It does not show that the output is the design that the source means. The source meaning would then live in prose and in Rust code, and no oracle would check parsing, name resolution, comptime evaluation, or the lowering.

[ADR 0010](0010-lean-reference-lowering.md) solved the same problem for the backend: a second path on the spec side, in Lean. [ADR 0002](0002-lean-spec-rust-compiler.md) puts the normative spec in Lean and the compiler in Rust.

## Decision

- A Lean reference elaborator in `lean/Silicon/Source/` defines the meaning of a source design. The meaning is the core IR `step` of its output. The front end adds no second semantics.
- Lean parses the `.si` text itself. It does not read an AST from Rust, so the oracle also covers the parser.
- `silicon-check validate` compares each Rust elaboration with the reference byte for byte, after `canonicalize`. A rejected design gives the same first error code and line in both front ends.
- `silicon build` validates by default. An interactive build can opt out.
- The end goal is a proof of the Rust front end against the reference through Aeneas, as issue #10 plans for the core IR. Until that proof exists, validation on each run is the oracle.

The front-end spec, `doc/design/2026-10-09-frontend.md`, gives the details.

## Consequences

- Rust stays the compiler language, as ADR 0002 requires. Lean now holds the spec of the source language as well as the spec of the core IR.
- Each language feature costs work in Lean and in Rust. A fresh Opus agent does the Lean work.
- The core IR names and the lowering of each operation are part of the spec, because byte equality needs them. Elaboration does no optimization. An optimization is a core-to-core pass, and LEC checks it.
- The Lean `Source` modules are a human gate for the language design ([ADR 0009](0009-cross-vendor-review-before-merge.md)).
- The Rust elaborator core keeps to the Rust subset that Aeneas supports, where this costs little.
- The initial state of a source design is free, as in the core IR. A real register has no defined value before its first reset. This replaces v0.1 section 4, which starts the native registers at their reset values. The source `run` starts from all zero only as a test convention.
- A build without validation has no guarantee for its front end. [The trust document](../trust.md) records this.
