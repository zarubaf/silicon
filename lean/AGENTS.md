# Lean

## Purpose

The Lean model is the normative spec for Silicon.

## Owns

This directory owns two models. Dispatch Lean work to a fresh Opus subagent.

- `Silicon/Core/` holds the core IR semantics.
- `Silicon/Source/` holds the reference front end: the lexer, the parser, the printer, the resolver, the generic pre-check, the evaluator, the elaborator, and the lowering. `Source/Test/` holds its `#guard` tests. Its spec is [the front-end spec](../doc/design/2026-10-09-frontend.md).

## Invariants

- Do not use `sorry`. Check: `cargo xtask check` (rule `lean-sorry`).
- Add no new `axiom`. Check: `cargo xtask check` (rule `lean-axiom`, with `allowlist.toml`).
- Use `native_decide` only in files listed in `allowlist.toml`. Check: `cargo xtask check` (rule `lean-native-decide`).
- Use at most 100 characters per line, no tabs, and no trailing spaces. Check: `cargo xtask check` (rule `lean-style`).
- Put each Lean source in `Silicon.lean` or under `Silicon/`. Lake builds only these files. Check: `cargo xtask check` (rule `lean-layout`).
- Treat build warnings as errors. Check: `lake -d lean build --wfail`.

## Dependencies

Lean has no dependencies on `crates/`.

## How to test

Run `just check` from the repository root.

Run `lake -d lean exe silicon-check check FILE` to check a design. Run `silicon-check parse`, `eval`, `cost`, `elab`, or `validate` for the front end.
