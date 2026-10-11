# Testkit

## Purpose

The `testkit` crate holds the helpers that the test suites of the compiler share. It is a development tool. No shipped binary depends on it. Only `[dev-dependencies]` name it.

## Owns

This crate owns the parser of the directive `expected-error XNNN @+N` for both comment markers. It owns the parser of the report `error[XNNN]: L:C: message` and the check of the outcome of a `parse` command. It also picks the binary under test and the checker. A helper runs a command with a given standard input.

## Invariants

- A file has at most one `expected-error` directive. A second directive and a malformed directive are errors. Check: `cargo nextest run -p testkit`.
- `SILICON_BIN` names the binary under test, else the caller gives a default. `SILICON_CHECK` names the checker, else the Lean package output. Check: `cargo nextest run -p testkit`.
- The outcome check accepts only exit 0 and exit 1 with a valid diagnostic. A signal and every other exit code fail. Check: `cargo nextest run -p testkit`.
- The code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate depends on the standard library only. It sits after `backend-circt` and before `driver` in the layer order. See [the testing design](../../doc/design/2026-10-10-testing.md).

## How to test

Run `cargo nextest run -p testkit`, then `just check` from the repository root.
