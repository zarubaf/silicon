# Driver

## Purpose

The `driver` crate builds the binary `silicon`. It is the command-line front end of the compiler. The Lean tool `silicon-check` follows the same contract.

## Owns

This crate owns the commands `check`, `fmt`, and `run`, the output bytes of each, and the exit codes. It owns no logic of the language: it calls `core-ir`.

## Invariants

- Exit code 0 means success, 1 means a design error, and 2 means a usage error or an input or output error. Check: `cargo nextest run -p driver`.
- A design error prints as `error[Exxx]: L:C: message` on stdout. Check: `cargo nextest run -p driver`.
- `run` prints the `out=` lines before a bad input line, then exits with 2. Check: `cargo nextest run -p driver`.
- The code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate depends on `core-ir` and on `clap`. It is the last stage of the pipeline.

## How to test

Run `cargo nextest run -p driver`, then `just check` from the repository root.
