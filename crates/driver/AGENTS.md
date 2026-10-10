# Driver

## Purpose

The `driver` crate builds the binary `silicon`. It is the command-line front end of the compiler. The Lean tool `silicon-check` follows the same contract.

## Owns

This crate owns the commands `check`, `fmt`, `run`, `lower`, and `verilog`, the output bytes of each, and the exit codes. It owns no logic of the language: it calls `core-ir` and `backend-circt`.

## Invariants

- Exit code 0 means success, 1 means a design error, and 2 means a usage error or an input or output error. Check: `cargo nextest run -p driver`.
- A design error prints as `error[Exxx]: L:C: message` on stdout. Check: `cargo nextest run -p driver`.
- `run` prints the `out=` lines before a bad input line, then exits with 2. Check: `cargo nextest run -p driver`.
- A missing CIRCT tool is a usage error with exit code 2, and the message names the tool. Check: `cargo nextest run -p driver`.
- `lower` and `verilog` read the file once, check it with Rust, and then give the same bytes to `silicon-check check`. They fail when it rejects them. A rejection prints the Lean error line and exits with 1. A missing or failing checker is a usage error that names `--no-validate`. `--no-validate` prints `not validated` on stderr. Check: `cargo nextest run -p driver`.
- The code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate depends on `core-ir`, `backend-circt`, and `clap`. The command `verilog` runs `firtool`, and the tests run `circt-verilog` and `FileCheck`, from the development shell. The files of `tests/lower/` hold `; CHECK:` lines for `FileCheck`. The variable `SILICON_CHECK` names the checker, else the search path finds `silicon-check`. The tests use `lean/.lake/build/bin/silicon-check`, which `just check` builds. It is the last stage of the pipeline.

## How to test

A fresh clone needs `lake -d lean build` (or `just check`) before `just test`. Run `cargo nextest run -p driver`, then `just check` from the repository root.
