# Driver

## Purpose

The `driver` crate builds the binary `silicon`. It is the command-line front end of the compiler. The Lean tool `silicon-check` follows the same contract.

## Owns

This crate owns the commands `check`, `fmt`, `run`, `lower`, `verilog`, `parse`, `eval`, and `cost`, the output bytes of each, and the exit codes. It owns no logic of the language: it calls `core-ir`, `backend-circt`, `parse`, `resolve`, `typeck`, and `elab`.

## Invariants

- Exit code 0 means success, 1 means a design error, and 2 means a usage error or an input or output error. Check: `cargo nextest run -p driver`.
- A design error prints as `error[Exxx]: L:C: message` on stdout. Check: `cargo nextest run -p driver`.
- `run` prints the `out=` lines before a bad input line, then exits with 2. Check: `cargo nextest run -p driver`.
- A missing CIRCT tool is a usage error with exit code 2, and the message names the tool. Check: `cargo nextest run -p driver`.
- `lower` and `verilog` read the file once, check it with Rust, and then give the same bytes to `silicon-check check`. They fail when it rejects them. A rejection prints the Lean error line and exits with 1. A missing or failing checker is a usage error that names `--no-validate`. `--no-validate` prints `not validated` on stderr. Check: `cargo nextest run -p driver`.
- `parse` prints the AST dump, or the first syntax error as `error[S0xx]: L:C: message` with exit code 1. `--syntax-depth N` sets the syntax depth from 1 to 65536, and another value is a usage error. The front end runs on a thread with a stack for the depth. If the machine cannot give the stack, the command exits with 2 before it parses. Check: `cargo nextest run -p driver`.
- `eval F.si EXPR` prints the serialization of the value, or the first error of the file, then of the expression, with exit code 1. `--fuel N` and `--depth N` take the digits of a natural number with one `_` between two digits, as `silicon-check` does. The output and the exit code equal those of `silicon-check eval`, and only the message text can differ. Check: `cargo nextest run -p driver`.
- `cost F.si --top T` prints `total <units>`, then one line `<emitted name> <units>` for each instantiation, sorted by name, or the first error with exit code 1. A top selection that is not a module name with literal arguments is a usage error. The lines equal those of `silicon-check cost` without the charges of the lowering, which a later part of #72 adds. Check: `cargo nextest run -p driver`.
- The code has no `unwrap`, no `expect`, and no panic on user input. Check: `just clippy`.

## Dependencies

This crate depends on `core-ir`, `backend-circt`, `parse`, `resolve`, `typeck`, `elab`, and `clap`. The command `verilog` runs `firtool`, and the tests run `circt-verilog` and `FileCheck`, from the development shell. The files of `tests/lower/` hold `; CHECK:` lines for `FileCheck`. The variable `SILICON_CHECK` names the checker, else the search path finds `silicon-check`. The tests use `lean/.lake/build/bin/silicon-check`, which `just check` builds. It is the last stage of the pipeline.

## How to test

A fresh clone needs `lake -d lean build` (or `just check`) before `just test`. Run `cargo nextest run -p driver`, then `just check` from the repository root.
