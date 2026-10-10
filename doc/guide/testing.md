# Testing

Each layer has one oracle. An oracle is a tool or a model that can say "wrong" mechanically. Each agent works against an oracle.

## Oracles

| Layer                                | Oracle                                                                                                                     | Command                          |
| ------------------------------------ | -------------------------------------------------------------------------------------------------------------------------- | -------------------------------- |
| Rust crates                          | Unit tests and `insta` snapshot tests; `proptest` property tests                                                           | `just test`                      |
| `lean/`                              | The Lean kernel, with warnings as errors. `xtask` rejects `sorry`, new `axiom`, and `native_decide` outside the allowlist. | `just lean`, `cargo xtask check` |
| Checker and interpreter against Lean | The shared `tests/check` and `tests/run` files run with `silicon` and with `silicon-check`                                 | `just lean-check`, in `just ci`  |
| Compiler against Lean                | Translation validation (build step 2)                                                                                      | Not in `just ci` yet             |
| Implementations together             | The differential tests: random designs through the Lean interpreter, `silicon run`, and `arcilator`                        | `just diff`, in `just ci`        |
| Emitted Verilog                      | LEC with `circt-lec` against the Lean reference MLIR                                                                       | `just lec`, in `just ci`         |

## Rust crates

- Each compiler stage has snapshot tests with `insta`. A snapshot file is compiler output. The test compares it byte for byte.
- In CI, `insta` writes no snapshot files. GitHub Actions sets `CI=true`, and `insta` then compares only.
- `cargo nextest` shows failures only.
- A test expectation changes in its own commit. A `refactor` commit does not change test expectations. See [the commits guide](commits.md).

## Lean

- `lake -d lean build --wfail` treats warnings as errors.
- `cargo xtask check` rejects `sorry`, a new `axiom`, and `native_decide` outside `lean/allowlist.toml`.

## LEC

`just lec` runs `circt-lec` on each file of `tests/corpus/`. It compares the emitted Verilog and the Rust MLIR with the Lean reference MLIR. It also compares each Rust memory model with the Lean memory model. [The core IR spec](../design/2026-10-08-core-ir.md), section 8.1, gives the flow. Run it in the development shell.

## Check inventory

A SKIP hides a check, and a vanished check hides a bug. Thus `just lec` and `cargo xtask diff` compare their checks with a reviewed inventory. The files are `tests/lec-checks.txt` and `tests/diff-checks.txt`. Each tool fails for two separate causes:

- It runs no comparison. A run with only SKIP lines, or with an empty corpus, fails. `diff` fails on an empty corpus for each `--count`, because the random designs stay outside the inventory.
- Its checks differ from the inventory. A missing line, an extra line, and a changed line all fail. Thus a fixed bug forces its `SKIP` line to become `PASS`.

The format of a line is `FILE CHECK PASS` or `FILE CHECK SKIP TAG`.

- `FILE` is the corpus file. A model check of LEC uses `-`, because it belongs to a memory configuration, not to a file.
- `CHECK` is the name in the output line, and it may hold spaces. `diff` uses `run`.
- `TAG` is `#ISSUE` or an error code such as `E014`. It must equal the tag that the tool reports. `cargo xtask check` requires that `doc/trust.md` names the tag as a gap (rule `arch-skips`).

## Later oracles

Fuzzing and translation validation join `just ci` in build step 2, when their oracles exist. See [the build order](../architecture.md).

- Translation validation: each compiler run emits the core IR as a `.sil` file. The Lean checker `silicon-check` confirms it.

The designs for LEC and the differential tests live in `tests/corpus/`.

## Differential tests

`cargo xtask diff` runs the designs of `tests/corpus/` and random designs from the generator of `core-ir`, with random inputs. It sends each design to the Lean interpreter, to `silicon run`, and to `arcilator` on the Lean reference MLIR. Each tool starts from the all-zero state. A disagreement is a failure. The failure prints the design and the input vectors as a `tests/run` file.

- A corpus design with an extern prints `SKIP`. The interpreters reject it with `E014`.
- The defaults are the seed 1 and 200 random designs. Use `--seed` and `--count` to change them.
- A failure prints its seed. `cargo xtask diff --seed N --count 1` repeats it.
- LEC covers the emitted Verilog, so the differential tests use no Verilator (core IR spec, section 8.2).
