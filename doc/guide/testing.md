# Testing

Each layer has one oracle. An oracle is a tool or a model that can say "wrong" mechanically. Each agent works against an oracle.

## Oracles

| Layer                    | Oracle                                                                                                                     | Command                          |
| ------------------------ | -------------------------------------------------------------------------------------------------------------------------- | -------------------------------- |
| Rust crates              | Unit tests and `insta` snapshot tests; `proptest` property tests                                                           | `just test`                      |
| `lean/`                  | The Lean kernel, with warnings as errors. `xtask` rejects `sorry`, new `axiom`, and `native_decide` outside the allowlist. | `just lean`, `cargo xtask check` |
| Compiler against Lean    | Translation validation (build step 2)                                                                                      | Not in `just ci` yet             |
| Implementations together | Differential testing (build step 2)                                                                                        | Not in `just ci` yet             |
| Emitted Verilog          | LEC with `circt-lec` or Yosys equivalence                                                                                  | Not in `just ci` yet             |

## Rust crates

- Each compiler stage has snapshot tests with `insta`. A snapshot file is compiler output. The test compares it byte for byte.
- CI runs `insta` with `INSTA_UPDATE=no`.
- `cargo nextest` shows failures only.
- A test expectation changes in its own commit. A `refactor` commit does not change test expectations. See [the commits guide](commits.md).

## Lean

- `lake -d lean build --wfail` treats warnings as errors.
- `cargo xtask check` rejects `sorry`, a new `axiom`, and `native_decide` outside `lean/allowlist.toml`.

## Later oracles

Fuzzing, translation validation, and LEC join `just ci` in build step 2, when their oracles exist. LEC needs the CIRCT backend, which comes in build step 3. See [the build order](../architecture.md).

- Translation validation: each compiler run emits the core IR as a Lean term. A checker confirms the term.
- Differential testing: random core IR generators drive the Lean interpreter, the Rust simulator, `arcilator`, and Verilator. A disagreement between them is a failure.
- LEC: `circt-lec` or the Yosys equivalence tools compare the emitted Verilog with the core IR.

The designs for validation and differential testing live in `tests/corpus/`.
