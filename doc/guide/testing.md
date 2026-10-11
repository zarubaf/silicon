# Testing

This guide is the single map of the tests. Each layer has one oracle. An oracle is a tool or a model that can say "wrong" mechanically. Each agent works against an oracle.

[The testing spec](../design/2026-10-10-testing.md) and [ADR 0015](../adr/0015-unified-exhaustive-testing.md) give the decisions. Each language spec keeps only what is special to its language:

- [The core IR spec](../design/2026-10-08-core-ir.md), section 9, for the `.sil` suites.
- [The front-end spec](../design/2026-10-09-frontend.md), section 11.3, for the `.si` suites.

## Status

Issue #87 builds this layout in steps. Section 11 of the testing spec gives the order. A step that has not landed keeps the old form:

- Step 2 has landed. The core suites are in `tests/core/`. The inventories of LEC and the differential tests are `tests/inventory/lec.txt` and `tests/inventory/diff.txt`.
- Steps 3 to 5 add spec coverage, code coverage, and mutation testing.
- Phase 9 of the front end (#73) has landed. The source suites are in `tests/source/`. The suites `llm`, the metamorphic tests, and LEC with the differential tests on the source corpus wait for #116, #117, and #118.

## Oracles

| Layer                                | Oracle                                                                                                                     | Command                          |
| ------------------------------------ | -------------------------------------------------------------------------------------------------------------------------- | -------------------------------- |
| Rust crates                          | Unit tests and `insta` snapshot tests; `proptest` property tests                                                           | `just test`                      |
| `lean/`                              | The Lean kernel, with warnings as errors. `xtask` rejects `sorry`, new `axiom`, and `native_decide` outside the allowlist. | `just lean`, `cargo xtask check` |
| Checker and interpreter against Lean | The shared files of the suites run with `silicon` and with `silicon-check`                                                 | `just lean-check`, in `just ci`  |
| Compiler against Lean                | Translation validation (build step 2)                                                                                      | Not in `just ci` yet             |
| Implementations together             | The differential tests: random designs through the Lean interpreter, `silicon run`, and `arcilator`                        | `just diff`, in `just ci`        |
| Emitted Verilog                      | LEC with `circt-lec` against the Lean reference MLIR                                                                       | `just lec`, in `just ci`         |

## Suites

Each language has one tree. A suite is one directory of a tree. The directory selects the command, and the crate `testkit` runs it. The suites use no shell `RUN:` lines. They find their files on their own, so a new file needs no change to `Cargo.toml`.

| Suite                  | Command                                                         | Oracle                                         | Directives                             |
| ---------------------- | --------------------------------------------------------------- | ---------------------------------------------- | -------------------------------------- |
| `tests/core/check/`    | The Rust checker and the Lean checker                           | The same first code and line in both           | `expected-error`                       |
| `tests/core/run/`      | The Rust interpreter and the Lean interpreter                   | The expected outputs in both                   | `STEP`                                 |
| `tests/core/lower/`    | `silicon lower`                                                 | LLVM `FileCheck`                               | `CHECK` lines                          |
| `tests/core/corpus/`   | LEC and the differential tests                                  | `circt-lec`, the interpreters, `arcilator`     | None                                   |
| `tests/source/parse/`  | `parse` in Rust and in Lean                                     | The AST dumps are equal byte for byte          | None                                   |
| `tests/source/check/`  | `elab` in Rust and in Lean                                      | The same first code, line, and column in both  | `TOP`, `expected-error`                |
| `tests/source/run/`    | `run` in Rust and in Lean                                       | The expected outputs in both                   | `TOP`, `STEP`                          |
| `tests/source/elab/`   | `elab`, then `FileCheck` on both outputs                        | LLVM `FileCheck`                               | `TOP`, `CHECK` lines                   |
| `tests/source/budget/` | `elab` with the budgets of the file                             | Success at the limit, failure one unit above   | `TOP`, `FUEL`, `DEPTH`, `SYNTAX-DEPTH` |
| `tests/source/corpus/` | `validate`, then LEC and the differential tests                 | `silicon-check`, `circt-lec`, the interpreters | `TOP`                                  |
| `tests/source/llm/`    | `elab`, and the quality loop of the front-end spec, section 6.3 | The expected first error, and a fixed version  | `TOP`, `expected-error`                |

The `corpus` suites keep their smoke checks: `silicon check` accepts each file, `circt-opt` parses the output of `silicon lower`, and `silicon verilog` succeeds with and without `--models`.

`commit-check` treats each file of a suite as a test expectation. See [the commits guide](commits.md).

## Directives

A directive is a comment line that gives the expectation of a test file. Both languages use the same names. Only the comment marker differs: `;` in a `.sil` file, `//` in a `.si` file.

| Directive                                                                             | Meaning                                                                                   |
| ------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| `expected-error CODE @+N`                                                             | The first error has the code `CODE` at N lines below the directive                        |
| `STEP in=(...) out=(...)`                                                             | One clock cycle: the inputs and the expected outputs                                      |
| All `FileCheck` directives, for example `CHECK:`, `CHECK-NEXT:`, and `CHECK-COUNT-2:` | LLVM `FileCheck` reads these lines and checks the output                                  |
| `TOP M(args)`                                                                         | The top selection of a source file                                                        |
| `FUEL N`                                                                              | The file elaborates with the fuel N. With the fuel N - 1, it fails with `S015`.           |
| `DEPTH N`                                                                             | The file elaborates with the nesting depth N. With the depth N - 1, it fails with `S015`. |
| `SYNTAX-DEPTH N`                                                                      | The file parses with the syntax depth N. With the depth N - 1, it fails with `S001`.      |

A budget file passes only when both front ends meet both conditions. A budget file has no `expected-error`. At N, both front ends succeed with the same design. The `cost` command with the default budgets exits 0 in both and gives the same output. At N - 1, each front end gives the exact code with the error exit code 1: `S015` for `FUEL` and `DEPTH`, `S001` for `SYNTAX-DEPTH`. A crash, a signal, a timeout, or a usage error with exit code 2 fails the test and covers nothing.

Examples: `; expected-error E004 @+1`, `// expected-error S010 @+1`, and `; STEP in=(en 1 rst 0) out=(q 3)`.

- `@+1` means the next line. A `check` file without `expected-error` must pass. A `run` file can also have `expected-error`, for an error that only `run` reports. An `llm` file has `expected-error` for its first error.
- The harness uses the real LLVM `FileCheck` from Nix.

## Measures

Three measures find a missing test. Each has an inventory of known gaps in `tests/inventory/`.

| Measure          | Question                                  | Tool             | Command                                      |
| ---------------- | ----------------------------------------- | ---------------- | -------------------------------------------- |
| Spec coverage    | Does each item of the spec have a test?   | `testkit`        | `cargo xtask coverage`, in `just ci`         |
| Code coverage    | Does a test run each line of Rust?        | `cargo-llvm-cov` | `just coverage`, in `just ci`                |
| Mutation testing | Does a test find each change of the code? | `cargo-mutants`  | On each pull request, and in a weekly CI job |

### Spec coverage

`cargo xtask coverage` requires these tests:

- **Error code.** At least 2 different files in the suite whose command reports the code. This suite is `check`, except for `E014`, which only `run` reports. The codes come from the code tables of the two specs, as rule `arch-codes` reads them. The intent is a minimal case and a case in another context. The review checks the intent.
- **Construct.** At least 1 file in each behavior suite. These are `run` and `lower` for the core IR, and `run` and `elab` for the source.
- **Command.** At least 1 suite or CLI test for each command of `silicon` and `silicon-check`.
- **Budget.** For each budget of the front-end spec, section 5.4, a file at the limit that passes, and one unit above that fails.

A construct ID is `LANG:Enum::Variant`, for example `core:BinOp::Shrs` or `source:Item::Fn`. The enums are `Item`, `Stmt`, `Expr`, `UnOp`, `BinOp`, and `Pred` of `core-ir`, and `Item`, `Stmt`, `Expr`, `TypeExpr`, `UnOp`, and `BinOp` of `parse`. Each operator variant is a separate construct.

`testkit` writes a record for each check that ran and passed. `cargo xtask coverage` runs the tests and reads the records:

- A check that failed or printed SKIP covers nothing.
- A file covers constructs only when it passes and has no `expected-error`. A `run` file needs at least one `STEP`.
- A file covers only the constructs in the code that its top reaches. For the core IR, this is the top module and the modules that it instantiates, transitively. For the source, it is the items that `TOP` reaches through instances, calls, and constant uses, transitively. The reachability is syntactic: both branches of a reached `comptime if` count. An operator in an unused module thus stays uncovered.
- An `expected-error` line covers its code, also in a file that does not parse. A `run` file that expects `E014` thus covers `E014`, but no construct.
- A suite covers the command of its table row. A CLI test of `driver` starts its command through one `testkit` function that names the command.
- A file has no hand-written coverage tags.

A failure prints the item and the suite that has no test for it. The testing spec, section 6, gives the full rules.

### Code coverage

- `just coverage` runs all Rust tests with instrumentation, also the tests that start `silicon`.
- The measure is the line coverage of each crate. `xtask` is exempt.
- CI fails when a crate goes below its floor. The target is 90 % for each compiler crate.
- A floor can rise in any commit. A commit that lowers a floor changes nothing else.
- The run is deterministic: `just coverage` sets a fixed seed and a fixed case count for `proptest`.
- The unit tests and the `proptest` tests of the crates count toward code coverage only. A CLI test of `driver` also covers its command.

### Mutation testing

`cargo-mutants` changes the code, for example it replaces a condition with `true`. Each changed program is a mutant. A test kills a mutant when the test fails on it.

- On each pull request, `cargo mutants --in-diff` makes mutants on the changed lines.
- A weekly CI job makes mutants on all compiler crates.
- A surviving mutant fails, unless the inventory lists it.
- A pull request run checks only the entries of the mutants that it made. The weekly run checks the full inventory.
- Each mutant has a timeout, and the pull request job has a runtime limit. A mutant that runs into its timeout does not survive.

### Lean

Lean has no coverage tool and no mutation tool. The shared files cover Lean, because each file runs through both front ends.

## Inventories

A SKIP hides a check, and a vanished check hides a bug. Thus each tool compares its results with a reviewed inventory in `tests/inventory/`. There are three kinds of inventory:

| Kind         | Files                         | Rule                                                                                                                                |
| ------------ | ----------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| Exact result | `lec.txt`, `diff.txt`         | Each result must equal its line. A missing line, an extra line, and a changed line all fail. A fixed gap forces its line to change. |
| Gap          | `coverage.txt`, `mutants.txt` | Each line is an accepted gap. A stale line fails: an item that has its test, or a mutant that a test now kills.                     |
| Threshold    | `llvm-cov.txt`                | Each measured value must be at or above its floor. The tool does not compare the value for equality.                                |

| File           | Tool                   | Line format                                          |
| -------------- | ---------------------- | ---------------------------------------------------- |
| `lec.txt`      | `just lec`             | `FILE CHECK PASS` or `FILE CHECK SKIP TAG`           |
| `diff.txt`     | `cargo xtask diff`     | `FILE CHECK PASS` or `FILE CHECK SKIP TAG`           |
| `coverage.txt` | `cargo xtask coverage` | `ITEM SUITE SKIP TAG`                                |
| `llvm-cov.txt` | `just coverage`        | `CRATE FLOOR`                                        |
| `mutants.txt`  | `cargo-mutants`        | `#ISSUE MUTANT`, or `EQUIV MUTANT` and a reason line |

The fields:

- `FILE` is the corpus file. A model check of LEC uses `-`, because it belongs to a memory configuration, not to a file.
- `CHECK` is the name in the output line, and it may hold spaces. `diff` uses `run`.
- `TAG` is `#ISSUE` or an error code such as `E014`. It must equal the tag that the tool reports. `cargo xtask check` requires that `doc/trust.md` names the tag as a gap (rule `arch-skips`).
- `ITEM` is an error code, a construct ID, a command, or a budget, as the failure of `cargo xtask coverage` prints it. A new feature removes its exception.
- `SUITE` is the suite that has no test. It is `-` for an error code, a command, and a budget. An exception covers one item in one suite only, and the stale check runs for each pair. Examples: `core:Item::Extern run SKIP E014`, which keeps the extern required in `lower`, and `S016 - SKIP #11`.
- `CRATE` is a crate name, and `FLOOR` is its line coverage in percent. The first floors are the values of rollout step 4, rounded down.
- `MUTANT` is the name of a mutant, as `cargo-mutants` prints it. `#ISSUE` names the issue for the missing test. `EQUIV` marks a mutant with the same behavior as the original code. The next line gives the reason in one line.

`lec.txt` and `diff.txt` also fail when they run no comparison. A run with only SKIP lines, or with an empty corpus, fails. `diff` fails on an empty corpus for each `--count`, because the random designs stay outside the inventory.

## Rust crates

- Each compiler stage has snapshot tests with `insta`. A snapshot file is compiler output. The test compares it byte for byte.
- In CI, `insta` writes no snapshot files. GitHub Actions sets `CI=true`, and `insta` then compares only.
- `cargo nextest` shows failures only.
- A test expectation changes in its own commit. A `refactor` commit does not change test expectations. See [the commits guide](commits.md).

## Lean kernel

- `lake -d lean build --wfail` treats warnings as errors.
- `cargo xtask check` rejects `sorry`, a new `axiom`, and `native_decide` outside `lean/allowlist.toml`.

## LEC

`just lec` runs `circt-lec` on each file of the `corpus` suite. It compares the emitted Verilog and the Rust MLIR with the Lean reference MLIR. It also compares each Rust memory model with the Lean memory model. [The core IR spec](../design/2026-10-08-core-ir.md), section 8.1, gives the flow. Run it in the development shell.

## Differential tests

`cargo xtask diff` runs the designs of the `corpus` suite and random designs from the generator of `core-ir`, with random inputs. It sends each design to the Lean interpreter, to `silicon run`, and to `arcilator` on the Lean reference MLIR. Each tool starts from the all-zero state. A disagreement is a failure. The failure prints the design and the input vectors as a `run` file.

- A corpus design with an extern prints `SKIP`. The interpreters reject it with `E014`.
- The defaults are the seed 1 and 200 random designs. Use `--seed` and `--count` to change them.
- A failure prints its seed. `cargo xtask diff --seed N --count 1` repeats it.
- LEC covers the emitted Verilog, so the differential tests use no Verilator (core IR spec, section 8.2).

## Later oracles

Fuzzing and translation validation join `just ci` in build step 2, when their oracles exist. See [the build order](../architecture.md).

- Translation validation: each compiler run emits the core IR as a `.sil` file. The Lean checker `silicon-check` confirms it.
