# 15. One test approach for both languages, with three measures of completeness

- Status: accepted
- Date: 2026-10-10

## Context

The core IR has the suites `tests/check`, `tests/run`, `tests/lower`, and `tests/corpus`. The front-end spec plans the suites of `tests/si`. The two sets differ in their layout, their runner, and their documentation. Each spec describes its own suites, so one fact can have two descriptions.

The oracles of each suite are mechanical. Nothing checks that the suites are complete. An error code, a construct, a command, or a budget can thus have no test, and no check reports it. A line of Rust can have no test. A test can also run a line and still miss a defect in it.

## Decision

- One tree for each language: `tests/core/` and `tests/source/`. The inventories go to `tests/inventory/`.
- The same directive names in both languages. Only the comment marker differs: `;` in `.sil`, `//` in `.si`.
- One dev-only crate `testkit` runs all suites. It has one suite table, one directive parser, and one `datatest-stable` harness. The oracles stay unchanged.
- Spec coverage: `cargo xtask coverage` requires tests for each error code, construct, command, and budget. It reads the test files with the real parsers. An exception needs a tag in `tests/inventory/coverage.txt`.
- Code coverage: `cargo-llvm-cov` measures the line coverage of each crate. A floor for each crate in `tests/inventory/llvm-cov.txt` stops a decrease.
- Mutation testing: `cargo-mutants` runs on the changed lines of each pull request and on all compiler crates each week. A surviving mutant fails, unless `tests/inventory/mutants.txt` lists it.
- Lean gets no coverage tool and no mutation tool. The shared files cover Lean, because each runs through both front ends.
- `doc/guide/testing.md` is the single map of the tests. Each spec keeps only what is special to its language.

[The testing spec](../design/2026-10-10-testing.md) gives the details and the rollout.

## Consequences

- A test author writes the same form of test for both languages.
- A missing test for an item of the spec fails `just ci`. A known gap is visible as a tagged line in an inventory.
- Each exception names a gap of `doc/trust.md`, so the trust document and the tests stay in agreement.
- Coverage and mutation testing add CI time. The mutation run on a pull request covers only the changed lines. The full run is weekly.
- A commit that lowers a coverage floor changes nothing else. A decrease is thus visible in the history.
- The file move changes many paths at once. The rollout uses three commits, so each commit passes its checks.
