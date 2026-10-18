set positional-arguments

default:
    @just --list

fmt: fmt-rust fmt-files fmt-just

fmt-check: fmt-rust-check fmt-files-check fmt-just-check

fmt-rust:
    cargo fmt

check: fmt-check clippy repo-check prose deny machete lean

fmt-rust-check:
    cargo fmt --check

fmt-files:
    cargo xtask fmt

fmt-just:
    just --fmt --unstable

fmt-files-check:
    cargo xtask fmt --check

fmt-just-check:
    just --fmt --check --unstable

clippy:
    cargo clippy --workspace --all-targets --all-features --quiet -- -D warnings

repo-check:
    cargo xtask check

prose *files:
    cargo xtask prose "$@"

deny:
    cargo deny --log-level error check

machete:
    cargo machete

lean:
    lake -d lean build --wfail

lean-check:
    cargo xtask lean-check

diff:
    cargo xtask diff

diff-si:
    cargo xtask diff-si

lec:
    cargo xtask lec

test:
    cargo nextest run --workspace --all-features

commit-msg file:
    cargo xtask commit-msg {{ file }}

commit-check base="origin/main":
    cargo xtask commit-check --base {{ base }}

ci base="origin/main": check test lean-check diff diff-si lec (commit-check base)

setup:
    lefthook install

review base="main":
    cargo xtask review --base {{ base }}

review-scope base="origin/main":
    cargo xtask review-scope --base {{ base }}

review-due:
    cargo xtask review-due

arch-summary:
    cargo xtask arch-summary
