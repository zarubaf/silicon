default:
    @just --list

fmt: fmt-rust

fmt-rust:
    cargo fmt

check: fmt-rust-check clippy repo-check deny machete

fmt-rust-check:
    cargo fmt --check

clippy:
    cargo clippy --workspace --all-targets --quiet -- -D warnings

repo-check:
    cargo xtask check

deny:
    cargo deny --log-level error check

machete:
    cargo machete

test:
    cargo nextest run --workspace

ci: check test
