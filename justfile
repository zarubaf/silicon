default:
    @just --list

fmt: fmt-rust fmt-files fmt-just

fmt-check: fmt-rust-check fmt-files-check fmt-just-check

fmt-rust:
    cargo fmt

check: fmt-check clippy repo-check deny machete

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
