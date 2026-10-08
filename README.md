# Silicon

Silicon is a hardware description language with synchronous, 2-state semantics. Lean 4 holds the normative spec, Rust holds the compiler, and translation validation checks each compiler run against the spec.

## Setup

Install Nix and direnv. Then run this command in the repository:

```sh
direnv allow
```

The Nix flake then loads the pinned toolchain.

## Commands

The `justfile` is the only entry point.

| Command                  | Action                                                    |
| ------------------------ | --------------------------------------------------------- |
| `just`                   | List the recipes                                          |
| `just fmt`               | Format all files                                          |
| `just check`             | Run the formatter checks, the linters, and the Lean build |
| `just test`              | Run the Rust tests                                        |
| `just ci`                | Run `just check`, `just test`, and the commit checks      |
| `just prose`             | Lint the Markdown prose and the internal links            |
| `just lean`              | Build the Lean project                                    |
| `just commit-check base` | Check the commits from `base` to `HEAD`                   |

## Read next

- [`AGENTS.md`](AGENTS.md): the rules for each contributor and each agent.
- [`doc/architecture.md`](doc/architecture.md): the pipeline and the trust boundary.
