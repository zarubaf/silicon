# Trust boundary

This document is the authority for the trust boundary. It gives the status, the oracle, the gap, and the issue of each part. [The core IR spec](design/2026-10-08-core-ir.md) defines the parts.

## Statuses

- **Proven**: the Lean kernel checks a proof for all inputs.
- **Validated**: a mechanical oracle checks each run or each input of the corpus. No proof covers the part.
- **Trusted**: no check covers the part. The project assumes that it is correct.
- **Planned: X**: the part gets status X when its issue closes. Until then, no check covers the part.
- **Not supported**: the checker rejects the construct, or the text format has no syntax for it.
- **Out of scope**: Silicon does not check the property. Existing dedicated tools cover it. See [ADR 0005](adr/0005-synchronous-two-state-semantics.md).

## Parts

| Part                                                                                                | Status             | Oracle                                                                                                   | Gap                                                                            | Issue |
| --------------------------------------------------------------------------------------------------- | ------------------ | -------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ | ----- |
| The Lean theorems of the core IR spec, section 6.3, without `mem_model_correct` and `lower_correct` | Proven             | The Lean kernel                                                                                          | `canonicalize_step` and `canonicalize_sem` cover only designs without externs  |       |
| The core IR of each compiler run                                                                    | Planned: Validated | `silicon-check check`                                                                                    | None                                                                           | #27   |
| The Rust checker and interpreter                                                                    | Validated          | Differential tests against Lean                                                                          | No proof                                                                       | #10   |
| The Lean reference lowering and the Lean memory models                                              | Planned: Proven    | `lower_correct` and `mem_model_correct`                                                                  | The `Mlir` semantics must match CIRCT. `arcilator` and `circt-lec` check this. | #6    |
| The Rust memory models                                                                              | Planned: Validated | LEC against the Lean memory models                                                                       | None                                                                           | #9    |
| The Rust lowering and the CIRCT passes                                                              | Planned: Validated | LEC against the Lean reference MLIR                                                                      | None                                                                           | #9    |
| The compiled `silicon-check`                                                                        | Trusted            | None. It trusts the Lean compiler, as `native_decide` does.                                              | The Lean compiler                                                              |       |
| `circt-lec`, `circt-verilog`, Z3, and the MLIR parser                                               | Trusted            | None. They close the gap behind CIRCT.                                                                   | The tools themselves                                                           |       |
| A register whose next value is the register itself                                                  | Trusted            | None. LEC skips such designs.                                                                            | `--externalize-registers` of CIRCT 1.160 crashes                               | #20   |
| Black boxes                                                                                         | Trusted            | None. The project assumes their contracts.                                                               | The contract of each black box                                                 |       |
| Asynchronous reset, more than one clock domain, and CDC primitives                                  | Not supported      | The parser rejects a reset kind other than `sync` (`E001`). The checker rejects a second clock (`E009`). | No semantics                                                                   | #11   |
| Synchronous memory read ports and write masks                                                       | Not supported      | The text format has no syntax for them                                                                   | No semantics                                                                   | #12   |
| 4-state behavior, CDC verification, and timing                                                      | Out of scope       | None. Existing dedicated tools cover them.                                                               | None                                                                           |       |

## Gaps

### No proof of the Rust checker and interpreter

Differential tests compare the Rust checker and interpreter with Lean. A test finds a disagreement only on the designs and the inputs that it runs. Issue #10 proves the Rust code against the Lean spec, for example through Aeneas.

### The `Mlir` semantics and CIRCT

`lower_correct` will prove the Lean lowering against the `Mlir` semantics in Lean. The `Mlir` semantics must match the meaning that CIRCT gives to the same operations. No proof covers this match. `arcilator` runs the same MLIR in the differential tests, and `circt-lec` reads it in LEC. These two oracles check the match.

### The compiled `silicon-check`

Lake compiles `silicon-check` to native code. The Lean kernel does not check the compiled code. The checker thus trusts the Lean compiler, as `native_decide` does.

### A register whose next value is the register itself

The pass `--externalize-registers` of CIRCT 1.160 crashes on a register whose next value is the register itself. A design with `(next r r)` has such a register. A memory model without a write port also has one. LEC skips such designs, so no oracle checks them. Issue #20 tracks a fix.

### Black boxes

A black box has an assumed contract and no Silicon body. No check covers the contract. The interpreters reject a design with an extern.

### Asynchronous reset, more than one clock domain, and CDC

The semantics has one clock and synchronous reset only. The parser rejects a reset kind other than `sync` with `E001`. The checker rejects a second clock with `E009`. Issue #11 adds asynchronous reset, more than one clock domain, and CDC primitives.

### Synchronous memory read ports and write masks

A memory of the core IR has a combinational read and no write mask. Real SRAM macros nearly always have a synchronous read, so macro replacement needs these features. Issue #12 adds them.
