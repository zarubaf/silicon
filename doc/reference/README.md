# Silicon contracts and interoperability

Silicon combines hardware generators with independent, executable Lean contracts. A contract states what a component does. Different circuits can implement that contract, with proofs that relate their internal states to the same specification.

This is the central idea of the [language proposal](SILICON_SPEC.md). Generators construct explicit circuits; Lean connects those circuits to reusable specifications. The same specifications can serve as executable reference models for simulation and existing RTL.

These source attachments and integration APIs are proposals, not claims about implemented features. The repository's [architecture](../architecture.md) and [trust boundary](../trust.md) remain authoritative for the current compiler.

## Two roles for Lean

Lean has two distinct roles in Silicon:

| Role                           | Question                                                                 |
| ------------------------------ | ------------------------------------------------------------------------ |
| Language and core IR semantics | What does this circuit mean, and does compilation preserve that meaning? |
| Independent component contract | Does this particular circuit implement the intended behavior?            |

Translation validation and reference lowering address compiler correctness. A component contract addresses design correctness. A correct compiler can compile a circuit that violates its intended contract.

An independent contract has its own state, initial state, next-state function, observations, and assumptions. Its executable functions support simulation. Its propositions support proofs over all admitted behaviors.

The contract must not depend on generated implementation models or proof companions, even through another module. The proof companion can import both the contract and the generated model. Shared independent libraries are allowed.

```text
Independent Lean contract ────┐
                             ├── proof companion ── checked refinement
Silicon source → actual model┘

Independent Lean contract → executable reference → simulation comparison
```

A proof about the generated circuit alone cannot establish that it implements an independently chosen requirement. The selected contract supplies that requirement.

## A counter with two implementations

Consider a width parameter W, with W greater than zero. The contract exposes an enable input, a value output, and a full output. Its state is a W-bit count c.

On a selected clock edge, reset sets c to zero. Otherwise, enable increments c modulo 2^W; without enable, c holds. Outputs show the old count before the edge. Full means c equals 2^W minus one.

The proposed Silicon attachment has this form. The named Lean contract and proof companion are external declarations, not definitions supplied by this snippet.

```silicon
pub module Counter(comptime W: Nat)
    conforms demo::CounterStatus(W) using demo::CounterStatusProof(W) {
    input enable: Bool;
    output value: UInt[W];
    output full: Bool;
    reg count: UInt[W] = 0;
    count := if (enable) { count +% 1 } else { count };
    value := count;
    full := count == UInt[W]((1 << W) - 1);
}
```

Elaboration specializes this generator for W and freezes its circuit. The proof relates the actual register to the independent contract state through `R(actual, spec) := actual.count = spec.c`.

A second implementation stores the bitwise complement of c. It resets its register to all ones and subtracts one when enabled. Its value output complements the stored register. Its full output compares that value with all ones.

The second proof uses `R(actual, spec) := actual.stored = bitwise_not(spec.c)`. The contract stays unchanged. Both implementations must account for every output, including full, even if the parent does not use it.

For cycle refinement, the proof establishes these obligations:

1. The designated initial states satisfy R.
2. Each admitted step preserves R.
3. Related states produce equal complete outputs before the edge.
4. A complete reset establishes R from every actual state, without an input-admissibility premise.
5. The same reset takes every specification state to its designated initial state.

A component without that reset guarantee needs explicitly labeled evidence from its designated start. A false reset predicate cannot supply an after-reset guarantee.

### Composition preserves the contract boundary

A parent connects ports of a named child instance. Its proof uses that child's checked guarantee and the projections of its actual state, wired inputs, and complete outputs.

For example, a more general counter can expose an increment input. A unit-counter contract can require increment to equal one whenever enable is true. The parent binds increment to one and proves that the captured input satisfies this assumption.

Changing the child's state encoding need not change the parent's contract-based reasoning. The checker must still check the parent against the replacement child's current model and seal. A previous certificate cannot authorize changed wiring or a changed implementation.

The parent must discharge child assumptions under its own invariant and assumptions. It cannot assume an unproved child contract. It can instead unfold the child's implementation and prove the parent directly.

## Executable specifications across tool boundaries

Interoperability makes the independent contract useful beyond Silicon source. The same behavioral specification can guide a new circuit, test an existing RTL block, and support a host simulation harness.

| Boundary                                   | Intended use                                                 | Evidence                                              |
| ------------------------------------------ | ------------------------------------------------------------ | ----------------------------------------------------- |
| Lean contract to Silicon model             | Prove a circuit implements the selected contract             | Checked refinement, under explicit assumptions        |
| Lean contract to native reference          | Run the specification on concrete inputs                     | Execution of the independent specification closure    |
| Native reference to existing SystemVerilog | Compare through DPI-C, Verilator, UVM, or cocotb integration | Finite trace agreement                                |
| Generated circuit model to C, C++, or Rust | Drive simulation through a stable host ABI                   | Transport and simulation behavior                     |
| Foreign hardware to Silicon                | Instantiate existing RTL or a macro with a declared model    | Explicit model evidence and foreign trust assumptions |

These are integration paths, not a list of finished adapters. The [architecture](../architecture.md#verification-against-existing-systemverilog) also describes formal checks against existing SystemVerilog.

### Host execution and observation

The proposed host model boundary uses opaque, independently owned instances. C callers exchange canonical byte records rather than compiler-specific structs. Rust and C++ wrappers can enforce ownership and exclusive access.

The schema fixes field order, widths, signedness, domain identities, reset inputs, event bits, and observation timing. Arbitrary-width integers require an explicit byte encoding. A caller checks both model and schema identities before using an instance.

`eval` observes the current state without mutation. `step` returns outputs from its supplied inputs and old state, then commits the selected domain edges together. It does not depend on an earlier `eval` call. An empty edge set holds state, even when reset is asserted.

Batch execution must match repeated steps. Validation errors leave state and output buffers unchanged. The boundary has no callbacks into elaboration or implicit global simulation instance.

Compile the independent Lean specification separately from generated implementation and proof modules. Feed both models the same inputs and domain events. Compare complete observations, or use an explicitly selected event adapter.

Using one generated backend behind two language wrappers only checks transport consistency. It does not supply an independent semantic reference. Native Lean replacements and runtime dependencies also need an explicit execution trust boundary.

### Existing hardware

A proposed `extern module` binds a Silicon interface to a locked foreign artifact. Its descriptor supplies ports, parameters, clocks, resets, dependency arcs, timing, and an executable digital model.

This boundary permits integration with existing hardware while keeping the claimed evidence explicit. A proof about its digital model does not itself prove that vendor RTL or physical hardware matches that model.

Clock domain crossings require qualified boundaries and explicit assumptions. Digital refinement does not establish physical metastability safety. Native host calls cannot execute inside synthesized hardware or deterministic elaboration.

## Contracts across different latencies

Full cycle equality is appropriate when every output and cycle must match. Pipelines, transaction engines, and processors may need a contract over accepted requests and retired results instead.

An explicit executable observer maps actual inputs, outputs, and domain events to contract events. Its definition includes handshake guards, payloads, ordering, and reset cancellation. The checker binds the exact observer and independent specification to the actual circuit.

For example, an immediate incrementer and a delayed incrementer can implement the same request/result contract. Each must return operand plus one for its actual accepted requests. Different ready signals can produce different accepted sequences under the same offered inputs.

An event proof therefore does not claim cycle equality. The observer must cover the declared protocol observations; an observer that emits nothing cannot hide actual accepted requests.

Safety and progress are separate claims. Correct retired results do not show that every accepted request eventually retires. A progress theorem must identify each accepted occurrence, its matching retirement or reset cancellation, and the required environment assumptions.

Child event guarantees also require checked composition. They do not automatically provide cycle guarantees or parent progress.

## What the checker must bind

The final certificate must identify the exact contract application, proof, actual model, port schema, parameters, domain maps, and captured wiring. Source and dependency hashes, tool identities, theorem types, and the transitive axiom audit are part of that identity.

The checker owns this binding. A theorem for another model, an omitted output, a different observer, or stale source bytes cannot certify the current circuit.

Model refinement proves the selected behavioral relation under its assumptions. Compiler correctness, RTL correspondence, native reference execution, and physical behavior each have their own evidence boundaries.

Keep these distinctions when deriving the new language. The essential capability is to connect independent executable specifications, generated hardware, reusable proofs, and external tools through exact, checkable interfaces.

The [language reference](SILICON_SPEC.md) gives the detailed proposed rules. The [grammar](SILICON_GRAMMAR.ebnf) gives the proposed source syntax. This overview preserves the integration intent without importing the prototype compiler or fixing a new library ABI.
