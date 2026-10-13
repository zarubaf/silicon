# Context

This file is the project glossary. Each term has one definition. Use the term with this meaning only. An `_Avoid_` line lists synonyms that the project rejects. `xtask` makes the vale vocabulary from this file.

## Language and semantics

### core IR

The small intermediate representation that has a formal semantics in Lean 4. It contains registers, memories, combinational logic, and module instances. Elaboration produces it.

_Avoid_: intermediate language

### elaboration

The step that evaluates parameters, generics, and loops of the source. Its output is core IR without these constructs.

_Avoid_: unrolling

### register

A state element that updates once per clock edge. It is a first-class primitive of the language.

_Avoid_: flop, flip-flop

### memory

An addressable array of state elements in the core IR.

### module

A named hardware unit with ports. A module declaration defines it. A design uses it through instances.

_Avoid_: entity

### instance

One use of a module inside another module. Each instance has its own state.

### instantiation

A module together with its specific elaboration inputs, for example its parameters. `InstantiationId` identifies it.

### design

The full hierarchy of instances under one top module. Its semantics is a Mealy machine.

### port dependencies

The map from each output of a module to the inputs that the output reads in the same cycle. The checker infers them from the module body.

### step function

The Lean function that defines one clock cycle of a design. It maps a state and an input to the next state and an output.

_Avoid_: transition function

### black box

A primitive with an assumed contract and no Silicon body. Examples are SRAM macros, PLLs, vendor IP, and clock gates.

_Avoid_: blackbox

### clock domain

The set of registers and memories that one clock drives. A crossing between two clock domains goes through an explicit primitive.

### .sil file

A core IR file in the text format.

### .si file

A Silicon source file.

### edition

A version of the source language rules. Each package selects one edition. Packages with different editions work together.

_Avoid_: language version

## Correctness

### translation validation

A check for each compiler run. The compiler emits the core IR as a `.sil` file, and the Lean checker `silicon-check` confirms it. It replaces a verified compiler.

### LEC

Logical equivalence checking. A tool, for example `circt-lec`, proves that the core IR and the emitted Verilog have the same behavior.

_Avoid_: equivalence check

### reference lowering

The Lean function `lower` from the core IR to MLIR. LEC compares the output of the CIRCT pipeline against its output.

### memory model

The MLIR module for one memory configuration. Lean generates the reference memory model, and the theorem `mem_model_correct` proves it. The Rust backend generates its own memory model. LEC validates it against the Lean memory model.

### trust boundary

The line between the parts that are proven, the parts that are validated, and the parts that are trusted. `doc/trust.md` describes it.

### oracle

A tool or a model that can say "wrong" mechanically. Each agent works against an oracle.

### suite

A directory of test files under `tests/core/` or `tests/source/`. The directory selects the command and the oracle. The crate `testkit` runs each suite.

### directive

A comment line in a test file that gives its expectation, for example `expected-error` or `STEP`. Both languages use the same directive names.

### inventory

A reviewed file in `tests/inventory/` that lists the expected results of a tool or its known gaps. A difference between the tool and its inventory fails the check.

### spec coverage

The check that each error code, construct, command, and budget of the specs has a test in the suites. `cargo xtask coverage` runs it.

### mutant

A copy of the code with one small change from `cargo-mutants`. A test kills the mutant when it fails on it. A surviving mutant shows a missing test.

### source generator

The dev-only crate `srcgen`. It makes random source programs for `cargo xtask diff-si`: lifted core designs, typed programs, their twins, and their mutations. Its static evaluator models only the programs that its builder makes.

## Packages and names

### package

A unit of source that Lattice resolves and Silicon compiles. It has a name, a version, and an edition.

### PackageId

The exact identity of a source package. It contains the name, the version, the canonical source identity, and the source content digest.

### ModuleId

The identity of a module: a `PackageId` and the qualified declaration path.

### InstantiationId

The identity of an instantiation: a `ModuleId` and the canonical elaboration inputs.

### uniquification

The mandatory step that puts the package identity into each emitted module name. Two versions of one package then do not collide.

_Avoid_: name mangling

### emitted name

The globally unique name of a module in the output HDL. Uniquification makes it from a readable package prefix and an identity digest.

_Avoid_: mangled name

### name map

A machine-readable map from source names to full identities, emitted names, and source locations. Tools use it to find a source name from an emitted name.

### semantic artifact

A deterministic compiler output that holds the meaning of a package, for example its elaborated core IR. Proofs and synthesis depend on it.

## Front end

### front end

The compiler stages from a `.si` file to core IR: `syntax`, `parse`, `resolve`, `typeck`, and `elab`.

### reference elaborator

The Lean function that elaborates a `.si` file and a top selection into core IR. Its output defines the meaning of a source design. `silicon-check validate` compares each Rust elaboration with it.

### top selection

The top module of a build and its static arguments, for example `Counter(8)`.

### static value

A value that elaboration knows completely, for example an integer, a Boolean, a string, or a type. A signal never becomes a static value.

### comptime

The keyword that marks a static parameter, a static function, a static branch, or a static loop. Elaboration executes these constructs.

### generic pre-check

The checks of `typeck` that need no static values. They run on each item, also on an item that no instantiation uses.

### receiver call

The call `x.m(args)`. It calls the function `m`, and its receiver `x` binds to the first parameter of `m` without a written `comptime` mark. The receiver evaluates before the explicit arguments.

### pending root

The root of a place while a `mut` actual or an assignment with that root runs. In its window, a second `mut` actual or an assignment with this root is `S008`.

### window

The part of the source in which a root stays pending. For a `mut` actual, it is the indices of the actual and each later argument of the call. For an assignment, it is the indices of the place and the right side.

### budget

A limit of one elaboration: the fuel, which all parts of the elaboration share, or the nesting depth. An elaboration that goes above a budget fails with an error.

### cost unit

The unit of fuel. Elaboration charges cost units for each expression node and each statement. It also charges the size of each static value that it reads or makes, and each core node that it emits. This cost model is normative.

### structural path

The core IR name that elaboration gives to a declaration. It contains the enclosing loop values and call sites. It contains no byte offsets.

### slice

A set of language features that one milestone adds. A slice closes the full oracle loop before the next slice starts.

### source vector

An input line or an output line of a top module in source terms: source port names and source values.

### leaf

A part of a value or of a type, at any depth, that is not a container and not `()`. A leaf of a value is a static value or a hardware value. A leaf of a hardware data type has the type `Bool`, `UInt[W]`, or `SInt[W]`. A type without a leaf, for example `Unit` or `[T; 0]`, is empty.

### hardware leaf

A leaf of a value that is a hardware value. Elaboration lowers each hardware leaf of an aggregate to one core value.

### hardware aggregate

A container with at least one hardware leaf. A container without a hardware leaf is a static value. A list never holds a hardware leaf.

### reference aggregate

A hardware aggregate that refers to a whole port, register, wire, or child output, or to a static part of one. It holds its type. It does not expand into its leaves, so a read, a selection, and a typed use of it take constant work. It has the zero size of its type.

### leaf name

The core name of one leaf of an aggregate binding. It is the name of the binding and its version, then one field for each step to the leaf. A record field is a user field, and an array index or a tuple element is the made field `<k>e`. For example, the field `a` of the port `p` is `p$a`.

### shared condition

The condition of a hardware `if` whose walk makes two or more `mux` nodes. Elaboration marks it once, and the lowering binds it to one temporary that each leaf statement uses. A core name or a constant gets no mark.

### packing order

The order of the leaves of a hardware data type. Array index 0, tuple element 0, and the first record field come first, recursively. A memory word puts the first leaf in the least significant bits.

### port layout

The order of the core ports of a module: the domain ports, the inputs, then the outputs, each group sorted by source name. The leaves of one port follow in packing order. `Source.Layout` and `elab::layout` define it.

### observation record

The record that one call of the source builtin `diagnostic` appends during elaboration. The command `observe` prints the records. An observation record is not a diagnostic.

### diagnostic

The report of one error of the front end. It has a code, spans, notes, help, and suggested edits. Only its code, its line, and its column are normative. The records of the source builtin `diagnostic` are observation records, not diagnostics.

_Avoid_: hint

### applicability

The confidence of a suggested edit in a diagnostic: machine-applicable or maybe-incorrect. A tool applies only a machine-applicable edit without a human.

## Process

### architecture review

A review of the whole system against `doc/architecture.md`, the ADRs, and `doc/trust.md`. A reviewer from a different vendor with fresh context does it. It is separate from the review of a diff.

### architecture path

A path whose change requires an architecture review of the pull request. `doc/architecture.md` lists these paths.

### drift review

A periodic architecture review. It runs after 15 merged pull requests or after one week, whichever comes first.

### milestone review

A full architecture review at each milestone, for example at the end of a build step. Two reviewers from different vendors do it independently.

### human gate

An area where only the user accepts a decision. The areas are the core IR semantics, the language design, and the trust boundary.

### worktree

A git worktree under `.claude/worktrees/`. Each task has its own worktree and its own branch.

### orchestrator

The main Claude Code session. It splits work, dispatches subagents, reads their results, and merges. It does not write product code.

_Avoid_: coordinator
