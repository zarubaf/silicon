// SPDX-License-Identifier: Apache-2.0
//! The cases of the hardware resources in `Silicon.Source.Test.Elab`: an aggregate or an empty
//! port, register, and wire, the register initializer, the `:=` binding of an aggregate, the
//! copy charge, the `S017` targets, and a function type in an aggregate. The elaboration alone
//! runs here: `ok` with its units, or the code and the position of the first error.

use crate::tests_elab::{cost, total};

/// The elaboration of `src` with the top module `M`.
fn elab(src: &str) -> String {
    let c = cost(src, "M");
    match c.strip_prefix("total ") {
        Some(rest) => format!("ok {}", rest.lines().next().unwrap_or_default()),
        None => c,
    }
}

/// The units of the elaboration, or 0 for an error.
fn units(src: &str) -> u64 {
    elab(src)
        .strip_prefix("ok ")
        .and_then(|n| n.parse().ok())
        .unwrap_or(0)
}

fn ok(src: &str) {
    assert!(elab(src).starts_with("ok"), "{src}\n{}", elab(src));
}

const PS: &str = "struct P(comptime W: Nat) { a: UInt[W], b: Bool }\n";

fn agg(body: &str) -> String {
    format!("{PS}module M() {{\n  input x: P[8];\n{body}}}\n")
}

/// A port, a register, and a wire have a hardware data type: a struct, an array, or a tuple.
#[test]
fn aggregate_resources_read_select_and_bind() {
    ok(&agg(""));
    ok(&agg("  output y: P[8];\n  y := x;\n"));
    ok(&agg("  output y: UInt[8];\n  y := x.a;\n"));
    ok(&agg("  reg r: P[8] = P[8](3, true);\n  r := x;\n"));
    ok(&agg(
        "  reg r: P[8] = P[8]();\n  r := r;\n  output y: Bool;\n  y := r.b;\n",
    ));
    ok(&agg(
        "  wire w: [Bool; 2];\n  w := [x.b, true];\n  output y: Bool;\n  y := w[1];\n",
    ));
    ok(&agg(
        "  wire w: (UInt[8], Bool);\n  w := (x.a, x.b);\n  output y: UInt[8];\n  y := w.0;\n",
    ));
}

fn reg_init(ty: &str, v: &str) -> String {
    format!("module M() {{\n  reg r: {ty} = {v};\n  r := r;\n}}\n")
}

/// The register value takes the register type by a typed use. `[]` gets the register type.
#[test]
fn a_register_initializer_takes_the_register_type() {
    ok(&reg_init("[UInt[4]; 2]", "[1, 2]"));
    assert_eq!(elab(&reg_init("[UInt[4]; 2]", "[1, 16]")), "S012 2:3");
    assert_eq!(elab(&format!("{PS}{}", reg_init("P[8]", "1"))), "S010 3:3");
    ok(&reg_init("[Bool; 0]", "[]"));
    ok(&reg_init("([UInt[8]; 0], Bool)", "([], false)"));
    assert_eq!(elab(&reg_init("[Bool; 1]", "[]")), "S010 2:3");
}

/// A `:=` binding of an aggregate is one binding. A static leaf takes its type, and another
/// type is `S010`.
#[test]
fn a_binding_of_an_aggregate_is_one_binding() {
    ok(&agg("  output y: (UInt[8], UInt[8]);\n  y := (x.a, 1);\n"));
    assert_eq!(
        elab(&agg(
            "  output y: (UInt[8], UInt[8]);\n  y := (x.a, 256);\n"
        )),
        "S012 5:3"
    );
    assert_eq!(
        elab(&format!(
            "{PS}module M() {{\n  input x: P[4];\n  output y: P[8];\n  y := x;\n}}\n"
        )),
        "S010 5:3"
    );
    assert_eq!(elab(&agg("  output y: UInt[8];\n  y := x;\n")), "S010 5:3");
}

/// The copy of an aggregate handle charges 1 plus the zero size of its type. A port is a
/// reference already, so its copy charges the zero size alone.
#[test]
fn the_copy_of_an_aggregate_charges_its_zero_size() {
    let via = |y: &str| {
        format!(
            "module M() {{\n  input x: (UInt[256], Bool);\n  wire w: (UInt[256], Bool);\n  \
             output y: (UInt[256], Bool);\n  w := x;\n  y := {y};\n}}\n"
        )
    };
    assert_eq!(units(&via("w")), units(&via("x")) + 1);
    assert!(units(&via("x")) > 0);
}

/// A `:=` target is a whole resource. A part of a register, an output, or a child input is
/// `S017` at the start of the target. A hardware index is `S011`.
#[test]
fn a_part_of_a_resource_is_no_target() {
    assert_eq!(
        elab(&agg("  reg r: P[8] = P[8]();\n  r.a := 1;\n")),
        "S017 5:3"
    );
    assert_eq!(
        elab(&agg("  output y: P[8];\n  y.b := true;\n")),
        "S017 5:3"
    );
    assert_eq!(
        elab(&agg("  output y: P[8];\n  y := x;\n  x := y;\n")),
        "S017 6:3"
    );
    assert_eq!(
        elab(&agg(
            "  input z: [Bool; 4];\n  output y: Bool;\n  let k = x.a;\n  y := z[k];\n"
        )),
        "S011 7:10"
    );
    assert_eq!(
        elab("module M() {\n  input x: [Bool; 4];\n  output y: Bool;\n  y := x[4];\n}\n"),
        "S013 4:10"
    );
}

/// A reference stays lazy: a read and a static index of a port with 2^40 leaves take constant
/// work, and the copy of the whole port is `S015` at the statement.
#[test]
fn a_huge_port_selects_cheaply_and_copies_never() {
    let huge = |body: &str| format!("module M() {{\n  input x: [Bool; 1099511627776];\n{body}}}\n");
    assert!(units(&huge("  output y: Bool;\n  y := x[5];\n")) < 100);
    assert_eq!(
        elab(&huge("  output y: [Bool; 1099511627776];\n  y := x;\n")),
        "S015 4:3"
    );
}

const WITH_FN: &str = "struct R { f: fn () -> Bool, a: Bool }\n";

/// A type with a function type at any depth is not hardware data.
#[test]
fn a_function_type_in_an_aggregate_is_no_data() {
    let m = |body: &str| format!("{WITH_FN}module M() {{\n{body}}}\n");
    assert_eq!(elab(&m("  input x: R;\n")), "S010 3:3");
    assert_eq!(
        elab(&m("  output y: (Bool, [fn () -> Bool; 0]);\n")),
        "S010 3:3"
    );
    assert_eq!(elab(&m("  wire w: [R; 0];\n")), "S010 3:3");
    assert_eq!(elab(&m("  reg r: (Bool, R) = (true, R());\n")), "S010 3:3");
}

fn empty(body: &str) -> String {
    format!("module M() {{\n{body}}}\n")
}

/// A port, a register, and a wire can have an empty type. Each still needs exactly one `:=`.
/// A register in a combinational module is `S017` first.
#[test]
fn empty_resources_need_one_binding() {
    ok(&empty(
        "  input e: ();\n  output o: ();\n  o := e;\n  wire w: [UInt[8]; 0];\n  w := [];\n  \
         reg r: () = ();\n  r := ();\n",
    ));
    assert_eq!(elab(&empty("  wire w: ();\n")), "S018 2:3");
    assert_eq!(elab(&empty("  output o: [Bool; 0];\n")), "S018 2:3");
    assert_eq!(elab(&empty("  reg r: () = ();\n")), "S018 2:3");
    assert_eq!(
        elab("module M() domains() {\n  reg r: () = ();\n}\n"),
        "S017 2:3"
    );
    assert_eq!(
        elab(&empty("  wire w: ();\n  w := ();\n  w := ();\n")),
        "S018 4:3"
    );
}

fn empty_child(bind: &str) -> String {
    format!("module C() {{\n  input p: ();\n}}\nmodule M() {{\n  instance c = C();\n{bind}}}\n")
}

/// An empty input of a child still needs its binding at the `instance` statement.
#[test]
fn an_empty_child_input_needs_one_binding() {
    assert_eq!(elab(&empty_child("")), "S018 5:3");
    ok(&empty_child("  c.p := ();\n"));
}

fn empty_in(ty: &str, body: &str) -> String {
    format!("module M() {{\n  input x: {ty};\n{body}}}\n")
}

/// An empty input charges nothing at its declaration, also with 2^40 leaves. Each read of it
/// charges the zero size of its type. `[(); 8]` has the zero size 9, the `let` and the name
/// charge 1 each.
#[test]
fn an_empty_input_is_lazy() {
    assert_eq!(elab(&empty_in("[(); 1 << 40]", "")), "ok 43");
    assert_eq!(
        elab(&empty_in("[(); 1 << 40]", "  let y = x;\n")),
        "S015 3:11"
    );
    assert_eq!(
        units(&empty_in("[(); 8]", "  let y = x;\n")),
        units(&empty_in("[(); 8]", "")) + 11
    );
    assert_eq!(
        units(&empty_in("()", "  let y = x;\n")),
        units(&empty_in("()", "")) + 3
    );
    assert!(total(&empty_in("()", ""), "M") > 0);
}

fn agg_child(bind: &str) -> String {
    format!(
        "{PS}module C() {{\n  input p: P[8];\n  output q: P[8];\n  q := p;\n}}\n\
         module M() {{\n  input x: P[8];\n  output y: UInt[8];\n  instance c = C();\n{bind}  \
         y := c.q.a;\n}}\n"
    )
}

/// A child port can have an aggregate type. A `:=` of a child input is one binding. A child
/// output gives a reference, and a part of it is read. A part of a child input is `S017`.
#[test]
fn a_child_port_can_be_an_aggregate() {
    ok(&agg_child("  c.p := x;\n"));
    assert_eq!(elab(&agg_child("  c.p.a := x.a;\n")), "S017 11:3");
    assert_eq!(elab(&agg_child("")), "S018 10:3");
    assert_eq!(elab(&agg_child("  c.p := (x.a, x.b);\n")), "S010 11:3");
    let whole = format!(
        "{PS}module C() {{\n  output q: P[8];\n  q := P[8](1, true);\n}}\n\
         module M() {{\n  output y: P[8];\n  instance c = C();\n  y := c.q;\n}}\n"
    );
    ok(&whole);
}

fn read_child(ty: &str, read: &str) -> String {
    format!(
        "{PS}module C() {{\n  input p: {ty};\n}}\n\
         module M() {{\n  input x: {ty};\n  output y: Bool;\n  instance c = C();\n  \
         c.p := x;\n  y := {read};\n}}\n"
    )
}

/// A data selection is a data context (section 9.2). A read of a part of a child input is thus
/// `S017` at the start of the selection, before the field check.
#[test]
fn a_part_of_a_child_input_is_never_read() {
    for (ty, read, at) in [
        ("P[8]", "c.p.b", "10:8"),
        ("P[8]", "!c.p.b", "10:9"),
        ("P[8]", "c.p.c", "10:8"),
        ("[Bool; 2]", "c.p[0]", "10:8"),
        ("(Bool, Bool)", "c.p.1", "10:8"),
    ] {
        assert_eq!(elab(&read_child(ty, read)), format!("S017 {at}"), "{read}");
    }
}

fn mem_body(ss: &str) -> String {
    format!("module M() {{\n{ss}}}\n")
}

fn fuel_at(src: &str, fuel: u64) -> String {
    crate::tests_elab::cost_fuel(src, "M", fuel)
}

/// The `mem` statement (spec section 6.2). Each check is at the statement, in this order: the
/// charge, a combinational module, the word type, then the depth. The cases and their values
/// come from `Silicon.Source.Test.Elab`.
#[test]
fn the_mem_statement_checks_in_order() {
    let comb = "module M() domains() {\n  mem m: [Int; 0];\n}\n";
    assert_eq!(cost(comb, "M"), "S017 2:3");
    assert_eq!(fuel_at(comb, 28), "S017 2:3");
    assert_eq!(fuel_at(comb, 27), "S015 2:3");
    let hw = "  input x: UInt[4];\n  let h = x;\n";
    let cases = [
        ("  mem m: [Int; 4];\n".to_owned(), "S010 2:3"),
        ("  mem m: [(); 4];\n".to_owned(), "S010 2:3"),
        ("  mem m: [[Unit; 4]; 4];\n".to_owned(), "S010 2:3"),
        ("  mem m: [[fn () -> Bool; 0]; 4];\n".to_owned(), "S010 2:3"),
        (
            "  mem m: [UInt[65536]; 4];\n  mem k: [[UInt[65536]; 2]; 4];\n".to_owned(),
            "S012 3:3",
        ),
        ("  mem m: [Bool; 0];\n".to_owned(), "S012 2:3"),
        ("  mem m: [Bool; 16777217];\n".to_owned(), "S012 2:3"),
        ("  mem m: [Bool; -1];\n".to_owned(), "S012 2:3"),
        ("  mem m: [Bool; true];\n".to_owned(), "S010 2:3"),
        ("  mem m: [Bool; \"a\"];\n".to_owned(), "S010 2:3"),
        ("  mem m: [Bool; []];\n".to_owned(), "S010 2:3"),
        (format!("{hw}  mem m: [Bool; h];\n"), "S011 4:3"),
        (format!("{hw}  mem m: [Int; h];\n"), "S010 4:3"),
        (format!("{hw}  mem m: [[UInt[65536]; 2]; h];\n"), "S012 4:3"),
    ];
    for (body, want) in cases {
        assert_eq!(cost(&mem_body(&body), "M"), want, "{body}");
    }
}

/// A static `UInt[8]` depth is not an `Int`: `S010`, as the length of an array type.
#[test]
fn a_static_uint_depth_is_s010() {
    let src = mem_body("  mem m: [Bool; UInt[8](3)];\n");
    assert_eq!(cost(&src, "M"), "S010 2:3");
}

/// The charge: the statement, the type, and the depth, with no array type. A wide word with
/// the largest depth costs as much as one with the depth 1.
#[test]
fn the_mem_charge_has_no_array_type() {
    let small = mem_body("  mem m: [Bool; 4];\n");
    assert_eq!(fuel_at(&small, 31), "S018 2:3");
    assert_eq!(fuel_at(&small, 30), "S015 2:17");
    for depth in ["16777216", "1"] {
        let wide = mem_body(&format!("  mem m: [UInt[65536]; {depth}];\n"));
        assert_eq!(fuel_at(&wide, 36), "S018 2:3", "{depth}");
        assert_eq!(fuel_at(&wide, 35), "S015 2:24", "{depth}");
    }
}

/// A memory is never data: a read, an index, a field, and an operand are `S010` at the use. A
/// `let` alias keeps the handle, so only its read fails.
#[test]
fn a_memory_is_never_data() {
    let cases = [
        (
            "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m;\n",
            "S010 4:3",
        ),
        (
            "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m[0];\n",
            "S010 4:8",
        ),
        (
            "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m.a;\n",
            "S010 4:8",
        ),
        (
            "  output y: Bool;\n  mem m: [Bool; 4];\n  y := m + 1;\n",
            "S010 4:8",
        ),
        (
            "  mem m: [Bool; 4];\n  let a = m;\n  let b: Bool = a;\n",
            "S010 4:3",
        ),
        ("  mem m: [Bool; 16777216];\n  let a = m;\n", "S018 2:3"),
    ];
    for (body, want) in cases {
        assert_eq!(cost(&mem_body(body), "M"), want, "{body}");
    }
}

/// `S018` at the statement competes by position with the other bindings, also in a loop.
#[test]
fn a_memory_without_a_port_call_is_s018_at_its_statement() {
    let cases = [
        ("  mem m: [Bool; 4];\n  wire w: Bool;\n", "S018 2:3"),
        ("  wire w: Bool;\n  mem m: [Bool; 4];\n", "S018 2:3"),
        (
            "  output y: Bool;\n  y := true;\n  mem m: [Bool; 4];\n  y := false;\n",
            "S018 4:3",
        ),
        (
            "  comptime for i in 0..2 {\n    mem m: [Bool; 2];\n  }\n",
            "S018 3:5",
        ),
    ];
    for (body, want) in cases {
        assert_eq!(cost(&mem_body(body), "M"), want, "{body}");
    }
}
