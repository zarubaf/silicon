// SPDX-License-Identifier: Apache-2.0
//! The enum types and values of Lean `Source.Eval` (slice 3, sections 5.1, 5.4, and 5.6): the
//! first use with its checks and charges, `T()`, `data_bits`, the typed use, the join, and the
//! texts of the `S010` cases. The numbers come from the Lean binary. The work tests count the
//! steps of the walks and not the time.

use crate::counters::of;
use crate::tests::{cost, exact, message, out, run, serialized_len, type_work};
use crate::tests_elab::{cost as elab_cost, cost_fuel, names, order, total};
use std::fmt::Write as _;

const OPS: &str = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n";

const ZERO: &str = "(enum (enum root Op ()) 0 (uint 8 0))";

/// The first use of an enum charges as the first use of a struct: the node 1, the size of the
/// enum type 1, the tag type 6, the three variants 8, 18, and 23, and the metadata of the enum
/// 12. A later use charges only its node.
#[test]
fn the_first_use_of_an_enum_charges_its_checks_once() {
    assert_eq!(out(OPS, "Op", 1 << 20, 1000), "(type (enum root Op ()))");
    exact(OPS, "Op", 69);
    exact(OPS, "[Op, Op]", 1 + 69 + 1 + 3);
}

#[test]
fn the_zero_of_an_enum_has_the_tag_0_and_the_payload_0() {
    assert_eq!(out(OPS, "Op()", 1 << 20, 1000), ZERO);
    exact(OPS, "Op()", 1 + 69 + 3);
    assert_eq!(out(OPS, "data_bits(Op)", 1 << 20, 1000), "(int 10)");
    exact(OPS, "data_bits(Op)", 2 + 69 + 1);
    assert_eq!(
        out("enum E: UInt[3] { A = 5 }\n", "E()", 1 << 20, 1000),
        "(enum (enum root E ()) 0)"
    );
    assert_eq!(
        out("enum E: UInt[1] {}\n", "data_bits(E)", 1 << 20, 1000),
        "(int 1)"
    );
    assert_eq!(
        out(OPS, "[Op(), Op()]", 1 << 20, 1000),
        format!("(array (enum root Op ()) ({ZERO} {ZERO}))")
    );
}

#[test]
fn the_checks_of_an_enum_run_in_their_order() {
    let e = |src: &str| out(src, "E", 1 << 20, 1000);
    assert_eq!(e("enum E: Bool { A = 0 }\n"), "S010 1:9");
    assert_eq!(e("enum E: UInt[1] { A = 2 }\n"), "S012 1:23");
    assert_eq!(e("enum E: UInt[1] { A = true }\n"), "S010 1:23");
    assert_eq!(e("enum E: UInt[1] { A = SInt[1](0) }\n"), "S010 1:23");
    assert_eq!(e("enum E: UInt[1] { A(Int) = 0 }\n"), "S010 1:21");
    assert_eq!(e("enum E: UInt[1] { A(Int) = 2 }\n"), "S012 1:28");
    let wide = "enum E: UInt[1] { A(UInt[65536], Bool) = 0, B(Int) = 1 }\n";
    assert_eq!(e(wide), "S010 1:47");
    let wide = "enum E: UInt[1] { A(UInt[65536], Bool) = 0 }\n";
    assert_eq!(e(wide), "S012 1:1");
    assert_eq!(
        message(wide, "E"),
        "the payload of `E` has 65537 bits, above 65536; use smaller payloads"
    );
    assert_eq!(
        out(
            "enum E: UInt[1] { A(UInt[65536]) = 0 }\n",
            "data_bits(E)",
            1 << 20,
            1000
        ),
        "(int 65537)"
    );
}

#[test]
fn an_enum_that_names_itself_is_s019_and_a_use_counts_toward_the_depth() {
    let e = |src: &str, depth: u64| out(src, "E", 1 << 20, depth);
    assert_eq!(e("enum E: UInt[1] { A(E) = 0 }\n", 1000), "S019 1:21");
    assert_eq!(
        message("enum E: UInt[1] { A(E) = 0 }\n", "E"),
        "the enum `E` depends on itself"
    );
    let through = "enum E: UInt[1] { A(S) = 0 }\nstruct S { e: E }\n";
    assert_eq!(e(through, 1000), "S019 2:15");
    assert_eq!(out(through, "S", 1 << 20, 1000), "S019 1:21");
    let nested = "enum E: UInt[1] { A(S) = 0 }\nstruct S { a: Bool }\n";
    assert_eq!(e(nested, 2), "(type (enum root E ()))");
    assert_eq!(e(nested, 1), "S015 1:21");
}

#[test]
fn a_tag_value_is_a_structural_context() {
    let src = "fn f() -> UInt[1] { let mut xs = list(Int); push(xs, 1); return 0; }\n\
               enum E: UInt[1] { A = f() }\n";
    assert_eq!(out(src, "E", 1 << 20, 1000), "(type (enum root E ()))");
}

#[test]
fn equality_on_a_type_with_an_enum_is_s010_by_the_flag() {
    let text = "`Op` has no `==`; compare with `match (x) { E::V => true, _ => false }`";
    assert_eq!(out(OPS, "Op() == Op()", 1 << 20, 1000), "S010 1:1");
    assert_eq!(message(OPS, "Op() == Op()"), text);
    assert_eq!(message(OPS, "Op() != 1"), text);
    assert_eq!(message(OPS, "1 == Op()"), text);
    assert_eq!(
        message(OPS, "[Op()] != [Op()]"),
        "`[Op; 1]` has no `==`; compare with `match (x) { E::V => true, _ => false }`"
    );
    assert_eq!(
        message(OPS, "(1, Op()) == (1, Op())"),
        "`(Int, Op)` has no `==`; compare with `match (x) { E::V => true, _ => false }`"
    );
    assert!(!out(OPS, "Op == Op", 1 << 20, 1000).starts_with('S'));
    assert!(!out(OPS, "(fn (Op) -> Bool) == (fn (Op) -> Bool)", 1 << 20, 1000).starts_with('S'));
}

#[test]
fn a_typed_use_needs_the_exact_enum_and_two_enums_join_as_a_type_equality() {
    let flags = format!("{OPS}enum Flag: UInt[1] {{ On = 1 }}\n");
    let id = format!("{OPS}fn f(x: Op) -> Op {{ return x; }}\n");
    assert_eq!(out(&id, "f(Op())", 1 << 20, 1000), ZERO);
    assert_eq!(out(&id, "f(1)", 1 << 20, 1000), "S010 1:1");
    let id = format!("{flags}fn f(x: Op) -> Op {{ return x; }}\n");
    assert_eq!(out(&id, "f(Flag())", 1 << 20, 1000), "S010 1:1");
    let constant = format!("{flags}const C: Op = Flag();\n");
    assert_eq!(out(&constant, "C", 1 << 20, 1000), "S010 3:1");
    assert!(!out(&flags, "[Op(), Op()]", 1 << 20, 1000).starts_with('S'));
    assert_eq!(out(&flags, "[Op(), Flag()]", 1 << 20, 1000), "S010 1:1");
    assert_eq!(out(&flags, "[Op(), 1]", 1 << 20, 1000), "S010 1:1");
    // The node, both zeros, the join 2 of the two enum types, and the size 7 of the literal.
    exact(
        &flags,
        "[Op(), Op()]",
        1 + (1 + 69 + 3) + (1 + 1 + 3) + 2 + 7,
    );
}

#[test]
fn a_field_or_a_selector_of_an_enum_is_s010() {
    let field = "`Op` is an enum and has no field `tag`; read a payload with `match`, or the bits \
                 with `reinterpret(UInt[10], e)`";
    assert_eq!(out(OPS, "Op().tag", 1 << 20, 1000), "S010 1:1");
    assert_eq!(message(OPS, "Op().tag"), field);
    assert_eq!(message(OPS, "Op().0"), field.replace("`tag`", "`0`"));
    let assign = format!("{OPS}fn f() -> Int {{ let mut e = Op(); e.payload = 1; return 0; }}\n");
    assert_eq!(out(&assign, "f()", 1 << 20, 1000), "S010 2:35");
}

#[test]
fn a_call_of_an_enum_with_arguments_is_s010_before_they_evaluate() {
    assert_eq!(out(OPS, "Op(1)", 1 << 20, 1000), "S010 1:1");
    assert_eq!(
        message(OPS, "Op(1 / 0, 2)"),
        "`Op` is an enum, so `Op(...)` takes no arguments; construct a variant such as \
         `Op::V(...)`, or write `Op()` for the zero"
    );
}

#[test]
fn an_enum_value_is_one_container_node_in_the_serialization() {
    // The length comes from the table and the walk writes the text once.
    let len = serialized_len(OPS, "[Op(), Op()]");
    let text = out(OPS, "[Op(), Op()]", 1 << 20, 1000);
    assert_eq!(len, text.len() as u64);
}

/// A variant constructor is one node, then a use of the enum. Then its payload values evaluate,
/// their copies charge, and each gets its typed use at its payload type. Then the size of the
/// result charges, 3 for a static `Op` value, and the static pack makes it.
#[test]
fn a_static_constructor_charges_in_the_order_of_section_5_4() {
    let one = |expr: &str| out(OPS, expr, 1 << 20, 1000);
    assert_eq!(one("Op::Add"), ZERO);
    exact(OPS, "Op::Add", 1 + 68 + 3);
    assert_eq!(one("Op::Load(5)"), "(enum (enum root Op ()) 1 (uint 8 5))");
    exact(OPS, "Op::Load(5)", 1 + 68 + 2 + 1 + 2 + 3);
    exact(OPS, "Op::Pair(true, 5)", 1 + 68 + 4 + 2 + 2 + 3);
    exact(
        OPS,
        "[Op::Add, Op::Add]",
        1 + (1 + 68 + 3) + (1 + 3) + 2 + 7,
    );
}

/// The payload packs its leaves in packing order, the first leaf in the low bits, with zero high
/// bits up to `P`. A nested enum packs its tag, then its payload, and `()` adds no bit. A payload
/// across several words of 64 bits packs each leaf at its offset.
#[test]
fn a_static_payload_packs_into_one_bit_buffer() {
    let at = |src: &str, expr: &str| out(src, expr, 1 << 24, 1000);
    assert_eq!(
        at(OPS, "Op::Pair(true, 5)"),
        "(enum (enum root Op ()) 2 (uint 8 11))"
    );
    assert_eq!(
        at(OPS, "Op::Pair(false, 15)"),
        "(enum (enum root Op ()) 2 (uint 8 30))"
    );
    let nested = "enum F: UInt[1] { A = 0, B = 1 }\n\
                  enum E: UInt[2] { X(F, [UInt[3]; 2], ()) = 3 }\n";
    assert_eq!(
        at(nested, "E::X(F::B, [5, 2], ())"),
        "(enum (enum root E ()) 3 (uint 7 43))"
    );
    let wide = "enum E: UInt[1] { A(UInt[63], UInt[70], Bool) = 1, B = 0 }\n";
    let one = num_bigint::BigUint::from(1u8);
    let big = (&one << 63) - 1u8 + ((&one << 70) - 3u8) * (&one << 63) + (&one << 133);
    assert_eq!(
        at(wide, "E::A(UInt[63](0) -% 1, UInt[70](0) -% 3, true)"),
        format!("(enum (enum root E ()) 1 (uint 134 {big}))")
    );
    assert_eq!(at(wide, "E::B"), "(enum (enum root E ()) 0 (uint 134 0))");
    let signed = "enum E: UInt[1] { A(SInt[4], Bool) = 1 }\n";
    assert_eq!(
        at(signed, "E::A(-1, true)"),
        "(enum (enum root E ()) 1 (uint 5 31))"
    );
    let words = "enum E: UInt[1] { A(UInt[64], UInt[64], Bool) = 1 }\n";
    assert_eq!(
        at(words, "E::A(UInt[64](0) -% 1, 2, true)"),
        "(enum (enum root E ()) 1 (uint 129 340282366920938463518714839652896866303))"
    );
    let top = "enum E: UInt[1] { A(UInt[65536]) = 1 }\n";
    let value = at(top, "E::A(UInt[65536](0) -% 1)");
    assert!(
        value.starts_with("(enum (enum root E ()) 1 (uint 65536 "),
        "{}",
        &value[..40]
    );
    assert!(value.ends_with("))") && value.len() > 19000);
}

/// The errors of a constructor come in its order. An error of a payload value comes first. Then
/// each typed use runs in order. A value of another type is `S010`, and a value that does not
/// fit is `S012`, each at the start of the path. The copies charge before the typed uses.
#[test]
fn the_errors_of_a_constructor_come_in_their_order() {
    let at = |expr: &str, fuel: u64| out(OPS, expr, fuel, 1000);
    assert_eq!(at("Op::Pair(1 / 0, 16)", 1 << 20), "S013 1:10");
    assert_eq!(at("Op::Pair(1, 16)", 1 << 20), "S010 1:1");
    assert_eq!(at("Op::Pair(true, 16)", 1 << 20), "S012 1:1");
    assert_eq!(
        message(OPS, "Op::Pair(true, 16)"),
        "16 does not fit UInt[4]"
    );
    assert_eq!(at("Op::Load(5)", 1 + 68 + 2 + 1), "S015 1:1");
    let fuel = 1 + 68 + 2 + 1 + 2;
    assert_eq!(
        message_fuel(OPS, "Op::Load(256)", fuel),
        "256 does not fit UInt[8]"
    );
    let call = format!("{OPS}fn f(x: UInt[8]) -> Op {{ return Op::Load(x); }}\n");
    assert_eq!(
        out(&call, "f(7)", 1 << 20, 1000),
        "(enum (enum root Op ()) 1 (uint 8 7))"
    );
}

/// The message of the error of `expr` with the fuel `fuel`.
fn message_fuel(src: &str, expr: &str, fuel: u64) -> String {
    use crate::Budget;
    let budget = Budget {
        fuel,
        ..Budget::default()
    };
    crate::tests::message_with(src, expr, budget)
}

/// `reinterpret` converts between an enum and exactly `UInt[W + P]` (F26): the tag in the low
/// `W` bits, then the payload. A static conversion charges the copies of its arguments, then
/// the size of its result. The result can have a tag without a variant. Another type on the
/// other side is `S010` at the call.
#[test]
fn a_static_reinterpret_converts_between_an_enum_and_its_bits() {
    let at = |src: &str, expr: &str| out(src, expr, 1 << 20, 1000);
    assert_eq!(
        at(OPS, "reinterpret(UInt[10], Op::Pair(true, 5))"),
        "(uint 10 46)"
    );
    exact(
        OPS,
        "reinterpret(UInt[10], Op::Pair(true, 5))",
        2 + 6 + 80 + 5 + 1,
    );
    assert_eq!(
        at(OPS, "reinterpret(Op, UInt[10](45))"),
        "(enum (enum root Op ()) 1 (uint 8 11))"
    );
    exact(OPS, "reinterpret(Op, UInt[10](45))", 2 + 69 + 12 + 2 + 3);
    assert_eq!(
        at(OPS, "reinterpret(Op, UInt[10](1023))"),
        "(enum (enum root Op ()) 3 (uint 8 255))"
    );
    assert_eq!(
        at(
            OPS,
            "reinterpret(Op, reinterpret(UInt[10], Op::Pair(true, 5)))"
        ),
        "(enum (enum root Op ()) 2 (uint 8 11))"
    );
    let tag = "enum E: UInt[3] { A = 5 }\n";
    assert_eq!(at(tag, "reinterpret(UInt[3], E::A)"), "(uint 3 5)");
    assert_eq!(
        at(tag, "reinterpret(E, UInt[3](2))"),
        "(enum (enum root E ()) 2)"
    );
    for bad in [
        "reinterpret(Op, UInt[9](45))",
        "reinterpret(Op, SInt[10](45))",
        "reinterpret(Op, 45)",
        "reinterpret(Op, true)",
        "reinterpret(UInt[9], Op::Add)",
        "reinterpret(Bool, Op::Add)",
        "reinterpret(UInt[10], Op)",
    ] {
        assert_eq!(at(OPS, bad), "S010 1:1", "{bad}");
    }
    assert_eq!(
        message(OPS, "reinterpret(Op, UInt[9](45))"),
        "`reinterpret` makes Op only from UInt[10], not UInt[9]"
    );
    assert_eq!(
        message(OPS, "reinterpret(SInt[10], Op::Add)"),
        "`reinterpret` gives the bits of Op only as UInt[10], not SInt[10]"
    );
    let other = format!("{OPS}enum F: UInt[10] {{ A = 0 }}\n");
    assert_eq!(at(&other, "reinterpret(F, Op::Add)"), "S010 1:1");
}

/// A new enum value has the depth 3 of section 5.5: 1 more than its type `Op` of the depth 2. A
/// variant constructor and `reinterpret` to an enum check it before the value exists, as `T()`
/// does, after the typed uses and after the type check.
#[test]
fn a_new_enum_value_checks_its_depth() {
    let at = |expr: &str, depth: u64| out(OPS, expr, 1 << 20, depth);
    for expr in ["Op::Add", "Op::Load(5)", "reinterpret(Op, UInt[10](0))"] {
        assert!(!at(expr, 3).starts_with('S'), "{expr}");
        assert_eq!(at(expr, 2), "S015 1:1", "{expr}");
    }
    assert_eq!(at("Op()", 2), "S015 1:1");
    assert_eq!(at("[Op::Add][0]", 2), "S015 1:2");
    let text = "the depth 3 goes above the nesting depth 2; raise --depth to at least 3";
    for expr in ["Op::Add", "reinterpret(Op, UInt[10](0))"] {
        let budget = crate::Budget {
            depth: 2,
            ..crate::Budget::default()
        };
        assert_eq!(crate::tests::message_with(OPS, expr, budget), text);
    }
    assert_eq!(at("Op::Load(true)", 2), "S010 1:1");
    assert_eq!(at("reinterpret(Op, UInt[9](0))", 2), "S010 1:1");
}

/// The module `M` with the hardware inputs `x`, `c`, `y`, and `e`, and the statements `body`.
fn hw_enum(body: &str) -> String {
    format!(
        "{OPS}module M() {{\n  input x: UInt[8];\n  input c: Bool;\n  input y: UInt[4];\n  \
         input e: Op;\n  output o: Bool;\n{body}  o := true;\n}}\n"
    )
}

/// The units of the elaboration of the module of `hw_enum`.
fn hw_units(body: &str) -> u64 {
    total(&hw_enum(body), "M")
}

/// A hardware constructor charges as a static one: the payload values, their copies, and their
/// typed uses. Then the size of the result charges from the stored sizes. The pack node has no
/// charge, because the lowering charges each core node of a pack.
#[test]
fn a_hardware_constructor_charges_the_stored_sizes() {
    let add = hw_units("  let a = Op::Add;\n");
    assert_eq!(hw_units("  let a = Op::Load(x);\n"), add + 3);
    assert_eq!(hw_units("  let a = Op::Pair(c, y);\n"), add + 6);
    assert_eq!(hw_units("  let a = Op::Load(3);\n"), add + 5);
    assert_eq!(
        elab_cost(&hw_enum("  let a = Op::Load(y);\n"), "M"),
        "S010 8:11"
    );
    assert_eq!(hw_units("  let a = reinterpret(UInt[10], e);\n"), add + 10);
}

/// The binding of an enum binds each of its leaves, `tag`, then `payload` when `P` is not 0.
#[test]
fn a_binding_of_an_enum_binds_its_leaves() {
    let bind = |op: &str| {
        format!(
            "{op}module M() {{\n  input a: Op;\n  output b: Bool;\n  let x = a;\n  b := true;\n}}\n"
        )
    };
    assert_eq!(names(&bind(OPS), "M", "M"), ["x$tag", "x$payload"]);
    assert_eq!(
        names(&bind("enum Op: UInt[2] { A = 0 }\n"), "M", "M"),
        ["x$tag"]
    );
}

/// The mark of a shared condition charges the size of the condition once, and a value that holds
/// it counts a core name. `!c` charges its node 1 and its hardware operation 2, and its mark
/// charges the size 2 of `(! c)`. Nested round trips charge 29 units each.
#[test]
fn a_shared_mark_charges_its_operand_once() {
    let if_with = |c: &str| format!("  let a = if ({c}) {{ Op::Load(x) }} else {{ e }};\n");
    assert_eq!(hw_units(&if_with("!c")), hw_units(&if_with("c")) + 3 + 2);
    let copy = |c: &str| format!("{}  let b = a;\n", if_with(c));
    assert_eq!(
        hw_units(&copy("!c")) - hw_units(&if_with("!c")),
        hw_units(&copy("c")) - hw_units(&if_with("c"))
    );
    let trips = |k: u64| {
        let mut e = "reinterpret(Op, resize(UInt[10], x))".to_owned();
        for _ in 0..k {
            e = format!("reinterpret(Op, reinterpret(UInt[10], {e}))");
        }
        hw_units(&format!("  let a = {e};\n"))
    };
    for k in 0..30 {
        assert_eq!(trips(k + 1), trips(k) + 29, "{k}");
    }
    assert_eq!(trips(30), 1011);
}

/// A hardware `if` with enum arms joins the two enum types, 1 plus 1. Then it walks them as a
/// container pair: the root, `tag`, and `payload`, 1 each. Two different enums, and an enum and
/// another type, have no join (`S010`). Two static enums in a static pair compare by their tags
/// and payloads, and different ones are `S011`.
#[test]
fn a_hardware_if_walks_enum_arms_as_a_container_pair() {
    let add = hw_units("  let a = Op::Add;\n");
    // The node 1, `c` 1, the arms 5, the join 2, the walk 3, and two `mux` nodes 8.
    assert_eq!(
        hw_units("  let a = if (c) { Op::Add } else { e };\n") + 4,
        add + (1 + 1 + 5 + 2 + 3 + 8)
    );
    let cost_of = |body: &str| elab_cost(&hw_enum(body), "M");
    assert_eq!(
        cost_of("  let a = if (c) { Op::Add } else { 1 };\n"),
        "S010 8:11"
    );
    let both = format!(
        "enum F: UInt[2] {{ A = 0 }}\n{}",
        hw_enum("  let a = if (c) { Op::Add } else { F::A };\n")
    );
    assert_eq!(elab_cost(&both, "M"), "S010 9:11");
    let lists = |b: &str| {
        hw_enum(&format!(
            "  let mut p = list(Op);\n  push(p, Op::Add);\n  let mut q = list(Op);\n  push(q, {b});\n  \
             let k = if (c) {{ p }} else {{ q }};\n"
        ))
    };
    assert_eq!(elab_cost(&lists("Op::Load(1)"), "M"), "S011 12:11");
    assert_eq!(elab_cost(&lists("Op::Pair(false, 0)"), "M"), "S011 12:11");
    assert!(elab_cost(&lists("Op::Add"), "M").starts_with("total"));
}

/// The measures of one run of `expr`: the steps of the table, the counters of the walks, and
/// the used fuel. The fuel makes the run unique.
fn measure(src: &str, expr: &str, fuel: u64) -> [u64; 8] {
    let (text, used) = run(src, expr, fuel, 1000);
    assert!(text.starts_with("(int 0)"), "{text}");
    let c = of(fuel);
    [
        type_work(src, expr),
        c.compared,
        c.visited,
        c.flagged,
        c.walked,
        c.cloned,
        c.serialized,
        used,
    ]
}

/// W1. `n` variants and `k` uses of one enum: the declaration is paid once, so each measure grows
/// by the same amount for each equal step of `n`, and of `k`, and the growth in `k` does not
/// depend on `n`.
#[test]
fn w1_n_uses_of_one_enum_pay_the_declaration_once() {
    let source = |n: usize| {
        let mut variants = String::new();
        for v in 0..n {
            write!(variants, "V{v}(UInt[8]) = {v}, ").unwrap();
        }
        format!("enum E: UInt[32] {{ {variants}}}\n")
    };
    let uses = |k: usize| {
        format!("fn f() -> Int {{ comptime for i in 0..{k} {{ let e = E(); }} return 0; }}")
    };
    let at = |n: usize, k: usize| {
        let src = source(n) + &uses(k);
        measure(&src, "f()", 700_000_000 + (n as u64) * 1000 + k as u64)
    };
    let base = at(50, 50);
    let (n2, n4) = (at(100, 50), at(200, 50));
    let (k2, k4) = (at(50, 100), at(50, 200));
    let (n4k2, n4k4) = (at(200, 100), at(200, 200));
    for m in 0..base.len() {
        assert_eq!(n4[m] - n2[m], 2 * (n2[m] - base[m]), "measure {m} in n");
        assert_eq!(k4[m] - k2[m], 2 * (k2[m] - base[m]), "measure {m} in k");
        assert_eq!(n4k2[m] - n4[m], k2[m] - base[m], "measure {m} n*k");
        assert_eq!(n4k4[m] - n4k2[m], k4[m] - k2[m], "measure {m} n*k");
    }
}

/// W2. `==` on arrays of a million enums is `S010` by the flag: no pair compares, no type
/// joins, and the check reads the flag of each operand once.
#[test]
fn w2_equality_on_a_large_array_of_enums_walks_nothing() {
    let src = format!("{OPS}type A = [Op; 1048576];\n");
    let fuel = 710_000_000;
    let (text, _) = run(&src, "A() == A()", fuel, 1000);
    assert_eq!(text, "S010 1:1");
    let c = of(fuel);
    assert_eq!((c.compared, c.visited), (0, 0));
    assert!(c.flagged <= 4, "{}", c.flagged);
}

/// W3. The zero of an enum with a payload of `p` bits charges from the metadata in the words of
/// `p`, and no walk grows with `p`.
#[test]
fn w3_the_zero_of_a_wide_payload_costs_the_words_of_its_width() {
    let units = |p: u64| {
        let src = format!("enum E: UInt[2] {{ A(UInt[{p}]) = 0 }}\n");
        let c = |expr: &str| cost(&src, expr);
        (c("E()"), c("data_bits(E)"), c("E"))
    };
    let (z1, d1, e1) = units(8192);
    let (z2, d2, e2) = units(16384);
    let (z4, d4, e4) = units(65536);
    // The words of the payload: 128, 256, and 1024.
    assert_eq!(z4 - z2, (1024 - 256) / (256 - 128) * (z2 - z1));
    assert_eq!((d1, d2), (d4, d4));
    assert_eq!((e1, e2), (e4, e4));
    let src = "enum E: UInt[2] { A(UInt[65536]) = 0 }\n";
    let fuel = 720_000_000;
    let (text, _) = run(src, "E()", fuel, 1000);
    assert!(text.starts_with("(enum (enum root E ()) 0 (uint 65536 0))"));
    let c = of(fuel);
    assert!(c.compared == 0 && c.walked <= 16 && c.cloned <= 16, "{c:?}");
}

/// W4. An enum value as a module argument serializes once, after the length: the text of the
/// instantiation is written one time, and the digest name of its module comes from it.
#[test]
fn w4_an_enum_argument_serializes_once() {
    let src = format!(
        "{OPS}module M(comptime e: Op) {{\n}}\nmodule T() {{\n  instance a = M(Op());\n}}\n"
    );
    let fuel = 730_000_000;
    assert!(cost_fuel(&src, "T", fuel).starts_with("total"));
    assert_eq!(of(fuel).serialized, ZERO.len() as u64);
    let text = format!("(instantiation root M ({ZERO}))");
    let digest = format!("M$0h{}", crate::names::sha16(&text));
    assert_eq!(order(&src, "T"), [digest, "T".to_owned()]);
}
