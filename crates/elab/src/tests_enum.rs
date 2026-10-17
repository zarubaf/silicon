// SPDX-License-Identifier: Apache-2.0
//! The enum types and values of Lean `Source.Eval` (slice 3, sections 5.1, 5.4, and 5.6): the
//! first use with its checks and charges, `T()`, `data_bits`, the typed use, the join, and the
//! texts of the `S010` cases. The numbers come from the Lean binary. The work tests count the
//! steps of the walks and not the time.

use crate::counters::of;
use crate::tests::{cost, exact, message, out, run, serialized_len, type_work};
use crate::tests_elab::{cost_fuel, order};
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
