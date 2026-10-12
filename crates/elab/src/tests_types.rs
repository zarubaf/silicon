// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Eval` for the types as values: the type expressions, the
//! aliases, the struct specializations with their cycles, and the work of the table of types.
//! The tests of the work count the steps of the table and not the time, so a walk that does
//! not share the parts of a type fails them.

use crate::tests::{message, out, serialized_len, type_work};
use std::fmt::Write;

/// The result of `eval` with the default budgets.
fn o(src: &str, expr: &str) -> String {
    out(src, expr, 100_000_000, 1000)
}

const ITEMS: &str = "type A = [UInt[8]; 4];\n\
    type Cyc1 = Cyc2;\n\
    type Cyc2 = Cyc1;\n\
    struct P(comptime W: Nat) {\n\
    \x20   a: UInt[W],\n\
    \x20   b: (Bool, [UInt[W]; 2]),\n\
    }\n\
    struct Q(comptime T: Type, comptime n: Nat) {\n\
    \x20   x: [T; n],\n\
    }\n\
    struct Rec {\n\
    \x20   a: Rec,\n\
    }\n\
    struct Bad(comptime W: UInt[Bad[1]]) {\n\
    \x20   a: Bool,\n\
    }\n\
    const K: Type = (Bool, Bool);\n\
    fn f(comptime T: Type) -> Type { return [T; 2]; }\n\
    fn g() -> Type { type L = UInt[3]; return (L, L); }";

#[test]
fn a_type_is_a_value() {
    assert_eq!(o("", "Bool"), "(type bool)");
    assert_eq!(o("", "Nat"), "(type nat)");
    assert_eq!(o("", "Int"), "(type int)");
    assert_eq!(o("", "Unit"), "(type unit)");
    assert_eq!(o("", "Type"), "(type type)");
    assert_eq!(o("", "UInt[8]"), "(type (uint 8))");
    assert_eq!(o("", "[Bool; 3]"), "(type (array bool 3))");
    assert_eq!(o("", "[Bool; 0]"), "(type (array bool 0))");
    assert_eq!(o("", "[[Bool; 2]; 3]"), "(type (array (array bool 2) 3))");
    assert_eq!(
        o("", "[Bool, UInt[8]]"),
        "(array type ((type bool) (type (uint 8))))"
    );
    assert_eq!(
        o("", "(Bool, UInt[8])"),
        "(tuple ((type bool) (type (uint 8))))"
    );
}

#[test]
fn an_alias_is_a_constant_of_type_type() {
    assert_eq!(o(ITEMS, "A"), "(type (array (uint 8) 4))");
    assert_eq!(o(ITEMS, "K"), "S010 17:1");
    assert_eq!(o(ITEMS, "f(Bool)"), "(type (array bool 2))");
    assert_eq!(o(ITEMS, "g()"), "S010 19:36");
    assert_eq!(o(ITEMS, "A == [UInt[8]; 4]"), "(bool true)");
    assert_eq!(o(ITEMS, "A == [UInt[8]; 5]"), "(bool false)");
    assert_eq!(
        o(ITEMS, "[A, A]"),
        "(array type ((type (array (uint 8) 4)) (type (array (uint 8) 4))))"
    );
    assert_eq!(o(ITEMS, "A[3]"), "S007 1:1");
    assert_eq!(o(ITEMS, "Bool[3]"), "S007 1:1");
    assert_eq!(o(ITEMS, "Type[1]"), "S007 1:1");
}

#[test]
fn a_cycle_of_aliases_is_s019() {
    assert_eq!(o(ITEMS, "Cyc1"), "S019 3:13");
    assert_eq!(o(ITEMS, "Cyc2"), "S019 2:13");
}

#[test]
fn the_length_of_an_array_type_is_a_static_nat() {
    assert_eq!(o("", "[Bool; 0 - 1]"), "S012 1:8");
    assert_eq!(o("", "[Bool; true]"), "S010 1:8");
    assert_eq!(
        o("fn f(x: UInt[8]) -> Type { return [Bool; x]; }", "f(1)"),
        "S010 1:42"
    );
}

#[test]
fn a_struct_specialization_is_a_type() {
    assert_eq!(o(ITEMS, "P[8]"), "(type (struct root P ((int 8))))");
    assert_eq!(o(ITEMS, "P[300]"), "(type (struct root P ((int 300))))");
    assert_eq!(o(ITEMS, "P[8] == P[8]"), "(bool true)");
    assert_eq!(o(ITEMS, "P[8] == P[9]"), "(bool false)");
    assert_eq!(
        o(ITEMS, "Q[Bool, 3]"),
        "(type (struct root Q ((type bool) (int 3))))"
    );
    assert_eq!(
        o(ITEMS, "Q[Q[Bool, 2], 1]"),
        "(type (struct root Q ((type (struct root Q ((type bool) (int 2)))) (int 1))))"
    );
    assert_eq!(o(ITEMS, "P"), "S007 1:1");
    assert_eq!(o(ITEMS, "P[1, 2]"), "S007 1:1");
}

#[test]
fn a_cycle_through_a_struct_is_s019() {
    assert_eq!(o(ITEMS, "Rec"), "S019 12:8");
    assert_eq!(o(ITEMS, "Bad[1]"), "S019 14:29");
}

#[test]
fn the_message_of_a_struct_names_its_arguments() {
    assert_eq!(
        message(ITEMS, "[P[8], 1]"),
        "the elements of an array have no common type"
    );
}

/// A doubling chain of tuple types: `P0 = base` and `P(k+1) = (Pk, Pk)`. The term of `Pk` has
/// `2^k` leaves, and the table has one entry for each level.
fn doubling(prefix: &str, base: &str, levels: usize) -> String {
    let mut src = format!("type {prefix}0 = {base};\n");
    for k in 1..=levels {
        writeln!(
            src,
            "type {prefix}{k} = ({prefix}{}, {prefix}{});",
            k - 1,
            k - 1
        )
        .unwrap();
    }
    src
}

/// The use of a struct type as the argument of the next one repeats `levels` times. The type
/// nests its arguments, but each specialization stores only the id of the one before.
fn nested_arguments(levels: usize) -> String {
    format!(
        "struct P(comptime T: Type) {{ x: Bool }}\n\
         fn f() -> Type {{ let mut t = Bool; comptime for i in 0..{levels} {{ t = P[t]; }} return t; }}"
    )
}

#[test]
fn a_loop_of_type_arguments_does_linear_work() {
    let work = |levels: usize| type_work(&nested_arguments(levels), "f()");
    let (a, b, c) = (work(100), work(200), work(300));
    assert_eq!(c - b, b - a, "{a} {b} {c}");
}

/// The size of a tuple type counts its term, so the fuel allows about 24 levels of a doubling
/// chain. A struct type has the size of its arguments, so its chain goes on.
#[test]
fn a_doubling_chain_of_types_builds_one_entry_per_level() {
    let work = |levels: usize| type_work(&doubling("A", "Int", levels), &format!("A{levels}"));
    let (a, b, c) = (work(6), work(12), work(18));
    assert_eq!(c - b, b - a, "{a} {b} {c}");
}

#[test]
fn the_length_of_a_shared_type_comes_from_the_table() {
    let len = |levels: usize| serialized_len(&doubling("A", "Int", levels), &format!("A{levels}"));
    // `int` has 3 bytes, and each level adds `(tuple (` and `))` and the space: 11 bytes.
    let mut want = 3u64;
    for _ in 0..22 {
        want = want * 2 + 11;
    }
    // `(type T)` adds 7 bytes.
    assert_eq!(len(22), want + 7);
}

/// The join of two doubling chains charges one unit for each pair of their terms, so 2^22 units
/// pay for it, but its walk visits each pair of the table once.
#[test]
fn a_join_of_shared_types_does_work_in_the_table() {
    let program = |levels: usize| {
        let mut src = doubling("A", "Int", levels);
        src.push_str(&doubling("B", "UInt[8]", levels));
        write!(
            src,
            "fn f() -> Int {{ let e: [A{levels}; 0] = []; let g: [B{levels}; 0] = []; \
             let c = [e, g]; return 0; }}"
        )
        .unwrap();
        src
    };
    let work = |levels: usize| type_work(&program(levels), "f()");
    let (a, b, c) = (work(6), work(12), work(18));
    assert_eq!(c - b, b - a, "{a} {b} {c}");
    let cost = |levels: usize| crate::tests::cost(&program(levels), "f()");
    let (small, large) = (cost(12), cost(14));
    assert!(large > 4 * small - 4 * 1000, "{small} {large}");
}
