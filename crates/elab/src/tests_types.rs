// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Eval` for the types as values: the type expressions, the
//! aliases, the struct specializations with their cycles, and the work of the table of types.
//! The tests of the work count the steps of the table and not the time, so a walk that does
//! not share the parts of a type fails them.

use crate::tests::{exact, message, out, path_steps, serialized_len, type_work};
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

const RECORDS: &str = "struct P(comptime W: Nat) {\n\
    \x20   a: UInt[W],\n\
    \x20   b: (Bool, [UInt[W]; 2]),\n\
    \x20   c: Bool,\n\
    }\n\
    struct Q {\n\
    \x20   x: P[8],\n\
    \x20   y: Unit,\n\
    }\n\
    struct E {}\n\
    struct K {\n\
    \x20   t: Type,\n\
    \x20   n: Nat,\n\
    }\n\
    struct Wrap(comptime T: Type) {\n\
    \x20   v: T,\n\
    }\n\
    fn place() -> P[8] {\n\
    \x20   let mut r: P[8] = P[8]();\n\
    \x20   r.a = 5;\n\
    \x20   r.b.1[0] = 7;\n\
    \x20   r.c = true;\n\
    \x20   return r;\n\
    }\n\
    fn bad_place() -> P[8] {\n\
    \x20   let mut r = P[8]();\n\
    \x20   r.zz = 1;\n\
    \x20   return r;\n\
    }";

const P8: &str = "(struct root P ((int 8)))";

#[test]
fn a_constructor_makes_a_record() {
    assert_eq!(
        o(RECORDS, "P[8](1, (true, [2, 3]), false)"),
        format!(
            "(record {P8} ((uint 8 1) (tuple ((bool true) (array (uint 8) ((uint 8 2) (uint 8 3))))) (bool false)))"
        )
    );
    assert_eq!(o(RECORDS, "P[8](1)"), "S007 1:1");
    assert_eq!(o(RECORDS, "P[8](1, 2, 3)"), "S010 1:1");
    assert_eq!(o(RECORDS, "P[8](300, (true, [2, 3]), false)"), "S012 1:1");
    assert_eq!(o(RECORDS, "P[8](1, (true, []), false)"), "S010 1:1");
    assert_eq!(o(RECORDS, "Q(P[9](), ())"), "S010 1:1");
    assert_eq!(
        o(RECORDS, "K(Bool, 3)"),
        "(record (struct root K ()) ((type bool) (int 3)))"
    );
    assert_eq!(
        o(RECORDS, "Wrap[UInt[4]](3)"),
        "(record (struct root Wrap ((type (uint 4)))) ((uint 4 3)))"
    );
    assert_eq!(o(RECORDS, "Wrap[UInt[4]](16)"), "S012 1:1");
}

#[test]
fn the_zero_of_a_hardware_data_type() {
    assert_eq!(
        o(RECORDS, "P[8]()"),
        format!(
            "(record {P8} ((uint 8 0) (tuple ((bool false) (array (uint 8) ((uint 8 0) (uint 8 0))))) (bool false)))"
        )
    );
    assert_eq!(o(RECORDS, "E()"), "(record (struct root E ()) ())");
    assert_eq!(o("", "UInt[8]()"), "(uint 8 0)");
    assert_eq!(
        o("", "[Bool; 3]()"),
        "(array bool ((bool false) (bool false) (bool false)))"
    );
    assert_eq!(o("", "Unit()"), "(unit)");
    assert_eq!(o("", "Nat()"), "S010 1:1");
    assert_eq!(o("", "(Bool, UInt[4])()"), "S010 1:1");
    assert_eq!(o(RECORDS, "K()"), "S010 1:1");
    assert_eq!(o(RECORDS, "Wrap[K]()"), "S010 1:1");
    assert_eq!(o("", "Bool(1, 2)"), "S007 1:1");
}

#[test]
fn a_field_refers_to_the_field() {
    assert_eq!(o(RECORDS, "P[8]().a"), "(uint 8 0)");
    assert_eq!(o(RECORDS, "P[8]().b.1[1]"), "(uint 8 0)");
    assert_eq!(o(RECORDS, "K(Bool, 3).t"), "(type bool)");
    assert_eq!(o(RECORDS, "Q().x.a"), "(uint 8 0)");
    assert_eq!(o(RECORDS, "K(Bool, 3).m"), "S010 1:1");
    assert_eq!(o(RECORDS, "P[8]().a.b"), "S010 1:1");
    assert_eq!(o(RECORDS, "E().f"), "S010 1:1");
    assert_eq!(o("", "(1).f"), "S010 1:1");
}

#[test]
fn a_place_assigns_a_field() {
    assert_eq!(
        o(RECORDS, "place()"),
        format!(
            "(record {P8} ((uint 8 5) (tuple ((bool false) (array (uint 8) ((uint 8 7) (uint 8 0))))) (bool true)))"
        )
    );
    assert_eq!(o(RECORDS, "bad_place()"), "S010 27:5");
}

#[test]
fn a_record_equals_a_record_of_its_type() {
    assert_eq!(o(RECORDS, "P[8]() == P[8]()"), "(bool true)");
    assert_eq!(o(RECORDS, "P[8]() != P[8]()"), "(bool false)");
    assert_eq!(o(RECORDS, "Q() == Q()"), "(bool true)");
    assert_eq!(o(RECORDS, "P[8]() == P[9]()"), "S010 1:1");
    assert_eq!(o(RECORDS, "P[8]() == (1,)"), "S010 1:1");
}

#[test]
fn data_bits_reads_the_width_from_the_metadata() {
    assert_eq!(o(RECORDS, "data_bits(P[8])"), "(int 26)");
    assert_eq!(o(RECORDS, "data_bits(Q)"), "(int 26)");
    assert_eq!(o(RECORDS, "data_bits(E)"), "(int 0)");
    assert_eq!(o("", "data_bits(Nat)"), "S010 1:1");
    assert_eq!(o("", "data_bits(1)"), "S010 1:1");
    assert_eq!(o("", "data_bits()"), "S007 1:1");
    assert_eq!(o(RECORDS, "Q.data_bits()"), "(int 26)");
    assert_eq!(o("", "Int.data_bits()"), "S010 1:1");
}

/// A chain of structs that doubles at each step: `S(k+1) { a: S(k), b: S(k) }`. The term of
/// the zero of `S(k)` has `2^k` leaves, and each struct stores its numbers.
fn struct_doubling(levels: usize) -> String {
    let mut src = "struct S0 { a: Bool }\n".to_owned();
    for k in 1..=levels {
        writeln!(src, "struct S{k} {{ a: S{}, b: S{} }}", k - 1, k - 1).unwrap();
    }
    src
}

#[test]
fn data_bits_of_a_doubling_chain_does_constant_work() {
    let src = struct_doubling(60);
    assert_eq!(o(&src, "data_bits(S60)"), "(int 1152921504606846976)");
    let base = type_work(&src, "S60");
    let work = |calls: usize| {
        let body = (0..calls)
            .map(|_| "data_bits(S60)")
            .collect::<Vec<_>>()
            .join(", ");
        type_work(&src, &format!("({body},)")) - base
    };
    assert_eq!(work(80) - work(40), 2 * (work(40) - work(20)));
    assert!(work(40) - work(20) <= 20 * 20, "{}", work(40) - work(20));
}

/// The zero of `S60` has `2^61` nodes, so the test finishes only if the charge comes before the
/// value.
#[test]
fn the_zero_of_a_doubling_chain_fails_before_it_builds() {
    assert_eq!(o(&struct_doubling(60), "S60()"), "S015 1:1");
}

/// A struct and a tuple type with `parts` parts of an alias of a type with a large width. The
/// alias charges only its node, but the metadata sums read each word of each part.
fn wide_parts(parts: usize) -> String {
    let names = (0..parts)
        .map(|k| format!("f{k}: B"))
        .collect::<Vec<_>>()
        .join(", ");
    let tuple = vec!["B"; parts].join(", ");
    format!(
        "type B = [Bool; 1 << 6400];\nstruct W {{ {names} }}\n\
         fn f() -> Int {{ type T = ({tuple}); return 0; }}"
    )
}

#[test]
fn the_metadata_sums_pay_for_the_words_that_they_read() {
    for expr in ["W", "f()"] {
        let work = |parts: usize| type_work(&wide_parts(parts), expr);
        let cost = |parts: usize| crate::tests::cost(&wide_parts(parts), expr);
        let (work_100, work_200) = (work(100), work(200));
        let (cost_100, cost_200) = (cost(100), cost(200));
        assert!(
            work_200 - work_100 > 100 * 300,
            "{expr}: {work_100} {work_200}"
        );
        assert!(
            cost_200 - cost_100 >= work_200 - work_100,
            "{expr}: {cost_100} {cost_200} {work_100} {work_200}"
        );
    }
}

#[test]
fn the_zero_charges_its_size_before_it_builds() {
    let src = "struct P { a: [UInt[8]; 16], b: (Bool, UInt[4]) }";
    // The units are those of `silicon-check eval`: the first use of the struct, then the zero
    // with the size 1 + (1 + 16) + (1 + 1 + 1) from the metadata.
    exact(src, "P()", 76);
}

/// The text of a struct type in a message prints its arguments, and it stops after 1024 bytes
/// of them, so a message never grows with the size of an argument.
#[test]
fn the_message_of_a_large_struct_type_is_short() {
    let src = "struct A(comptime xs: [Nat; 5000]) { v: Bool }";
    let xs = (0..5000)
        .map(|k| k.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let text = message(src, &format!("A[[{xs}]]() == 1"));
    assert!(
        text.starts_with("`==` needs a common type, not A[[0, 1, 2, 3"),
        "{text}"
    );
    assert!(text.len() < 1100 + 40, "{}", text.len());
}

/// `uses` later uses of a struct with an argument of `len` elements. The lookup hashes and
/// compares the argument, so each use reads it in full.
fn repeated_argument(len: usize, uses: usize) -> String {
    let xs = vec!["0"; len].join(", ");
    format!(
        "struct A(comptime xs: [Nat; {len}]) {{ v: Bool }}\n\
         const X: [Nat; {len}] = [{xs}];\n\
         fn f() -> Int {{ comptime for i in 0..{uses} {{ type T = A[X]; }} return 0; }}"
    )
}

#[test]
fn a_later_use_pays_for_the_lookup_of_its_arguments() {
    let work = |uses: usize| type_work(&repeated_argument(2000, uses), "f()");
    let cost = |uses: usize| crate::tests::cost(&repeated_argument(2000, uses), "f()");
    let (work_100, work_200) = (work(100), work(200));
    let (cost_100, cost_200) = (cost(100), cost(200));
    assert!(work_200 - work_100 > 100 * 2000, "{work_100} {work_200}");
    assert!(
        cost_200 - cost_100 >= work_200 - work_100,
        "{cost_100} {cost_200} {work_100} {work_200}"
    );
}

const EMPTIES: &str = "struct P(comptime X: [Bool; 0]) { a: Bool }\n\
    struct Q(comptime n: Nat, comptime X: [[Bool; 0]; n]) { a: Bool }";

#[test]
fn an_empty_struct_argument_takes_its_parameter_type() {
    assert_eq!(
        o(EMPTIES, "P[[]]"),
        "(type (struct root P ((array bool ()))))"
    );
    assert_eq!(o(EMPTIES, "P[[]] == P[[Bool; 0]()]"), "(bool true)");
    assert_eq!(
        o(EMPTIES, "Q[1, [[]]]"),
        "(type (struct root Q ((int 1) (array (array bool 0) ((array bool ()))))))"
    );
    assert_eq!(o(EMPTIES, "Q[2, [[]]]"), "S010 1:1");
    assert_eq!(o(EMPTIES, "P[[[]]]"), "S010 1:1");
}

/// A struct and a tuple type with one part of a large width first, then `small` parts of
/// `Bool`. The sums add each part in place, so a small part touches a few words, and not the
/// words of the large sum.
fn large_then_small(small: usize) -> String {
    let names = (0..small)
        .map(|k| format!("f{k}: Bool"))
        .collect::<Vec<_>>()
        .join(", ");
    let tuple = vec!["Bool"; small].join(", ");
    format!(
        "type B = [Bool; (1 << 6400) - 1];\nstruct W {{ a: B, {names} }}\n\
         fn f() -> Int {{ type T = (B, {tuple}); return 0; }}"
    )
}

#[test]
fn a_metadata_sum_adds_small_parts_in_place() {
    for expr in ["W", "f()"] {
        let work = |small: usize| type_work(&large_then_small(small), expr);
        let (work_200, work_400) = (work(200), work(400));
        assert!(
            work_400 - work_200 <= 200 * 20,
            "{expr}: {work_200} {work_400}"
        );
    }
}

/// The result of `expr` at each fuel from 0: the runs of fuels with one result, then the
/// fuel that finishes and its value. The values come from the Lean binary.
fn at_each_fuel(expr: &str, runs: &[(u64, u64, &str)], done: (u64, &str)) {
    for &(from, to, want) in runs {
        for fuel in from..=to {
            assert_eq!(o_at(expr, fuel), want, "{expr} with the fuel {fuel}");
        }
    }
    assert_eq!(
        o_at(expr, done.0),
        done.1,
        "{expr} with the fuel {}",
        done.0
    );
    assert_eq!(o_at(expr, done.0 + 1000), done.1);
}

fn o_at(expr: &str, fuel: u64) -> String {
    out("", expr, fuel, 1000)
}

#[test]
fn the_prelude_struct_serializes_with_the_token_prelude() {
    assert_eq!(
        o("", "ReadResponse[UInt[8]]"),
        "(type (struct prelude ReadResponse ((type (uint 8)))))"
    );
    assert_eq!(
        o("", "ReadResponse[Bool]"),
        "(type (struct prelude ReadResponse ((type bool))))"
    );
    assert_eq!(
        o("", "[ReadResponse[Bool]; 2]"),
        "(type (array (struct prelude ReadResponse ((type bool))) 2))"
    );
    assert_eq!(
        o("", "ReadResponse[UInt[8]](UInt[8](3), true)"),
        "(record (struct prelude ReadResponse ((type (uint 8)))) ((uint 8 3) (bool true)))"
    );
    assert_eq!(o("", "ReadResponse[Bool]().valid"), "(bool false)");
}

#[test]
fn a_user_struct_with_the_name_serializes_with_the_token_root() {
    let items = "struct ReadResponse(comptime T: Type) { data: T, valid: Bool }\n";
    assert_eq!(
        o(items, "ReadResponse[UInt[8]]"),
        "(type (struct root ReadResponse ((type (uint 8)))))"
    );
}

#[test]
fn the_prelude_struct_checks_its_argument_like_a_struct() {
    assert_eq!(o("", "ReadResponse[1]"), "S010 1:1");
    assert_eq!(
        o("", "ReadResponse[Int]"),
        "(type (struct prelude ReadResponse ((type int))))"
    );
}

/// Each error in the work of the prelude struct reports at the use, never at the position
/// `0:0` of the item (design section 6.2). The fuel that runs out in its parameter type, in its
/// field types, or in its metadata is such an error. The last fuel finishes the evaluation, which
/// is 28 units for `UInt[8]` and 21 units for `Bool`.
#[test]
fn an_error_in_the_prelude_struct_reports_at_the_use() {
    at_each_fuel(
        "ReadResponse[UInt[8]]",
        &[
            (0, 1, "S015 1:1"),
            (2, 3, "S015 1:14"),
            (4, 5, "S015 1:19"),
            (6, 7, "S015 1:14"),
            (8, 27, "S015 1:1"),
        ],
        (28, "(type (struct prelude ReadResponse ((type (uint 8)))))"),
    );
    at_each_fuel(
        "ReadResponse[Bool]",
        &[(0, 1, "S015 1:1"), (2, 2, "S015 1:14"), (3, 20, "S015 1:1")],
        (21, "(type (struct prelude ReadResponse ((type bool))))"),
    );
}

/// A struct with `uses` fields that use its parameter `n` in their types, and a use of the
/// struct whose argument is the leaf of a nested array of the depth `depth`.
fn linked_path(depth: usize, uses: usize) -> String {
    let fields = (0..uses)
        .map(|i| format!("f{i}: UInt[n], g{i}: Q[n]"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "struct Q(comptime m: Nat) {{ x: UInt[m] }}\n\
         struct P(comptime n: Nat) {{ {fields} }}\n\
         fn f() -> Int {{ let a = {}3{}; type S = P[a{}]; return 0; }}",
        "[".repeat(depth),
        "]".repeat(depth),
        "[0]".repeat(depth)
    )
}

/// The argument walks its path a constant number of times, and a use of the parameter in a
/// field type walks nothing: the steps do not grow with the uses, and the steps of the depth
/// are the same for any number of uses.
#[test]
fn the_uses_of_a_parameter_linked_to_a_deep_path_do_constant_work() {
    let steps = |depth: usize, uses: usize| path_steps(&linked_path(depth, uses), "f()");
    let (base, more_uses) = (steps(100, 100), steps(100, 200));
    assert_eq!(more_uses, base, "{base} {more_uses}");
    assert_eq!(steps(200, 200) - steps(200, 100), 0);
}

/// `k` parameters of one array of `len` elements, all bound to the same element of `a`.
fn shared_target(len: usize, k: usize) -> String {
    let xs = vec!["0"; len].join(", ");
    let params = (0..k)
        .map(|i| format!("comptime x{i}: [Nat; {len}]"))
        .collect::<Vec<_>>()
        .join(", ");
    let args = vec!["a[0]"; k].join(", ");
    format!(
        "struct P({params}) {{ v: Bool }}\n\
         const X: [Nat; {len}] = [{xs}];\n\
         fn f() -> Int {{ let a = [X]; type S = P[{args}]; return 0; }}"
    )
}

/// Each argument copies into the frame after the charge of its own size. A run that fails in the
/// parameters copies at most the units that it charged, for any `k`.
#[test]
fn a_failed_charge_copies_at_most_the_charged_units() {
    for k in [8, 16] {
        let src = shared_target(1000, k);
        let fuel = crate::tests::cost(&src, "f()") / 2;
        let text = crate::tests::out(&src, "f()", fuel, 1000);
        assert!(text.starts_with("S015"), "{text}");
        let copies = crate::counters::of(fuel).copies;
        assert!(0 < copies && copies <= fuel, "{k} {copies}");
    }
}

/// `k` parameters after `n`, whose types read `n`, and a use whose first argument is the leaf of
/// a nested array of the depth `depth`: a path with `depth` steps.
fn parameter_reads(depth: usize, k: usize) -> String {
    let params = (0..k)
        .map(|i| format!("comptime z{i}: [Nat; n * 0 + 1]"))
        .collect::<Vec<_>>()
        .join(", ");
    let args = vec!["[0]"; k].join(", ");
    format!(
        "struct P(comptime n: Nat, {params}) {{ v: Bool }}\n\
         fn f() -> Int {{ let a = {}3{}; type S = P[a{}, {args}]; return 0; }}",
        "[".repeat(depth),
        "]".repeat(depth),
        "[0]".repeat(depth)
    )
}

/// A read of an earlier parameter in a parameter type is a local read: the steps do not grow with
/// the number of reads, and they grow at most with the depth of the path of the argument (#190).
#[test]
fn the_reads_of_an_earlier_parameter_do_constant_work() {
    let steps = |depth: usize, k: usize| path_steps(&parameter_reads(depth, k), "f()");
    let base = steps(100, 100);
    assert_eq!(steps(100, 200), base);
    assert!(steps(200, 100) <= 2 * base, "{base}");
}

/// The type of a message for `let a: Int = <expr>`, from the text `expected Int, but the value
/// is <type>`.
fn value_type(items: &str, expr: &str) -> String {
    let text = message(
        &format!("{items}\nfn f() -> Int {{ let a: Int = {expr}; return 0; }}"),
        "f()",
    );
    text.strip_prefix("expected Int, but the value is ")
        .unwrap_or(&text)
        .to_owned()
}

/// A user struct or enum with a prelude type name prints as `crate::X` at each depth, and a
/// prelude struct keeps its source form (design section 5.6, Lean `Test/Value.lean`).
#[test]
fn a_user_type_with_a_prelude_name_prints_as_crate() {
    let user_bool = "struct Bool { a: UInt[1] }";
    assert_eq!(value_type(user_bool, "Bool(1)"), "crate::Bool");
    assert_eq!(
        value_type("struct Reg(comptime n: Nat) { a: UInt[8] }", "Reg[3](1)"),
        "crate::Reg[3]"
    );
    assert_eq!(
        value_type("enum PortKey: UInt[1] { A = 0, B = 1 }", "PortKey::A"),
        "crate::PortKey"
    );
    assert_eq!(
        value_type(user_bool, "[Bool(1), Bool(0)]"),
        "[crate::Bool; 2]"
    );
    assert_eq!(
        value_type(user_bool, "(true, Bool(1))"),
        "(Bool, crate::Bool)"
    );
    assert_eq!(value_type("", "PortKey(\"x\", false, 0)"), "PortKey");
    assert_eq!(
        value_type("struct Packet2 { a: Bool }", "Packet2(true)"),
        "Packet2"
    );
}

/// The cut at 1024 bytes keeps the first bytes of the full text, so the prefix is a part of the
/// name: 1015 bytes before the name leave `crate::Bo` and `...`.
#[test]
fn the_cut_treats_the_crate_prefix_as_a_part_of_the_name() {
    let wide = format!("({}, Bool)", vec!["UInt[65536]"; 78].join(", "));
    let text = message(
        &format!("struct Bool {{ a: UInt[1] }}\nfn f() -> Int {{ let a: {wide} = 0; return 0; }}"),
        "f()",
    );
    let ty = text
        .strip_prefix("expected ")
        .and_then(|t| t.split(", but the value is").next())
        .unwrap_or_default();
    assert_eq!(ty.len(), 1024 + 3, "{text}");
    assert!(ty.ends_with(", crate::Bo..."), "{text}");
}
