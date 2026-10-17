// SPDX-License-Identifier: Apache-2.0
//! The `match` of Lean `Source.Eval` (slice 3, sections 5.4 and 5.6): the charges of the arm
//! checks, the coverage check, the kinds and fits of the patterns, and the static selection with
//! its binders. The cases come from the `#guard` lines of `Silicon.Source.Test.Eval`.

use crate::tests::{exact, message, out};

const OPS: &str = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n";

/// The result of `expr` with the default budget.
fn at(src: &str, expr: &str) -> String {
    out(src, expr, 100_000_000, 1000)
}

/// The result of `expr` with the fuel `fuel`.
fn fuel(src: &str, expr: &str, fuel: u64) -> String {
    out(src, expr, fuel, 1000)
}

/// A `match` charges its node 1, then its scrutinee. Each arm charges its pattern. `_` charges
/// 1, and a literal `1 + s`, with the size `s` of its value. A variant charges `1 + s` and 1
/// for each binder and `_`, with `s` the size of a value of the tag type. Each arm that is not
/// `_` then charges its coverage share `1 + floor(log2 n) + s`, with `n` such arms. A static
/// scrutinee then evaluates only the selected arm.
#[test]
fn a_static_match_charges_the_checks_of_each_arm() {
    assert_eq!(at("", "match (1) { _ => 2 }"), "(int 2)");
    exact("", "match (1) { _ => 2 }", 1 + 2 + 1 + 2);
    assert_eq!(at("", "match (true) { true => 1, false => 2 }"), "(int 1)");
    assert_eq!(at("", "match (false) { true => 1, false => 2 }"), "(int 2)");
    exact(
        "",
        "match (true) { true => 1, false => 2 }",
        1 + 2 + 2 * (2 + 3) + 2,
    );
    assert_eq!(at("", "match (true) { false => 2, _ => 3 }"), "(int 3)");
    exact(
        "",
        "match (true) { false => 2, _ => 3 }",
        1 + 2 + (2 + 2) + 1 + 2,
    );
    let all = "match (UInt[2](3)) { 0 => 0, 1 => 1, 2 => 2, 3 => 3 }";
    assert_eq!(at("", all), "(int 3)");
    exact("", all, 1 + 12 + 4 * (2 + 4) + 2);
    assert_eq!(
        at("", "match (SInt[4](-1)) { -1 => 10, _ => 0 }"),
        "(int 10)"
    );
    let three = "match (-5) { 5 => 1, -5 => 3, _ => 2 }";
    assert_eq!(at("", three), "(int 3)");
    exact("", three, 1 + 4 + 2 * (2 + 3) + 1 + 2);
}

/// The pattern charge is the first step of an arm, so the fuel stops at the pattern. The share
/// comes after the checks of the arm, at the pattern too.
#[test]
fn the_fuel_stops_at_the_pattern_and_at_the_share() {
    let e = "match (true) { true => 1, false => 2 }";
    assert_eq!(fuel("", e, 14), "S015 1:24");
    assert_eq!(fuel("", e, 8), "S015 1:27");
    assert_eq!(fuel("", e, 5), "S015 1:16");
    assert_eq!(fuel("", e, 3), "S015 1:16");
}

/// The scrutinee is `Bool`, `UInt[W]`, `SInt[W]`, `Int`, `Nat`, or an enum, else `S010` at the
/// scrutinee, after it evaluates. An error of the scrutinee comes first.
#[test]
fn the_scrutinee_has_a_scalar_or_enum_type() {
    assert_eq!(at("", "match (\"a\") { _ => 3 }"), "S010 1:8");
    assert_eq!(
        message("", "match (\"a\") { _ => 3 }"),
        "a `match` takes `Bool`, `UInt`, `SInt`, `Int`, `Nat`, or an enum, not `String`; match \
         on a part of the value"
    );
    assert_eq!(
        message("", "match ((1, 2)) { _ => 3 }"),
        "a `match` takes `Bool`, `UInt`, `SInt`, `Int`, `Nat`, or an enum, not `(Int, Int)`; \
         match on a part of the value"
    );
    assert_eq!(at("", "match (1 / 0) { _ => 3 }"), "S013 1:8");
}

/// A pattern has the kind of the scrutinee type (`S010` at the pattern), and a literal fits it
/// (`S012`). The kind check of a variant compares the enum items. Thus a variant of another enum
/// is `S010`, also when that enum has an error of its own (`E` has two tags 0).
#[test]
fn a_pattern_has_the_kind_of_the_scrutinee_and_a_literal_fits() {
    assert_eq!(at("", "match (true) { 1 => 2, _ => 3 }"), "S010 1:16");
    assert_eq!(
        message("", "match (true) { 1 => 2, _ => 3 }"),
        "a pattern of `Bool` is `true` or `false`, not `1`; write `true` or `false`, or `_`"
    );
    assert_eq!(
        message("", "match (1) { true => 2, _ => 3 }"),
        "a pattern of `Int` is an integer, not `true`; write an integer, or `_`"
    );
    assert_eq!(
        message("", "match (-1) { -3 => 2, true => 3, _ => 3 }"),
        "a pattern of `Int` is an integer, not `true`; write an integer, or `_`"
    );
    assert_eq!(at(OPS, "match (Op::Add) { 1 => 1, _ => 2 }"), "S010 1:19");
    assert_eq!(
        message(OPS, "match (Op::Add) { 1 => 1, _ => 2 }"),
        "a pattern of `Op` is a variant of `Op`, not `1`; write a variant of `Op`, or `_`"
    );
    assert_eq!(
        message(OPS, "match (1) { Op::Pair(a, _) => 1, _ => 2 }"),
        "a pattern of `Int` is an integer, not `Op::Pair(a, _)`; write an integer, or `_`"
    );
    let other = format!("{OPS}enum E: UInt[1] {{ A = 0, B = 0 }}\n");
    let e = "match (Op::Add) { E::A => 1, _ => 2 }";
    assert_eq!(at(&other, e), "S010 1:19");
    assert_eq!(
        message(&other, e),
        "a pattern of `Op` is a variant of `Op`, not `E::A`; write a variant of `Op`, or `_`"
    );
    assert_eq!(at("", "match (UInt[2](0)) { 4 => 2, _ => 3 }"), "S012 1:22");
    assert_eq!(
        message("", "match (UInt[2](0)) { 4 => 2, _ => 3 }"),
        "4 does not fit UInt[2]"
    );
    assert_eq!(
        message("", "match (UInt[2](0)) { -1 => 2, _ => 3 }"),
        "-1 does not fit UInt[2]"
    );
    assert_eq!(
        message("", "match (SInt[2](0)) { 2 => 2, _ => 3 }"),
        "2 does not fit SInt[2]"
    );
    assert_eq!(at("", "match (SInt[2](0)) { -2 => 2, _ => 3 }"), "(int 3)");
}

/// Coverage (`S021`). An arm after `_`, also a second `_`, is `S021` at its pattern, before a
/// second match. A second match of a value names the first arm. After the last arm, a `_`
/// without values comes first, then the smallest uncovered value at the `match`, written in
/// source syntax. `Int` and `Nat` need `_`.
#[test]
fn the_coverage_check_names_the_first_problem() {
    assert_eq!(at("", "match (5) { _ => 1, 5 => 2 }"), "S021 1:21");
    assert_eq!(
        message("", "match (5) { _ => 1, 5 => 2 }"),
        "this arm comes after `_`, so it matches no value; move `_` to the end, or remove this \
         arm"
    );
    assert_eq!(at("", "match (5) { _ => 1, _ => 2 }"), "S021 1:21");
    assert_eq!(at("", "match (5) { _ => 1, true => 2 }"), "S010 1:21");
    // The share of an arm after `_` charges before its `S021`.
    let late = "match (5) { _ => 1, 5 => 2 }";
    assert_eq!(fuel("", late, 1 + 2 + 1 + 2 + 1), "S015 1:21");
    assert_eq!(fuel("", late, 1 + 2 + 1 + 2 + 2), "S021 1:21");
    assert_eq!(at("", "match (5) { 5 => 1, _ => 3, 5 => 2 }"), "S021 1:29");
    assert_eq!(at("", "match (5) { 5 => 1, 5 => 2, _ => 3 }"), "S021 1:21");
    assert_eq!(
        message("", "match (5) { 5 => 1, 5 => 2, _ => 3 }"),
        "this arm matches `5`, and the arm at 1:13 matches it too; remove one of the two patterns"
    );
    let big = format!("{}", crate::int::Int::from_u64(1).shl(300));
    assert_eq!(
        message("", &format!("match (true) {{ {big} => 1, _ => 0 }}")),
        "a pattern of `Bool` is `true` or `false`, not `an integer of 301 bits`; write `true` or \
         `false`, or `_`"
    );
    assert_eq!(
        message(
            "",
            &format!("match (0) {{ {big} => 1, {big} => 2, _ => 0 }}")
        ),
        "this arm matches `an integer of 301 bits`, and the arm at 1:13 matches it too; remove \
         one of the two patterns"
    );
    assert_eq!(
        message(
            OPS,
            "match (Op::Add) { Op::Load(x) => 1, Op::Load(_) => 3, _ => 2 }"
        ),
        "this arm matches `Op::Load(_)`, and the arm at 1:19 matches it too; remove one of the \
         two patterns"
    );
    let all = "match (UInt[2](3)) { 0 => 0, 1 => 1, 2 => 2, 3 => 3, _ => 4 }";
    assert_eq!(at("", all), "S021 1:54");
    assert_eq!(
        message("", all),
        "the arms before `_` cover each value of `UInt[2]`; remove the `_` arm"
    );
    assert_eq!(at("", "match (true) { true => 1 }"), "S021 1:1");
    let uncovered = |what: &str, ty: &str| {
        format!(
            "the `match` does not cover `{what}` of `{ty}`; add an arm for it, or add `_ => ...` \
             as the last arm"
        )
    };
    assert_eq!(
        message("", "match (true) { true => 1 }"),
        uncovered("false", "Bool")
    );
    assert_eq!(
        message("", "match (false) { false => 1 }"),
        uncovered("true", "Bool")
    );
    assert_eq!(
        message("", "match (UInt[2](3)) { 0 => 0, 1 => 1, 3 => 3 }"),
        uncovered("2", "UInt[2]")
    );
    assert_eq!(
        message("", "match (SInt[4](-1)) { 0 => 10, 1 => 0 }"),
        uncovered("-8", "SInt[4]")
    );
    assert_eq!(
        message("", "match (SInt[4](-1)) { -8 => 10, 1 => 0 }"),
        uncovered("-7", "SInt[4]")
    );
    assert_eq!(
        message(OPS, "match (Op::Add) { Op::Add => 1, Op::Pair(a, b) => 3 }"),
        uncovered("Op::Load(_)", "Op")
    );
    assert_eq!(
        message(
            OPS,
            "match (Op::Add) { Op::Load(x) => 1, Op::Pair(a, b) => 3 }"
        ),
        uncovered("Op::Add", "Op")
    );
    let tags = "match (Op::Add) { Op::Add => 1, Op::Load(x) => 2, Op::Pair(a, b) => 3 }";
    assert_eq!(at(OPS, tags), "S021 1:1");
    assert_eq!(
        message(OPS, tags),
        "the tag `3` of `Op` has no variant, but a port or a memory can hold it; add `_ => ...` \
         as the last arm"
    );
    assert_eq!(at("", "match (5) { 5 => 1 }"), "S021 1:1");
    assert_eq!(
        message("", "match (5) { 5 => 1 }"),
        "a `match` on `Int` has no finite set of values; add `_ => ...` as the last arm"
    );
    assert_eq!(at("", "match (5) { }"), "S021 1:1");
    assert_eq!(at("", "match (true) { }"), "S021 1:1");
}

/// The checks of all arms and the coverage check come before an arm evaluates. Thus an error
/// does not depend on the value of the scrutinee. The arms that are not selected never evaluate.
#[test]
fn the_checks_come_before_an_arm_evaluates() {
    assert_eq!(
        at("", "match (true) { true => 1, false => 1 / 0 }"),
        "(int 1)"
    );
    assert_eq!(
        at("", "match (true) { true => 1 / 0, false => 1, true => 2 }"),
        "S021 1:43"
    );
}

/// A wide scrutinee needs no walk over its `2^W` values. The count of the keys compares with
/// `2^W` by `W`. The smallest uncovered value comes from one pass over the keys.
#[test]
fn a_wide_scrutinee_needs_no_walk_over_its_values() {
    assert_eq!(
        at("", "match (UInt[1024](5)) { 0 => 1, 5 => 2, _ => 3 }"),
        "(int 2)"
    );
    let uncovered = |ty: &str| {
        format!(
            "the `match` does not cover `2` of `{ty}`; add an arm for it, or add `_ => ...` as \
             the last arm"
        )
    };
    assert_eq!(
        message("", "match (UInt[1024](5)) { 0 => 1, 1 => 3, 5 => 2 }"),
        uncovered("UInt[1024]")
    );
    assert_eq!(
        message("", "match (UInt[65536](5)) { 0 => 1, 1 => 3, 5 => 2 }"),
        uncovered("UInt[65536]")
    );
    let wide = |ty: &str, low: &str| {
        format!(
            "the `match` does not cover `{low}` of `{ty}`; add an arm for it, or add `_ => ...` \
             as the last arm"
        )
    };
    assert_eq!(
        message("", "match (SInt[1024](5)) { 0 => 1 }"),
        wide("SInt[1024]", "a negative integer of 1024 bits")
    );
    assert_eq!(
        message("", "match (SInt[257](5)) { 0 => 1 }"),
        wide("SInt[257]", "a negative integer of 257 bits")
    );
    let low = format!("-{}", crate::int::Int::from_u64(1).shl(255));
    assert_eq!(
        message("", "match (SInt[256](5)) { 0 => 1 }"),
        wide("SInt[256]", &low)
    );
    assert_eq!(
        at("", "match (UInt[64](5)) { 0 => 1, 5 => 2, _ => 3 }"),
        "(int 2)"
    );
    exact(
        "",
        "match (UInt[1024](5)) { 0 => 1, 5 => 2, _ => 3 }",
        1 + 27 + 2 * (2 + 3) + 1 + 2,
    );
}

/// A variant pattern charges `1 + s` with `s` the size 1 of a `UInt[2]` tag, and 1 for each
/// binder and `_`. Three arms that are not `_` give the share `3 + s`. A binder of the selected
/// arm then charges the zero size of its type. It binds the static unpack of its payload value,
/// at the offset of the value in the pack. `Op::Load(7)` binds `x` for the zero size 1 of
/// `UInt[8]`.
#[test]
fn a_static_binder_charges_its_zero_size_and_binds_the_unpack() {
    let e = "match (Op::Add) { Op::Add => 1, Op::Load(x) => 2, Op::Pair(a, b) => 3, _ => 4 }";
    assert_eq!(at(OPS, e), "(int 1)");
    exact(OPS, e, 1 + 72 + (2 + 3) + (3 + 3) + (4 + 3) + 1 + 2);
    let e = "match (Op::Load(7)) { Op::Add => 1, Op::Load(x) => x, _ => 4 }";
    assert_eq!(at(OPS, e), "(uint 8 7)");
    exact(OPS, e, 1 + 77 + (2 + 3) + (3 + 3) + 1 + 1 + 1);
    assert_eq!(
        at(
            OPS,
            "match (Op::Pair(true, 9)) { Op::Pair(a, b) => (a, b), _ => (false, 4) }"
        ),
        "(tuple ((bool true) (uint 4 9)))"
    );
    assert_eq!(
        at(
            OPS,
            "match (Op::Pair(true, 9)) { Op::Pair(_, b) => b, _ => 4 }"
        ),
        "(uint 4 9)"
    );
    let f = format!(
        "{OPS}fn f(o: Op) -> UInt[8] {{ return match (o) {{ Op::Load(v) => v, _ => 0 }}; }}\n"
    );
    assert_eq!(at(&f, "f(Op::Load(3)) +% f(Op::Add)"), "(uint 8 3)");
    let nested = "enum F: UInt[1] { A = 0, B = 1 }\nstruct S { a: UInt[3], f: F }\n\
                  enum E: UInt[2] { X(F, [UInt[3]; 2], (), S, SInt[4]) = 3, Y = 0 }\n";
    assert_eq!(
        at(
            nested,
            "match (E::X(F::B, [5, 2], (), S(6, F::B), -3)) { E::X(f, a, u, s, i) => (f, a, u, s, \
             i), _ => (F::A, [0, 0], (), S(0, F::A), 0) }"
        ),
        "(tuple ((enum (enum root F ()) 1) (array (uint 3) ((uint 3 5) (uint 3 2))) (unit) \
         (record (struct root S ()) ((uint 3 6) (enum (enum root F ()) 1))) (sint 4 -3)))"
    );
    let wide = "enum E: UInt[1] { A(UInt[63], UInt[70], Bool) = 1, B = 0 }\n";
    assert_eq!(
        at(
            wide,
            "match (E::A(UInt[63](0) -% 1, UInt[70](0) -% 3, true)) { E::A(a, b, c) => (a, b, c), \
             E::B => (0, 0, false) }"
        ),
        format!(
            "(tuple ((uint 63 {}) (uint 70 {}) (bool true)))",
            (1u128 << 63) - 1,
            (1u128 << 70) - 3
        )
    );
}

/// A binder checks the size limit at the zero size of its type, then charges the zero size.
/// Thus a payload of no bits with a large zero size pays for its value. `A(x)` pays
/// `1 + 4096 * 4097`. A zero size above 2^32 is `S015` at the binder, and `_` makes no value.
#[test]
fn a_binder_pays_the_zero_size_of_its_type() {
    let big = "enum E: UInt[1] { A([[(); 4096]; 4096]) = 0, B([[[(); 65536]; 65536]; 2]) = 1 }\n";
    exact(
        big,
        "match (reinterpret(E, UInt[1](0))) { E::A(_) => 1, _ => 2 }",
        124,
    );
    exact(
        big,
        "match (reinterpret(E, UInt[1](0))) { E::A(x) => 1, _ => 2 }",
        124 + 1 + 4096 * 4097,
    );
    let e = "match (reinterpret(E, UInt[1](1))) { E::A(x) => 1, E::B(y) => 2 }";
    assert_eq!(at(big, e), "S015 1:57");
    assert_eq!(
        message(big, e),
        "the value of the type has a size above 2^32, the limit of a value from a type; use a \
         smaller type or keep it a reference"
    );
    assert_eq!(
        at(
            big,
            "match (reinterpret(E, UInt[1](1))) { E::A(x) => 1, E::B(_) => 2 }"
        ),
        "(int 2)"
    );
}
