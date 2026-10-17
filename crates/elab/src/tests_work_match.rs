// SPDX-License-Identifier: Apache-2.0
//! The work of the `match`, as the work bound of design sections 5.4 and 5.5 states it for the
//! Rust front end. The coverage check compares the count of the keys with `2^W` by `W`, so it
//! never loops over the values of a type, and it makes one insert into an ordered map for each
//! arm. A binder unpacks its payload once for each part of its type, which its zero size paid
//! for. The tests count the steps of the walks and not the time.

use crate::counters::{Counts, of};
use crate::tests::run;
use std::fmt::Write as _;

/// The result, the used fuel, and the counts of the evaluation of `expr`. The key makes the
/// fuel budget of the run unique, so it keys the counters.
fn counted(key: u64, src: &str, expr: &str) -> (String, u64, Counts) {
    let fuel = 960_000_000 + key;
    let (text, used) = run(src, expr, fuel, 1000);
    (text, used, of(fuel))
}

/// A `match` on a `UInt[16]` with the arms `0`, ..., `n - 1`, and `_` unless `n` is `2^16`.
fn many(n: u64) -> String {
    let mut arms = String::new();
    for i in 0..n {
        write!(arms, "{i} => {i}, ").unwrap();
    }
    let wild = if n < 65536 { "_ => 99" } else { "" };
    format!("match (UInt[16](7)) {{ {arms}{wild} }}")
}

/// W1. A `match` on `UInt[16]` with `n` arms and `_` pays `4 + floor(log2 n)` units for each arm
/// (the pattern, and the share of the coverage check), and it makes `n` inserts into its map.
/// The work is `n log n`, and `2^16` arms need no walk over the values of the type.
#[test]
fn w1_n_arms_pay_n_log_n_and_make_n_inserts() {
    let at = |n: u64, key: u64| {
        let (text, used, counts) = counted(key, "", &many(n));
        assert_eq!(text, "(int 7)", "{n}");
        (used, counts.covered)
    };
    let (small, wide, widest) = (at(1024, 1), at(2048, 2), at(4096, 3));
    assert_eq!((small.1, wide.1, widest.1), (1024, 2048, 4096));
    assert_eq!(wide.0 - small.0, 2048 * (4 + 11) - 1024 * (4 + 10));
    assert_eq!(widest.0 - wide.0, 4096 * (4 + 12) - 2048 * (4 + 11));
    // The most arms of `UInt[16]` is `2^16`.
    let (used, counts) = at(65536, 4);
    assert_eq!(counts, 65536);
    // The arm `_` charges its pattern 1, and it never evaluates its value.
    assert_eq!(used + 1 - small.0, 65536 * (4 + 16) - 1024 * (4 + 10));
}

/// W2. A `match` on `UInt[W]` with two arms and `_` makes two inserts and compares the count of
/// the keys with `2^W` by `W`, whatever `W` is. A `match` without `_` that misses a value finds
/// it in one pass over its two keys.
#[test]
fn w2_the_coverage_of_a_wide_type_walks_no_value() {
    let e = |w: u64| format!("match (UInt[{w}](5)) {{ 0 => 1, 1 => 3, _ => 2 }}");
    let scrut = |w: u64| format!("UInt[{w}](5)");
    let extra = |w: u64, key: u64| {
        let (text, used, counts) = counted(key, "", &e(w));
        let (_, scrutinee, _) = counted(key + 100, "", &scrut(w));
        assert_eq!(text, "(int 2)");
        (used - scrutinee, counts.covered)
    };
    let (narrow, wide, widest) = (extra(16, 10), extra(1024, 11), extra(65536, 12));
    assert_eq!(narrow, wide);
    assert_eq!(wide, widest);
    assert_eq!(widest.1, 2);
    let missing = |w: u64, key: u64| {
        let src = format!("match (UInt[{w}](5)) {{ 0 => 1, 1 => 3 }}");
        let (text, _, counts) = counted(key, "", &src);
        assert_eq!(text, "S021 1:1", "{w}");
        counts.covered
    };
    assert_eq!(missing(16, 13), 4);
    assert_eq!(missing(65536, 14), 4);
    // Every key of `UInt[2]` is an arm, so `_` is an error and no pass runs.
    let all = "match (UInt[2](1)) { 0 => 0, 1 => 1, 2 => 2, 3 => 3, _ => 4 }";
    let (text, _, counts) = counted(15, "", all);
    assert_eq!((text.as_str(), counts.covered), ("S021 1:54", 4));
}

/// W3. A `match` on a static `Int` of `n` bits adds a constant to the charge of its scrutinee:
/// the key is the integer itself and no copy of it, and each compare with a small key reads
/// its length first.
#[test]
fn w3_a_large_static_scrutinee_costs_its_own_size_only() {
    let extra = |bits: u64, key: u64| {
        let scrutinee = format!("1 << {bits}");
        let e = format!("match ({scrutinee}) {{ 0 => 1, 5 => 3, _ => 2 }}");
        let (text, used, _) = counted(key, "", &e);
        let (_, base, _) = counted(key + 100, "", &scrutinee);
        assert_eq!(text, "(int 2)");
        used - base
    };
    let (small, large, larger) = (extra(1 << 10, 20), extra(1 << 20, 21), extra(1 << 21, 22));
    assert_eq!(small, large);
    assert_eq!(large, larger);
}

/// W4. A static binder of a payload `[[(); n]; n]` makes one value for each part of its type: its
/// work equals its zero size `1 + n * (1 + n)`, which it paid before.
#[test]
fn w4_a_static_binder_unpacks_in_its_zero_size() {
    let at = |n: u64, key: u64| {
        let src = format!("enum E: UInt[1] {{ A([[(); {n}]; {n}]) = 0, B = 1 }}\n");
        let e = "match (reinterpret(E, UInt[1](0))) { E::A(x) => 1, _ => 2 }";
        let with_binder = counted(key, &src, e);
        let with_wild = counted(
            key + 100,
            &src,
            "match (reinterpret(E, UInt[1](0))) { E::A(_) => 1, _ => 2 }",
        );
        assert_eq!(with_binder.0, "(int 1)");
        assert_eq!(with_wild.2.unpacked, 0);
        // The binder adds its zero size to the charge of the `_` arm.
        assert_eq!(with_binder.1 - with_wild.1, 1 + n * (1 + n));
        with_binder.2.unpacked
    };
    assert_eq!(at(64, 30), 1 + 64 * (1 + 64));
    assert_eq!(at(128, 31), 1 + 128 * (1 + 128));
}
