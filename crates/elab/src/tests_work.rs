// SPDX-License-Identifier: Apache-2.0
//! The work of the comparisons of types, as the work bound of design section 5.5 states it for
//! the Rust front end: a type is an id, so a comparison, a key, and a join cost constant work
//! for each use and one walk for each pair of ids. Each family has an alias `Tn` of `n` types
//! and `k` repeated uses. The work then grows in `n + k` and not in `n * k`. The tests count
//! the steps of the walks and not the time.

use crate::counters::of;
use crate::tests::{out, type_work};

/// The alias of a tuple of `n` Booleans.
fn tn(n: usize) -> String {
    format!("type Tn = ({});\n", vec!["Bool"; n].join(", "))
}

/// Repeated specialization keys: one list `xs` of `Tn`, and `k` uses of `P[xs]`.
fn keys(n: usize, k: usize) -> String {
    format!(
        "{}type A = List[Tn];\nstruct P(comptime xs: A) {{ }}\n\
         fn f() -> Int {{ let xs = list(Tn); \
         comptime for i in 0..{k} {{ type S = P[xs]; }} return 0; }}",
        tn(n)
    )
}

/// Repeated typed uses of a function value: `k` assignments of `v` to a typed `g`.
fn typed(n: usize, k: usize) -> String {
    format!(
        "{}fn f1(x: Tn) -> Bool {{ return true; }}\n\
         fn f() -> Int {{ let v = f1; let mut g: fn (Tn) -> Bool = v; \
         comptime for i in 0..{k} {{ g = v; }} return 0; }}",
        tn(n)
    )
}

/// Repeated `==` on the empty list of `Tn`.
fn equals(n: usize, k: usize) -> String {
    format!(
        "{}fn f() -> Int {{ let xs = list(Tn); \
         comptime for i in 0..{k} {{ let b = xs == xs; }} return 0; }}",
        tn(n)
    )
}

/// The work of a run: the steps of the table, the pairs compared, the pairs of types joined,
/// the operands that the check of `==` read the function flag of, and the nodes of the size
/// walks. The family number and the sizes make the fuel of the run unique.
fn work(family: u64, source: fn(usize, usize) -> String, n: usize, k: usize) -> [u64; 5] {
    let fuel = 500_000_000 + family * 1_000_000 + (n as u64) * 1000 + k as u64;
    let src = source(n, k);
    assert_eq!(out(&src, "f()", fuel, 1000), "(int 0)", "{n} {k}");
    let counts = of(fuel);
    [
        type_work(&src, "f()"),
        counts.compared,
        counts.visited,
        counts.flagged,
        counts.walked,
    ]
}

/// Each count grows by the same amount for each equal step of `n`, and for each equal step of
/// `k`, and the growth in `k` does not depend on `n`. A product `n * k` breaks one of these.
fn assert_linear(family: u64, source: fn(usize, usize) -> String) {
    let at = |n: usize, k: usize| work(family, source, n, k);
    let base = at(100, 100);
    let (n2, n4) = (at(200, 100), at(400, 100));
    let (k2, k4) = (at(100, 200), at(100, 400));
    let (n4k2, n4k4) = (at(400, 200), at(400, 400));
    for m in 0..base.len() {
        assert_eq!(n4[m] - n2[m], 2 * (n2[m] - base[m]), "count {m} in n");
        assert_eq!(k4[m] - k2[m], 2 * (k2[m] - base[m]), "count {m} in k");
        assert_eq!(n4k2[m] - n4[m], k2[m] - base[m], "count {m} n*k");
        assert_eq!(n4k4[m] - n4k2[m], k4[m] - k2[m], "count {m} n*k");
    }
    // The type work does grow in `n`: the first use of the alias walks its types once.
    assert!(n2[0] > base[0], "{base:?} {n2:?}");
}

/// A later use of a specialization compares its key, a list of an id: it does not walk the `n`
/// types of the element type.
#[test]
fn the_work_of_specialization_keys_is_linear_in_n_and_k() {
    assert_linear(1, keys);
}

/// The typed use of a function value compares the ids of the signatures.
#[test]
fn the_work_of_typed_uses_of_a_function_value_is_linear_in_n_and_k() {
    assert_linear(2, typed);
}

/// The function flag and the join of two equal tuple types do not walk the `n` types again for
/// each `==`: the table keeps the join of a pair of ids.
#[test]
fn the_work_of_repeated_equality_is_linear_in_n_and_k() {
    assert_linear(3, equals);
}
