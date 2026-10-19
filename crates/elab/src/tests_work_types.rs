// SPDX-License-Identifier: Apache-2.0
//! The work of the type table, as the work bound of design section 5.5 states it for the Rust
//! front end. A type carries its size and its depth, so building a type and reading it take
//! constant work for each step, and no query walks the type term. The tests count the steps of
//! the table (`Count::Table`) and the nodes that `Value::size` and `Value::depth` visited
//! (`Count::Walked`), and not the time.

use crate::tests_work_handles::{Run, passing, run};
use std::fmt::Write;

/// The work of the type table in a run.
fn work(r: &Run) -> u64 {
    r.counts.table + r.counts.walked
}

/// The program that makes the type `t` by `n` steps of `step`, and then adds `tail`.
fn nested(n: u64, step: &str, tail: &str) -> String {
    format!(
        "struct W(comptime T: Type) {{\n    v: T,\n}}\nmodule M() domains() {{\n    let mut t = Bool;\n\
         \x20   comptime for i in 0..{n} {{\n        {step}\n    }}\n{tail}}}\n"
    )
}

/// The constructors of types that nest: a step for each one.
const STEPS: [(&str, &str); 5] = [
    ("array", "t = [t; 1];"),
    ("tuple", "type U = (t, Bool); t = U;"),
    ("list", "t = List[t];"),
    ("function", "t = fn (t) -> Bool;"),
    ("struct", "t = W[t];"),
];

/// W1. A type that nests to the depth `n` with each constructor takes work in proportion to `n`,
/// while the fuel grows with the square of `n`: each level charges its size, which is its depth.
/// A walk of the size at each level would make the work grow with the square too.
#[test]
fn w1_a_nested_type_takes_work_in_proportion_to_its_depth() {
    for (k, (name, step)) in STEPS.iter().enumerate() {
        let at = |n: u64, j: u64| passing(20_000 + 10 * k as u64 + j, 10_000, &nested(n, step, ""));
        let runs = [at(32, 0), at(64, 1), at(128, 2)];
        for (r, n) in runs.iter().zip([32, 64, 128]) {
            assert!(work(r) <= 16 * n, "{name}: the work {} at N={n}", work(r));
        }
        for pair in runs.windows(2) {
            assert!(
                2 * pair[1].used >= 5 * pair[0].used,
                "{name}: the fuel {} and {} is not quadratic",
                pair[0].used,
                pair[1].used
            );
        }
    }
}

/// W2. `k` copies of one type of the size `s`: `let t{i}: Type = t;`. A copy of a type is a copy
/// of its id, so the work of a copy does not depend on `s`. The work for the added `k` copies is
/// the same at `s` and at `2s`. A re-walk of the type for each read makes it grow with `s`.
#[test]
fn w2_a_copy_of_a_type_takes_work_that_does_not_depend_on_its_size() {
    for (j, (name, step)) in STEPS.iter().enumerate() {
        let copies = |s: u64, k: u64, i: u64| {
            let mut tail = String::new();
            for c in 0..k {
                writeln!(tail, "    let t{c}: Type = t;").unwrap();
            }
            let key = 21_000 + 10 * j as u64 + i;
            work(&passing(key, 10_000, &nested(s, step, &tail)))
        };
        let added = |s: u64, i: u64| copies(s, 16, i) - copies(s, 8, i + 2);
        let (small, large) = (added(32, 0), added(64, 4));
        assert!(small > 0, "{name}: no work for the copies");
        assert!(
            small.abs_diff(large) <= 4,
            "{name}: the work of 8 copies is {small} at S=32 and {large} at S=64"
        );
    }
}

/// W3. The chain `type T{i+1} = (T{i}, T{i});` doubles the size at each step, so the size of the
/// type is exponential in the steps. The work follows the steps: the table shares the parts, and
/// no query walks the tree. The run ends in `S015` once the fuel cannot pay the size.
#[test]
fn w3_a_doubling_chain_takes_work_in_proportion_to_its_steps() {
    let chain = |n: u64, key: u64| {
        let mut src = String::from("module M() domains() {\n    type T0 = Bool;\n");
        for i in 0..n {
            writeln!(src, "    type T{} = (T{i}, T{i});", i + 1).unwrap();
        }
        src.push_str("}\n");
        run(22_000 + key, 10_000, &src)
    };
    let (a, b, c) = (chain(8, 0), chain(16, 1), chain(24, 2));
    for r in [&a, &b, &c] {
        assert_eq!(r.error, None);
    }
    let (steps, more) = (work(&b) - work(&a), work(&c) - work(&b));
    assert!(steps > 0 && steps.abs_diff(more) <= 4, "{steps} and {more}");
    let long = chain(60, 3);
    assert!(
        matches!(&long.error, Some((code, _)) if code == "S015"),
        "{:?}",
        long.error
    );
    assert!(work(&long) <= 400, "the work {} before S015", work(&long));
}
