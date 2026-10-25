// SPDX-License-Identifier: Apache-2.0
//! The work of `@TypeOf`, as the work bound of design section 5.5 states it for the Rust front end
//! (issue #344). Each family runs at a size `n` and at `2n`. The work is the sum of all counters
//! of the run, and the work of the queries is the work of the run less the work of the same run
//! without them. The tests count the steps of the walks and not the time.

use crate::counters::Counts;
use crate::tests_work_handles::{Run, passing};
use std::fmt::Write;

/// The key of the first run of this file. It keeps the fuel of each run unique.
const KEY: u64 = 13000;

/// The work and the units that `queries` more queries cost, in the run of `src` with them and in
/// the run without them.
fn extra(with: &Run, without: &Run) -> (u64, u64) {
    (
        with.counts.total() - without.counts.total(),
        with.used - without.used,
    )
}

/// W1. `n` queries `@TypeOf(a[0]...[0])` of depth `d` on a static nest of arrays. The steps walk
/// the part once from the root, so one query takes work in `d`. A walk from the root for each step
/// gives `d * d`. The work of the queries at `2d` is at most twice the work at `d`, and it stays
/// within a constant times the units that they used.
#[test]
fn w1_a_query_of_a_deep_place_walks_the_place_once() {
    let at = |d: usize, n: usize, key: u64| {
        let mut src = "module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n".to_owned();
        writeln!(src, "    let a = {}0{};", "[".repeat(d), "]".repeat(d)).unwrap();
        for k in 0..n {
            writeln!(src, "    let t{k} = @TypeOf(a{});", "[0]".repeat(d)).unwrap();
        }
        src.push_str("    o := x;\n}\n");
        passing(KEY + key, 1000, &src)
    };
    let n = 8;
    let (small, large) = (at(32, n, 1), at(64, n, 2));
    let (small_base, large_base) = (at(32, 0, 3), at(64, 0, 4));
    let ((a, units_a), (b, units_b)) = (extra(&small, &small_base), extra(&large, &large_base));
    assert!(
        a < b && b <= 2 * a + 8 * n as u64,
        "the work {a} at d and {b} at 2d"
    );
    assert!(
        a <= 8 * units_a && b <= 8 * units_b,
        "{a}/{units_a} {b}/{units_b}"
    );
    // The queries walk once: about 4 steps for each index, not `d` for each.
    assert!(
        b <= 8 * (n * 64) as u64,
        "the work {b} of {n} queries of depth 64"
    );
}

/// W2. `n` queries of a static tuple of `t` nested tuples. A tuple stores no type, so each query
/// builds it. Each tuple node charges before the walk visits it, and the type charges its size
/// once. The work of the queries stays within a constant times the units that they used, and it
/// doubles when `t` doubles. A walk that ticks without a charge, as `Value::ty` does, gives more.
#[test]
fn w2_the_type_of_a_static_tuple_is_built_for_its_charge() {
    let at = |t: usize, n: usize, key: u64| {
        let mut src = "module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n".to_owned();
        writeln!(src, "    let v = {}0{};", "(1, ".repeat(t), ")".repeat(t)).unwrap();
        for k in 0..n {
            writeln!(src, "    let t{k} = @TypeOf(v);").unwrap();
        }
        src.push_str("    o := x;\n}\n");
        passing(KEY + key, 1000, &src)
    };
    let n = 4;
    let (small, large) = (at(32, n, 10), at(64, n, 11));
    let (small_base, large_base) = (at(32, 0, 12), at(64, 0, 13));
    let ((a, units_a), (b, units_b)) = (extra(&small, &small_base), extra(&large, &large_base));
    assert!(
        a < b && b <= 2 * a + 8 * n as u64,
        "the work {a} at t and {b} at 2t"
    );
    assert!(
        a <= 4 * units_a && b <= 4 * units_b,
        "{a}/{units_a} {b}/{units_b}"
    );
}

/// The counters of a run that a hardware node or a read of a resource moves: the words of the
/// nodes of the graph, the parts that the read of a container of handles visited, the nodes of
/// the path arena, and the parts that a reference expanded into.
fn hardware(c: &Counts) -> [u64; 5] {
    [c.words, c.read, c.paths, c.expanded, c.nodes]
}

/// W8. A query of a part of a register, a wire, or a child output makes no hardware node and no
/// read. The run with the queries and the run with a `let` of a type in place of each query move
/// none of the counters of the hardware.
#[test]
fn w8_a_query_makes_no_hardware_node_and_no_read() {
    let at = |queries: bool, key: u64| {
        let mut src = "struct P {\n    a: UInt[8],\n    b: (Bool, UInt[4]),\n}\n\
                       module C() domains() {\n    input a: P;\n    output q: P;\n    q := a;\n}\n\
                       module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n    \
                       reg rg: P = P();\n    wire w: P;\n    instance u = C();\n"
            .to_owned();
        for k in 0..16 {
            for (i, operand) in ["rg.a", "rg.b.1", "w.b", "u.q.a", "u.q.b.1", "u.a.a"]
                .into_iter()
                .enumerate()
            {
                let value = if queries {
                    format!("@TypeOf({operand})")
                } else {
                    "UInt[8]".to_owned()
                };
                writeln!(src, "    let r{k}x{i} = {value};").unwrap();
            }
        }
        src.push_str(
            "    rg := P(x, (true, 1));\n    w := P(x, (true, 1));\n    u.a := P(x, (true, 1));\n    \
             o := read(rg).a +% u.q.a;\n}\n",
        );
        passing(KEY + key, 1000, &src)
    };
    let (with, without) = (at(true, 20), at(false, 21));
    assert_eq!(hardware(&with.counts), hardware(&without.counts));
    assert!(with.counts.queried > 0, "the queries counted no step");
}
