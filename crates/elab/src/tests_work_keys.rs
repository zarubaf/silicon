// SPDX-License-Identifier: Apache-2.0
//! The work of the ports with an `as` key and of the ports of helpers, as the work bound of
//! design section 5.5 states it for the Rust front end (issue #339). Each family runs at a size
//! `n` and at `2n`. The work is the sum of all counters of the run. A doubled size must give at
//! most the work that the bound allows, and the work must stay within a constant times the fuel
//! that the run used. The tests count the steps of the walks and not the time.

use crate::counters::of;
use crate::tests_flatten::lowered;
use crate::tests_work_handles::{Run, passing, run};
use std::fmt::Write;

/// The key of the first run of this file. It keeps the fuel of each run unique.
const KEY: u64 = 9000;

/// The work of the run of `src` with its lowering, under a fuel that no other run uses.
fn lowered_work(key: u64, src: &str) -> u64 {
    let fuel = 930_000_000 + key;
    lowered(src, "M", fuel).unwrap_or_else(|e| panic!("{e}\n{src}"));
    of(fuel).total()
}

/// The error of a run, as the pair of its code and its message.
fn error_of(r: &Run) -> (&str, &str) {
    r.error
        .as_ref()
        .map_or(("", ""), |(c, m)| (c.as_str(), m.as_str()))
}

/// W1. `n` scalar ports `as "p" + str(i)` from a loop. Each port looks up and inserts its name
/// in the table of public names and in the symbol table, each one ordered-map operation, so the
/// work is linear in the counted steps. A scan of the table for each port gives `n^2`.
#[test]
fn w1_computed_names_of_a_loop_are_linear_with_a_log_factor() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "module M() {{\n    output o: UInt[8];\n    comptime for i in 0..{n} {{\n        \
             input p: UInt[8] as \"p\" + str(i);\n    }}\n    o := 0;\n}}\n"
        );
        passing(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 1), at(128, 2));
    let (a, b) = (n.counts.total(), twice.counts.total());
    assert!(a < b && b <= 21 * a / 10, "the work {a} at n and {b} at 2n");
    assert!(twice.counts.total() <= 40 * twice.used);
}

/// W2. A child with `n` input entries `as PortKey(B, true, i)`, `B` of `l` bytes. The parent
/// selects `u.B[i]` for each of the `n` keys, `n` times each, then binds each entry once. A
/// selection of an input gives a handle and holds the symbol of the name, so a use copies,
/// hashes, and compares no name. The work at `l` and `2l` differs by at most a constant times
/// `n * l`, the cost of the `n` declarations and bindings. A copy of the name for each use gives
/// `n * n * l`.
#[test]
fn w2_selections_of_a_long_computed_family_name_copy_no_name() {
    let at = |n: usize, l: usize, key: u64| {
        let name = "a".repeat(l);
        let src = format!(
            "module C(comptime n: Nat) {{\n    comptime for i in 0..n {{\n        \
             input g: UInt[8] as PortKey(\"{name}\", true, i);\n    }}\n}}\n\
             module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             instance u = C({n});\n    comptime for j in 0..{n} {{\n        \
             comptime for i in 0..{n} {{\n            let h = u.{name}[i];\n        }}\n    }}\n    \
             comptime for i in 0..{n} {{\n        u.{name}[i] := x;\n    }}\n    o := x;\n}}\n"
        );
        lowered_work(KEY + key, &src)
    };
    let (n, l) = (64usize, 256usize);
    let (short, long) = (at(n, l, 10), at(n, 2 * l, 11));
    let bound = 2 * (n * l) as u64;
    assert!(
        long - short <= bound,
        "the work {short} at l and {long} at 2l"
    );
}

/// W3. A helper that recurses to the depth `n`, and each level declares a keyed port. A port of a
/// helper belongs to the owner and builds no path of its call frame, so the work is linear in
/// the calls. A walk of the call frames for each port gives `n^2`.
#[test]
fn w3_a_recursive_helper_with_a_keyed_port_at_each_level_is_linear() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "fn lane(i: Nat) -> () {{\n    input x: UInt[8] as \"x\" + str(i);\n    \
             comptime if (i > 0) {{\n        lane(i - 1);\n    }}\n    return ();\n}}\n\
             module M() {{\n    output o: UInt[8];\n    lane({n});\n    o := 0;\n}}\n"
        );
        passing(KEY + key, 100_000, &src)
    };
    let (n, twice) = (at(100, 20), at(200, 21));
    let (a, b) = (n.counts.total(), twice.counts.total());
    assert!(a < b && b <= 21 * a / 10, "the work {a} at n and {b} at 2n");
    assert!(twice.counts.total() <= 40 * twice.used);
}

/// W4. `n` keyed ports, then one public name again. The check looks the name up in the table, so
/// the error `S019` comes after the work of the declarations, and its text renders once.
#[test]
fn w4_a_public_name_twice_is_found_without_a_scan() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "module M() {{\n    output o: UInt[8];\n    comptime for i in 0..{n} {{\n        \
             input p: UInt[8] as \"p\" + str(i);\n    }}\n    input q: UInt[8] as \"p0\";\n    \
             o := 0;\n}}\n"
        );
        run(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 30), at(128, 31));
    for r in [&n, &twice] {
        assert_eq!(error_of(r).0, "S019", "{:?}", r.error);
    }
    let (a, b) = (n.counts.total(), twice.counts.total());
    assert!(a < b && b <= 5 * a / 2, "the work {a} at n and {b} at 2n");
    assert_eq!(twice.counts.text_bytes, n.counts.text_bytes);
}

/// W5. A scalar `PortKey` whose index has the bit length `b`. The check of the index reads the
/// bit length, and the text names the length and not the digits. The work at `b` and `2b` differs
/// by at most a constant times `b`, and no digit is made. A decimal form of the index gives `b^2`.
#[test]
fn w5_the_index_of_a_port_key_is_never_rendered_in_decimal() {
    let at = |b: usize, indexed: bool, key: u64| {
        let src = format!(
            "module M() {{\n    output o: UInt[8];\n    \
             input p: UInt[8] as PortKey(\"x\", {indexed}, 1 << {b});\n    o := 0;\n}}\n"
        );
        run(KEY + key, 1000, &src)
    };
    for (indexed, code, key) in [(false, "S022", 40), (true, "S012", 44)] {
        let (small, big) = (at(1024, indexed, key), at(2048, indexed, key + 1));
        assert_eq!(error_of(&small).0, code, "{:?}", small.error);
        assert_eq!(error_of(&big).0, code, "{:?}", big.error);
        assert!(error_of(&big).1.contains("an integer of 2049 bits"));
        let (a, b) = (small.counts.total(), big.counts.total());
        assert!(b - a <= 4 * 1024, "the work {a} at b and {b} at 2b");
        assert_eq!(big.counts.formatted, 0);
        assert_eq!(big.counts.converted, 0);
    }
}

/// W6. `n` hardware `let`s of the module body, then `n` keyed ports with other names, then one
/// port with a taken name. The reservation of the core name looks it up in the table of versions,
/// so the error `S019` comes after the work of the declarations, and its text renders once.
#[test]
fn w6_a_taken_port_name_is_found_without_a_scan() {
    let at = |n: usize, key: u64| {
        let mut src = "module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n".to_owned();
        for i in 0..n {
            writeln!(src, "    let l{i} = x +% {};", i % 200).unwrap();
        }
        writeln!(
            src,
            "    comptime for i in 0..{n} {{\n        input p: UInt[8] as \"k\" + str(i);\n    }}"
        )
        .unwrap();
        src.push_str("    input t: UInt[8] as \"l0\";\n    o := x;\n}\n");
        run(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 50), at(128, 51));
    for r in [&n, &twice] {
        assert_eq!(error_of(r).0, "S019", "{:?}", r.error);
        assert!(error_of(r).1.contains("is already the core name"));
    }
    let (a, b) = (n.counts.total(), twice.counts.total());
    assert!(a < b && b <= 5 * a / 2, "the work {a} at n and {b} at 2n");
    assert_eq!(twice.counts.text_bytes, n.counts.text_bytes);
}
