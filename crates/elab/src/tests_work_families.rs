// SPDX-License-Identifier: Apache-2.0
//! The work of the port families, as the work bound of design section 5.5 states it for the Rust
//! front end (issue #338). Each family runs at a size `n` and at `2n`. The work is the sum of all
//! counters of the run. A doubled size must give at most twice the work, and the work must stay
//! within a constant times the fuel that the run used. The tests count the steps of the walks and
//! not the time.

use crate::counters::of;
use crate::tests_flatten::lowered;
use crate::tests_work_handles::{doubles, passing, run};
use std::fmt::Write;

/// The key of the first run of this file. It keeps the fuel of each run unique.
const KEY: u64 = 7000;

/// The work of the run of `src` with its lowering, under a fuel that no other run uses.
fn lowered_work(key: u64, src: &str) -> u64 {
    let fuel = 930_000_000 + key;
    lowered(src, "M", fuel).unwrap_or_else(|e| panic!("{e}\n{src}"));
    of(fuel).total()
}

/// W1. `n` entries from a loop, then `n` selections `req[i]` in a second loop. A selection finds
/// its entry in the table of entries by the binder and the key, so the work is linear.
#[test]
fn w1_selections_of_the_entries_of_a_loop_are_linear() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             comptime for i in 0..{n} {{\n        input req[i]: UInt[8];\n    }}\n    \
             comptime for i in 0..{n} {{\n        let b = req[i];\n    }}\n    o := x;\n}}\n"
        );
        passing(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 1), at(128, 2));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 20 * twice.used);
}

/// W2. A child with `n` output entries, built once. The parent reads `u.gnt[i]` for `n` keys. A
/// selection finds the port in the interface of the child by its symbol and key, so the work is
/// linear.
#[test]
fn w2_selections_of_the_entries_of_a_child_are_linear() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "module C(comptime n: Nat) {{\n    comptime for i in 0..n {{\n        \
             output gnt[i]: UInt[8];\n        gnt[i] := 0;\n    }}\n}}\n\
             module M() {{\n    output o: UInt[8];\n    instance u = C({n});\n    \
             comptime for i in 0..{n} {{\n        let b = u.gnt[i];\n    }}\n    o := 0;\n}}\n"
        );
        passing(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 3), at(128, 4));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 20 * twice.used);
}

/// W3. `n` entries of the empty type `()` with a basename of `l` bytes. The entries hold the
/// symbol of the name, so a declaration, the layout sort, and the lowering copy and compare no
/// name. The work at `(n, l)` and `(n, 2l)` differs by at most a constant times `l`. A copy of the
/// name for each entry, or a sort by the text, gives `n * l`.
#[test]
fn w3_entries_of_a_long_family_name_copy_and_compare_no_name() {
    let at = |n: usize, l: usize, key: u64| {
        let name = format!("{}req", "a".repeat(l));
        let src = format!(
            "module M() {{\n    output o: UInt[8];\n    comptime for i in 0..{n} {{\n        \
             input {name}[i]: ();\n    }}\n    o := 0;\n}}\n"
        );
        lowered_work(KEY + key, &src)
    };
    let (n, l) = (64, 256);
    let (short, long) = (at(n, l, 10), at(n, 2 * l, 11));
    assert!(
        long - short <= 20 * l as u64,
        "the work {short} at l and {long} at 2l"
    );
    let (small, twice) = (at(n, l, 12), at(2 * n, l, 13));
    assert!(twice <= 2 * small + 40 * l as u64, "{small} and {twice}");
}

/// W4. `n` entries, then a second declaration of one key. The check of the duplicate looks up the
/// table of entries, so the error comes after the work of the declarations, and the text renders
/// once.
#[test]
fn w4_a_second_key_is_found_without_a_scan() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             comptime for i in 0..{n} {{\n        input req[i]: UInt[8];\n    }}\n    \
             input req[0]: UInt[8];\n    o := x;\n}}\n"
        );
        run(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 20), at(128, 21));
    for r in [&n, &twice] {
        let code = r.error.as_ref().map(|e| e.0.as_str());
        assert_eq!(code, Some("S019"), "{:?}", r.error);
    }
    doubles(&n, &twice);
    assert_eq!(twice.counts.text_bytes, n.counts.text_bytes);
}

/// W5. The instance `u` nests in `d` arrays, and `n` targets `h[0]...[0].req[i] := x;` bind the
/// `n` inputs of `u`. The family key is taken in the step of the field, so a target walks its
/// path once. The work at `(n, d)` and `(n, 2d)` at most doubles. A walk from the root at the
/// family field gives `d` more steps for each target.
#[test]
fn w5_targets_of_a_nested_child_family_walk_the_path_once() {
    let at = |n: usize, d: usize, key: u64| {
        let (open, close) = ("[".repeat(d), "]".repeat(d));
        let mut src = format!(
            "module C(comptime n: Nat) {{\n    comptime for i in 0..n {{\n        \
             input req[i]: UInt[8];\n    }}\n}}\n\
             module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             instance u = C({n});\n    let h = {open}u{close};\n"
        );
        for i in 0..n {
            writeln!(src, "    h{}.req[{i}] := x;", "[0]".repeat(d)).unwrap();
        }
        src.push_str("    o := x;\n}\n");
        passing(KEY + key, 100_000, &src)
    };
    let (n, twice) = (at(32, 32, 30), at(32, 64, 31));
    let (a, b) = (n.counts.total(), twice.counts.total());
    assert!(a < b && b <= 2 * a, "the work {a} at d and {b} at 2d");
    assert!(twice.counts.total() <= 40 * twice.used);
}

/// W6. A child with `n` input entries. The parent binds all but the last. The error `S018` comes
/// at the end of the body after the work of the bindings, and its text renders once.
#[test]
fn w6_an_unbound_entry_of_a_child_renders_its_text_once() {
    let at = |n: usize, key: u64| {
        let mut src = format!(
            "module C(comptime n: Nat) {{\n    comptime for i in 0..n {{\n        \
             input req[i]: UInt[8];\n    }}\n}}\n\
             module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             instance u = C({n});\n"
        );
        for i in 0..n - 1 {
            writeln!(src, "    u.req[{i}] := x;").unwrap();
        }
        src.push_str("    o := x;\n}\n");
        run(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 40), at(128, 41));
    for (r, last) in [(&n, 63), (&twice, 127)] {
        let message = format!(
            "the input `req[{last}]` of the instance `u` has no binding; bind it with \
             `u.req[{last}] := ...;`"
        );
        assert_eq!(r.error, Some(("S018".to_owned(), message)));
    }
    doubles(&n, &twice);
    let bytes = |r: &crate::tests_work_handles::Run| r.counts.text_bytes;
    assert!(bytes(&twice) <= bytes(&n) + 4, "the text renders once");
    assert!(bytes(&n) > 0);
}
