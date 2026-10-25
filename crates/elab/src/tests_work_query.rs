// SPDX-License-Identifier: Apache-2.0
//! The work of `@TypeOf` and of `@field` as a value, as the work bound of design section 5.5
//! states it for the Rust front end (issue #344). Each family runs at a size `n` and at `2n`. The
//! work is the sum of all counters of the run, and the work of the queries is the work of the run
//! less the work of the same run without them. The tests count the steps of the walks and not the
//! time.

use crate::counters::Counts;
use crate::tests_work_handles::{Run, passing, run};
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

/// The number of fields of the struct of W3.
const F: usize = 64;

/// The number of entries of the child of W4.
const E: usize = 32;

/// The struct `P` with `f` fields and the names of its fields. The names have `l` bytes and
/// differ in their last four.
fn record_with(f: usize, l: usize) -> (String, Vec<String>) {
    let names: Vec<String> = (0..f)
        .map(|i| format!("{}{i:04}", "a".repeat(l.saturating_sub(4))))
        .collect();
    let mut src = "struct P {\n".to_owned();
    for name in &names {
        writeln!(src, "    {name}: UInt[8],").unwrap();
    }
    src.push_str("}\n");
    (src, names)
}

/// W3. A struct with `f` fields, and `f` values `@field(p, "<name>")` with names of `l` bytes. A
/// key charges its size, and the look-up of its symbol is one look-up of the ordered map of the
/// table of symbols, then one of the fields by the symbol. The work at `l` and `2l` differs by 3
/// times `f * l`: the interning of each name at its field, at the scan of its struct, and the
/// look-up of the key. A scan of the fields for each use adds `f * l` more. So does a copy of the
/// key for each use, which would render the name as a text: the run renders no text.
#[test]
fn w3_a_string_key_is_read_once_and_found_by_its_symbol() {
    let at = |l: usize, key: u64| {
        let (mut src, names) = record_with(F, l);
        src.push_str(
            "module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n    let p = P();\n",
        );
        for (k, name) in names.iter().enumerate() {
            writeln!(src, "    let a{k} = @field(p, \"{name}\");").unwrap();
        }
        src.push_str("    o := x;\n}\n");
        passing(KEY + key, 1000, &src)
    };
    let l = 256;
    let (short, long) = (at(l, 20), at(2 * l, 21));
    let grown = long.counts.total() - short.counts.total();
    assert!(
        grown <= (3 * F * l + 8 * F) as u64,
        "the work grew by {grown} when the names doubled"
    );
    assert_eq!(long.counts.text_bytes, 0, "a key rendered its text");
    assert!(long.counts.total() <= 40 * long.used);
}

/// W4. A child with `e` input entries `req[i]` that an `as PortKey(B, true, i)` names with a
/// basename `B` of `l` bytes. The parent selects an entry by `@field(u, PortKey(B, true, i))`
/// for each of the `e` keys, `e` times each. The size of the name charges, and its symbol finds
/// the entry in the interface of the child, so a use copies no name. The work at `l` and `2l`
/// differs by at most a constant times `e * e * l`, the look-ups, and a bit more for the `e`
/// declarations. A copy of the name for each use adds `e * e * l` more.
#[test]
fn w4_a_port_key_with_a_long_basename_copies_no_name() {
    let at = |l: usize, key: u64| {
        let name = "a".repeat(l);
        let src = format!(
            "module C() {{\n    comptime for i in 0..{E} {{\n        \
             input g: UInt[8] as PortKey(\"{name}\", true, i);\n    }}\n}}\n\
             module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             instance u = C();\n    comptime for j in 0..{E} {{\n        \
             comptime for i in 0..{E} {{\n            \
             let h = @field(u, PortKey(\"{name}\", true, i));\n        }}\n    }}\n    \
             comptime for i in 0..{E} {{\n        u.{name}[i] := x;\n    }}\n    o := x;\n}}\n"
        );
        passing(KEY + key, 1000, &src)
    };
    let l = 256;
    let (short, long) = (at(l, 30), at(2 * l, 31));
    let grown = long.counts.total() - short.counts.total();
    assert!(
        grown <= ((E * E + 2 * E) * l) as u64,
        "the work grew by {grown} when the basename doubled"
    );
    assert_eq!(long.counts.text_bytes, 0, "a key rendered its text");
}

/// The error of a run: its code and its text.
fn error_of(r: &Run) -> (&str, &str) {
    r.error
        .as_ref()
        .map_or(("", ""), |(c, m)| (c.as_str(), m.as_str()))
}

/// W5. A key of 2^20 characters that names no field of a struct, and none of the public ports of a
/// child. The error is one `S010`, and its text names at most 64 characters of the key. The text
/// renders once, and its bytes stay within a limit, and not within the length of the key.
#[test]
fn w5_a_missing_key_of_a_million_characters_gives_a_bounded_text() {
    let at = |port: bool, key: u64| {
        let name = "z".repeat(1 << 20);
        let src = if port {
            format!(
                "module C() {{\n    output q: UInt[8];\n    q := 0;\n}}\n\
                 module M() {{\n    output o: UInt[8];\n    instance u = C();\n    \
                 let b = @field(u, \"{name}\");\n    o := 0;\n}}\n"
            )
        } else {
            format!(
                "struct P {{\n    a: UInt[8],\n}}\n\
                 module M() {{\n    output o: UInt[8];\n    let p = P();\n    \
                 let b = @field(p, \"{name}\");\n    o := 0;\n}}\n"
            )
        };
        run(KEY + key, 1000, &src)
    };
    for (port, key) in [(false, 40), (true, 41)] {
        let r = at(port, key);
        let (code, text) = error_of(&r);
        assert_eq!(code, "S010", "{text}");
        assert!(text.contains("(1048576 characters)"), "{text}");
        assert!(text.len() < 256, "{} bytes of text", text.len());
        assert!(
            r.counts.text_bytes <= 256,
            "{} bytes of text for the error",
            r.counts.text_bytes
        );
    }
}

/// The run of a read `m.0` through `d` steps over a hardware aggregate root. Each step is a key
/// `@field(..., key)` if `named`, else an index `[key]`. The function `fns` defines `key`.
fn chain_run(d: usize, named: bool, (fns, key): (&str, &str), run_key: u64) -> Run {
    let nest = format!("{}x{}", "[".repeat(d), "]".repeat(d));
    let mut read = "m.0".to_owned();
    for _ in 0..d {
        read = if named {
            format!("@field({read}, {key})")
        } else {
            format!("{read}[{key}]")
        };
    }
    let src = format!(
        "{fns}module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
         let mut m = ({nest}, list(Int), [1, 2]);\n    let y = {read};\n    o := y;\n}}\n"
    );
    passing(KEY + run_key, 100_000, &src)
}

/// W7b. A chain of `d` steps `@field(..., zero(m.2))` over a hardware aggregate root: each key
/// calls a function that changes a static sibling of the root while the read waits. The step holds
/// the root once, and pays for the copy of its result, as the index of the same chain does. The
/// steps of the walks stay linear in `d`, and the units, the steps, and the copies equal those
/// of the chain of indices.
#[test]
fn w7b_a_field_chain_with_a_call_in_each_key_holds_the_root_once() {
    let zero = (
        "fn zero(mut ys: [Int; 2]) -> Int { ys[0] = 7; return 0; }\n",
        "zero(m.2)",
    );
    let (small, large) = (chain_run(32, true, zero, 50), chain_run(64, true, zero, 51));
    let (index_small, index_large) = (
        chain_run(32, false, zero, 52),
        chain_run(64, false, zero, 53),
    );
    let (a, b) = (small.counts.stepped, large.counts.stepped);
    assert!(a > 0 && b <= 2 * a + 16, "the steps {a} at d and {b} at 2d");
    assert!(b <= 16 * large.used, "{b} steps for {} units", large.used);
    assert_eq!(a, index_small.counts.stepped);
    assert_eq!(b, index_large.counts.stepped);
    assert_eq!(large.counts.copies, index_large.counts.copies);
    assert_eq!(large.used, index_large.used);
}

/// W7b. A chain of `d` steps `@field(..., one())` over a hardware aggregate root, where the call
/// leaves the root alone. The whole chain is one segment of a read, so the walk takes the path
/// from the root once. A step that ends its segment walks the path again, and the steps then
/// grow with `d` times `d`.
#[test]
fn w7b_a_field_chain_with_a_call_that_leaves_the_root_walks_its_path_once() {
    let one = ("fn one() -> Int { return 0; }\n", "one()");
    let (small, large) = (chain_run(32, true, one, 54), chain_run(64, true, one, 55));
    let (index_small, index_large) = (chain_run(32, false, one, 56), chain_run(64, false, one, 57));
    let (a, b) = (small.counts.stepped, large.counts.stepped);
    assert!(a > 0 && b <= 2 * a + 16, "the steps {a} at d and {b} at 2d");
    assert!(b <= 8 * large.used, "{b} steps for {} units", large.used);
    assert_eq!(a, index_small.counts.stepped);
    assert_eq!(b, index_large.counts.stepped);
}

/// The run of a read of `d` fields `a` of a zero record that nests `d` structs, once as
/// `@field(..., "a")` and once as `.a`.
fn record_chain_run(d: usize, named: bool, run_key: u64) -> Run {
    let mut src = "struct S0 {\n    a: UInt[8],\n}\n".to_owned();
    for i in 1..=d {
        writeln!(src, "struct S{i} {{\n    a: S{},\n}}", i - 1).unwrap();
    }
    let mut read = "p".to_owned();
    for _ in 0..=d {
        read = if named {
            format!("@field({read}, \"a\")")
        } else {
            format!("{read}.a")
        };
    }
    writeln!(
        src,
        "module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    let p = S{d}();\n    \
         let y = {read};\n    o := x;\n}}"
    )
    .unwrap();
    passing(KEY + run_key, 100_000, &src)
}

/// W7b. A chain of `d` steps `@field(..., "a")` over a record that nests `d` structs. The key of
/// a step pays its name at the step, and the look-up reads it after. The whole chain is one
/// segment of a read, so the steps equal those of the chain `.a`, and they stay linear in `d`.
#[test]
fn w7b_a_field_chain_of_names_walks_its_path_once() {
    let (small, large) = (
        record_chain_run(32, true, 60),
        record_chain_run(64, true, 61),
    );
    let (field_small, field_large) = (
        record_chain_run(32, false, 62),
        record_chain_run(64, false, 63),
    );
    let (a, b) = (small.counts.stepped, large.counts.stepped);
    assert!(b <= 2 * a + 16, "the steps {a} at d and {b} at 2d");
    assert_eq!(a, field_small.counts.stepped);
    assert_eq!(b, field_large.counts.stepped);
}
