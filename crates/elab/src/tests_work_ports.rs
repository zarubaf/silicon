// SPDX-License-Identifier: Apache-2.0
//! The work of `@ports`, as the work bound of design section 5.5 states it for the Rust front end
//! (issue #346). Each family runs at a size `n` and at `2n`. The work is the sum of all counters
//! of the run, and the work of the calls is the work of the run less the work of the same run
//! without them. The tests count the steps of the walks and the bytes that they copy or compare,
//! and not the time. An escape that no counter sees is no escape: each test names the one that
//! it catches.

use crate::counters::Counts;
use crate::tests_work_handles::{Run, passing, run, run_with};
use std::fmt::Write;

/// The key of the first run of this file. It keeps the fuel of each run unique.
const KEY: u64 = 17000;

/// The bytes of the name of the default domain, `clock`. Each record of `@ports` copies it.
const DOMAIN: u64 = 5;

/// The work, the units, and the bytes of text that one more call costs: the run with `2n` calls
/// less the run with `n` calls, over `n`. The instantiation of the child is in both.
fn per_call(more: &Run, fewer: &Run, n: u64) -> (u64, u64, u64) {
    (
        (more.counts.total() - fewer.counts.total()) / n,
        (more.used - fewer.used) / n,
        (more.counts.text_bytes - fewer.counts.text_bytes) / n,
    )
}

/// A child `C` whose ports are the lines of `ports`, and a module `M` that binds each input of
/// `u` with `binds` and then runs `n` copies of `call`, with the lines `before` first.
fn module(ports: &str, (before, binds): (&str, &str), (n, call): (usize, &str)) -> String {
    let mut src = format!("module C() {{\n{ports}}}\n");
    src.push_str("module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n");
    src.push_str("    instance u = C();\n");
    src.push_str(binds);
    src.push_str(before);
    for k in 0..n {
        writeln!(src, "    {}", call.replace("{k}", &k.to_string())).unwrap();
    }
    src.push_str("    o := x;\n}\n");
    src
}

/// The module with the child `C` of `ports` and `M` with `binds` and one `@ports(u)` as its last
/// statement, so the charges of the call are the last charges of the run. Each bind uses `0`.
fn last_call(ports: &str, binds: &str) -> String {
    format!(
        "module C() {{\n{ports}}}\nmodule M() {{\n    instance u = C();\n{binds}    let ps = @ports(u);\n}}\n"
    )
}

/// The first fuel at which the run of `src` passes, and the run with the fuel one below it. The
/// call is the last charge, so that run fails at the size charge of the call.
fn at_the_size_charge(src: &str) -> (Run, Run) {
    let ok = first_fuel(src, |r| r.error.is_none());
    (run_with(ok, 1000, src), run_with(ok - 1, 1000, src))
}

/// The ports of a child with `p` scalar inputs `p0`, `p1`, ..., each bound in `M`.
fn scalar_ports(p: usize) -> (String, String) {
    let mut ports = String::new();
    let mut binds = String::new();
    for k in 0..p {
        writeln!(ports, "    input p{k}: UInt[8];").unwrap();
        writeln!(binds, "    u.p{k} := x;").unwrap();
    }
    (ports, binds)
}

/// The total length of the names `p0` to `p{p-1}`.
fn name_bytes(p: usize) -> u64 {
    (0..p).map(|k| 1 + k.to_string().len() as u64).sum()
}

/// W1. A child with `P` ports of distinct names, and `n` calls of `@ports(u)`. The interface sorted
/// its ports once, when the instantiation ended, so a call compares no name: the text of a call
/// is the bytes that its records copy, `P` names and `P` domains. A sort for each call compares
/// the names of different symbols and adds their bytes.
#[test]
fn w1_a_call_compares_no_name_after_the_instantiation() {
    let p = 64;
    let (ports, binds) = scalar_ports(p);
    let at = |n: usize, key: u64| {
        let src = module(&ports, ("", &binds), (n, "let ps{k} = @ports(u);"));
        passing(KEY + key, 1000, &src)
    };
    let (few, many) = (at(4, 1), at(8, 2));
    let (work, units, bytes) = per_call(&many, &few, 4);
    assert_eq!(
        bytes,
        name_bytes(p) + DOMAIN * p as u64,
        "the bytes of a call are its copies"
    );
    assert!(
        work <= bytes + 8 * p as u64,
        "the work {work} of a call for {p} ports"
    );
    assert!(work <= 8 * units, "{work} work for {units} units");
}

/// W2. A child with `P` entries of one family, whose name has `L` bytes. The entries share one
/// symbol, so the sort of the interface compares the keys and no text. A compare of the text when
/// the symbols are equal makes `L` bytes for each compare. The run with no call shows the sort
/// alone, and the run with a call copies `P * (L + 5)` bytes and compares nothing more.
#[test]
fn w2_the_entries_of_one_family_compare_no_text() {
    let (p, len) = (64_u64, 256);
    let basename = "a".repeat(len);
    let mut ports = String::new();
    let mut binds = String::new();
    for k in 0..p {
        writeln!(ports, "    input {basename}[{k}]: UInt[8];").unwrap();
        writeln!(binds, "    u.{basename}[{k}] := x;").unwrap();
    }
    let none = passing(KEY + 3, 1000, &module(&ports, ("", &binds), (0, "")));
    let one = passing(
        KEY + 4,
        1000,
        &module(&ports, ("", &binds), (1, "let ps = @ports(u);")),
    );
    assert_eq!(none.counts.text_bytes, 0, "the sort compares no text");
    assert_eq!(
        one.counts.text_bytes,
        p * (len as u64 + DOMAIN),
        "the call copies and compares nothing more"
    );
}

/// A type of the depth `d`: `d` arrays of one element around `Bool`.
fn nest(d: usize) -> String {
    format!("{}Bool{}", "[".repeat(d), "; 1]".repeat(d))
}

/// W3. A child with an output of a type of the depth `d`, and `n` calls. A call reads the stored
/// depth and size of the port type, so the work of a call does not grow with `d`. A walk of the
/// type for its depth or its size adds `d` steps to each call, and the work at `2d` is then more
/// than the work at `d`.
#[test]
fn w3_a_port_type_is_never_walked() {
    let at = |d: usize, n: usize, key: u64| {
        let ports = "    output q: T;\n    q := T();\n";
        let src = format!("type T = {};\n", nest(d))
            + &module(ports, ("", ""), (n, "let ps{k} = @ports(u);"));
        passing(KEY + key, 10_000, &src)
    };
    let work = |d: usize, key: u64| per_call(&at(d, 8, key), &at(d, 4, key + 1), 4).0;
    let (shallow, deep) = (work(16, 10), work(32, 12));
    assert_eq!(
        deep, shallow,
        "the work of a call at depth 16 and at depth 32"
    );
    assert!(shallow <= 64, "the work {shallow} of a call");
}

/// W4. A child with `P` ports whose names have `L` bytes, and one call as the last statement. The
/// size charge pays for the names before the build copies one. The run whose fuel ends at that
/// charge copied nothing and built no record. The whole run copies at most the bytes that it
/// charged.
#[test]
fn w4_no_name_is_copied_before_its_charge() {
    let (p, len) = (16, 512);
    let mut ports = String::new();
    let mut binds = String::new();
    for k in 0..p {
        writeln!(ports, "    input {}{k}: UInt[8];", "a".repeat(len)).unwrap();
        writeln!(binds, "    u.{}{k} := 0;", "a".repeat(len)).unwrap();
    }
    let src = last_call(&ports, &binds);
    let base = passing(KEY + 21, 1000, &src.replace("let ps = @ports(u);", ""));
    let (whole, below) = at_the_size_charge(&src);
    assert_eq!(whole.error, None);
    let (bytes, units) = (
        whole.counts.text_bytes - base.counts.text_bytes,
        whole.used - base.used,
    );
    assert!(bytes >= (p * len) as u64, "the names are copied: {bytes}");
    assert!(bytes <= units, "{bytes} bytes for {units} units");
    assert_eq!(below.error.as_ref().map(|e| e.0.as_str()), Some("S015"));
    assert_eq!(
        below.counts.text_bytes, base.counts.text_bytes,
        "the bytes copied before the charge"
    );
}

/// The first fuel at which `done` holds on the counts of a run of `src`. A run with more fuel
/// does more, so the test holds for more fuel when it holds for less.
fn first_fuel(src: &str, done: impl Fn(&Run) -> bool) -> u64 {
    let (mut lo, mut hi) = (0, 1_000_000);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if done(&run_with(mid, 1000, src)) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

/// The module with a handle `u` in an array nested `d` levels deep, and one call
/// `@ports(a[0]...[0])` when `call` holds.
fn nest_run(d: usize, call: bool, key: u64) -> Run {
    let path = "[0]".repeat(d);
    let line = if call {
        format!("let ps = @ports(a{path});")
    } else {
        String::new()
    };
    let src = format!(
        "module C() domains() {{\n    output q: Bool;\n    q := true;\n}}\n\
         module M() domains() {{\n    instance u = C();\n    let a = {}u{};\n    {line}\n}}\n",
        "[".repeat(d),
        "]".repeat(d)
    );
    passing(KEY + key, 100_000, &src)
}

/// W5. A call on the path `a[0]...[0]` of depth `d` into a nest of handles. The walk goes once
/// from the root, so the steps stay linear in `d`. A walk from the root for each step gives `d * d`.
#[test]
fn w5_a_deep_operand_is_walked_once() {
    let steps = |d: usize, key: u64| {
        let (with, without) = (nest_run(d, true, key), nest_run(d, false, key + 1));
        with.counts.stepped - without.counts.stepped
    };
    let (a, b) = (steps(32, 30), steps(64, 32));
    assert!(a > 0 && b <= 2 * a + 8, "the steps {a} at d and {b} at 2d");
    assert!(b <= 8 * 64, "the steps {b} at depth 64");
}

/// The run of a local `us` that holds a list of two handles and a static array of `size` numbers,
/// and `@ports(us.0[f()])` when `call` holds. The function `f` is a call in the key. A copy of
/// the root copies the numbers.
fn hold_run(size: usize, call: bool, key: u64) -> Run {
    let elems = vec!["0"; size].join(", ");
    let line = if call {
        "let ps = @ports(us.0[f()]);"
    } else {
        ""
    };
    let src = format!(
        "module C() domains() {{\n    output q: Bool;\n    q := true;\n}}\n\
         fn f() -> Nat {{\n    return 0;\n}}\n\
         module M() domains() {{\n    instance u = C();\n    let us = ([u, u], [{elems}]);\n    {line}\n}}\n"
    );
    passing(KEY + key, 1000, &src)
}

/// The counters of the work that a copy of the list would add.
fn copied(c: &Counts) -> [u64; 4] {
    [c.copies, c.cloned, c.logged, c.nodes]
}

/// W6. `@ports(us.0[f()])` on a local that holds a static array of `S` numbers, with a call in the
/// key. The operand keeps the part in the store with no copy, so the call adds no copy of the
/// local, no entry to its log, and no work that grows with `S`. A copy of the local for the call
/// copies the `S` numbers.
#[test]
fn w6_an_index_with_a_call_holds_the_list_once() {
    let extra = |size: usize, key: u64| {
        let (with, without) = (hold_run(size, true, key), hold_run(size, false, key + 1));
        let moved: Vec<u64> = copied(&with.counts)
            .iter()
            .zip(copied(&without.counts))
            .map(|(a, b)| a - b)
            .collect();
        (with.counts.total() - without.counts.total(), moved)
    };
    let (small, large) = (extra(32, 40), extra(64, 42));
    assert_eq!(small.1, [0, 0, 0, 0], "the copies of the list at 32");
    assert_eq!(large.1, [0, 0, 0, 0], "the copies of the list at 64");
    assert_eq!(small.0, large.0, "the work at 32 and at 64 handles");
}

/// W7. `@ports(t)` of a static tuple of `S` elements is `S010`. The check reads the type of the
/// part and renders its cut text. It builds no type for the tuple, so the walk of the type visits
/// no node and `queried` stays constant, and the text stays within the limit of a message.
#[test]
fn w7_the_kind_check_of_a_static_tuple_builds_no_type() {
    let at = |size: usize, key: u64| {
        let elems = vec!["1"; size].join(", ");
        let src = format!(
            "module C() domains() {{\n    output q: Bool;\n    q := true;\n}}\n\
             module M() domains() {{\n    instance u = C();\n    let t = ({elems});\n    \
             let ps = @ports(t);\n}}\n"
        );
        run(KEY + key, 1000, &src)
    };
    for (size, key) in [(2000, 50), (4000, 51)] {
        let r = at(size, key);
        assert_eq!(r.error.as_ref().map(|e| e.0.as_str()), Some("S010"));
        assert_eq!(r.counts.type_nodes, 0, "the type nodes of {size} elements");
        assert!(r.counts.queried <= 4, "{} steps", r.counts.queried);
        assert!(r.counts.text_bytes <= 1024, "{} bytes", r.counts.text_bytes);
        assert!(r.counts.texted <= 1024, "{} pieces", r.counts.texted);
        let message = r.error.map(|e| e.1).unwrap_or_default();
        assert!(
            message.len() <= 1024 + 256,
            "{} bytes of message",
            message.len()
        );
    }
}

/// The run of `K` registers in a list `rs`, and `@ports(rs)` when `call` holds, else a failed
/// `static_assert`. The line is the last, and it fails.
fn registers_run(k: usize, call: bool, key: u64) -> Run {
    let mut regs = String::new();
    for i in 0..k {
        writeln!(regs, "    reg r{i}: UInt[4] = 0;\n    r{i} := x;").unwrap();
    }
    let names = (0..k)
        .map(|i| format!("r{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let line = if call {
        "let ps = @ports(rs);"
    } else {
        "static_assert(false, \"stop\");"
    };
    let src = format!(
        "module C() domains() {{\n    output q: Bool;\n    q := true;\n}}\n\
         module M() {{\n    input x: UInt[4];\n    instance u = C();\n{regs}    \
         let rs = [{names}];\n    {line}\n}}\n"
    );
    run(KEY + key, 1000, &src)
}

/// W8. `@ports(rs)` of a list of `K` registers is `S010`. The check reads the handle, never a
/// register, and it copies and builds nothing: the call adds no node, no read, no copy, and no
/// work that grows with `K`, against the same module that stops at a failed `static_assert` there.
/// The message renders the type of the list in three type nodes, at each `K`.
#[test]
fn w8_the_kind_check_of_registers_in_a_container_reads_nothing() {
    let extra = |k: usize, key: u64| {
        let (with, without) = (
            registers_run(k, true, key),
            registers_run(k, false, key + 1),
        );
        assert_eq!(with.error.as_ref().map(|e| e.0.as_str()), Some("S010"));
        assert_eq!(without.error.as_ref().map(|e| e.0.as_str()), Some("S014"));
        let c = (with.counts, without.counts);
        assert_eq!(
            [c.0.nodes, c.0.read, c.0.cloned, c.0.copies],
            [c.1.nodes, c.1.read, c.1.cloned, c.1.copies],
            "the work of the kind check"
        );
        assert_eq!(c.0.type_nodes, 3, "the type nodes of the message");
        c.0.total() - c.1.total()
    };
    let (small, large) = (extra(16, 60), extra(32, 62));
    assert_eq!(small, large, "the extra work at 16 and at 32 registers");
}

/// W9. A child with `P` ports, and one call as the last statement. The build visits one record
/// for each port, and the run whose fuel is one below the size charge visits none: the depth
/// check, the count, and the size charge come before the first record.
#[test]
fn w9_the_build_follows_the_size_charge() {
    let p = 32;
    let (ports, binds) = scalar_ports(p);
    let (whole, below) = at_the_size_charge(&last_call(&ports, &binds.replace(":= x", ":= 0")));
    assert_eq!(whole.error, None);
    assert_eq!(whole.counts.reflected, p as u64, "one record for each port");
    assert_eq!(below.error.as_ref().map(|e| e.0.as_str()), Some("S015"));
    assert_eq!(below.counts.reflected, 0, "the build before its charge");
}
