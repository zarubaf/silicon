// SPDX-License-Identifier: Apache-2.0
//! The work of the helpers that declare resources, as the work bound of design section 5.5 states
//! it for the Rust front end (issue #279). Each family runs at a size `n` and at `2n`. The work is
//! the sum of all counters of the run. A doubled size must give at most twice the work, and the
//! work must stay within a constant times the fuel that the run used. The tests count the steps
//! of the walks and not the time.

use crate::tests_work_handles::{doubles, passing, run};
use std::fmt::Write;

/// The key of the first run of this file. It keeps the fuel of each run unique.
const KEY: u64 = 5000;

/// W2. One helper declares and binds `n` wires in a `comptime for`. The path of each wire comes
/// from the frame of the loop in O(1), so the work is linear.
#[test]
fn w2_a_helper_that_declares_wires_in_a_loop_is_linear() {
    let at = |n: usize, key: u64| {
        let src = format!(
            "fn fill(x: UInt[8]) -> UInt[8] {{\n    let mut v = x;\n    comptime for i in 0..{n} {{\n        \
             wire w: UInt[8];\n        w := v;\n        v = read(w);\n    }}\n    return v;\n}}\n\
             module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    o := fill(x);\n}}\n"
        );
        passing(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 1), at(128, 2));
    doubles(&n, &twice);
    assert!(twice.counts.total() <= 40 * twice.used);
}

/// W3. `n` calls of a helper that makes `instance u = C(8)` and binds `u.a`. The instantiation
/// is one `InstantiationId`, so the child body runs once, and the work follows the calls.
#[test]
fn w3_calls_of_a_helper_that_makes_one_child_run_the_body_once() {
    let at = |n: usize, key: u64| {
        let mut src = "module C(comptime K: UInt[8]) domains() {\n    input a: UInt[8];\n    \
                       output q: UInt[8];\n    q := a +% K;\n}\n\
                       fn spawn(x: UInt[8]) -> UInt[8] {\n    instance u = C(8);\n    u.a := x;\n    \
                       return u.q;\n}\n\
                       module M() domains() {\n    input x: UInt[8];\n    output o: UInt[8];\n"
            .to_owned();
        for k in 0..n {
            writeln!(src, "    let t{k} = spawn(x);").unwrap();
        }
        writeln!(src, "    o := t{};\n}}", n - 1).unwrap();
        passing(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 3), at(128, 4));
    // The calls pay a name and a version lookup, so the work is `O(n log n)`.
    let (a, b) = (n.counts.total(), twice.counts.total());
    assert!(a < b && b <= 5 * a / 2, "the work {a} at n and {b} at 2n");
    assert!(twice.counts.total() <= 40 * twice.used);
}

/// W4. `k` waiting reads of a local array around a call that makes a new child. The save and the
/// restore of the instantiation swap the tables of the caller. The work of the call does not grow
/// with the reads that wait, so the work with the child minus the work without it stays constant.
#[test]
fn w4_waiting_reads_around_a_call_that_makes_a_child_cost_the_call_once() {
    let at = |k: usize, child: bool, key: u64| {
        let decl = if child {
            "instance u = C(8);\n    u.a := x;"
        } else {
            "wire w: UInt[8];\n    w := x;"
        };
        let out = if child { "u.q" } else { "read(w)" };
        let mut sum = "mk(x)".to_owned();
        for j in (0..k).rev() {
            sum = format!("a[{}] +% ({sum})", j % 4);
        }
        let src = format!(
            "module C(comptime K: UInt[8]) domains() {{\n    input a: UInt[8];\n    \
             output q: UInt[8];\n    q := a +% K;\n}}\n\
             fn mk(x: UInt[8]) -> UInt[8] {{\n    {decl}\n    return {out};\n}}\n\
             module M() domains() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             let a = [x, x, x, x];\n    o := {sum};\n}}\n"
        );
        passing(KEY + key, 1000, &src).counts.total()
    };
    let delta = |k: usize, key: u64| at(k, true, key) - at(k, false, key + 1);
    let (small, large) = (delta(16, 10), delta(64, 12));
    assert_eq!(
        small, large,
        "the call of the helper follows the waiting reads"
    );
}

/// W5. `k` calls of a helper that declares a wire and binds it twice. The first `S018` waits for
/// the end of the body, the records are O(1) each, and the text renders once.
#[test]
fn w5_second_bindings_of_helper_resources_cost_one_record_each() {
    let at = |k: usize, key: u64| {
        let mut src =
            "fn mk(x: UInt[8]) -> UInt[8] {\n    wire w: UInt[8];\n    w := x;\n    w := x;\n    \
                       return read(w);\n}\n\
                       module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n"
                .to_owned();
        for j in 0..k {
            writeln!(src, "    let t{j} = mk(x);").unwrap();
        }
        writeln!(src, "    o := t{};\n}}", k - 1).unwrap();
        run(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 20), at(128, 21));
    let message = "`w` has a second binding; the first binding is at 3:5, and the declaration is at \
                   2:5; remove one of the two bindings";
    for r in [&n, &twice] {
        assert_eq!(r.error, Some(("S018".to_owned(), message.to_owned())));
    }
    doubles(&n, &twice);
    let bytes = |r: &crate::tests_work_handles::Run| r.counts.text_bytes;
    assert_eq!(bytes(&twice), bytes(&n), "the text renders once");
    assert!(bytes(&n) > 0);
}

/// W7. `k` calls of a helper with `read_port` on a `Mem` formal of one memory. Each second call
/// records in O(1), and the text renders once.
#[test]
fn w7_second_port_calls_through_a_helper_cost_one_record_each() {
    let at = |k: usize, key: u64| {
        let mut src = "fn get(m: Mem[UInt[8], 4], a: UInt[2], e: Bool) -> UInt[8] {\n    \
                       let r = m.read_port(a, e);\n    return r.data;\n}\n\
                       module M() {\n    input a: UInt[2];\n    input e: Bool;\n    \
                       input d: UInt[8];\n    output o: UInt[8];\n    mem m: [UInt[8]; 4];\n    \
                       write_port(m, a, d, e);\n"
            .to_owned();
        for j in 0..k {
            writeln!(src, "    let t{j} = get(m, a, e);").unwrap();
        }
        writeln!(src, "    o := t{};\n}}", k - 1).unwrap();
        run(KEY + key, 1000, &src)
    };
    let (n, twice) = (at(64, 30), at(128, 31));
    let message = "the memory `m` has a second `read_port`, because the call in `get` runs again \
                   for it; run the call once for each memory, for example with one call of `get` \
                   for each";
    for r in [&n, &twice] {
        assert_eq!(r.error, Some(("S018".to_owned(), message.to_owned())));
    }
    assert_eq!((n.counts.seconds, twice.counts.seconds), (63, 127));
    doubles(&n, &twice);
    assert_eq!(twice.counts.text_bytes, n.counts.text_bytes);
    assert!(n.counts.text_bytes > 0);
}

/// R3. `n` calls of a function with a name of 2000 characters. The mode and the guard record the
/// item index of the function, so a call copies no name and the work follows the calls and the
/// source. `comptime fn` sets the mode, and `fn` under a hardware arm sets the record of the guard.
#[test]
fn r3_a_call_copies_no_name_into_the_mode_or_the_guard() {
    let name = "c".repeat(2000);
    let comptime = |n: usize, key: u64| {
        let mut src = format!(
            "comptime fn {name}() -> Nat {{ return 1; }}\n\
             module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    let f = {name};\n"
        );
        for k in 0..n {
            writeln!(src, "    let a{k} = f();").unwrap();
        }
        src.push_str("    o := x;\n}\n");
        (passing(KEY + key, 1000, &src), src.len() as u64)
    };
    let guarded = |n: usize, key: u64| {
        let mut src = format!(
            "fn {name}(x: UInt[8]) -> UInt[8] {{ return x; }}\n\
             module M() {{\n    input c: Bool;\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             let f = {name};\n"
        );
        for k in 0..n {
            writeln!(src, "    let a{k} = if (c) {{ f(x) }} else {{ 0 }};").unwrap();
        }
        src.push_str("    o := x;\n}\n");
        (passing(KEY + key, 1000, &src), src.len() as u64)
    };
    for k in 0..2u64 {
        let at = |n: usize, key: u64| {
            if k == 0 {
                comptime(n, key)
            } else {
                guarded(n, key)
            }
        };
        let key = 40 + 4 * k;
        let ((n, sn), (twice, s2)) = (at(64, key), at(128, key + 1));
        let (a, b) = (n.counts.total(), twice.counts.total());
        // The work is `O(n + s)`: the source holds the name twice, and the calls are linear.
        assert!(b <= 2 * a, "family {k}: the work {a} at n and {b} at 2n");
        assert!(a <= 60 * 64 + 4 * sn, "family {k}: the work {a}, s = {sn}");
        assert!(b <= 60 * 128 + 4 * s2, "family {k}: the work {b}, s = {s2}");
    }
}

/// R4. A helper at the recursion depth `l` declares `n` registers in a `comptime for`. No
/// register has a binding, so the run ends with `S018` before the lowering. The path of a frame
/// is one node of the path arena for each level, and the work is linear in `n + l`.
#[test]
fn r4_registers_of_a_deep_helper_cost_the_registers_and_the_depth() {
    let at = |n: usize, l: usize, key: u64| {
        let src = format!(
            "fn deep(comptime d: Nat) -> Nat {{\n    comptime if (d > 0) {{\n        \
             return deep(d - 1);\n    }}\n    comptime for i in 0..{n} {{\n        \
             reg r: UInt[8] = 0;\n    }}\n    return 0;\n}}\n\
             module M() {{\n    output o: UInt[8];\n    let z = deep({l});\n    o := 0;\n}}\n"
        );
        let r = run(KEY + key, 100_000, &src);
        let code = r.error.as_ref().map(|e| e.0.as_str());
        assert_eq!(code, Some("S018"), "{:?}", r.error);
        r.counts.total()
    };
    let (small, large) = (at(64, 64, 60), at(128, 128, 61));
    assert!(small < large && large <= 2 * small, "{small} and {large}");
    // The depth alone and the registers alone: no product of the two.
    let (deep, wide) = (at(1, 256, 62), at(256, 1, 63));
    let both = at(256, 256, 64);
    assert!(both <= deep + wide, "the work {both} follows n * l");
    assert!(both <= 120 * (256 + 256), "the work {both}");
}
