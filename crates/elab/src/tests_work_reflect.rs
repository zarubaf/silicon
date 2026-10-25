// SPDX-License-Identifier: Apache-2.0
//! The work of `@typeInfo`, as the work bound of design section 5.5 states it for the Rust front
//! end (issue #380). Each family runs at a size `n` and at `2n`. The work is the sum of all
//! counters of the run, and the work of the queries is the work of the run less the work of the
//! same run without them. The tests count the steps of the walks and the bytes that they copy,
//! and not the time.

use crate::tests_work_handles::{Run, passing};
use std::fmt::Write;

/// The key of the first run of this file. It keeps the fuel of each run unique.
const KEY: u64 = 15000;

/// The work, the units, and the bytes of names that one more call costs: the run with `2n` calls
/// less the run with `n` calls, over `n`. The first use of a struct or an enum is in both.
fn per_call(more: &Run, fewer: &Run, n: u64) -> (u64, u64, u64) {
    (
        (more.counts.total() - fewer.counts.total()) / n,
        (more.used - fewer.used) / n,
        (more.counts.text_bytes - fewer.counts.text_bytes) / n,
    )
}

/// A type of the depth `d`: `d` tuples around `Bool`.
fn nest(d: usize) -> String {
    let mut t = "Bool".to_owned();
    for _ in 0..d {
        t = format!("({t}, Bool)");
    }
    t
}

/// The module `M` with `n` lets of `@typeInfo(ty)` after the declarations `decls`.
fn module(decls: &str, ty: &str, n: usize) -> String {
    let mut src = format!("{decls}module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n");
    for k in 0..n {
        writeln!(src, "    let t{k} = @typeInfo({ty});").unwrap();
    }
    src.push_str("    o := x;\n}\n");
    src
}

/// The run of a struct `S` with `f` fields of the type of the depth `d`, `n` times.
fn struct_run(f: usize, d: usize, n: usize, key: u64) -> Run {
    let mut decls = format!("type T = {};\nstruct S {{\n", nest(d));
    for k in 0..f {
        writeln!(decls, "    f{k}: T,").unwrap();
    }
    decls.push_str("}\n");
    passing(KEY + key, 1000, &module(&decls, "S", n))
}

/// W1. `@typeInfo` of a struct with `F` fields of the depth `d`, `n` times. The result reads the
/// fifth metadata number of each field type and never enters it, so the work is in `n * F` and
/// does not grow with `d`. A walk into each field type for its size gives `d` more for each field.
#[test]
fn w1_the_info_of_a_struct_walks_no_field_type() {
    let n = 4;
    let at = |f: usize, d: usize, key: u64| {
        per_call(
            &struct_run(f, d, 2 * n, key),
            &struct_run(f, d, n, key + 1),
            n as u64,
        )
    };
    let (shallow, deep) = (at(16, 8, 1), at(16, 64, 3));
    let (narrow, wide) = (at(16, 8, 5), at(32, 8, 7));
    assert_eq!(
        deep.0, shallow.0,
        "the work of a call at depth 8 and at depth 64"
    );
    assert!(
        wide.0 <= 2 * narrow.0,
        "{} at 16 fields, {} at 32",
        narrow.0,
        wide.0
    );
    assert!(
        deep.0 <= 24 * 16,
        "the work {} of a call for 16 fields",
        deep.0
    );
}

/// The run of an enum `E` with `v` variants of three payload types, `n` times.
fn enum_run(v: usize, n: usize, key: u64) -> Run {
    let mut decls = "enum E: UInt[8] {\n".to_owned();
    for k in 0..v {
        writeln!(
            decls,
            "    V{k}((Bool, Bool, Bool, Bool), UInt[4], (Bool, Bool)) = {k},"
        )
        .unwrap();
    }
    decls.push_str("}\n");
    passing(KEY + key, 1000, &module(&decls, "E", n))
}

/// W2. `@typeInfo` of an enum with `V` variants and `P` payload types, `n` times. The counts charge
/// before the walk visits the variants, and the payload types charge before the walk visits them.
/// The work of the call stays within half the units that it used, and it doubles when `V` doubles.
#[test]
fn w2_the_info_of_an_enum_pays_for_its_variants_and_payloads() {
    let n = 4;
    let at =
        |v: usize, key: u64| per_call(&enum_run(v, 2 * n, key), &enum_run(v, n, key + 1), n as u64);
    let (small, large) = (at(32, 10), at(64, 12));
    assert!(
        small.0 < large.0 && large.0 <= 2 * small.0 + 16,
        "the work {} at 32 variants and {} at 64",
        small.0,
        large.0
    );
    assert!(
        2 * small.0 <= small.1 && 2 * large.0 <= large.1,
        "{}/{} {}/{}",
        small.0,
        small.1,
        large.0,
        large.1
    );
}

/// The run of a read `m[k][k]...[k]` of depth `d` over a hardware aggregate root, where each key
/// `k` is `key`. The functions `fns` declare what `key` calls.
fn chain_run(d: usize, (fns, key): (&str, &str), run_key: u64) -> Run {
    let nest = format!("{}x{}", "[".repeat(d), "]".repeat(d));
    let read = format!("m.0{}", format!("[{key}]").repeat(d));
    let src = format!(
        "struct P {{\n    a: UInt[8],\n}}\n{fns}module M() {{\n    input x: UInt[8];\n    \
         output o: UInt[8];\n    let mut m = ({nest}, list(Int), [1, 2]);\n    let y = {read};\n    \
         o := y;\n}}\n"
    );
    passing(KEY + run_key, 100_000, &src)
}

/// W10. A key `@typeInfo(f()).length - 1` is an index with a call. The read holds its root once for
/// the whole chain, so the steps of the walks stay linear in the depth, and they equal those of the
/// chain with a plain call in each key. The checks before each key run, as for any index with a call.
#[test]
fn w10_a_key_with_a_call_in_a_typeinfo_argument_holds_the_root_once() {
    let info = (
        "fn f() -> Type { return P; }\n",
        "@typeInfo(f()).length - 1",
    );
    let plain = ("fn g() -> P { return P(0); }\n", "g().a");
    let (small, large) = (chain_run(32, info, 20), chain_run(64, info, 21));
    let (plain_small, plain_large) = (chain_run(32, plain, 22), chain_run(64, plain, 23));
    let (a, b) = (small.counts.stepped, large.counts.stepped);
    assert!(a > 0 && b <= 2 * a + 16, "the steps {a} at d and {b} at 2d");
    assert_eq!(a, plain_small.counts.stepped);
    assert_eq!(b, plain_large.counts.stepped);
    assert_eq!(large.counts.copies, plain_large.counts.copies);
    assert_eq!(large.counts.logged, plain_large.counts.logged);
    // The scan marks the key as an index with a call, so the steps before it pass their checks.
    assert!(
        large.counts.checked >= 64,
        "{} checks",
        large.counts.checked
    );
    assert_eq!(large.counts.checked, plain_large.counts.checked);
}

/// The run of a struct `S` with `f` fields whose names have `len` characters, `n` times.
fn names_run(f: usize, len: usize, n: usize, key: u64) -> Run {
    let mut decls = "struct S {\n".to_owned();
    for k in 0..f {
        writeln!(decls, "    {}{k}: Bool,", "a".repeat(len)).unwrap();
    }
    decls.push_str("}\n");
    passing(KEY + key, 1000, &module(&decls, "S", n))
}

/// W11. The result of `@typeInfo` of a struct with `F` fields of names with `L` characters copies
/// `F * L` bytes of names. The size of the result charges each name by its length before any name
/// is copied, so the bytes stay within a constant times the units of the call, at each `L`.
#[test]
fn w11_the_names_of_the_result_are_paid_by_their_length() {
    let n = 4;
    let at = |len: usize, key: u64| {
        per_call(
            &names_run(16, len, 2 * n, key),
            &names_run(16, len, n, key + 1),
            n as u64,
        )
    };
    let (short, long) = (at(8, 30), at(256, 32));
    for (bytes, units) in [(short.2, short.1), (long.2, long.1)] {
        assert!(
            bytes > 0 && bytes <= units,
            "{bytes} bytes for {units} units"
        );
    }
    assert!(long.2 >= 16 * 256, "the names are copied: {} bytes", long.2);
    assert!(
        long.0 <= 4 * long.1,
        "the work {} for {} units",
        long.0,
        long.1
    );
}
