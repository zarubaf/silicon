// SPDX-License-Identifier: Apache-2.0
//! The work of `@typeInfo`, as the work bound of design section 5.5 states it for the Rust front
//! end (issue #380). Each family runs at a size `n` and at `2n`. The work is the sum of all
//! counters of the run, and the work of the queries is the work of the run less the work of the
//! same run without them. The tests count the steps of the walks and the bytes that they copy,
//! and not the time.

use crate::tests_work_handles::{Run, passing, run, run_with};
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

/// The first fuel in `lo..hi` for which `done` holds on the counts of the run. The test `done`
/// holds for more fuel when it holds for less, because a run with more fuel does more.
fn first_fuel(src: &str, (mut lo, mut hi): (u64, u64), done: impl Fn(&Run) -> bool) -> u64 {
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

/// The module `M` with `n` lets of `@typeInfo(E)` for an enum of `v` variants, each with `p`
/// payload types.
fn charge_module(v: usize, p: usize, n: usize) -> String {
    let payload = if p == 0 {
        String::new()
    } else {
        format!("({})", vec!["Bool"; p].join(", "))
    };
    let mut decls = "enum E: UInt[8] {\n".to_owned();
    for k in 0..v {
        writeln!(decls, "    V{k}{payload} = {k},").unwrap();
    }
    decls.push_str("}\n");
    module(&decls, "E", n)
}

/// W2, the order of the charges. The call charges the counts, then the payload counts, and only
/// then the size, before the shape visits a part and before the build copies a name. The fuel
/// that ends at the size charge leaves the shape done and the build undone. The fuel that ends
/// before the shape leaves both undone. The payload charge shows in the fuel that the shape
/// needs: an enum of `P` more payload types needs `P` more fuel before its shape starts.
#[test]
fn w2_the_charges_of_an_enum_come_before_the_shape_and_the_build() {
    let (v, p) = (8, 3);
    let heavy = (charge_module(v, p, 1), charge_module(v, p, 2));
    let light = (charge_module(v, 0, 1), charge_module(v, 0, 2));
    let ceiling = 100_000;
    let whole = run_with(ceiling, 1000, &heavy.0);
    assert_eq!(whole.error, None);
    let shaped = whole.counts.reflected;
    let size_fuel = first_fuel(&heavy.0, (0, ceiling), |r| r.counts.text_bytes > 0);
    let shape_fuel = first_fuel(&heavy.0, (0, ceiling), |r| r.counts.reflected > 0);
    let before_shape = run_with(shape_fuel - 1, 1000, &heavy.0);
    assert!(before_shape.error.is_some());
    assert_eq!(
        (
            before_shape.counts.reflected,
            before_shape.counts.text_bytes
        ),
        (0, 0)
    );
    let at_size = run_with(size_fuel - 1, 1000, &heavy.0);
    assert!(at_size.error.is_some());
    assert_eq!(
        (at_size.counts.reflected, at_size.counts.text_bytes),
        ((v + v * p) as u64, 0),
        "the shape visits the variants and the payloads, and the build copies no name"
    );
    assert_eq!(
        shaped,
        2 * v as u64 + (v * p) as u64,
        "the build visits the variants"
    );
    // The second call starts after the first, so the fuel before its shape less the fuel of
    // the whole run with one call holds the charges of the second call and nothing of the enum.
    let before = |src: &(String, String), floor: u64| {
        let one = run_with(ceiling, 1000, &src.0);
        let shape = first_fuel(&src.1, (0, ceiling), |r| r.counts.reflected > floor);
        shape - one.used
    };
    let (with, without) = (before(&heavy, shaped), before(&light, 2 * v as u64));
    assert_eq!(with - without, (v * p) as u64, "the payload charge");
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

/// W10. A key `@typeInfo(f()).length - 1` is an index with a call. The read holds its root once
/// for the whole chain, so the steps of the walks stay linear in the depth, and they equal those
/// of the chain with a plain call in each key. The checks before each key run, as for any index
/// with a call.
#[test]
fn w10_a_key_with_a_call_in_a_typeinfo_argument_holds_the_root_once() {
    for (k, key) in [
        "@typeInfo(f()).length - 1",
        "len(@typeInfo(f()).fields) - 1",
    ]
    .into_iter()
    .enumerate()
    {
        let k = 4 * k as u64;
        let info = ("fn f() -> Type { return P; }\n", key);
        let plain = ("fn g() -> P { return P(0); }\n", "g().a");
        let (small, large) = (chain_run(32, info, 20 + k), chain_run(64, info, 21 + k));
        let (plain_small, plain_large) =
            (chain_run(32, plain, 22 + k), chain_run(64, plain, 23 + k));
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

/// The module `M` with `n` lets of `@Struct(fs)` after the declarations `decls`.
fn struct_module(decls: &str, fs: &str, n: usize) -> String {
    let mut src = format!("{decls}module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n");
    for k in 0..n {
        writeln!(src, "    let t{k} = @Struct({fs});").unwrap();
    }
    src.push_str("    o := x;\n}\n");
    src
}

/// The declarations of a constant `FS` with `f` fields named `n0`, `n1`, ... of the type `ty`.
fn fields_decls(f: usize, ty: &str) -> String {
    named_decls(f, "n", ty)
}

/// The declarations of a constant `FS` with `f` fields. The name of the field `i` is `prefix` and
/// the number `i`.
fn named_decls(f: usize, prefix: &str, ty: &str) -> String {
    format!(
        "comptime fn fields(comptime f: Nat) -> List[FieldInfo] {{\n    \
         let mut l = list(FieldInfo);\n    \
         comptime for i in 0..f {{ l.push(FieldInfo(\"{prefix}\" + str(i), {ty})); }}\n    \
         return l;\n}}\nconst FS: List[FieldInfo] = fields({f});\n"
    )
}

/// The run of `n` calls of `@Struct` with `f` fields.
fn fields_run(f: usize, n: usize, key: u64) -> Run {
    passing(
        KEY + key,
        1000,
        &struct_module(&fields_decls(f, "Bool"), "FS", n),
    )
}

/// W3. `@Struct` with `F` field names, `n` times. Each call inserts the `F` symbols into the
/// member map of the new type, so a call takes `O(F log F)` compares of two symbols, and a map
/// that compares each earlier symbol takes `F` times `F`. The count is that of the compares in the
/// map, not of its calls.
#[test]
fn w3_the_member_map_of_a_struct_takes_log_compares() {
    let n = 4;
    let at = |f: usize, key: u64| {
        let (more, fewer) = (fields_run(f, 2 * n, key), fields_run(f, n, key + 1));
        (more.counts.mapped - fewer.counts.mapped) / n as u64
    };
    let (small, large) = (at(128, 60), at(256, 62));
    let bound = |f: u64| 4 * f * u64::from(f.ilog2());
    assert!(small > 0, "the map compared nothing");
    assert!(small <= bound(128), "{small} compares for 128 names");
    assert!(large <= bound(256), "{large} compares for 256 names");
    assert!(
        large <= 3 * small,
        "{small} compares at F and {large} at 2F"
    );
}

/// W4. A name of 2^20 characters that breaks the name rule at its last character. The name
/// charges its size first, and the count of its characters for that charge is the first scan. The
/// rule scans the name once more, and the error text names at most 64 characters of it, so no text
/// copies the name. The fuel that ends at the charge scans the name only for the count.
#[test]
fn w4_a_long_invalid_name_is_scanned_twice_and_charged_between() {
    let len = 1usize << 20;
    let name = format!("{}-", "a".repeat(len));
    let src = struct_module("", &format!("[FieldInfo(\"{name}\", Bool)]"), 1);
    let whole = run_with(920_000_000 + KEY + 70, 1000, &src);
    let (code, text) = whole.error.clone().unwrap_or_default();
    assert_eq!(code, "S022", "{text}");
    assert!(
        text.contains(&format!("({} characters)", len + 1)),
        "{text}"
    );
    assert!(text.len() < 256, "{} bytes of text", text.len());
    assert_eq!(
        whole.counts.scanned,
        2 * (len as u64 + 1),
        "the name is scanned for its charge and once for the rule"
    );
    assert!(
        whole.counts.text_bytes <= 1024,
        "{} bytes of text for the error",
        whole.counts.text_bytes
    );
    // The charge of the name comes before the scan of the rule: the least fuel that reaches the
    // name rule pays the charge, and the fuel one unit below it scans the name for the count only.
    let named = |r: &Run| r.error.as_ref().is_some_and(|e| e.0 == "S022");
    let first = first_fuel(&src, (1, 100_000_000), named);
    let below = run_with(first - 1, 1000, &src);
    let (code, text) = below.error.unwrap_or_default();
    assert_eq!(code, "S015", "{text}");
    assert!(
        text.contains(&format!("cannot pay {} unit(s)", len + 2)),
        "the charge of the name: {text}"
    );
    assert_eq!(
        below.counts.scanned,
        len as u64 + 1,
        "a name scanned by the rule before its charge"
    );
}

/// The run of two chains of `d` nested generated record types: each type holds the one before it,
/// and the second chain repeats the first, so each of its types is a hit of the table.
fn nest_run(d: usize, key: u64) -> Run {
    let mut src = "module M() {\n    input x: UInt[8];\n    output o: UInt[8];\n".to_owned();
    for chain in ["t", "u"] {
        writeln!(src, "    let {chain}0 = @Struct([FieldInfo(\"a\", Bool)]);").unwrap();
        for k in 1..d {
            let before = k - 1;
            writeln!(
                src,
                "    let {chain}{k} = @Struct([FieldInfo(\"a\", {chain}{before})]);"
            )
            .unwrap();
        }
    }
    src.push_str("    o := x;\n}\n");
    passing(KEY + key, 1000, &src)
}

/// W5. `@Struct` over a chain of `d` nested generated record types, then again over the same
/// chain. The look-up of each type compares ids, so a level costs a constant number of steps, and
/// the work doubles with `d`. The copy of a type value pays the size of its term, which grows with
/// `d` times `d`, so the work leaves out the counter of the copies. A compare of the field types
/// themselves walks the nest at each level.
#[test]
fn w5_a_nest_of_generated_types_compares_ids() {
    let (small, large) = (nest_run(64, 72), nest_run(128, 73));
    let work = |r: &Run| r.counts.total() - r.counts.copies;
    let (a, b) = (work(&small), work(&large));
    assert!(a < b && b <= 2 * a + 64, "the work {a} at d and {b} at 2d");
    assert_eq!(small.counts.generated, 64);
    assert_eq!(large.counts.generated, 128);
    assert_eq!(small.counts.matched, 64, "one id compared for each hit");
    assert_eq!(large.counts.matched, 128);
}

/// W6. `n` equal calls of `@Struct` make one entry of the table, and each call after the first
/// compares the field list of the entry once. A call that does not look up the table makes `n`
/// entries.
#[test]
fn w6_equal_calls_share_one_entry() {
    let (fewer, more) = (fields_run(16, 1, 80), fields_run(16, 32, 81));
    assert_eq!(fewer.counts.generated, 1);
    assert_eq!(more.counts.generated, 1, "an entry for each call");
    assert_eq!(
        more.counts.matched,
        31 * 16,
        "one compare of F pairs for each hit"
    );
}

/// The run of a module `C` with a parameter `t: Type` and the instance of `C` with the generated
/// record type of `FS`.
fn argument_run(decls: &str, key: u64) -> Run {
    let src = format!(
        "{decls}module C(comptime t: Type) {{\n    output o: Bool;\n    o := true;\n}}\n\
         module M() {{\n    output o: Bool;\n    instance u = C(@Struct(FS));\n    o := u.o;\n}}\n"
    );
    passing(KEY + key, 1000, &src)
}

/// W8. A generated record type as the argument of a module has the digest form of its
/// serialization. The serialization writes each name and each field type once, so its bytes stay
/// within a constant times the units of the run, and they double with `F`.
#[test]
fn w8_the_serialization_of_a_module_argument_follows_its_charge() {
    let at = |f: usize, key: u64| argument_run(&fields_decls(f, "UInt[8]"), key);
    let (small, large) = (at(64, 90), at(128, 91));
    let (a, b) = (small.counts.serialized, large.counts.serialized);
    // A field writes its name in quotes, its type, and four more bytes: 17 bytes for `n12`.
    assert!(a > 0 && b <= 2 * a + 64, "{a} bytes at F and {b} at 2F");
    assert!(b <= 18 * 128, "{b} bytes for 128 fields");
    assert!(4 * b <= large.used, "{b} bytes for {} units", large.used);
}

/// W7. The text of a generated record type with `F` field names of 200 characters in an error. The
/// walk stops soon after the limit of the text, and each name is cut at 64 characters. So the
/// bytes of text stay within a constant times the limit at any `F`. A text that renders every
/// field and then cuts grows with `F` times the length of a name.
#[test]
fn w7_the_text_of_a_type_with_long_names_is_bounded() {
    let at = |f: usize, key: u64| {
        let decls = named_decls(f, &"a".repeat(200), "Bool");
        let src = format!(
            "{decls}module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    \
             let t = @Struct(FS);\n    let y: UInt[8] = t();\n    o := x;\n}}\n"
        );
        let r = run(KEY + key, 1000, &src);
        let (code, text) = r.error.clone().unwrap_or_default();
        assert_eq!(code, "S010", "{text}");
        assert!(text.contains("@Struct { aaaa"), "{text}");
        assert!(text.len() <= 2 * 1024 + 64, "{} bytes of text", text.len());
        r
    };
    let (few, many) = (at(16, 100), at(256, 101));
    for r in [&few, &many] {
        assert!(
            r.counts.text_bytes <= 2 * 1024,
            "{} bytes of text",
            r.counts.text_bytes
        );
    }
    assert!(
        many.counts.text_bytes <= few.counts.text_bytes + 256,
        "{} bytes at 16 fields, {} at 256",
        few.counts.text_bytes,
        many.counts.text_bytes
    );
}

/// The run of `k` generated record types of `f` fields that differ in the last name, then `n`
/// more calls of the first.
fn lookup_run(f: usize, (k, n): (usize, usize), key: u64) -> Run {
    let mut decls = String::new();
    for j in 0..k {
        let names: Vec<String> = (0..f)
            .map(|i| {
                let name = if i + 1 == f {
                    format!("z{j}")
                } else {
                    format!("n{i}")
                };
                format!("FieldInfo(\"{name}\", Bool)")
            })
            .collect();
        writeln!(
            decls,
            "const FS{j}: [FieldInfo; {f}] = [{}];",
            names.join(", ")
        )
        .unwrap();
    }
    let mut src = format!("{decls}module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n");
    for j in 0..k {
        writeln!(src, "    let t{j} = @Struct(FS{j});").unwrap();
    }
    for m in 0..n {
        writeln!(src, "    let u{m} = @Struct(FS0);").unwrap();
    }
    src.push_str("    o := x;\n}\n");
    passing(KEY + key, 1000, &src)
}

/// W12. The look-up of a generated record type compares its field list with the entries of its
/// fingerprint only. `K` types that differ in the last name of `F` fields make `K` misses with no
/// compare, and each call that repeats one makes one compare of `F` pairs. A compare with every
/// entry of the table costs `K` times `F` for a call.
#[test]
fn w12_the_lookup_compares_only_the_bucket_of_the_fingerprint() {
    let f = 32;
    let (k, n) = (24, 8);
    let r = lookup_run(f, (k, n), 110);
    assert_eq!(r.counts.generated, k as u64);
    assert_eq!(
        r.counts.matched,
        (n * f) as u64,
        "{} pairs for {n} hits of {f} pairs",
        r.counts.matched
    );
}

/// The run of a module with the chain `p.f...f` of `d + 1` steps over a static record that nests `d`
/// structs. `form` selects the use: the type of a `let` (`Type`), the expression `@TypeOf` of a
/// `let` (`Expr`), or none (`Base`).
fn place_form_run(d: usize, form: Form, run_key: u64) -> Run {
    let mut src = "struct S0 {\n    f: UInt[8],\n}\n".to_owned();
    for i in 1..=d {
        writeln!(src, "struct S{i} {{\n    f: S{},\n}}", i - 1).unwrap();
    }
    let value = (0..=d).fold("0".to_owned(), |v, i| format!("S{i}({v})"));
    let place = format!("p{}", ".f".repeat(d + 1));
    let line = match form {
        Form::Type => format!("    let y: @TypeOf({place}) = 0;\n"),
        Form::Expr => format!("    let t = @TypeOf({place});\n"),
        Form::Base => String::new(),
    };
    let src = format!(
        "{src}module M() {{\n    input x: UInt[8];\n    output o: UInt[8];\n    let p = {value};\n\
         {line}    o := x;\n}}\n"
    );
    passing(KEY + run_key, 100_000, &src)
}

/// The use of a place chain in `place_form_run`.
#[derive(Clone, Copy)]
enum Form {
    Type,
    Expr,
    Base,
}

/// W9. `@TypeOf(p.f...f)` of depth `d` as the type of a `let`. The type node charges 1, and then the
/// builtin evaluates as in an expression. The work of the type form is that of the expression form
/// plus a constant, and it doubles with `d`. A type position that walks the place again from the
/// root at each step gives `d` times `d`.
#[test]
fn w9_a_builtin_in_a_type_position_walks_its_place_once() {
    let at = |d: usize, key: u64| {
        let base = place_form_run(d, Form::Base, key);
        let typed = place_form_run(d, Form::Type, key + 1);
        let expr = place_form_run(d, Form::Expr, key + 2);
        (extra(&typed, &base), extra(&expr, &base))
    };
    let (((a, ua), (ea, uea)), ((b, ub), (eb, ueb))) = (at(32, 200), at(64, 203));
    assert!(a < b && b <= 2 * a + 16, "the work {a} at d and {b} at 2d");
    assert!(
        a <= ea + 8 && b <= eb + 8,
        "the work {a} and {b} against {ea} and {eb} of the expression"
    );
    assert_eq!(ua - uea, ub - ueb, "the units beyond the expression form");
    assert!(ua > uea && ub > ueb, "the type node charges");
}

/// The work and the units that the run `with` costs over the run `without`.
fn extra(with: &Run, without: &Run) -> (u64, u64) {
    (
        with.counts.total() - without.counts.total(),
        with.used - without.used,
    )
}
