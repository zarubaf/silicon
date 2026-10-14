// SPDX-License-Identifier: Apache-2.0
//! The work of the records of `diagnostic`, as the work bound of design section 5.5 states it
//! for the Rust front end: the walk over the text of a record, the frames, the records, and the
//! guards. The text is paid by its bytes before it exists, so the walk is linear in the fuel
//! that the call charged. Each family doubles its size, and the counts then grow by the same
//! amount at each step, and they equal their closed form. A second walk, a copy of the frames,
//! or a replay of records breaks one of these. The tests count the steps of the walks and not
//! the time.

use crate::counters::{Counts, of};
use crate::tests_elab::load;
use crate::{Budget, observe_with};
use std::fmt::Write;

/// The sizes of a family: each is double the one before.
const SIZES: [u64; 4] = [32, 64, 128, 256];

/// A run: its counts and the bytes of its records. The bytes are what the calls charged for the
/// text, so a walk within a constant times them is within a constant times the fuel.
struct Run {
    counts: Counts,
    bytes: u64,
}

/// The run of the module `M()` in `src` with the depth limit `depth`. The family and the index
/// of the size make its fuel unique, and the counts of the run are keyed by it.
fn run(src: &str, depth: u64, family: u64, k: usize) -> Run {
    let fuel = 730_000_000 + family * 1000 + k as u64;
    let file = load(src).unwrap();
    let budget = Budget { fuel, depth };
    let Ok(done) = observe_with(
        &file,
        "M()",
        parse::DEFAULT_SYNTAX_DEPTH,
        budget,
        crate::names::sha16,
    ) else {
        panic!("the top selection must be valid")
    };
    if let Err(e) = &done.outcome {
        panic!(
            "{family} {k}: {} {}:{} {}",
            e.code, e.pos.line, e.pos.col, e.message
        );
    }
    Run {
        counts: of(fuel),
        bytes: done.records.iter().map(|r| r.len() as u64).sum(),
    }
}

/// The module `M()` with the ports `c`, `d`, and `o`, the extra ports `ports`, and the body.
fn module(ports: &str, body: &str) -> String {
    format!(
        "module M() {{\n  input c: Bool;\n  input d: UInt[8];\n{ports}  output o: UInt[8];\n{body}  o := 0;\n}}\n"
    )
}

/// The runs of a family at `SIZES`.
fn family(id: u64, depth: u64, source: impl Fn(u64) -> String) -> Vec<Run> {
    SIZES
        .iter()
        .enumerate()
        .map(|(k, n)| run(&source(*n), depth, id, k))
        .collect()
}

/// The count `of` grows by the same amount at each doubling of the size: it is affine in the
/// size. The count is the same at the first two sizes of a constant family.
fn assert_affine(runs: &[Run], of: fn(&Counts) -> u64, name: &str) {
    let counts: Vec<u64> = runs.iter().map(|r| of(&r.counts)).collect();
    for w in counts.windows(3) {
        assert_eq!(w[2] - w[1], 2 * (w[1] - w[0]), "{name} {counts:?}");
    }
}

/// The count `of` is `slope * n + base` at each size `n`.
fn assert_line(runs: &[Run], of: fn(&Counts) -> u64, slope: u64, base: u64, name: &str) {
    for (r, n) in runs.iter().zip(SIZES) {
        assert_eq!(of(&r.counts), slope * n + base, "{name} at {n}");
    }
}

/// The walk of the text visits at most 2 pieces for each byte that the call charged. It runs
/// twice for a record, once to count the bytes and once to write them.
fn assert_paid(runs: &[Run]) {
    for r in runs {
        assert!(r.counts.rendered > 0, "{:?}", r.counts);
        assert!(
            r.counts.rendered <= 4 * r.bytes,
            "{} pieces for {} bytes",
            r.counts.rendered,
            r.bytes
        );
    }
}

/// A reference of `n` tuples renders each part once for each of the two walks, and the work
/// reads the metadata of its type: one piece for the array and a constant number for each part.
#[test]
fn the_work_of_the_walk_over_a_reference_is_linear() {
    let runs = family(1, 1000, |n| {
        module(
            &format!("  input big: [(UInt[1],); {n}];\n"),
            "  diagnostic(\"big\", big);\n",
        )
    });
    assert_affine(&runs, |c| c.rendered, "rendered");
    assert_affine(&runs, |c| c.rendered_leaves, "leaves");
    assert_paid(&runs);
    assert_line(&runs, |c| c.recorded, 0, 1, "recorded");
    assert_line(&runs, |c| c.framed, 0, 0, "framed");
    assert_line(&runs, |c| c.guarded, 0, 10, "guarded");
    // Each part is a tuple piece, its text, a hardware leaf, and a space between the parts.
    assert_line(&runs, |c| c.rendered, 18, 20, "rendered");
    assert_line(&runs, |c| c.rendered_leaves, 2, 2, "leaves");
}

/// A tuple of `n` hardware leaves renders each leaf once for each of the two walks.
#[test]
fn the_work_of_the_walk_over_a_tuple_is_linear() {
    let runs = family(2, 1000, |n| {
        let parts = vec!["d"; n.try_into().unwrap_or_default()].join(", ");
        module("", &format!("  diagnostic(\"t\", ({parts}));\n"))
    });
    assert_affine(&runs, |c| c.rendered, "rendered");
    assert_affine(&runs, |c| c.rendered_leaves, "leaves");
    assert_paid(&runs);
    assert_line(&runs, |c| c.recorded, 0, 1, "recorded");
    assert_line(&runs, |c| c.guarded, 0, 5, "guarded");
    assert_line(&runs, |c| c.rendered, 12, 14, "rendered");
    assert_line(&runs, |c| c.rendered_leaves, 4, 0, "leaves");
}

/// A message of `n` bytes is one quoted piece: the walk does not grow in the length of the
/// message, and the bytes that it writes are paid by the charge of the bytes.
#[test]
fn the_work_of_the_walk_does_not_grow_with_the_message() {
    let runs = family(3, 1000, |n| {
        module(
            "",
            &format!(
                "  diagnostic(\"{}\", 1);\n",
                "a".repeat(n.try_into().unwrap_or_default())
            ),
        )
    });
    assert_line(&runs, |c| c.rendered, 0, 12, "rendered");
    assert_line(&runs, |c| c.recorded, 0, 1, "recorded");
    for (r, n) in runs.iter().zip(SIZES) {
        assert!(r.bytes >= n, "{n}");
    }
}

/// A loop of `n` iterations appends `n` records, each walked twice, with no replay.
#[test]
fn the_work_of_a_loop_of_records_is_linear() {
    let runs = family(4, 1000, |n| {
        module(
            "",
            &format!("  comptime for i in 0..{n} {{\n    diagnostic(\"i\", i);\n  }}\n"),
        )
    });
    assert_line(&runs, |c| c.recorded, 1, 0, "recorded");
    assert_affine(&runs, |c| c.rendered, "rendered");
    assert_paid(&runs);
    assert_line(&runs, |c| c.framed, 0, 0, "framed");
    let per = runs[0].counts.rendered / SIZES[0];
    assert_line(&runs, |c| c.rendered, per, 0, "rendered");
}

/// One record at the bottom of a recursion of depth `n` writes `n` frames for each of its two
/// walks, and the call pushes a frame in constant time.
#[test]
fn the_work_of_the_frames_of_one_record_is_linear() {
    let runs = family(5, 1000, |n| {
        format!(
            "fn rec(n: Nat) -> Nat {{\n  comptime if (n == 0) {{ diagnostic(\"b\", n); }}\n  \
             return if (n == 0) {{ 0 }} else {{ rec(n - 1) }};\n}}\n{}",
            module("", &format!("  rec({n});\n"))
        )
    });
    assert_line(&runs, |c| c.framed, 2, 2, "framed");
    assert_line(&runs, |c| c.recorded, 0, 1, "recorded");
    assert_affine(&runs, |c| c.rendered, "rendered");
    assert_paid(&runs);
}

/// A record at each level of a recursion of depth `n` writes the frames of every level: the
/// frames are quadratic in `n`, and the bytes that pay for them are quadratic too. Each frame
/// is at least 12 bytes, so the walk stays within the fuel.
#[test]
fn the_work_of_the_frames_of_every_level_is_paid_by_the_bytes() {
    let runs = family(6, 1000, |n| {
        format!(
            "fn rec(n: Nat) -> Nat {{\n  diagnostic(\"r\", n);\n  \
             return if (n == 0) {{ 0 }} else {{ rec(n - 1) }};\n}}\n{}",
            module("", &format!("  rec({n});\n"))
        )
    });
    for (r, n) in runs.iter().zip(SIZES) {
        assert_eq!(r.counts.recorded, n + 1, "records at {n}");
        // The record at depth j has j + 1 frames and is walked twice.
        assert_eq!(r.counts.framed, (n + 1) * (n + 2), "frames at {n}");
        assert!(12 * r.counts.framed / 2 <= r.bytes, "{n}: {}", r.bytes);
    }
    assert_paid(&runs);
}

/// A hardware arm and a structural context enter their guard once, in constant time.
#[test]
fn the_work_of_the_guards_is_linear() {
    let arms = family(7, 1000, |n| {
        module(
            "",
            &format!(
                "  comptime for i in 0..{n} {{\n    let z = if (c) {{ d }} else {{ d }};\n  }}\n"
            ),
        )
    });
    assert_line(&arms, |c| c.guarded, 1, 5, "arm guards");
    let types = family(8, 1000, |n| {
        module(
            "",
            &format!("  comptime for i in 0..{n} {{\n    let w: UInt[3] = 0;\n  }}\n"),
        )
    });
    assert_affine(&types, |c| c.guarded, "structural guards");
    for r in arms.iter().chain(&types) {
        assert_eq!(r.counts.recorded, 0);
        assert_eq!(r.counts.rendered, 0);
    }
}

/// The shared hierarchy of depth `d` gives one record for each depth, not the `2^d` of a replay.
#[test]
fn the_records_of_a_shared_hierarchy_are_linear_in_its_depth() {
    let src = "module M(comptime d: Nat) domains() {
    input a: UInt[1];
    output q: UInt[1];
    diagnostic(\"depth\", d);
    comptime if (d == 0) {
        q := a;
    } else {
        instance l = M(d - 1);
        instance r = M(d - 1);
        l.a := a;
        r.a := l.q;
        q := r.q;
    }
}
";
    let counts = |d: u64, k: usize| {
        let fuel = 730_000_000 + 9000 + k as u64;
        let file = load(src).unwrap();
        let top = format!("M({d})");
        let budget = Budget { fuel, depth: 1000 };
        let Ok(done) = observe_with(
            &file,
            &top,
            parse::DEFAULT_SYNTAX_DEPTH,
            budget,
            crate::names::sha16,
        ) else {
            panic!("the top selection must be valid")
        };
        assert!(done.outcome.is_ok(), "{d}");
        assert_eq!(done.records.len() as u64, d + 1);
        of(fuel)
    };
    let (a, b, c) = (counts(15, 0), counts(30, 1), counts(60, 2));
    assert_eq!((a.recorded, b.recorded, c.recorded), (16, 31, 61));
    assert_eq!(c.rendered - b.rendered, 2 * (b.rendered - a.rendered));
    assert_eq!(c.framed, 0);
}

/// The run of `src` at the fuel `fuel`: its records, the code of its first error, and the
/// counts of the run. The fuel must be unique in the test run.
fn run_at(src: &str, fuel: u64) -> (usize, Option<crate::Code>, Counts) {
    let file = load(src).unwrap();
    let budget = Budget { fuel, depth: 1000 };
    let Ok(done) = observe_with(
        &file,
        "M()",
        parse::DEFAULT_SYNTAX_DEPTH,
        budget,
        crate::names::sha16,
    ) else {
        panic!("the top selection must be valid")
    };
    (
        done.records.len(),
        done.outcome.err().map(|e| e.code),
        of(fuel),
    )
}

/// A record that does not fit its fuel measures its line from the borrowed names of its frames.
/// It copies no name before the charge of its bytes: the frames are `depth` times a name of
/// `len` characters, and the call stops with fuel left.
#[test]
fn a_record_that_does_not_fit_copies_no_frame() {
    // The least fuel that appends the record. One unit less stops at the charge of its bytes,
    // which is about 410,000 bytes, and the frames are still unwritten.
    const LEAST: u64 = 411_721;
    let (depth, len) = (40, 10_000);
    let name = "f".repeat(len);
    let src = format!(
        "fn {name}(n: Nat) -> Nat {{\n  comptime if (n == 0) {{ diagnostic(\"b\", n); }}\n  \
         return if (n == 0) {{ 0 }} else {{ {name}(n - 1) }};\n}}\n{}",
        module("", &format!("  {name}({depth});\n"))
    );
    assert_eq!(run_at(&src, LEAST).0, 1);
    let (records, code, counts) = run_at(&src, LEAST - 1);
    assert_eq!((records, code), (0, Some(crate::Code::S015)));
    assert_eq!(counts.recorded, 0);
    // The line holds `depth + 1` frames of the name; none of them exists before its charge.
    assert_eq!(counts.copied, 0, "{} bytes for {len}", counts.copied);
}

/// A read of a domain shares its name: the loop of `n` reads of a name of `len` characters
/// copies the name at most once, not once for each read.
#[test]
fn a_domain_read_copies_no_name() {
    let source = |len: usize, n: u64| {
        let name = "c".repeat(len);
        format!(
            "module M() domains({name}) {{\n  input d: UInt[8];\n  output o: UInt[8];\n  \
             comptime for i in 0..{n} {{\n    let x = {name};\n  }}\n  o := d;\n}}\n"
        )
    };
    for (k, n) in SIZES.iter().enumerate() {
        let (_, code, counts) = run_at(&source(1000, *n), 736_000_000 + k as u64);
        assert_eq!(code, None);
        assert!(
            counts.copied <= 1000,
            "{} bytes at {n} reads",
            counts.copied
        );
    }
    for (k, len) in [500usize, 1000, 2000].into_iter().enumerate() {
        let (_, code, counts) = run_at(&source(len, 64), 737_000_000 + k as u64);
        assert_eq!(code, None);
        assert!(
            counts.copied <= len as u64,
            "{} bytes at {len}",
            counts.copied
        );
    }
}

/// A record with a long name in a handle, a module, a port, or its message stops at the charge
/// of its bytes before it builds any name: the length pass measures the borrowed fields. Each
/// case is a source and the least fuel that appends its record.
#[test]
fn a_record_that_does_not_fit_builds_no_name() {
    let name = "w".repeat(10_000);
    let child = format!("module {name}() {{\n  input {name}: UInt[1];\n}}\n");
    let cases = [
        (
            module(
                "",
                &format!("  wire {name}: UInt[8];\n  diagnostic(\"w\", {name});\n"),
            ),
            10_107,
        ),
        (
            module("", &format!("  diagnostic(\"{name}\", 1);\n")),
            30_090,
        ),
        (
            format!(
                "{child}{}",
                module(
                    "",
                    &format!("  instance i = {name}();\n  diagnostic(\"i\", i);\n")
                )
            ),
            30_168,
        ),
        (
            format!(
                "{child}{}",
                module(
                    "",
                    &format!("  instance i = {name}();\n  diagnostic(\"p\", i.{name});\n")
                )
            ),
            30_156,
        ),
    ];
    for (k, (src, least)) in cases.iter().enumerate() {
        assert_eq!(run_at(src, *least).0, 1, "case {k}");
        let (records, code, counts) = run_at(src, least - 1);
        assert_eq!((records, code), (0, Some(crate::Code::S015)), "case {k}");
        assert_eq!(counts.copied, 0, "case {k}: {} bytes", counts.copied);
    }
}

/// The module `M()` that records a handle `kind` of the struct type nested `levels` deep. Each
/// level holds the one before in its type argument and in two empty arrays of it, so the term
/// of the type triples at each level while its size grows by a constant.
fn nested_handle(kind: &str, levels: u64) -> String {
    let mut src = String::from(
        "struct R(comptime A: Type, comptime e: [A; 0], comptime f: [A; 0]) { x: Bool }\n\
         type T0 = R[Bool, [], []];\n",
    );
    for i in 1..=levels {
        writeln!(src, "type T{i} = R[T{}, [], []];", i - 1).unwrap_or_default();
    }
    let body = if kind == "mem" {
        format!("  mem m: [T{levels}; 4];\n  diagnostic(\"m\", m);\n")
    } else {
        format!("  {kind} m: T{levels};\n  diagnostic(\"m\", m);\n")
    };
    format!("{src}module M() domains(clk) {{\n{body}}}\n")
}

/// The type of a handle measures through the table once: a record unfolds no type. The record stops
/// at the charge of its bytes, so no walk follows it.
#[test]
fn the_type_of_a_handle_measures_through_the_table() {
    // The length pass reads the stored length of each type and unfolds none.
    for (k, kind) in ["mem", "input", "output"].into_iter().enumerate() {
        for (j, n) in [6u64, 8, 10, 12].into_iter().enumerate() {
            let src = nested_handle(kind, n);
            let (_, code, counts) = run_at(&src, 9_100 + (k * 10 + j) as u64);
            assert_eq!(code, Some(crate::Code::S015), "{kind} {n}");
            assert_eq!(counts.unfolded, 0, "{kind} {n}");
        }
    }
}

/// The module `M()` that records `value` after the nested types `T0` to `T<levels>` and the
/// struct `Wrap` with a field of an array of the deepest. The term of the deepest type triples
/// at each level while its size grows by a constant.
fn nested_record(levels: u64, ports: &str, value: &str) -> String {
    let mut src = String::from(
        "struct R(comptime A: Type, comptime e: [A; 0], comptime f: [A; 0]) { x: Bool }\n\
         type T0 = R[Bool, [], []];\n",
    );
    for i in 1..=levels {
        writeln!(src, "type T{i} = R[T{}, [], []];", i - 1).unwrap_or_default();
    }
    writeln!(src, "struct Wrap {{ x: [T{levels}; 1] }}").unwrap_or_default();
    writeln!(
        src,
        "fn probe(w: Wrap, t: T{levels}) -> Bool {{ return true; }}"
    )
    .unwrap_or_default();
    format!("{src}module M() domains(clk) {{\n{ports}  diagnostic(\"m\", {value});\n}}\n")
}

/// A type that a record holds, whatever the way it holds it, measures through the table: the
/// type nodes that the length pass unfolds grow by a constant at each level, and no walk
/// follows the term of the type.
#[test]
fn a_type_in_a_record_unfolds_once_for_each_level() {
    let cases: [(&str, &str); 6] = [
        ("  input w: Wrap;\n", "w"),
        ("", "Wrap()"),
        ("", "[Wrap(), Wrap()]"),
        ("  input w: [Wrap; 2];\n", "w"),
        ("", "fn(Wrap, T{L}) -> Bool"),
        ("  input w: Wrap;\n", "(w, 1)"),
    ];
    for (k, (ports, value)) in cases.into_iter().enumerate() {
        let counts: Vec<u64> = [6u64, 9, 12]
            .into_iter()
            .enumerate()
            .map(|(j, n)| {
                let src = nested_record(n, ports, &value.replace("{L}", &n.to_string()));
                let (_, code, counts) = run_at(&src, 9_200 + (k * 10 + j) as u64);
                assert!(
                    code.is_none_or(|c| c == crate::Code::S015),
                    "{value} {code:?}"
                );
                counts.unfolded
            })
            .collect();
        // The count grows by the same amount for each three levels.
        assert_eq!(
            counts[2] - counts[1],
            counts[1] - counts[0],
            "{value} {counts:?}"
        );
        assert!(counts[2] <= 4 * 12, "{value} {counts:?}");
    }
}
