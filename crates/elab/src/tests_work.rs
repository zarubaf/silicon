// SPDX-License-Identifier: Apache-2.0
//! The work of the comparisons of types, as the work bound of design section 5.5 states it for
//! the Rust front end: a type is an id, so a comparison, a key, and a join cost constant work
//! for each use and one walk for each pair of ids. Each family has an alias `Tn` of `n` types
//! and `k` repeated uses. The work then grows in `n + k` and not in `n * k`. The tests count
//! the steps of the walks and not the time.

use crate::counters::{Counts, of};
use crate::tests::{out, type_work};
use std::fmt::Write as _;

/// The alias of a tuple of `n` Booleans.
fn tn(n: usize) -> String {
    format!("type Tn = ({});\n", vec!["Bool"; n].join(", "))
}

/// Repeated specialization keys: one list `xs` of `Tn`, and `k` uses of `P[xs]`.
fn keys(n: usize, k: usize) -> String {
    format!(
        "{}type A = List[Tn];\nstruct P(comptime xs: A) {{ }}\n\
         fn f() -> Int {{ let xs = list(Tn); \
         comptime for i in 0..{k} {{ type S = P[xs]; }} return 0; }}",
        tn(n)
    )
}

/// Repeated typed uses of a function value: `k` assignments of `v` to a typed `g`.
fn typed(n: usize, k: usize) -> String {
    format!(
        "{}fn f1(x: Tn) -> Bool {{ return true; }}\n\
         fn f() -> Int {{ let v = f1; let mut g: fn (Tn) -> Bool = v; \
         comptime for i in 0..{k} {{ g = v; }} return 0; }}",
        tn(n)
    )
}

/// Repeated `==` on the empty list of `Tn`.
fn equals(n: usize, k: usize) -> String {
    format!(
        "{}fn f() -> Int {{ let xs = list(Tn); \
         comptime for i in 0..{k} {{ let b = xs == xs; }} return 0; }}",
        tn(n)
    )
}

/// Repeated indices of a static array with an unused branch of `n` nodes: `k` evaluations of the
/// same index. The scan pass visits the branch once, and no evaluation scans it again.
fn branches(n: usize, k: usize) -> String {
    format!(
        "fn f() -> Int {{ let xs = [1, 2]; \
         comptime for i in 0..{k} {{ let y = xs[if (true) {{ 0 }} else {{ {} }}]; }} return 0; }}",
        vec!["0"; n].join(" + ")
    )
}

/// The work of a run: the steps of the table, the pairs compared, the pairs of types joined,
/// the operands that the check of `==` read the function flag of, the nodes of the size walks,
/// and the nodes that scans of the AST visited. The family number and the sizes make the fuel of the run unique.
fn work(family: u64, source: fn(usize, usize) -> String, n: usize, k: usize) -> [u64; 6] {
    let fuel = 500_000_000 + family * 1_000_000 + (n as u64) * 1000 + k as u64;
    let src = source(n, k);
    assert_eq!(out(&src, "f()", fuel, 1000), "(int 0)", "{n} {k}");
    let counts = of(fuel);
    [
        type_work(&src, "f()"),
        counts.compared,
        counts.visited,
        counts.flagged,
        counts.walked,
        counts.ast,
    ]
}

/// Each count grows by the same amount for each equal step of `n`, and for each equal step of
/// `k`, and the growth in `k` does not depend on `n`. A product `n * k` breaks one of these.
fn assert_linear(family: u64, source: fn(usize, usize) -> String) {
    let at = |n: usize, k: usize| work(family, source, n, k);
    let base = at(100, 100);
    let (n2, n4) = (at(200, 100), at(400, 100));
    let (k2, k4) = (at(100, 200), at(100, 400));
    let (n4k2, n4k4) = (at(400, 200), at(400, 400));
    for m in 0..base.len() {
        assert_eq!(n4[m] - n2[m], 2 * (n2[m] - base[m]), "count {m} in n");
        assert_eq!(k4[m] - k2[m], 2 * (k2[m] - base[m]), "count {m} in k");
        assert_eq!(n4k2[m] - n4[m], k2[m] - base[m], "count {m} n*k");
        assert_eq!(n4k4[m] - n4k2[m], k4[m] - k2[m], "count {m} n*k");
    }
    // The type work does grow in `n`: the first use of the alias walks its types once.
    assert!(n2[0] > base[0], "{base:?} {n2:?}");
}

/// A later use of a specialization compares its key, a list of an id: it does not walk the `n`
/// types of the element type.
#[test]
fn the_work_of_specialization_keys_is_linear_in_n_and_k() {
    assert_linear(1, keys);
}

/// The typed use of a function value compares the ids of the signatures.
#[test]
fn the_work_of_typed_uses_of_a_function_value_is_linear_in_n_and_k() {
    assert_linear(2, typed);
}

/// The function flag and the join of two equal tuple types do not walk the `n` types again for
/// each `==`: the table keeps the join of a pair of ids.
#[test]
fn the_work_of_repeated_equality_is_linear_in_n_and_k() {
    assert_linear(3, equals);
}

/// An index does not scan its arguments again at each evaluation, also not the branch that a
/// conditional skips: the nodes that scans visited grow in `n` and not in `k`.
#[test]
fn the_work_of_repeated_indices_is_linear_in_n_and_k() {
    let at = |n: usize, k: usize| work(4, branches, n, k)[5];
    let (n1, n2, n4) = (at(100, 100), at(200, 100), at(400, 100));
    assert!(n1 > 0 && n4 - n2 == 2 * (n2 - n1), "{n1} {n2} {n4}");
    assert_eq!(at(100, 400), n1);
    assert_eq!(at(400, 400), n4);
}

/// The leaves that the walk over the leaves of a port type visited during the elaboration and
/// during the lowering, and the fuel that the lowering charged. The lowering runs on a thread of
/// its own, which joins the run of its parent. The fuel of the run keys the counts.
fn lowering(family: u64, ports: &str, n: usize) -> (u64, u64, u64) {
    use crate::{Abort, Budget, elaborate, tests_elab::load};
    let fuel = 600_000_000 + family * 1_000_000 + n as u64;
    let src = format!("module M() {{\n{ports}}}\n").replace("{n}", &n.to_string());
    let file = load(&src).unwrap();
    let budget = Budget {
        fuel,
        ..Budget::default()
    };
    let design = match elaborate(&file, "M", parse::DEFAULT_SYNTAX_DEPTH, budget) {
        Ok(Ok(design)) => design,
        Ok(Err(e)) => panic!("{} {}:{} at {n}", e.code, e.pos.line, e.pos.col),
        Err(Abort::Usage(m)) => panic!("{m}"),
        Err(Abort::Stack(e)) => panic!("{e}"),
    };
    let elaborated = of(fuel).leaves;
    let lowered = design.lower().unwrap().ok().unwrap();
    let total = of(fuel).leaves;
    (
        elaborated,
        total - elaborated,
        lowered.used() - design.used(),
    )
}

/// Checks that the lowering walk grows at most in step with `n` and stays within a constant
/// times the fuel that the lowering charged: it makes one visit for each leaf, and no list.
fn assert_streams(family: u64, ports: &str) {
    let at = |n: usize| lowering(family, ports, n);
    let (a, b, c) = (at(256), at(512), at(1024));
    for (n, w) in [(256, a), (512, b), (1024, c)] {
        assert!(w.1 > 0, "the lowering thread counts nothing at {n}");
        assert!(w.1 <= w.2, "{n}: {} visits for {} units", w.1, w.2);
    }
    assert!(
        b.1 <= 2 * a.1 + 4 && c.1 <= 2 * b.1 + 4,
        "{a:?} {b:?} {c:?}"
    );
    assert!(
        b.2 <= 2 * a.2 + 4 && c.2 <= 2 * b.2 + 4,
        "{a:?} {b:?} {c:?}"
    );
}

/// A port, a register, and a binding of an array lower one leaf at a time. The visits grow with
/// the leaf count and the charge pays for each of them.
#[test]
fn the_lowering_walks_ports_registers_and_bindings_per_leaf() {
    assert_streams(
        10,
        "  input x: [UInt[8]; {n}];\n  output y: [UInt[8]; {n}];\n  y := x;\n",
    );
    assert_streams(
        11,
        "  input x: [UInt[8]; {n}];\n  output y: [UInt[8]; {n}];\n  \
         reg r: [UInt[8]; {n}] = [UInt[8]; {n}]();\n  r := x;\n  y := r;\n",
    );
}

/// Empty parts have no leaves: the walk skips them and the lowering takes constant work.
#[test]
fn the_lowering_walk_skips_a_huge_empty_part() {
    let at = |n: usize| lowering(12, "  input x: (Bool, [(); {n}]);\n", n);
    assert_eq!(at(1 << 10).1, at(1 << 40).1);
    assert_eq!(at(1 << 10).2, at(1 << 40).2);
}

/// The counts of the elaboration and of the whole run of a module `M`, and the fuel that the
/// run charged. The key makes the fuel budget of the run unique, so it keys the counters.
#[derive(Debug)]
struct MemRun {
    elab: Counts,
    all: Counts,
    units: u64,
}

/// The module `M` of `src`, elaborated and lowered under the budget of the key `key`. An error
/// of the elaboration gives its code, and the counts then cover the work up to the error.
fn mem_run(key: u64, src: &str) -> Result<MemRun, String> {
    use crate::{Abort, Budget, elaborate, tests_elab::load};
    let fuel = 900_000_000 + key;
    let file = load(src)?;
    let budget = Budget {
        fuel,
        ..Budget::default()
    };
    let design = match elaborate(&file, "M", parse::DEFAULT_SYNTAX_DEPTH, budget) {
        Ok(Ok(d)) => d,
        Ok(Err(e)) => return Err(format!("{} {}:{}", e.code, e.pos.line, e.pos.col)),
        Err(Abort::Usage(m)) => return Err(m),
        Err(Abort::Stack(e)) => panic!("{e}"),
    };
    let elab = of(fuel);
    let units = design.lower().unwrap().ok().unwrap().used();
    Ok(MemRun {
        elab,
        all: of(fuel),
        units,
    })
}

/// The sizes of a scaling test: each is double the one before.
const SIZES: [usize; 4] = [64, 128, 256, 512];

/// The count `of` of the run `at(n)` is not zero, stays within `factor` times the fuel that the
/// run charged, and at most doubles (plus `slack`) when the size doubles.
fn assert_doubles(family: u64, at: impl Fn(usize, u64) -> MemRun, of: fn(&MemRun) -> u64) {
    let mut before: Option<u64> = None;
    for (i, n) in SIZES.into_iter().enumerate() {
        let r = at(n, family * 100 + i as u64);
        let count = of(&r);
        assert!(count > 0, "family {family}: no work counted at {n}");
        assert!(
            count <= 2 * r.units,
            "family {family} at {n}: the work {count} is more than twice the fuel {}",
            r.units
        );
        if let Some(b) = before {
            assert!(
                count <= 2 * b + 4,
                "family {family} at {n}: the work {b} grew to {count}"
            );
        }
        before = Some(count);
    }
}

/// A struct `W` of `n` bytes.
fn word(n: usize) -> String {
    let mut fields = String::new();
    for i in 0..n {
        let _ = write!(fields, "f{i}: UInt[8], ");
    }
    format!("struct W {{ {fields}}}\n")
}

/// A module `M` with one memory of the word type `W`, one write, and the output `o` bound to
/// `body`.
fn memory_module(pre: &str, mems: &str, body: &str) -> String {
    format!(
        "{pre}module M() {{\n input ra: UInt[2];\n input re: Bool;\n input wa: UInt[2];\n \
         input wd: W;\n input we: Bool;\n output o: UInt[8];\n{mems}{body}}}\n"
    )
}

/// The step on a word adds one stored offset: the selection of the last field of a wide word
/// reads the same number of offsets at each width, in the elaboration.
#[test]
fn the_work_of_a_step_on_a_word_does_not_grow_with_its_width() {
    let at = |n: usize, key: u64| {
        let src = memory_module(
            &word(n),
            " mem m: [W; 4];\n write_port(m, wa, wd, we);\n",
            &format!(" o := read_port(m, ra, re).data.f{};\n", n - 1),
        );
        mem_run(key, &src).unwrap()
    };
    let rows: Vec<u64> = SIZES
        .into_iter()
        .enumerate()
        .map(|(i, n)| at(n, 100 + i as u64).elab.offsets)
        .collect();
    assert!(
        rows[0] > 0 && rows.iter().all(|r| *r == rows[0]),
        "{rows:?}"
    );
    // The lowering reads one offset for each leaf of the word.
    assert_doubles(2, at, |r| r.all.offsets - r.elab.offsets);
}

/// A response passed through `k` calls binds the leaves of the word at each call. The work of
/// the offsets and of the bindings is linear in the width and in `k`, and the copy charges pay
/// for it.
#[test]
fn the_work_of_a_response_passed_through_calls_is_linear() {
    let call = |n: usize, k: usize, key: u64| {
        let mut e = "read_port(m, ra, re)".to_owned();
        for _ in 0..k {
            e = format!("id({e})");
        }
        let pre = format!(
            "{}fn id(r: ReadResponse[W]) -> ReadResponse[W] {{ return r; }}\n",
            word(n)
        );
        let src = memory_module(
            &pre,
            " mem m: [W; 4];\n write_port(m, wa, wd, we);\n",
            &format!(" o := {e}.data.f{};\n", n - 1),
        );
        mem_run(key, &src).unwrap()
    };
    assert_doubles(3, |n, key| call(n, 4, key), |r| r.elab.offsets);
    assert_doubles(4, |n, key| call(16, n / 8, key), |r| r.elab.offsets);
    assert_doubles(5, |n, key| call(n, 4, key), |r| r.elab.bound);
}

/// The write chain of a word of `n` leaves makes `n - 1` steps, each after its charge.
#[test]
fn the_work_of_the_write_chain_is_linear_in_the_leaves() {
    let at = |n: usize, key: u64| {
        let src = memory_module(
            &word(n),
            " mem m: [W; 4];\n write_port(m, wa, wd, we);\n",
            " o := read_port(m, ra, re).data.f0;\n",
        );
        let r = mem_run(key, &src).unwrap();
        assert_eq!(r.all.chained, n as u64 - 1, "{n}");
        r
    };
    assert_doubles(6, at, |r| r.all.chained);
}

/// The memory block, apart from the write chain, does not depend on the width of the word.
/// A module of `n` memories has `n` blocks.
#[test]
fn the_work_of_the_memory_block_is_constant_for_a_memory_and_linear_in_the_memories() {
    let wide: Vec<u64> = SIZES
        .into_iter()
        .enumerate()
        .map(|(i, n)| {
            let src = memory_module(
                &word(n),
                " mem m: [W; 4];\n write_port(m, wa, wd, we);\n",
                " o := read_port(m, ra, re).data.f0;\n",
            );
            mem_run(700 + i as u64, &src).unwrap().all.blocked
        })
        .collect();
    assert!(
        wide[0] > 0 && wide.iter().all(|b| *b == wide[0]),
        "{wide:?}"
    );
    let many = |n: usize, key: u64| {
        let mut mems = String::new();
        for i in 0..n {
            let _ = write!(
                mems,
                " mem m{i}: [UInt[8]; 4];\n let r{i} = read_port(m{i}, ra, re);\n \
                 write_port(m{i}, wa, r{i}.data, we);\n"
            );
        }
        let src = memory_module("struct W { a: UInt[8], }\n", &mems, " o := 0;\n");
        let r = mem_run(key, &src).unwrap();
        assert_eq!(r.all.blocked, n as u64 * wide[0], "{n}");
        r
    };
    assert_doubles(8, many, |r| r.all.blocked);
}

/// A second call of a port records its `S018` in constant work: `k` second calls count `k`
/// records, and the error stays the first one.
#[test]
fn the_work_of_the_second_calls_is_linear() {
    let at = |n: usize, key: u64| {
        let mut body = " let first = read_port(m, ra, re);\n".to_owned();
        for i in 0..n {
            let _ = writeln!(body, " let again{i} = read_port(m, ra, re);");
        }
        body.push_str(" o := first.data.f0;\n");
        let src = memory_module(
            &word(2),
            " mem m: [W; 4];\n write_port(m, wa, wd, we);\n",
            &body,
        );
        let err = mem_run(key, &src).unwrap_err();
        assert!(err.starts_with("S018"), "{err}");
        // The run fails, so it has no fuel count. Each second call is one statement of the
        // source, so the scan of the AST bounds the work.
        let all = of(900_000_000 + key);
        MemRun {
            elab: all,
            all,
            units: all.ast,
        }
    };
    assert_doubles(9, at, |r| r.all.seconds);
    assert_eq!(at(64, 950).all.seconds, 64);
}
