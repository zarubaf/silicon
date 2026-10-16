// SPDX-License-Identifier: Apache-2.0
//! The work of the walks over hardware aggregates, as the work bound of design section 5.5
//! states it for the Rust front end: each walk visits a pair, a part, or a leaf after the unit
//! that pays for it, and a reference never expands. The tests count the steps of the walks with
//! the counters and not the time. Doubling the input at most doubles the count, and the count
//! stays within a constant times the fuel that the run charged.

use super::tests_bind::{assign_in, ref_x, run_f};
use crate::counters::{self, Counts};
use std::fmt::Write as _;

const FUEL: u64 = 1_000_000_000_000;

/// A run: the counts of its walks and the fuel that it charged.
struct Run {
    counts: Counts,
    units: u64,
    /// The recursive size of the values that references copied.
    copied: u64,
}

/// The run of `pre` and the statement `s` in the body of `f` with the formal `x` of the type
/// `t`. The number `run` keys the counters. A failed run gives its text.
fn run_with(pre: &str, t: &str, s: &str, run: u64) -> Result<Run, String> {
    let text = run_f(&format!("{pre}{}", assign_in(t, s)), run, FUEL, ref_x);
    match text.rsplit(" | ").next().map(str::parse::<u64>) {
        Some(Ok(units)) if text.contains(" | ") => Ok(Run {
            counts: counters::of(run),
            units,
            copied: counters::run(run).map_or(0, |c| c.copies),
        }),
        _ => Err(text),
    }
}

fn run_ok(pre: &str, t: &str, s: &str, run: u64) -> Run {
    run_with(pre, t, s, run).unwrap_or_else(|e| panic!("{t} {s}: {e}"))
}

/// The sizes of the inputs of a scaling test: each is double the one before.
const SIZES: [u64; 4] = [32, 64, 128, 256];

/// The count `of` of the run `at(n)` at least doubles by no more than its input: it is at most
/// twice the count at half the input plus a constant `slack`. The count stays within `factor`
/// times the fuel that the run charged, and it is not zero.
fn assert_linear(at: impl Fn(u64, u64) -> Run, of: fn(&Run) -> u64, factor: u64, slack: u64) {
    let mut before: Option<u64> = None;
    for (k, n) in SIZES.into_iter().enumerate() {
        let r = at(n, k as u64);
        let count = of(&r);
        assert!(count > 0, "no work counted at {n}");
        assert!(
            count <= factor * r.units,
            "{n}: the work {count} is more than {factor} times the fuel {}",
            r.units
        );
        if let Some(b) = before {
            assert!(count <= 2 * b + slack, "{n}: the work {b} grew to {count}");
        }
        before = Some(count);
    }
}

/// The key of a run: the family number and the index of the size keep it unique.
fn key(family: u64, k: u64) -> u64 {
    800_000_000 + family * 100 + k
}

/// `==` and `!=` pair the root and each element once: `n + 1` pairs, each paid by the fuel.
#[test]
fn the_work_of_the_equality_walk_is_linear_and_paid() {
    for (family, op) in [(1, "=="), (2, "!=")] {
        let at = |n: u64, k: u64| {
            run_ok(
                "",
                &format!("[UInt[8]; {n}]"),
                &format!("let y = x {op} x;"),
                key(family, k),
            )
        };
        assert_linear(at, |r| r.counts.paired, 1, 1);
        assert_eq!(at(64, 9).counts.paired, 65);
    }
}

/// The `if` pairs the root and each element once and builds one node for each leaf.
#[test]
fn the_work_of_the_if_walk_is_linear_and_paid() {
    let at = |n: u64, k: u64| {
        run_ok(
            "",
            &format!("(Bool, [UInt[8]; {n}], [UInt[8]; {n}])"),
            "let y = if (x.0) { x.1 } else { x.2 };",
            key(3, k),
        )
    };
    assert_linear(at, |r| r.counts.paired, 1, 1);
    assert_linear(at, |r| r.counts.nodes, 1, 2);
    assert_eq!(at(64, 9).counts.paired, 65);
}

/// A selection takes constant work in the length of the array, also at 2^40, and a typed use
/// of a reference at its own type checks no part. The binding of the typed use makes one `let`
/// for each leaf, and the copy pays for them.
#[test]
fn a_selection_and_a_typed_use_take_no_work_in_the_array_length() {
    let sizes = [16u64, 1 << 20, 1 << 40];
    let select = |shape: fn(u64) -> String, s: &str, family: u64| {
        let rows: Vec<Run> = sizes
            .iter()
            .enumerate()
            .map(|(k, n)| run_ok("", &shape(*n), s, key(family, k as u64)))
            .collect();
        for r in &rows {
            let (a, b) = (&rows[0].counts, &r.counts);
            assert_eq!(
                (a.selected, a.nodes, a.walked, a.expanded, a.bound),
                (b.selected, b.nodes, b.walked, b.expanded, b.bound)
            );
            assert_eq!(rows[0].units, r.units);
        }
    };
    select(|n| format!("[UInt[8]; {n}]"), "let y = x[3];", 4);
    select(|n| format!("[[UInt[8]; {n}]; 8]"), "let y = x[3][4];", 5);
    let typed = |n: u64, k: u64| {
        run_ok(
            "",
            &format!("[UInt[8]; {n}]"),
            &format!("let q: [UInt[8]; {n}] = x;"),
            key(6, k),
        )
    };
    for (k, n) in SIZES.into_iter().enumerate() {
        let r = typed(n, k as u64);
        let c = r.counts;
        assert_eq!((c.typed, c.nodes, c.expanded), (0, 1, 0), "{n}");
        assert!(
            c.bound <= r.units,
            "{n}: {} bound for {} units",
            c.bound,
            r.units
        );
    }
}

/// The empty sub-reference charges its zero size before it exists and builds nothing: the fuel
/// grows with the length of the empty array, and no count grows with it. At 2^40 the charge
/// fails before any part exists.
#[test]
fn an_empty_sub_reference_builds_nothing_beyond_its_charge() {
    let at = |n: u64, k: u64| {
        run_ok(
            "",
            &format!("(UInt[8], [(); {n}])"),
            "let e = x.1;",
            key(7, k),
        )
    };
    let (a, b) = (at(64, 0), at(1 << 20, 1));
    let (ca, cb) = (a.counts, b.counts);
    assert_eq!(
        (ca.nodes, ca.walked, ca.bound, ca.expanded, ca.selected),
        (cb.nodes, cb.walked, cb.bound, cb.expanded, cb.selected)
    );
    assert_eq!(
        b.units - a.units,
        (1 << 20) - 64,
        "the charge is the zero size"
    );
    let huge = run_with(
        "",
        "(UInt[8], [(); 1099511627776])",
        "let e = x.1;",
        key(7, 2),
    );
    assert_eq!(huge.err().as_deref(), Some("S015 2:11"));
    let c = counters::of(key(7, 2));
    assert_eq!((c.nodes, c.walked, c.bound, c.expanded), (0, 0, 0, 0));
}

/// The rebind of a place update binds each leaf once. Its work grows with the leaf count, and
/// the fuel pays for it. The rebind of an empty part charges the zero size first, and the
/// expansion of the part then takes a constant number of walks over it.
#[test]
fn the_rebind_and_the_empty_part_charge_are_paid() {
    let at = |n: u64, k: u64| run_ok("", &format!("[UInt[8]; {n}]"), "x[1] = 7;", key(8, k));
    assert_linear(at, |r| r.counts.bound, 1, 2);
    assert_linear(at, |r| r.counts.expanded, 1, 2);
    assert_linear(at, |r| r.counts.nodes, 4, 2);
    let empty =
        |n: u64, k: u64| run_ok("", &format!("(UInt[8], [(); {n}])"), "x.0 = 5;", key(9, k));
    let sizes = [64u64, 1 << 10, 1 << 16];
    for (k, n) in sizes.into_iter().enumerate() {
        let r = empty(n, k as u64);
        let c = r.counts;
        assert_eq!((c.nodes, c.expanded), (4, 2), "{n}");
        assert!(
            c.walked <= 5 * r.units,
            "{n}: {} walked for {} units",
            c.walked,
            r.units
        );
        assert!(r.units >= n, "{n}: the zero size is charged");
    }
    let huge = run_with("", "(UInt[8], [(); 1099511627776])", "x.0 = 5;", key(9, 9));
    assert_eq!(huge.err().as_deref(), Some("S015 2:3"));
    assert_eq!(counters::of(key(9, 9)).expanded, 0);
}

/// `push` into a list part of an aggregate root of width `n`, `n` times. Each push refreshes the
/// nodes above the list by a walk over their parts, and it charges the part count of each node
/// first. Thus the work and the fuel both grow by 4 when the width doubles, and the work stays
/// within a constant times the fuel.
#[test]
fn a_push_into_a_list_part_of_a_wide_root_is_paid() {
    for (k, n) in SIZES.into_iter().enumerate() {
        let ws = (0..n).map(|_| "x.0").collect::<Vec<_>>().join(", ");
        let r = run_ok(
            "",
            "(UInt[8], Bool)",
            &format!(
                "let mut t = ({ws}, list(Int));\n  comptime for i in 0..{n} {{ t.{n}.push(3); }}"
            ),
            key(10, k as u64),
        );
        for (name, count) in [("nodes", r.counts.nodes), ("walked", r.counts.walked)] {
            assert!(count > 0, "{n}: no {name} counted");
            assert!(
                count <= 8 * r.units,
                "{n}: {count} {name} for {} units",
                r.units
            );
        }
    }
}

/// A parked reference to a part of an aggregate root copies when a later operand changes the
/// root. The copy is one node for each part. The change charges the rebind of the root, so the
/// extra work of the copy stays within a constant times the extra fuel of the change.
#[test]
fn the_copy_of_a_parked_reference_is_paid_by_the_change() {
    let at = |n: u64, with: bool, k: u64| {
        let ws = (0..n).map(|_| "x.0").collect::<Vec<_>>().join(", ");
        let pre = format!(
            "fn h(a: [UInt[8]; {n}], b: Int) -> Int {{ return b; }}\n\
             fn p(mut l: List[Int]) -> Int {{\n  l.push(1);\n  return 0;\n}}\n"
        );
        let call = if with { "h(t.0, p(t.1))" } else { "h(t.0, 0)" };
        run_ok(
            &pre,
            "(UInt[8], Bool)",
            &format!("let mut t = ([{ws}], list(Int));\n  let y = {call};"),
            key(11, k * 2 + u64::from(with)),
        )
    };
    let mut before: Option<u64> = None;
    for (k, n) in SIZES.into_iter().enumerate() {
        let k = k as u64;
        let (base, changed) = (at(n, false, k), at(n, true, k));
        let nodes = changed.counts.nodes - base.counts.nodes;
        let units = changed.units - base.units;
        assert!(nodes > 0, "{n}: the change copied nothing");
        assert!(nodes <= 2 * units, "{n}: {nodes} nodes for {units} units");
        if let Some(b) = before {
            assert!(nodes <= 2 * b + 8, "{n}: {b} grew to {nodes}");
        }
        before = Some(nodes);
    }
}

/// A `push` under an aggregate root refreshes each node on the path from its stored numbers and
/// reads no sibling, so the walks over values count only the elements that the pushes add.
#[test]
fn a_push_into_a_list_part_reads_no_sibling() {
    let at = |n: u64, k: u64| {
        run_ok(
            "",
            "(UInt[8], Bool)",
            &format!(
                "let mut t = (x.0, list(Int));\n  comptime for i in 0..{n} {{ t.1.push(3); }}"
            ),
            key(12, k),
        )
    };
    assert_linear(at, |r| r.counts.walked, 8, 8);
}

/// The first update of a place through a lazy reference builds each node on the path once, and
/// a static part on the path is not walked again at each level.
#[test]
fn a_place_update_through_a_reference_walks_each_level_once() {
    let at = |n: u64, k: u64| {
        let structs: String = (0..n)
            .map(|i| format!("struct S{i} {{ a: S{}, }}\n", i + 1))
            .chain([format!("struct S{n} {{ a: UInt[8], }}\n")])
            .collect();
        let sel: String = (0..=n).map(|_| ".a").collect();
        let r = run_with(
            &structs,
            "S0",
            &format!("let mut m = x;\n  m{sel} = 7;"),
            key(13, k),
        );
        r.unwrap_or_else(|e| panic!("{n}: {e}"))
    };
    assert_linear(at, |r| r.counts.walked, 8, 8);
}

/// The walk of `==` and of `if` adds no path to the arena for a part without a hardware leaf:
/// `()` and an empty pair keep the base of their parent. Thus the paths stay the same when the
/// empty array grows by a factor of 16.
#[test]
fn the_walks_add_no_path_for_a_part_without_a_hardware_leaf() {
    let paths = |t: &str, s: &str, k: u64| run_ok("", t, s, key(14, k)).counts.paths;
    for (k, s) in [
        (0, "let y = x == x;"),
        (2, "let y = if (x.0 == 1) { x } else { x };"),
    ] {
        let small = paths("(UInt[8], [(); 16])", s, k);
        let large = paths("(UInt[8], [(); 256])", s, k + 1);
        assert!(small > 0, "{s}: no path counted");
        assert_eq!(small, large, "{s}");
    }
}

/// The text `s` `n` times.
fn rep(s: &str, n: u64) -> String {
    (0..n).map(|_| s).collect()
}

/// The declarations `S0` to `Sn` of a chain of `n + 1` levels. Each level `link`s to the next
/// one, and the last level takes the place of `leaf`. The text of `link` has the number of the
/// next level in place of `{}`.
fn chain_decls(n: u64, link: &str, leaf: &str) -> String {
    (0..n)
        .map(|i| {
            link.replace("{}", &(i + 1).to_string())
                .replace("{i}", &i.to_string())
        })
        .chain([leaf.replace("{i}", &n.to_string())])
        .collect()
}

/// A read through a chain of `n` stored nodes takes steps in `n`: one cursor walks the whole
/// chain, so the path from the root is not walked again at each level. The root is the formal
/// with one update along the chain, so the nodes of the chain are stored in the local. The
/// chain goes through fields, through fields and indices, and through selectors.
#[test]
fn a_read_through_stored_nodes_takes_linear_steps() {
    let cases: [(u64, &str, &str, &str); 3] = [
        (
            20,
            "struct S{i} { a: S{}, b: UInt[8], }\n",
            "struct S{i} { a: UInt[8], b: UInt[8], }\n",
            ".a",
        ),
        (
            21,
            "struct S{i} { a: [S{}; 1], b: UInt[8], }\n",
            "struct S{i} { a: [UInt[8]; 1], b: UInt[8], }\n",
            ".a[0]",
        ),
        (
            22,
            "type S{i} = (S{}, UInt[8]);\n",
            "type S{i} = (UInt[8], UInt[8]);\n",
            ".0",
        ),
    ];
    for (family, link, leaf, step) in cases {
        let at = |n: u64, k: u64| {
            let sel = rep(step, n + 1);
            run_ok(
                &chain_decls(n, link, leaf),
                "S0",
                &format!("let mut m = x;\n  m{sel} = 7;\n  let y = m{sel};"),
                key(family, k),
            )
        };
        assert_linear(at, |r| r.counts.stepped, 16, 16);
    }
}

/// A place through `n` empty parts of a stored root walks its path in `n` steps. The empty parts
/// are in a static part of the root, which holds no reference to normalize, so the walk does not
/// catch up at each one.
#[test]
fn a_place_through_empty_parts_of_a_stored_root_takes_linear_steps() {
    let at = |n: u64, k: u64| {
        let sel = rep(".a", n + 1);
        run_ok(
            &chain_decls(n, "struct E{i} { a: E{}, }\n", "struct E{i} { a: (), }\n"),
            "(UInt[8], E0)",
            &format!("let mut m = x;\n  m.0 = x.0;\n  m.1{sel} = ();"),
            key(23, k),
        )
    };
    assert_linear(at, |r| r.counts.stepped, 8, 16);
}

/// A place update that turns a static root of `n` nested tuples into hardware finds the type of
/// the root once, and the type of each level comes from it. The work of the table of types grows
/// with the update, and the update is paid by the fuel. The zero root is the same in both runs.
#[test]
fn the_promotion_of_nested_static_tuples_finds_the_type_once() {
    let at = |n: u64, update: bool, k: u64| {
        let sel = rep(".0", n);
        let set = if update {
            format!("m{sel} = x.0;")
        } else {
            String::new()
        };
        run_ok(
            &chain_decls(n, "type T{i} = (T{}, UInt[8]);\n", "type T{i} = UInt[8];\n"),
            "(UInt[8], Bool)",
            &format!("let mut m: T0 = T0();\n  {set}"),
            key(24, k * 2 + u64::from(update)),
        )
    };
    let mut before: Option<u64> = None;
    for (k, n) in SIZES.into_iter().enumerate() {
        let k = k as u64;
        let (with, without) = (at(n, true, k), at(n, false, k));
        let work = with.counts.table - without.counts.table;
        let units = with.units - without.units;
        assert!(work > 0, "{n}: no table work for the update");
        assert!(
            work <= 4 * units,
            "{n}: {work} table steps for {units} units"
        );
        if let Some(b) = before {
            assert!(work <= 2 * b + 8, "{n}: the work {b} grew to {work}");
        }
        before = Some(work);
    }
}

/// A hardware `if` over `n` nested empty parts keeps the size and the depth of each finished
/// part, so a node reads the numbers of its parts and does not walk a finished part again.
#[test]
fn the_if_over_nested_empty_parts_walks_each_part_once() {
    let at = |n: u64, k: u64| {
        run_ok(
            &chain_decls(n, "struct E{i} { a: E{}, }\n", "struct E{i} { a: (), }\n"),
            "(UInt[8], E0, E0)",
            "let y = if (x.0 == 1) { (x.0, x.1) } else { (x.0, x.2) };",
            key(25, k),
        )
    };
    assert_linear(at, |r| r.counts.walked, 4, 8);
    assert_linear(at, |r| r.counts.paired, 1, 4);
}

/// An index with a call, along a chain of `n` stored nodes, takes steps in `n`. A call can
/// change the root, so a read re-checks the part that it waits at (`segment`), but a call that
/// leaves the root alone must not walk the path from the root again at each index. The calls
/// are constant work, so the fuel grows in `n` too.
#[test]
fn an_index_with_a_call_along_stored_nodes_takes_linear_steps() {
    let zero = "fn zero() -> Int { return 0; }\n";
    let at = |n: u64, k: u64| {
        let place = rep(".a[0]", n + 1);
        let read = rep(".a[zero()]", n + 1);
        run_ok(
            &format!(
                "{zero}{}",
                chain_decls(
                    n,
                    "struct S{i} { a: [S{}; 1], b: UInt[8], }\n",
                    "struct S{i} { a: [UInt[8]; 1], b: UInt[8], }\n"
                )
            ),
            "S0",
            &format!("let mut m = x;\n  m{place} = 7;\n  let y = m{read};"),
            key(26, k),
        )
    };
    assert_linear(at, |r| r.counts.stepped, 16, 16);
}

/// An index that changes a sibling of a chain of `n` stored nodes takes steps in `n`. The change
/// alters the root, and the read at the end of the chain decides if it holds the root. A part
/// with a hardware leaf is no static part, so that decision walks no path, and the change pays
/// its own width only. The kinds: `push` and `pop` of a sibling list, a call that changes a
/// static sibling in place or by a new value, and a call that rebinds a hardware sibling, in the
/// root or in the chain. The calls are constant work, so the fuel grows in `n` too.
#[test]
fn an_index_that_changes_a_sibling_takes_linear_steps() {
    let fns = "fn zero(mut ys: [Int; 2]) -> Int { ys[0] = 7; return 0; }\n\
fn bump(mut a: UInt[8]) -> Int { a = a +% 1; return 0; }\n\
fn repl(mut ys: [Int; 2]) -> Int { ys = [3, 4]; return 0; }\n";
    let kinds = [
        "(push(m.1, 0), 0).1",
        "(push(m.1, 0), pop(m.1), 0).2",
        "zero(m.2)",
        "repl(m.2)",
        "bump(m.3)",
        "(bump(m.0.b), 0).1",
    ];
    for (family, index) in (27..).zip(kinds) {
        let at = |n: u64, k: u64| {
            let place = rep(".a[0]", n + 1);
            let read = rep(&format!(".a[{index}]"), n + 1);
            run_ok(
                &format!(
                    "{fns}{}",
                    chain_decls(
                        n,
                        "struct S{i} { a: [S{}; 1], b: UInt[8], }\n",
                        "struct S{i} { a: [UInt[8]; 1], b: UInt[8], }\n",
                    )
                ),
                "(S0, UInt[8])",
                &format!(
                    "let mut m = (x.0, list(Int), [1, 2], x.1);\n  m.0{place} = 7;\n  let y = m.0{read};"
                ),
                key(family, k),
            )
        };
        assert_linear(at, |r| r.counts.stepped, 16, 16);
    }
}

/// A sibling push in an index of a read does not copy a parked part that the push leaves alone.
/// The read waits at the hardware array `m.0`, and each push goes to `m.1`, so no push copies
/// the array: the nodes that clones visit stay linear in the number of pushes and the width.
#[test]
fn a_sibling_push_in_an_index_copies_no_parked_part() {
    let at = |n: u64, k: u64| {
        let ws = (0..n).map(|_| "x").collect::<Vec<_>>().join(", ");
        let mut reads = String::new();
        for i in 0..n {
            let _ = write!(reads, "let k{i} = m.0[(m.1.push(0), 1).1];\n  ");
        }
        run_ok(
            "",
            "UInt[8]",
            &format!("let mut m = ([{ws}], list(Int), x);\n  {reads}"),
            key(40, k),
        )
    };
    assert_linear(at, |r| r.counts.nodes, 16, 16);
}

/// An index chain over static siblings takes steps in the depth. Each level `Si` holds the next
/// level and a static `Bool`, and the deepest leaf is hardware. The root has many static type
/// leaves, so no bound on them tells that a part holds a hardware leaf. The read has a `push`
/// into a sibling list at each level, and the decision of each level follows the witness to the
/// hardware leaf instead of walking the path from the root again.
#[test]
fn an_index_chain_over_static_siblings_takes_linear_steps() {
    let at = |n: u64, k: u64| {
        let place = rep(".a[0]", n + 1);
        let read = rep(".a[(m.1.push(0), 0).1]", n + 1);
        run_ok(
            &chain_decls(
                n,
                "struct S{i} { a: [S{}; 1], b: Bool, }\n",
                "struct S{i} { a: [UInt[8]; 1], b: Bool, }\n",
            ),
            "UInt[8]",
            &format!("let mut m = (S0(), list(Int));\n  m.0{place} = x;\n  let y = m.0{read};"),
            key(60, k),
        )
    };
    assert_linear(at, |r| r.counts.stepped, 16, 16);
}

/// The count `of` of the run `at(n)` at most doubles when the input doubles, up to a constant
/// `slack`. Unlike `assert_linear`, the count can be zero.
fn assert_doubles(at: impl Fn(u64, u64) -> Run, of: fn(&Run) -> u64, slack: u64) {
    let mut before: Option<u64> = None;
    for (k, n) in SIZES.into_iter().enumerate() {
        let count = of(&at(n, k as u64));
        if let Some(b) = before {
            assert!(count <= 2 * b + slack, "{n}: the work {b} grew to {count}");
        }
        before = Some(count);
    }
}

/// A read at a part of a hardware root, with a `push` into a list part of the root in its index,
/// copies no part of the root: the list changes in place, and the read resolves the change when
/// its last step is known. The copied size of the values stays at most linear in the number of
/// reads. The kinds: a sibling list, a list below a hardware node, and a `pop`.
#[test]
fn a_push_in_an_index_copies_no_list_for_a_read_that_misses_it() {
    let kinds = [
        ("(x, list(Nat))", "t[(t.1.push(1), 0).1];"),
        (
            "(x, list(Nat))",
            "t[(t.1.push(1), 0).1];\n    t[(t.1.pop(), 0).1];",
        ),
        ("((x, list(Nat)), [1, 2])", "t.0[(t.0.1.push(1), 0).1];"),
        (
            "(x, list(Nat))",
            "t[(t.1.push(1), t[(t.1.push(2), 0).1], 0).2];",
        ),
    ];
    for (family, (root, read)) in (61..).zip(kinds) {
        let at = |n: u64, k: u64| {
            run_ok(
                "",
                "UInt[8]",
                &format!("let mut t = {root};\n  comptime for i in 0..{n} {{\n    {read}\n  }}"),
                key(family, k),
            )
        };
        assert_doubles(at, |r| r.copied, 16);
        assert_linear(at, |r| r.counts.stepped, 16, 16);
    }
}

/// A step of a read goes into a list that the index of the same read changes. The read copies
/// the part where it waits, with the list as it was, and the held charge pays for the copy: the
/// copy undoes the changes that came before, so the old list comes back from the log. The copied
/// size is not zero, and it stays within the fuel.
#[test]
fn a_held_read_rebuilds_the_old_value_within_its_charge() {
    let at = |n: u64, k: u64| {
        run_ok(
            "",
            "UInt[8]",
            &format!(
                "let mut t: (UInt[8], [UInt[8]; 2], List[Nat]) =\n    (x, [UInt[8](1), UInt[8](2)], list(Nat));\n  \
                 t.2.push(7);\n  comptime for i in 0..{n} {{\n    t.2[(t.2.push(1), 0).1];\n  }}"
            ),
            key(70, k),
        )
    };
    for (k, n) in SIZES.into_iter().enumerate() {
        let r = at(n, k as u64);
        assert!(r.copied > 0, "{n}: no copy");
        assert!(
            r.copied <= r.units,
            "{n}: copied {} for {}",
            r.copied,
            r.units
        );
    }
}

/// A read that goes through the light part of a node misses its witness, and each miss walks the
/// path from the root once. Each light part has at most half the hardware leaves of its node, so
/// a read misses at most log2 of the leaves of the root plus one times. Here four levels near the
/// leaf have a heavier sibling of 2, 4, 8, and 16 leaves, and the levels above have a sibling of
/// one leaf. The read misses at four levels only, so its steps are linear in the depth `n`. A
/// walk from the root at each level would take steps in the square of `n`.
#[test]
fn a_read_through_light_parts_walks_a_path_for_each_halving_of_the_leaves() {
    let at = |n: u64, k: u64| {
        let decls: String = (0..=n)
            .map(|i| {
                if i == 0 {
                    "struct L0 { c: [UInt[8]; 1], h: [UInt[8]; 1], }\n".to_owned()
                } else {
                    let w = if i <= 4 { 1u64 << i } else { 1 };
                    format!("struct L{i} {{ c: [L{}; 1], h: [UInt[8]; {w}], }}\n", i - 1)
                }
            })
            .collect();
        let place = rep(".c[0]", n + 1);
        let read = rep(".c[(m.1.push(0), 0).1]", n + 1);
        run_ok(
            &decls,
            &format!("L{n}"),
            &format!("let mut m = (x, list(Int));\n  m.0{place} = 7;\n  let y = m.0{read};"),
            key(71, k),
        )
    };
    assert_linear(at, |r| r.counts.stepped, 16, 64);
}

/// A `push` or `pop` of an aggregate root visits no read that waits, however many reads wait.
/// The reads nest `k` deep, and the innermost index has `m` pushes. The push appends one entry,
/// and each read resolves once at its last step. Thus the entries handled are `m` for the
/// pushes and a constant for each read, and no read copies a part.
#[test]
fn a_push_visits_no_waiting_read() {
    let at = |k: u64, m: u64, family: u64| {
        let pushes = rep("t.1.push(1), ", m);
        let mut e = format!("({pushes}0).{m}");
        for _ in 0..k {
            e = format!("t[({e}, 0).1]");
        }
        run_ok(
            "",
            "UInt[8]",
            &format!("let mut t = (x, list(Nat));\n  {e};"),
            key(family, k * 8 + m % 8),
        )
    };
    for (family, k) in (76..).zip([2u64, 4, 8, 16]) {
        let run = at(k, 64, family);
        assert!(
            run.counts.logged <= 64 + 4 * k,
            "{k} reads: {}",
            run.counts.logged
        );
        assert_eq!(run.copied, 0, "{k} reads");
    }
    for (family, m) in (80..).zip([32u64, 64, 128]) {
        let run = at(8, m, family);
        assert!(
            run.counts.logged <= m + 32,
            "{m} pushes: {}",
            run.counts.logged
        );
    }
}

/// The zero of a chain of `n` nested singleton arrays clones no child that it drops: the clones
/// of its values are linear in `n`.
#[test]
fn the_zero_of_nested_singleton_arrays_clones_no_dropped_child() {
    let at = |n: u64, k: u64| {
        run_ok(
            &chain_decls(
                n,
                "struct S{i} { a: [S{}; 1], }\n",
                "struct S{i} { a: [Bool; 1], }\n",
            ),
            "UInt[8]",
            "let z = S0();",
            key(85, k),
        )
    };
    assert_doubles(at, |r| r.counts.cloned, 16);
}

/// The work of the reads that wait: the entries of the log that were handled, the steps of the
/// walks, the size of the values that a copy made, and the nodes that a clone visited.
fn waiting_work(r: &Run) -> u64 {
    r.counts.logged + r.counts.stepped + r.copied + r.counts.cloned + r.counts.nodes
}

/// The work of `at(n, i)` is the work with `m = n` changes of a root and `k = n / 8` reads that
/// wait at it. Doubling `n` at most doubles the work, up to a constant `slack`. The work of `k`
/// reads and `m` changes thus stays in `k + m` and not in `k * m`.
fn assert_scales(at: impl Fn(u64, u64) -> Run, slack: u64) {
    let mut before: Option<u64> = None;
    for (i, n) in SIZES.into_iter().enumerate() {
        let work = waiting_work(&at(n, i as u64));
        if let Some(b) = before {
            assert!(work <= 2 * b + slack, "{n}: the work {b} grew to {work}");
        }
        before = Some(work);
    }
}

/// Path 1 of #242: `k` reads nest, and each one selects the unchanged hardware part `t.0`. The
/// innermost index pushes `m` times into `t.1`. A read must not handle the whole window of
/// pushes again for each of the `k` reads.
#[test]
fn k_quiet_reads_and_m_pushes_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let pushes = rep("t.1.push(1), ", n);
        let mut e = format!("({pushes}0).{n}");
        for _ in 0..n / 8 {
            e = format!("t[({e}, 0).1]");
        }
        run_ok(
            "",
            "UInt[8]",
            &format!("let mut t = (x, list(Nat));\n  {e};"),
            key(90, i),
        )
    };
    assert_scales(at, 64);
}

/// Path 2 of #242: `k` plain references to `t.0` wait while `m` pushes change `t.1`. No push
/// visits a reference that its path does not reach.
#[test]
fn k_waiting_references_and_m_pushes_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let reads = rep("t.0, ", n);
        let pushes = rep("t.1.push(1), ", n);
        run_ok(
            "",
            "[UInt[8]; 2]",
            &format!(
                "let mut t = (x, list(Nat));\n  ({reads}{pushes}0).{};",
                2 * n
            ),
            key(91, i),
        )
    };
    assert_scales(at, 64);
}

/// Path 3 of #242: `k` reads nest, and the innermost index calls a function that writes the
/// whole root `t` back, with a list of `m` elements in it. The write binds the root again. The
/// `k` reads of the unchanged part `t.0` must not copy or replay the list for each read.
#[test]
fn k_reads_and_a_rebind_of_a_list_of_m_elements_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let mut e = "(set(t), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("t[({e}, 0).1]");
        }
        run_ok(
            "fn set(mut u: (UInt[8], List[Nat])) -> Int { u = (u.0, u.1); return 0; }\n",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut t: (UInt[8], List[Nat]) = (x, l);\n  {e};"
            ),
            key(92, i),
        )
    };
    assert_scales(at, 64);
}

/// The sweep of #242 for a static local: `k` references to the list `u.0` wait while `m` pushes
/// change the list `u.1`. No push visits a reference that its path does not reach, and no
/// reference copies its list.
#[test]
fn k_static_references_and_m_pushes_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let reads = rep("u.0, ", n);
        let pushes = rep("u.1.push(1), ", n);
        run_ok(
            "",
            "UInt[8]",
            &format!(
                "let mut u = (list(Nat), list(Nat));\n  ({reads}{pushes}0).{};",
                2 * n
            ),
            key(95, i),
        )
    };
    assert_scales(at, 64);
}

/// The old list of a read that an index of the same read changed is a result of the read: the
/// reads of a static list nest `k` deep, the innermost index pushes into the list, and the list
/// has `m` elements. Each read copies the list, and no charge pays for the copies (#237). Once
/// a charge pays for them, the copied size stays within the fuel.
#[test]
#[ignore = "#237"]
fn the_copies_of_an_old_list_that_a_read_finds_are_paid() {
    for (i, n) in SIZES.into_iter().enumerate() {
        let mut e = "(xs.push(0), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("xs[{e}]");
        }
        let r = run_ok(
            "",
            "UInt[8]",
            &format!(
                "let mut xs = list(Nat);\n  comptime for i in 0..{n} {{ xs.push(0); }}\n  {e};"
            ),
            key(93, i as u64),
        );
        assert!(
            r.copied <= r.units,
            "{n}: copied {} for {}",
            r.copied,
            r.units
        );
    }
}

/// The reads follow a write that bound the root again, and a later index of each read changes
/// the root again. The old root stays in the log: the hold decisions walk it and copy nothing.
/// The innermost index clears the list `t.1` of `m` elements, and the `k` reads of `t.0` nest.
#[test]
fn k_reads_that_decide_after_a_rebind_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let mut e = "(clear(t.1), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("t[({e}, 0).1][(t.1.push(1), 0).1]");
        }
        run_ok(
            "fn clear(mut l: List[Nat]) -> Int { l = list(Nat); return 0; }\n",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut t: ((UInt[8], Int), List[Nat]) = ((x, 0), l);\n  {e};"
            ),
            key(96, i),
        )
    };
    assert_scales(at, 64);
}

/// The same sweep with an assignment in the index: the index calls a function that replaces the
/// list `t.1` of `m` elements, below the `k` waiting reads of `t.0`.
#[test]
fn k_reads_and_an_assignment_in_an_index_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let mut e = "(clear(t.1), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("t[({e}, 0).1]");
        }
        run_ok(
            "fn clear(mut l: List[Nat]) -> Int { l = list(Nat); return 0; }\n",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut t: (UInt[8], List[Nat]) = (x, l);\n  {e};"
            ),
            key(94, i),
        )
    };
    assert_scales(at, 64);
}

/// A read that holds a static part of the root follows a write that bound the root again. The
/// hold decides at the static part `t.0`, and the read must still copy only the part where it
/// ends. The innermost index and a later index of each read clear the list `t.2` of `m` elements.
#[test]
fn k_held_reads_after_a_rebind_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let mut e = "(clear(t.2), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("t[({e}, 0).1][(clear(t.2), 0).1]");
        }
        run_ok(
            "fn clear(mut l: List[Nat]) -> Int { l = list(Nat); return 0; }\n",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut t: ((UInt[8], Int), UInt[8], List[Nat]) = ((0, 0), x, l);\n  {e};"
            ),
            key(97, i),
        )
    };
    assert_scales(at, 64);
}

/// The reads of a part of a static local nest `k` deep while the innermost index pushes into
/// another list of the local, which has `m` elements. A read copies at most the part where it
/// ends, so it copies none of the lists.
#[test]
fn k_reads_of_a_static_part_and_m_pushes_into_another_part_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let mut e = "(u.0.push(1), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("u.1[({e}, 0).1]");
        }
        run_ok(
            "",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut u = (l, [1, 2]);\n  {e};"
            ),
            key(98, i),
        )
    };
    assert_scales(at, 64);
}

/// A write that leaves an aggregate root with no hardware leaf copies the static rest of the
/// root once, and the charge that built the root pays for it. The `k` reads of `t.0` nest, the
/// innermost index replaces the hardware part, and the list `t.1` has `m` elements.
#[test]
fn k_reads_and_a_static_write_over_the_hardware_part_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let mut e = "(fix(t.0), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("t[({e}, 0).1]");
        }
        run_ok(
            "fn fix(mut v: UInt[8]) -> Int { v = UInt[8](3); return 0; }\n",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut t: (UInt[8], List[Nat]) = (x, l);\n  {e};"
            ),
            key(99, i),
        )
    };
    assert_scales(at, 64);
}

/// The largest step number is out of range, and the history of the local adds to it with a
/// check: a read of such an index is `S013` and does not overflow.
#[test]
fn the_largest_index_number_is_out_of_range_and_does_not_overflow() {
    let text = run_f(
        &assign_in(
            "UInt[8]",
            "let xs = [0];\n  let y = xs[18446744073709551615];",
        ),
        key(100, 0),
        FUEL,
        ref_x,
    );
    assert!(text.starts_with("S013 "), "{text}");
}

/// The reads of a list of a static local nest `k` deep, and the innermost index pushes into the
/// same list. Each read goes into a list that a change reached, so it copies a part, and that part
/// is the list and not the local: the sibling list `u.0` has `m` elements and no read copies it.
#[test]
#[ignore = "#242"]
fn k_reads_that_cross_a_changed_list_copy_only_that_list() {
    let at = |n: u64, i: u64| {
        let mut e = "(u.1.push(1), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("u.1[({e}, 0).1]");
        }
        run_ok(
            "",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut s = list(Nat);\n  s.push(0);\n  let mut u = (l, s);\n  {e};"
            ),
            key(101, i),
        )
    };
    assert_scales(at, 64);
}

/// A write gives a static local its first hardware leaf. The write copies the static rest of the
/// local once, and the held local charged its size before. The `k` reads of `t.1` nest, the
/// innermost index writes the hardware value `x` into `t.1`, and the list `t.0` has `m` elements.
#[test]
fn k_reads_and_a_hardware_write_into_a_static_local_take_work_in_k_plus_m() {
    let at = |n: u64, i: u64| {
        let mut e = "(put(t.1, x), 0).1".to_owned();
        for _ in 0..n / 8 {
            e = format!("t[({e}, 1).1]");
        }
        run_ok(
            "fn put(mut v: UInt[8], y: UInt[8]) -> Int { v = y; return 0; }\n",
            "UInt[8]",
            &format!(
                "let mut l = list(Nat);\n  comptime for i in 0..{n} {{ l.push(1); }}\n  \
                 let mut t: (List[Nat], UInt[8]) = (l, UInt[8](0));\n  {e};"
            ),
            key(102, i),
        )
    };
    assert_scales(at, 64);
}
