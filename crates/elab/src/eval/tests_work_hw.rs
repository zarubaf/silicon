// SPDX-License-Identifier: Apache-2.0
//! The work of the walks over hardware aggregates, as the work bound of design section 5.5
//! states it for the Rust front end: each walk visits a pair, a part, or a leaf after the unit
//! that pays for it, and a reference never expands. The tests count the steps of the walks with
//! the counters and not the time. Doubling the input at most doubles the count, and the count
//! stays within a constant times the fuel that the run charged.

use super::tests_bind::{assign_in, ref_x, run_f};
use crate::counters::{self, Counts};

const FUEL: u64 = 1_000_000_000_000;

/// A run: the counts of its walks and the fuel that it charged.
struct Run {
    counts: Counts,
    units: u64,
}

/// The run of `pre` and the statement `s` in the body of `f` with the formal `x` of the type
/// `t`. The number `run` keys the counters. A failed run gives its text.
fn run_with(pre: &str, t: &str, s: &str, run: u64) -> Result<Run, String> {
    let text = run_f(&format!("{pre}{}", assign_in(t, s)), run, FUEL, ref_x);
    match text.rsplit(" | ").next().map(str::parse::<u64>) {
        Some(Ok(units)) if text.contains(" | ") => Ok(Run {
            counts: counters::of(run),
            units,
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
            key(24, k),
        )
    };
    assert_linear(at, |r| r.counts.stepped, 16, 16);
}
