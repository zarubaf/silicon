// SPDX-License-Identifier: Apache-2.0
//! The cases of `==` and `!=` on a hardware aggregate in `Silicon.Source.Test.Eval` in Lean
//! (design sections 5.4 and 7.4): the exact charges of the join, the walk, and the chain, the
//! parts that mix static and hardware pairs, the order of the errors, and the walk of a huge
//! reference that fails on the budget before the chain exists.

use super::Evaluator;
use super::tests_bind::{assign_in, int, leaf_x, name_of, node, ref_x, run_shown};
use crate::agg::Agg;
use crate::counters;
use crate::hw::Op::Bin;
use crate::hw::{HwId, Op, Val};
use crate::names::PathId;
use crate::ops::binop_text;
use crate::types::{Ty, TyId};
use crate::value::Value;

/// A hardware value as its tree: a name, a constant, or an operator with its operands.
fn tree(ev: &Evaluator<'_>, h: HwId) -> String {
    let Some(n) = ev.graph.node(h) else {
        return String::new();
    };
    match &n.op {
        Op::Ref(p) => name_of(ev, *p),
        Op::Lit(v) => v.serialize(&ev.tys),
        Bin(op) => {
            let xs: Vec<String> = n.args.iter().map(|x| tree(ev, *x)).collect();
            format!("({} {})", binop_text(*op), xs.join(" "))
        }
        _ => "hardware".to_owned(),
    }
}

/// `y` is the expression `e` in the body of `f` with the formal `x`. The units count the
/// statement and the operands too.
fn run_eq(
    t: &str,
    e: &str,
    run: u64,
    fuel: u64,
    base: impl FnOnce(&mut Evaluator<'_>, PathId, TyId) -> Val + Send,
) -> String {
    let src = assign_in(t, &format!("let y = {e};"));
    run_shown(&src, run, fuel, base, tree)
}

const ALL: u64 = 1_000_000;

/// The exact charges of `x == x`. The statement and the operands charge 4, the join 1, and the
/// root pair 1. Each leaf pair charges 1 plus 3 for its `icmp` node. The `and` node charges 3
/// after the walk. `return true;` charges 4. `!=` adds the `xor` node last, 3 more. The chain
/// charges after the walk, so at the fuel 16 it fails at the operator, and at 17 only the
/// `return` fails.
#[test]
fn the_equality_of_two_references_charges_the_join_the_pairs_and_the_chain() {
    let t = "(UInt[8], Bool)";
    assert_eq!(
        run_eq(t, "x == x", 700_000_400, ALL, ref_x),
        "y=(& (== x$0e x$0e) (== x$1e x$1e)) | ref x | 21"
    );
    assert_eq!(
        run_eq(t, "x != x", 700_000_401, ALL, ref_x),
        "y=(^ (& (== x$0e x$0e) (== x$1e x$1e)) (bool true)) | ref x | 24"
    );
    assert_eq!(run_eq(t, "x == x", 700_000_402, 16, ref_x), "S015 2:11");
    assert_eq!(run_eq(t, "x == x", 700_000_403, 17, ref_x), "S015 3:3");
    assert_eq!(counters::of(700_000_400).paired, 3);
}

/// A reference pairs leaf by leaf through its type, also in nested containers and records. `()`
/// adds no pair to the chain. A reference against a literal: each static leaf converts to the
/// type of its pair with its conversion charge, here 2 for `3`, before its `icmp`.
#[test]
fn a_reference_pairs_leaf_by_leaf_also_against_a_literal() {
    assert_eq!(
        run_eq("[[UInt[8]; 2]; 2]", "x == x", 700_000_410, ALL, ref_x),
        "y=(& (& (& (== x$0e$0e x$0e$0e) (== x$0e$1e x$0e$1e)) (== x$1e$0e x$1e$0e)) \
         (== x$1e$1e x$1e$1e)) | ref x | 38"
    );
    assert_eq!(
        run_eq("(Bool, ())", "x == (true, ())", 700_000_411, ALL, ref_x),
        "y=(== x$0e (bool true)) | ref x | 22"
    );
    assert_eq!(
        run_eq("[UInt[8]; 2]", "x == [1, 2]", 700_000_412, ALL, ref_x),
        "y=(& (== x$0e (uint 8 1)) (== x$1e (uint 8 2))) | ref x | 32"
    );
    assert_eq!(
        run_eq("(UInt[8], Bool)", "x == (3, true)", 700_000_413, ALL, ref_x),
        "y=(& (== x$0e (uint 8 3)) (== x$1e (bool true))) | ref x | 30"
    );
    let src = format!(
        "struct S {{ a: UInt[8], b: Bool }}\n{}",
        assign_in("S", "let y = x == S(1, true);")
    );
    assert_eq!(
        run_shown(&src, 700_000_414, ALL, ref_x, tree),
        "y=(& (== x$a (uint 8 1)) (== x$b (bool true))) | ref x | 34"
    );
}

/// The tuple `(UInt[8], Int, List[Int])` with a hardware first part and two static parts.
fn mixed(ev: &mut Evaluator<'_>, p: PathId, t: TyId) -> Val {
    let a = leaf_x(ev, p, 0);
    let list = Value::List(ev.tys.mk(Ty::Int), vec![int(1)]);
    node(ev, t, vec![a, Agg::Static(int(3)), Agg::Static(list)])
}

/// Static and hardware parts mix. A static pair charges as a static equality, and its result
/// goes into `s`. Thus the chain starts at `(const 1 s)`. `s` is 0 when a static pair differs,
/// also by the length of a list. The operands can take either side.
#[test]
fn static_and_hardware_pairs_mix_with_the_free_constant() {
    let t = "(UInt[8], Int, List[Int])";
    let shape = "[x$0e, (int 3), (list int ((int 1)))]";
    let cases = [
        (
            "x == (5, 3, x.2)",
            "y=(& (bool true) (== x$0e (uint 8 5)))",
            39,
        ),
        (
            "x == (5, 4, x.2)",
            "y=(& (bool false) (== x$0e (uint 8 5)))",
            39,
        ),
        (
            "x != (5, 3, list(Int))",
            "y=(^ (& (bool false) (== x$0e (uint 8 5))) (bool true))",
            43,
        ),
        (
            "(5, 3, list(Int)) == x",
            "y=(& (bool false) (== (uint 8 5) x$0e))",
            40,
        ),
    ];
    for (k, (e, lets, units)) in cases.into_iter().enumerate() {
        let run = 700_000_420 + k as u64;
        assert_eq!(
            run_eq(t, e, run, ALL, mixed),
            format!("{lets} | {shape} | {units}"),
            "{e}"
        );
    }
}

/// The order of the errors. The function flag comes first: with the fuel 42 the operands are
/// done, and the flag fails with no charge of the operator. The join comes next: it charges 1
/// for the pair of arrays and fails, before any walk unit. The walk then visits the pairs in
/// order: the second pair fails its fit after its conversion charge.
#[test]
fn the_errors_come_in_the_order_of_the_flag_the_join_and_the_walk() {
    let r = |t: &str, e: &str, run: u64, fuel: u64| run_eq(t, e, run, fuel, ref_x);
    assert_eq!(
        r("(UInt[8], Bool)", "x == (1, f)", 700_000_430, 41),
        "S015 2:16"
    );
    assert_eq!(
        r("(UInt[8], Bool)", "x == (1, f)", 700_000_431, 42),
        "S010 2:11"
    );
    assert_eq!(
        r("[UInt[8]; 2]", "x == [1, 2, 3]", 700_000_432, 14),
        "S015 2:11"
    );
    assert_eq!(
        r("[UInt[8]; 2]", "x == [1, 2, 3]", 700_000_433, 15),
        "S010 2:11"
    );
    assert_eq!(
        r("(UInt[8], UInt[8])", "x == (3, 300)", 700_000_434, 21),
        "S015 2:11"
    );
    assert_eq!(
        r("(UInt[8], UInt[8])", "x == (3, 300)", 700_000_435, 22),
        "S012 2:11"
    );
    assert_eq!(
        r("(UInt[8], Bool)", "x == 3", 700_000_436, ALL),
        "S010 2:11"
    );
    assert_eq!(r("(UInt[8], Bool)", "x < x", 700_000_437, ALL), "S010 2:11");
}

/// The walk charges each pair before it visits it, and a reference never expands. Thus `==` of
/// two references to a huge array fails on the budget in the walk, before the chain exists.
#[test]
fn the_equality_of_two_huge_references_fails_in_the_walk() {
    let run = 700_000_440;
    assert_eq!(
        run_eq("[UInt[8]; 1 << 40]", "x == x", run, ALL, ref_x),
        "S015 2:11"
    );
    assert!(counters::of(run).paired <= ALL);
}
