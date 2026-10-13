// SPDX-License-Identifier: Apache-2.0
//! The cases of a hardware `if` by leaf in `Silicon.Source.Test.Eval` in Lean (design sections
//! 5.4 and 7.4): the exact charges of the join, the walk, and each `mux` node, the mark of a
//! shared condition, the static pairs and their F19 rule, and the walk of a huge reference that
//! fails on the budget.

use super::Evaluator;
use super::tests_bind::{assign_in, int, name_of, node, ref_x, run_shown};
use crate::agg::Agg;
use crate::counters;
use crate::hw::{HwId, Op, Val};
use crate::names::{PathId, Step};
use crate::ops::{binop_text, unop_text};
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::Pos;

const AT: Pos = Pos { line: 1, col: 1 };
const ALL: u64 = 1_000_000;

/// A hardware value as its tree: a name, a constant, or an operator with its operands, also a
/// `mux` and the mark `share k` of a shared condition.
fn tree(ev: &Evaluator<'_>, h: HwId) -> String {
    let Some(n) = ev.graph.node(h) else {
        return String::new();
    };
    let xs: Vec<String> = n.args.iter().map(|x| tree(ev, *x)).collect();
    match &n.op {
        Op::Ref(p) => name_of(ev, *p),
        Op::Lit(v) => v.serialize(&ev.tys),
        Op::Mux => format!("(mux {})", xs.join(" ")),
        Op::Share(k) => format!("(share {k} {})", xs.join(" ")),
        Op::Un(op) => format!("({} {})", unop_text(*op), xs.join(" ")),
        Op::Bin(op) => format!("({} {})", binop_text(*op), xs.join(" ")),
        _ => "hardware".to_owned(),
    }
}

/// `y` is the expression `s` in the body of `f` with the formal `x` of the type `t`.
fn run_if(
    t: &str,
    s: &str,
    run: u64,
    fuel: u64,
    base: impl FnOnce(&mut Evaluator<'_>, PathId, TyId) -> Val,
) -> String {
    run_shown(&assign_in(t, s), run, fuel, base, tree)
}

/// The hardware leaf of the type `ty` at the steps `steps` below `x`.
fn leaf_at(ev: &mut Evaluator<'_>, p: PathId, steps: &[u64], ty: Ty) -> Agg {
    let q = steps
        .iter()
        .fold(p, |q, k| ev.paths.push(q, Step::Elem(*k)));
    Agg::Hw(ev.graph.mk(AT, ty, Op::Ref(q), Vec::new()))
}

const ARMS: &str = "(Bool, [UInt[8]; 2], [UInt[8]; 2])";

/// The exact charges of an `if` with array arms. The statement charges 1, the `if` node 1, and
/// each operand 2. The join charges 1 for the pair of arrays. The walk charges 1 for the root
/// pair, and each leaf pair charges 1 plus 4 for its `mux` node. `return true;` charges 4. The
/// condition `x.0` is a core name, so it gets no mark. `!x.0` gets the mark `share 0`, with no
/// charge, because the walk makes two `mux` nodes. One `mux` node and a `()` pair give no mark.
#[test]
fn an_if_with_array_arms_charges_the_join_the_pairs_and_the_muxes() {
    let r = |s: &str, run: u64, fuel: u64| run_if(ARMS, s, run, fuel, ref_x);
    assert_eq!(
        r("let y = if (x.0) { x.1 } else { x.2 };", 710_000_400, ALL),
        "y$0e=(mux x$0e x$1e$0e x$2e$0e) y$1e=(mux x$0e x$1e$1e x$2e$1e) | ref x | 24"
    );
    assert_eq!(counters::of(710_000_400).paired, 3);
    let negated = "let y = if (!x.0) { x.1 } else { x.2 };";
    assert_eq!(
        r(negated, 710_000_401, ALL),
        "y$0e=(mux (share 0 (! x$0e)) x$1e$0e x$2e$0e) \
         y$1e=(mux (share 0 (! x$0e)) x$1e$1e x$2e$1e) | ref x | 27"
    );
    assert_eq!(r(negated, 710_000_402, 22), "S015 2:11");
    assert_eq!(r(negated, 710_000_403, 23), "S015 3:3");
    assert_eq!(
        run_if(
            "(Bool, (UInt[8], ()), (UInt[8], ()))",
            negated,
            710_000_404,
            ALL,
            ref_x
        ),
        "y$0e=(mux (! x$0e) x$1e$0e x$2e$0e) | ref x | 23"
    );
}

/// Two static leaves of a data type are a leaf pair: they make a `mux` of constants, and each
/// such `mux` counts for the mark. A static list pair compares by the static equality of `==`,
/// so `[1]` equals the typed list `xs`, and the result has the joined type.
#[test]
fn static_leaves_make_muxes_and_static_lists_compare_by_equality() {
    let r = |s: &str, run: u64| run_if(ARMS, s, run, ALL, ref_x);
    assert_eq!(
        r(
            "let a: [UInt[8]; 2] = [1, 2];\n  let y = if (!x.0) { a } else { [3, 4] };",
            710_000_410
        ),
        "y$0e=(mux (share 0 (! x$0e)) (uint 8 1) (uint 8 3)) \
         y$1e=(mux (share 0 (! x$0e)) (uint 8 2) (uint 8 4)) | ref x | 67"
    );
    let lists = |k: u32| {
        format!(
            "let mut xs = list(UInt[8]);\n  push(xs, 1);\n  let mut ys = list(Int);\n  \
             push(ys, {k});\n  let y = if (x.0) {{ ys }} else {{ xs }};"
        )
    };
    assert_eq!(
        r(
            &format!("{}\n  let z: List[UInt[8]] = y;", lists(1)),
            710_000_411
        ),
        " | ref x | 62"
    );
    assert_eq!(r(&lists(2), 710_000_412), "S011 6:11");
}

/// Each mark of one instantiation takes the next number.
#[test]
fn each_mark_of_an_instantiation_takes_the_next_number() {
    assert_eq!(
        run_if(
            ARMS,
            "let y = if (!x.0) { x.1 } else { x.2 };\n  let z = if (!x.0) { x.2 } else { x.1 };",
            710_000_420,
            ALL,
            ref_x
        ),
        "y$0e=(mux (share 0 (! x$0e)) x$1e$0e x$2e$0e) \
         y$1e=(mux (share 0 (! x$0e)) x$1e$1e x$2e$1e) \
         z$0e=(mux (share 1 (! x$0e)) x$2e$0e x$1e$0e) \
         z$1e=(mux (share 1 (! x$0e)) x$2e$1e x$1e$1e) | ref x | 50"
    );
}

/// A record descends by its named fields. The join of two struct types charges as a type
/// equality, the sum of the two sizes 1 + 1, instead of 1.
#[test]
fn a_record_descends_by_its_fields_and_joins_as_a_type_equality() {
    let src = format!(
        "struct S {{ a: UInt[8], b: Bool }}\n{}",
        assign_in("(Bool, S, S)", "let y = if (!x.0) { x.1 } else { x.2 };")
    );
    assert_eq!(
        run_shown(&src, 710_000_430, ALL, ref_x, tree),
        "y$a=(mux (share 0 (! x$0e)) x$1e$a x$2e$a) y$b=(mux (share 0 (! x$0e)) x$1e$b x$2e$b) \
         | ref x | 28"
    );
}

/// The tuple `(Bool, Int)` with a hardware first part and a static second part.
pub(super) fn int_part(ev: &mut Evaluator<'_>, p: PathId, t: TyId) -> Val {
    let bit = leaf_at(ev, p, &[0], Ty::Bool);
    node(ev, t, vec![bit, Agg::Static(int(0))])
}

/// Scalar arms keep the rule of slice 1: no join charge and no walk unit. Two arms of type `()`
/// give `()`. Two static arms of a type that is not hardware data are a static pair (F19). It
/// charges the sum of the sizes, here 1 + 1. Equal arms give the static value, and different
/// arms are `S011` at the `if`. An `Int` arm and a `Bool` arm have no join, so they are `S010`.
/// The assignment `x.1 = ...` binds the hardware leaf of `x` again, at the next version.
#[test]
fn scalar_arms_keep_the_rule_of_slice_one_and_static_pairs_follow_f19() {
    let r = |s: &str, run: u64, fuel: u64| run_if("(Bool, Int)", s, run, fuel, int_part);
    assert_eq!(
        run_if(
            "(Bool, UInt[8])",
            "let y = if (!x.0) { () } else { () };",
            710_000_440,
            ALL,
            ref_x
        ),
        " | ref x | 15"
    );
    let same = "x.1 = if (x.0) { 3 } else { 3 };";
    assert_eq!(
        r(same, 710_000_441, ALL),
        "x$1v$0e=x$0e | [x$1v$0e, (int 3)] | 18"
    );
    assert_eq!(r(same, 710_000_442, 11), "S015 2:3");
    let differ = "x.1 = if (x.0) { 3 } else { 4 };";
    assert_eq!(r(differ, 710_000_443, 10), "S015 2:9");
    assert_eq!(r(differ, 710_000_444, 11), "S011 2:9");
    assert_eq!(
        r(
            "let y = if (x.0) { \"a\" } else { \"a\" };",
            710_000_445,
            ALL
        ),
        " | [x$0e, (int 0)] | 18"
    );
    let errors = [
        ("let y = if (x.0) { \"a\" } else { \"b\" };", "S011 2:11"),
        ("let y = if (x.0) { 3 } else { true };", "S010 2:11"),
        ("let y = if (x.0) { () } else { 3 };", "S010 2:11"),
    ];
    for (k, (s, code)) in errors.into_iter().enumerate() {
        assert_eq!(r(s, 710_000_446 + k as u64, ALL), code, "{s}");
    }
}

/// A tuple of the type `(Bool, (Int, Int, UInt[8]), (Int, Int, UInt[8]))` whose static parts
/// are 5 and 6 on the left and 5 and `u` on the right.
fn static_arms(u: i64) -> impl FnOnce(&mut Evaluator<'_>, PathId, TyId) -> Val {
    move |ev, p, t| {
        let bit = leaf_at(ev, p, &[0], Ty::Bool);
        let parts = [Ty::Int, Ty::Int, Ty::UInt(8)].map(|u| ev.tys.mk(u));
        let ts = ev.tys.tuple(parts.to_vec());
        let left = leaf_at(ev, p, &[1, 2], Ty::UInt(8));
        let right = leaf_at(ev, p, &[2, 2], Ty::UInt(8));
        let a = node(ev, ts, vec![Agg::Static(int(5)), Agg::Static(int(6)), left]);
        let b = node(
            ev,
            ts,
            vec![Agg::Static(int(5)), Agg::Static(int(u)), right],
        );
        let (Ok(a), Ok(b)) = (Agg::of_val(a), Agg::of_val(b)) else {
            return Val::Static(Value::Unit);
        };
        node(ev, t, vec![bit, a, b])
    }
}

/// A static pair in an aggregate. Equal sides give the value, and a hardware pair beside them
/// makes a `mux`. The first static pair whose sides differ is `S011` at the `if`, and the walk
/// stops there. The units up to that pair are 16. The statement, the `if`, and the three
/// operands charge 8. The join of the tuples and the root pair charge 1 each. Each static pair
/// charges 1 + 2. Thus the fuel 16 gives `S011`, and the `mux` of the third pair never charges.
#[test]
fn the_first_differing_static_pair_stops_the_walk() {
    let t = "(Bool, (Int, Int, UInt[8]), (Int, Int, UInt[8]))";
    assert_eq!(
        run_if(
            t,
            "let y = if (!x.0) { x.1 } else { x.2 };",
            710_000_450,
            ALL,
            static_arms(6)
        ),
        "y$2e=(mux (! x$0e) x$1e$2e x$2e$2e) | [x$0e, [(int 5), (int 6), x$1e$2e], \
         [(int 5), (int 6), x$2e$2e]] | 28"
    );
    let differ = "let y = if (x.0) { x.1 } else { x.2 };";
    assert_eq!(
        run_if(t, differ, 710_000_451, ALL, static_arms(7)),
        "S011 2:11"
    );
    assert_eq!(
        run_if(t, differ, 710_000_452, 15, static_arms(7)),
        "S015 2:11"
    );
    assert_eq!(
        run_if(t, differ, 710_000_453, 16, static_arms(7)),
        "S011 2:11"
    );
}

/// The walk charges each pair before it visits it, and a reference never expands. Thus an `if`
/// with two references to a huge array fails on the budget in the walk.
#[test]
fn an_if_of_two_huge_references_fails_in_the_walk() {
    let run = 710_000_460;
    assert_eq!(
        run_if(
            "(Bool, [UInt[8]; 1 << 40], [UInt[8]; 1 << 40])",
            "let y = if (x.0) { x.1 } else { x.2 };",
            run,
            ALL,
            ref_x
        ),
        "S015 2:11"
    );
    assert!(counters::of(run).paired <= ALL);
}

/// The walk visits one pair for the root and one for each element, and it builds one node for
/// each leaf: the work grows with the pairs that the charge paid for.
#[test]
fn the_walk_of_an_if_counts_its_pairs() {
    let run = 710_000_470;
    let r = run_if(
        "(Bool, [UInt[8]; 40], [UInt[8]; 40])",
        "let y = if (x.0) { x.1 } else { x.2 };",
        run,
        ALL,
        ref_x,
    );
    assert!(r.ends_with(" | ref x | 214"), "{r}");
    assert_eq!(counters::of(run).paired, 41);
}
