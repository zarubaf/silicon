// SPDX-License-Identifier: Apache-2.0
//! The cases of a hardware `match` in `Silicon.Source.Test.Eval` in Lean (design sections 5.4
//! and 7.4): the exact charges of the marks, the binders, the selects, the join, and the
//! `onehot` node of each leaf, the static parts and their `S011`, and the nested `match` that
//! grows linearly. The tests count the work of each walk and not the time.

use super::Evaluator;
use super::tests_bind::{assign_in, name_of, ref_x, run_shown};
use crate::hw::{HwId, Op};
use crate::ops::{binop_text, unop_text};

const OPS: &str = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }\n";
const TRI: &str = "(Bool, UInt[8], UInt[8])";
const ALL: u64 = 1_000_000;

/// A hardware value as its tree: a name, a constant, or an operator with its operands, also the
/// nodes of a `match` and the mark `share k` of a shared operand.
fn tree(ev: &Evaluator<'_>, h: HwId) -> String {
    let Some(n) = ev.graph.node(h) else {
        return String::new();
    };
    let xs: Vec<String> = n.args.iter().map(|x| tree(ev, *x)).collect();
    let node = |name: &str| {
        if xs.is_empty() {
            format!("({name})")
        } else {
            format!("({name} {})", xs.join(" "))
        }
    };
    match &n.op {
        Op::Ref(p) => name_of(ev, *p),
        Op::Lit(v) => v.serialize(&ev.tys),
        Op::Onehot => node("onehot"),
        Op::Rest => node("rest"),
        Op::Extract { off, w } => node(&format!("extract {off} {w}")),
        Op::Share(k) => node(&format!("share {k}")),
        Op::Un(op) => node(unop_text(*op)),
        Op::Bin(op) => node(binop_text(*op)),
        Op::Pack(w) => node(&format!("pack {w}")),
        Op::Resize => node("resize"),
        _ => "hardware".to_owned(),
    }
}

/// `y` is the expression `s` in the body of `f` with the formal `x` of the type `t`, after the
/// items `src`.
fn run_match(t: &str, s: &str, src: &str, run: u64, fuel: u64) -> String {
    let text = format!("{src}{}", assign_in(t, s));
    run_shown(&text, run, fuel, ref_x, tree)
}

/// The exact charges of a `match` with one leaf, one arm that is not `_`, and `_`. The statement
/// charges 1, the `match` node 1, and the scrutinee 2. The pattern `true` charges 2 and its share
/// `1 + 0 + 1`, and `_` charges 1. Each arm charges 2. The select `s_0` has `L + 1 = 2` uses, so
/// its mark charges the size 3 of `(== x$0e true)`. The scrutinee is a core name, and `n` is 1,
/// so it gets no mark. The node `rest` charges `1 + 1`, and with `L = 1` it gets no mark. The
/// node `onehot` charges `1 + 2 * 2`. `return true;` charges 4.
#[test]
fn one_leaf_with_a_wild_arm_charges_the_marks_and_the_nodes() {
    let one_leaf = "let y = match (x.0) { true => x.1, _ => x.2 };";
    let total = 1 + 1 + 2 + 2 + 2 + 1 + 2 + 2 + 3 + 2 + 5 + 4;
    assert_eq!(
        run_match(TRI, one_leaf, "", 720_000_001, ALL),
        format!(
            "y=(onehot (share 0 (== x$0e (bool true))) (rest (share 0 (== x$0e (bool true)))) \
             x$1e x$2e) | ref x | {total}"
        )
    );
    assert_eq!(run_match(TRI, one_leaf, "", 720_000_002, 22), "S015 2:11");
    assert_eq!(run_match(TRI, one_leaf, "", 720_000_003, 23), "S015 3:3");
}

/// Without `_`, a select has `L = 1` use and gets no mark, and no `rest` node exists. With two
/// arms that are not `_`, the scrutinee `x.1 +% 1` gets the mark `share 0`, for the size 3 of its
/// node. Each select has two uses and gets a mark, in arm order. `rest` reads both selects and
/// charges `1 + 2`. The node `onehot` charges `1 + 2 * 3`.
#[test]
fn selects_get_marks_by_their_uses_in_arm_order() {
    assert_eq!(
        run_match(
            TRI,
            "let y = match (x.0) { true => x.1, false => x.2 };",
            "",
            720_000_010,
            ALL
        ),
        "y=(onehot (== x$0e (bool true)) (== x$0e (bool false)) x$1e x$2e) | ref x | 27"
    );
    assert_eq!(
        run_match(
            TRI,
            "let y = match (x.1 +% 1) { 0 => x.1, 1 => x.2, _ => x.1 };",
            "",
            720_000_011,
            ALL
        ),
        "y=(onehot (share 1 (== (share 0 (+% x$1e (uint 8 1))) (uint 8 0))) \
         (share 2 (== (share 0 (+% x$1e (uint 8 1))) (uint 8 1))) \
         (rest (share 1 (== (share 0 (+% x$1e (uint 8 1))) (uint 8 0))) \
         (share 2 (== (share 0 (+% x$1e (uint 8 1))) (uint 8 1)))) x$1e x$2e x$1e) | ref x | 52"
    );
}

/// A joined type with two leaves walks the arms by position, one `onehot` node for each leaf.
/// The select `rest` has two uses, so it gets a mark. One arm `_` gives its value with no node.
/// The static part of each arm must be equal (F19): the arms `(1, x.1)` and `(2, x.2)` are `S011`
/// at the `match`, and equal static parts give the static value.
#[test]
fn a_joined_type_with_two_leaves_has_one_onehot_for_each() {
    let tree2 = |s: &str, run: u64| run_match(TRI, s, "", run, ALL);
    assert_eq!(
        tree2(
            "let y = match (x.0) { true => (x.1, x.2), _ => (x.2, x.1) };",
            720_000_020
        ),
        "y$0e=(onehot (share 0 (== x$0e (bool true))) \
         (share 1 (rest (share 0 (== x$0e (bool true))))) x$1e x$2e) \
         y$1e=(onehot (share 0 (== x$0e (bool true))) \
         (share 1 (rest (share 0 (== x$0e (bool true))))) x$2e x$1e) | ref x | 50"
    );
    assert_eq!(
        tree2("let y = match (x.0) { _ => x.2 };", 720_000_021),
        "y=x$2e | ref x | 12"
    );
    assert_eq!(
        tree2(
            "let y = match (x.0) { true => (1, x.1), _ => (2, x.2) };",
            720_000_022
        ),
        "S011 2:11"
    );
    assert_eq!(
        tree2(
            "let y = match (x.0) { true => (1, x.1), _ => (1, x.2) };",
            720_000_023
        ),
        "y$1e=(onehot (share 0 (== x$0e (bool true))) (rest (share 0 (== x$0e (bool true)))) \
         x$1e x$2e) | ref x | 45"
    );
}

/// An enum with a static tag is a hardware scrutinee (G7): its selects compare two constants.
/// The binder `v` is one `extract` of the payload, bound as a `let`. The arm `0` converts to the
/// joined type `UInt[8]`. When the binders of all arms have two or more leaves, the payload gets
/// a mark: here `v`, `a`, and `b` read the `pack` node of the constructor. The tag is a
/// constant, so it gets no mark.
#[test]
fn an_enum_with_a_static_tag_is_a_hardware_scrutinee() {
    assert_eq!(
        run_match(
            TRI,
            "let o = Op::Load(x.1);\n  let y = match (o) { Op::Load(v) => v, _ => 0 };",
            OPS,
            720_000_030,
            ALL
        ),
        "o$payload=(pack 8 x$1e) v=(extract 0 8 o$payload) \
         y=(onehot (share 0 (== (uint 2 1) (uint 2 1))) \
         (rest (share 0 (== (uint 2 1) (uint 2 1)))) v (uint 8 0)) | ref x | 108"
    );
    assert_eq!(
        run_match(
            TRI,
            "let y = match (Op::Load(x.1)) { Op::Load(v) => v, \
             Op::Pair(a, b) => resize(UInt[8], b), _ => 0 };",
            OPS,
            720_000_031,
            ALL
        ),
        "v=(extract 0 8 (share 0 (pack 8 x$1e))) a=(extract 0 1 (share 0 (pack 8 x$1e))) \
         b=(extract 1 4 (share 0 (pack 8 x$1e))) y=(onehot (share 1 (== (uint 2 1) (uint 2 1))) \
         (share 2 (== (uint 2 1) (uint 2 2))) (rest (share 1 (== (uint 2 1) (uint 2 1))) \
         (share 2 (== (uint 2 1) (uint 2 2)))) v (resize b) (uint 8 0)) | ref x | 142"
    );
}

const BIG: &str = "enum E: UInt[1] { A([[(); 4096]; 4096]) = 0, \
                   B([[(); 4096]; 4096], UInt[8]) = 1 }\n";
const BIG_T: &str = "(Bool, UInt[1], UInt[9])";
const BIG_TREE: &str = "(onehot (share 0 (== (extract 0 1 x$2e) (uint 1 0))) \
                        (rest (share 0 (== (extract 0 1 x$2e) (uint 1 0)))) x$0e (bool false)) \
                        | ref x | ";

/// A hardware binder charges the zero size of its type first (G5). A payload part
/// `[[(); 4096]; 4096]` has no leaf, so it binds a static value with no node, and the binder pays
/// `1 + 4096 * 4097`, as in a static `match`. A part with a leaf is an `extract`.
#[test]
fn a_hardware_binder_pays_the_zero_size_of_its_type_first() {
    let big = |s: &str, run: u64| run_match(BIG_T, s, BIG, run, 100_000_000);
    assert_eq!(
        big(
            "let y = match (reinterpret(E, x.2)) { E::A(_) => x.0, _ => false };",
            720_000_040
        ),
        format!("y={BIG_TREE}131")
    );
    assert_eq!(
        big(
            "let y = match (reinterpret(E, x.2)) { E::A(z) => x.0, _ => false };",
            720_000_041
        ),
        format!("y={BIG_TREE}{}", 131 + 1 + 4096 * 4097)
    );
    assert_eq!(
        big(
            "let y = match (reinterpret(E, x.2)) { E::B(z, b) => b, _ => 2 };",
            720_000_042
        ),
        format!(
            "b=(extract 0 8 (extract 1 8 x$2e)) y=(onehot (share 0 (== (extract 0 1 x$2e) \
             (uint 1 1))) (rest (share 0 (== (extract 0 1 x$2e) (uint 1 1)))) b (uint 8 2)) \
             | ref x | {}",
            136 + 1 + 4096 * 4097
        )
    );
}

/// `k` nested `match (match (c) { true => p, _ => q }) { true => p, _ => q }` grow linearly (D7):
/// each level adds 8 nodes and charges 25, because the `+ 1` use of each select marks it.
/// `count` counts each mark and its operand once.
#[test]
fn nested_matches_grow_linearly() {
    fn count(ev: &Evaluator<'_>, h: HwId, seen: &mut Vec<u64>) -> u64 {
        let mut total = 0;
        let mut work = vec![h];
        while let Some(h) = work.pop() {
            let Some(n) = ev.graph.node(h) else {
                continue;
            };
            total += 1;
            if let Op::Share(k) = n.op {
                if seen.contains(&k) {
                    continue;
                }
                seen.push(k);
            }
            work.extend(n.args.iter().rev());
        }
        total
    }
    fn nodes(ev: &Evaluator<'_>, h: HwId) -> String {
        count(ev, h, &mut Vec::new()).to_string()
    }
    let nest = |k: u64| {
        let mut e = "x.0".to_owned();
        for _ in 0..k {
            e = format!("match ({e}) {{ true => x.1, _ => x.2 }}");
        }
        e
    };
    let at = |k: u64, run: u64| {
        run_shown(
            &assign_in("(Bool, Bool, Bool)", &format!("let y = {};", nest(k))),
            run,
            100_000_000,
            ref_x,
            nodes,
        )
    };
    for k in 1..=5 {
        assert_eq!(
            at(k, 720_000_050 + k),
            format!("y={} | ref x | {}", 1 + 8 * k, 2 + 25 * k),
            "{k}"
        );
    }
    assert_eq!(
        at(40, 720_000_060),
        format!("y={} | ref x | {}", 1 + 8 * 40, 2 + 25 * 40)
    );
}

/// A hardware tag with two arms that are not `_` gets the mark `share 0`, then the payload gets
/// `share 1`. Two arms with the binder `v` give the core names `v` and `v$1v`.
#[test]
fn a_hardware_tag_and_payload_get_marks_and_the_binders_get_core_names() {
    let tag = |a: &str, run: u64| {
        run_match(
            "(Bool, UInt[8], UInt[10])",
            &format!(
                "let y = match (reinterpret(Op, x.2)) {{ Op::Load(v) => v, \
                 Op::Pair({a}, b) => resize(UInt[8], b), _ => 0 }};"
            ),
            OPS,
            run,
            ALL,
        )
    };
    let tree = "y=(onehot (share 2 (== (share 0 (extract 0 2 x$2e)) (uint 2 1))) \
                (share 3 (== (share 0 (extract 0 2 x$2e)) (uint 2 2))) \
                (rest (share 2 (== (share 0 (extract 0 2 x$2e)) (uint 2 1))) \
                (share 3 (== (share 0 (extract 0 2 x$2e)) (uint 2 2)))) v (resize b) \
                (uint 8 0)) | ref x | 143";
    assert_eq!(
        tag("a", 720_000_070),
        format!(
            "v=(extract 0 8 (share 1 (extract 2 8 x$2e))) \
             a=(extract 0 1 (share 1 (extract 2 8 x$2e))) \
             b=(extract 1 4 (share 1 (extract 2 8 x$2e))) {tree}"
        )
    );
    assert_eq!(
        tag("v", 720_000_071),
        format!(
            "v=(extract 0 8 (share 1 (extract 2 8 x$2e))) \
             v$1v=(extract 0 1 (share 1 (extract 2 8 x$2e))) \
             b=(extract 1 4 (share 1 (extract 2 8 x$2e))) {tree}"
        )
    );
}

/// Arms without a common type are `S010` at the `match`. A binder with a zero size above 2^32 is
/// `S015` at the binder, before its charge. An arm runs under the guard `arm`, so a `push` to a
/// list from before the `match` is `S016`. One arm `_` charges the node 1, the scrutinee 2, and
/// the pattern 1 on top of its value: `let y = x.2;` charges 8.
#[test]
fn the_arms_have_a_common_type_and_run_under_the_guard() {
    assert_eq!(
        run_match(
            TRI,
            "let y = match (x.0) { true => x.1, _ => (x.1, x.2) };",
            "",
            720_000_080,
            ALL
        ),
        "S010 2:11"
    );
    let huge = "enum E: UInt[1] { A = 0, B([[[(); 65536]; 65536]; 2], UInt[8]) = 1 }\n";
    assert_eq!(
        run_match(
            BIG_T,
            "let y = match (reinterpret(E, x.2)) { E::B(z, b) => b, _ => 2 };",
            huge,
            720_000_081,
            ALL
        ),
        "S015 3:46"
    );
    assert_eq!(
        run_match(
            TRI,
            "let mut xs = list(Int);\n  let y = match (x.0) { true => xs.push(1), _ => () };",
            "",
            720_000_082,
            ALL
        ),
        "S016 3:33"
    );
    assert_eq!(
        run_match(TRI, "let y = x.2;", "", 720_000_083, ALL),
        "y=x$2e | ref x | 8"
    );
}

/// The walk of `match_join` with two tuple arms of a static `Int` and a hardware leaf. The join
/// charges 1, the select mark 3, and `rest` 2. The root charges 1, the static position 1 and its
/// equality `1 + 1`, and the leaf position 1 and its `onehot` node 5. Different static parts are
/// `S011` with the text of section 6.2.
#[test]
fn the_walk_compares_the_static_parts_of_the_arms() {
    use super::tests_bind::{evaluator, node, tuple_of};
    use crate::agg::Agg;
    use crate::int::Int;
    use crate::tests_elab::load;
    use crate::value::Value;
    use parse::ast::Pos;
    let at = Pos { line: 1, col: 1 };
    let parts = |a: u64, b: u64, run: u64| {
        let file = load("").unwrap();
        let mut ev = evaluator(&file, run);
        let first = ev.syms.texts.len();
        ev.syms.texts.push("c".to_owned());
        ev.syms.texts.push("h".to_owned());
        let (pc, ph) = (ev.paths.child(None, first), ev.paths.child(None, first + 1));
        let sel = ev
            .graph
            .mk(at, crate::types::Ty::Bool, Op::Ref(pc), Vec::new());
        let leaf = ev
            .graph
            .mk(at, crate::types::Ty::UInt(8), Op::Ref(ph), Vec::new());
        let ty = tuple_of(
            &mut ev,
            vec![crate::types::Ty::Int, crate::types::Ty::UInt(8)],
        );
        let arm = |n: u64| {
            let int = Value::Int(Int::from_u64(n));
            super::Out::Made(node(&ev, ty, vec![Agg::Static(int), Agg::Hw(leaf)]))
        };
        let arms = vec![arm(a), arm(b)];
        ev.fuel = crate::ops::Fuel::new(1000);
        let keys = [Some(Int::from_u64(1)), None];
        match ev.match_join(at, sel, &keys, arms) {
            Ok(_) => format!("hardware {}", 1000 - ev.fuel.left()),
            Err(super::Stop::Error(error)) => {
                let (code, p) = (error.code, error.pos);
                format!("{code} {}:{} {}", p.line, p.col, error.message)
            }
            Err(super::Stop::Stack(_)) => "stack".to_owned(),
        }
    };
    assert_eq!(
        parts(1, 1, 720_000_090),
        format!("hardware {}", 1 + 3 + 2 + 1 + 1 + 2 + 1 + 5)
    );
    assert_eq!(
        parts(1, 2, 720_000_091),
        "S011 1:1 the arms of a hardware `match` differ in a static part: Int and Int"
    );
}
