// SPDX-License-Identifier: Apache-2.0
//! The cases of the literals, the record constructors, and the place updates that hold a
//! hardware part, as `Silicon.Source.Test.Eval` and `Test.Elab` guard them in Lean (design
//! sections 5.1, 5.4, and 9.2): the charges of a new node, the common type of the elements, the
//! literal that waits for its type, the `S011` of a list and a module argument, a static root
//! that takes a hardware leaf, a held aggregate root, a `mut` actual that is a part of an
//! aggregate root, and `push` and `pop` into a list part of an aggregate root. The tests count
//! the work of each walk and not the time.

use super::Evaluator;
use super::tests_bind::{assign_in, leaf_x, node, ref_x, run_f};
use super::tests_if::int_part;
use crate::agg::Agg;
use crate::counters;
use crate::hw::Val;
use crate::names::PathId;
use crate::tests_elab::{cost, cost_depth, cost_fuel};
use crate::tests_flatten::lowered_cost;
use crate::types::{Ty, TyId};
use crate::value::Value;

/// The formal `x: (UInt[8], Bool)` and the statement `s` in the body of `f`.
fn on_x(s: &str, run: u64, fuel: u64) -> String {
    run_f(&assign_in("(UInt[8], Bool)", s), run, fuel, ref_x)
}

/// A literal with a hardware part makes a node that charges as a static literal does: the
/// elements, the conversions to the common type, then the size of the result. `(x.0, 3)` charges
/// the statement 1, the literal 1, `x.0` 2, `3` 2, and the size 3 of the node, with `return`
/// that is 13. A binding of the new node is no copy, and each hardware leaf gets a core `let`.
#[test]
fn a_literal_with_a_hardware_part_charges_as_a_static_literal_does() {
    let run = 700_000_500;
    assert_eq!(
        on_x("let y = (x.0, 3);", run, 1_000_000),
        "y$0e=x$0e | ref x | 13"
    );
    assert_eq!(on_x("let y = (x.0, 3);", run + 1, 8), "S015 2:11");
    assert_eq!(
        on_x("let y = [x.0, 1];", run + 2, 1_000_000),
        "y$0e=x$0e | ref x | 15"
    );
    assert_eq!(
        on_x("let y = [x.0, 1];", run + 3, 14),
        "S015 3:3",
        "the literal is paid, and the return is not"
    );
    assert_eq!(
        on_x("let y = (x.0, 3, 4);", run + 4, 1_000_000),
        "y$0e=x$0e | ref x | 16"
    );
    assert_eq!(
        on_x("let y = [(x.0, 1), (2, 3)];", run + 5, 1_000_000),
        "y$0e$0e=x$0e | ref x | 36"
    );
    assert_eq!(
        on_x("let y = [x, (2, true)];", run + 6, 1_000_000),
        "y$0e$0e=x$0e y$0e$1e=x$1e | ref x | 29"
    );
    assert_eq!(
        on_x("let y = [x, x];", run + 7, 1_000_000),
        "y$0e$0e=x$0e y$0e$1e=x$1e y$1e$0e=x$0e y$1e$1e=x$1e | ref x | 16"
    );
    assert_eq!(
        on_x("let y = ((x.0, x.0), x);", run + 8, 1_000_000),
        "y$0e$0e=x$0e y$0e$1e=x$0e y$1e$0e=x$0e y$1e$1e=x$1e | ref x | 22"
    );
}

const SX: &str = "struct S { a: UInt[8], b: Bool }\n";

/// A record constructor with a hardware argument makes a node. A literal that waits takes its
/// type at a typed use, also with a hardware part.
#[test]
fn a_record_and_a_literal_that_waits_take_hardware_parts() {
    let run = 700_000_510;
    let record = format!(
        "{SX}{}",
        assign_in("(UInt[8], Bool)", "let y = S(x.0, true);")
    );
    assert_eq!(
        run_f(&record, run, 1_000_000, ref_x),
        "y$a=x$0e | ref x | 36"
    );
    assert_eq!(
        on_x(
            "let y: ([Bool; 0], UInt[8]) = ([], x.0);",
            run + 1,
            1_000_000
        ),
        "y$1e=x$0e | ref x | 48"
    );
}

/// The elements need a common type, and each field its type. A static leaf checks its fit.
#[test]
fn the_parts_need_their_types_and_a_static_leaf_its_fit() {
    let run = 700_000_520;
    assert_eq!(on_x("let y = [x.0, x.1];", run, 1_000_000), "S010 2:11");
    assert_eq!(on_x("let y = [x.0, 300];", run + 1, 1_000_000), "S012 2:11");
    let record = format!(
        "{SX}{}",
        assign_in("(UInt[8], Bool)", "let y = S(x.1, true);")
    );
    assert_eq!(run_f(&record, run + 2, 1_000_000, ref_x), "S010 3:11");
}

/// The size, the depth, and the leaf count of an element come from its stored numbers. A literal
/// of two references to a huge array fails at the charge of its node. It builds the node by its
/// two parts and never expands a reference.
#[test]
fn a_literal_of_huge_references_fails_at_the_charge_before_it_expands() {
    let run = 700_000_530;
    let src = assign_in("([UInt[8]; 1 << 40], Bool)", "let y = (x.0, x.0);");
    assert_eq!(run_f(&src, run, 1_000_000, ref_x), "S015 2:11");
    let c = counters::of(run);
    assert_eq!(
        (c.expanded, c.bound, c.typed),
        (0, 0, 0),
        "no expansion, no binding, no typed use"
    );
    assert!(c.nodes <= 4, "{c:?}");
}

fn list_in(s: &str, run: u64) -> String {
    on_x(
        &format!("let mut l = list([UInt[8]; 1]);\n  {s}"),
        run,
        1_000_000,
    )
}

/// A list holds no value with a hardware leaf: `S011` at the value, also through a place with a
/// step after the list. A static root of a type with a hardware part takes a hardware value and
/// binds its leaves under its plain name the first time. A later update binds them again, and a
/// root without a hardware leaf is static.
#[test]
fn a_list_holds_no_hardware_leaf_and_a_static_root_binds_on_its_first_leaf() {
    let run = 700_000_540;
    assert_eq!(list_in("l.push([5]);\n  l[0][0] = x.0;", run), "S011 4:13");
    assert_eq!(
        list_in("l.push([5]);\n  l[0] = [x.0];", run + 1),
        "S011 4:10"
    );
    assert_eq!(list_in("l.push([x.0]);", run + 2), "S011 3:10");
    assert_eq!(
        on_x("let mut t = (1, 2);\n  t.0 = x.0;", run + 3, 1_000_000),
        "S010 3:3"
    );
    let typed = "let mut t: (UInt[8], Int) = (1, 2);\n  t.0 = x.0;\n  ";
    assert_eq!(
        on_x(&format!("{typed}t.1 = 4;"), run + 4, 1_000_000),
        "t$0e=x$0e t$1v$0e=t$0e | ref x | 58"
    );
    assert_eq!(
        on_x(&format!("{typed}t.0 = 7;"), run + 5, 1_000_000),
        "t$0e=x$0e | ref x | 57"
    );
    assert_eq!(
        on_x(
            "let mut t: (List[Int], UInt[8]) = (list(Int), 1);\n  t.1 = x.0;\n  t.0.push(1);",
            run + 6,
            1_000_000
        ),
        "t$1e=x$0e | ref x | 68"
    );
}

const GX: &str = "fn g(mut a: (Bool, Int)) -> Int {\n  a.1 = 5;\n  return 0;\n}\n";
const GB: &str = "fn g(mut a: Bool) -> Int {\n  a = !a;\n  return 0;\n}\n";

fn on_pair(pre: &str, s: &str, run: u64) -> String {
    run_f(
        &format!("{pre}{}", assign_in("(Bool, Int)", s)),
        run,
        1_000_000,
        int_part,
    )
}

/// A held aggregate root charges its size 3 at the write-back, the last step before the change.
/// The waiting `x.1` costs as much as `0`, so the difference is the held charge. A `mut` actual
/// that is a part of an aggregate root writes back into that part, and the root binds again.
#[test]
fn a_held_aggregate_root_charges_its_size_and_a_mut_part_writes_back() {
    let run = 700_000_550;
    assert_eq!(
        on_pair(GX, "let y = x.1 + g(x);", run),
        "g$0c$a$0e=x$0e g$0c$a$1v$0e=g$0c$a$0e x$1v$0e=g$0c$a$1v$0e | [x$1v$0e, (int 5)] | 52"
    );
    assert_eq!(
        on_pair(GX, "let y = 0 + g(x);", run + 1),
        "g$0c$a$0e=x$0e g$0c$a$1v$0e=g$0c$a$0e x$1v$0e=g$0c$a$1v$0e | [x$1v$0e, (int 5)] | 49"
    );
    assert_eq!(
        on_pair(GB, "let y = g(x.0);", run + 2),
        "g$0c$a=x$0e g$0c$a$1v=hardware Bool x$1v$0e=g$0c$a$1v | [x$1v$0e, (int 0)] | 25"
    );
    assert_eq!(
        on_pair(GB, "let y = x.1 + g(x.0);", run + 3),
        "g$0c$a=x$0e g$0c$a$1v=hardware Bool x$1v$0e=g$0c$a$1v | [x$1v$0e, (int 0)] | 33"
    );
}

/// `push` and `pop` change a static list part of an aggregate root in place. The leaves keep
/// their names, so the root takes no new version. The change charges the element, as it does for
/// a static root. A hardware element is `S011`. The nodes above the list refresh their stored
/// numbers without a charge (Lean `changeAt`); the counters show that refresh.
#[test]
fn push_and_pop_change_a_list_part_of_an_aggregate_root_in_place() {
    let run = 700_000_560;
    let t = "let mut t = (x.0, list(Int));\n  ";
    assert_eq!(
        on_x(&format!("{t}t.1.push(3);"), run, 1_000_000),
        "t$0e=x$0e | ref x | 25"
    );
    assert_eq!(
        on_x(
            &format!("{t}t.1.push(3);\n  t.1.push(4);"),
            run + 1,
            1_000_000
        ),
        "t$0e=x$0e | ref x | 34"
    );
    let popped = format!("{t}t.1.push(3);\n  let a = t.1.pop();");
    assert_eq!(on_x(&popped, run + 2, 1_000_000), "t$0e=x$0e | ref x | 32");
    assert_eq!(on_x(&popped, run + 3, 22), "S015 4:11");
    assert_eq!(on_x(&popped, run + 4, 23), "S015 4:15");
    assert_eq!(
        on_x(&format!("{t}t.1.push(x.0);"), run + 5, 1_000_000),
        "S011 3:12"
    );
    assert_eq!(
        on_x(&format!("{t}let a = t.1.pop();"), run + 6, 1_000_000),
        "S013 3:11"
    );
    assert_eq!(
        on_x(
            "let mut t = ((x.0, 1), list(Int));\n  t.1.push(3);\n  let b = t;",
            run + 7,
            1_000_000
        ),
        "t$0e$0e=x$0e b$0e$0e=t$0e$0e | ref x | 41"
    );
    assert_eq!(
        on_x(&format!("{t}let k = t.1.len();"), run + 8, 1_000_000),
        "t$0e=x$0e | ref x | 21"
    );
}

/// The refresh of the nodes above the list reads the parts of each node on the path once. A
/// `push` into the list of a tuple of `n` parts reads `n` parts, and its charge is the element.
#[test]
fn a_push_refreshes_each_node_on_the_path_once() {
    let run = 700_000_570;
    let one = on_x(
        "let mut t = (x.0, list(Int));\n  t.1.push(3);",
        run,
        1_000_000,
    );
    assert_eq!(one, "t$0e=x$0e | ref x | 25");
    let before = counters::of(run).nodes;
    let two = on_x(
        "let mut t = (x.0, x.0, x.0, list(Int));\n  t.3.push(3);",
        run + 1,
        1_000_000,
    );
    assert_eq!(two, "t$0e=x$0e t$1e=x$0e t$2e=x$0e | ref x | 33");
    let after = counters::of(run + 1).nodes;
    assert!(after > before, "{before} {after}");
    assert!(after - before <= 12, "{before} {after}");
}

/// The aggregate root `(UInt[8], .., List[UInt[8]])` with a hardware first part, the parts
/// `mid` and a static list that holds `list`.
fn with_list(ev: &mut Evaluator<'_>, p: PathId, t: TyId, mid: Option<bool>, list: &[u64]) -> Val {
    let a = leaf_x(ev, p, 0);
    let e = ev.tys.mk(Ty::UInt(8));
    let xs = list
        .iter()
        .map(|&n| Value::UInt(crate::int::finite(8, n).unwrap_or_else(|| panic!("a byte"))))
        .collect();
    let mut parts = vec![a];
    parts.extend(mid.map(|b| Agg::Static(Value::Bool(b))));
    parts.push(Agg::Static(Value::List(e, xs)));
    node(ev, t, parts)
}

/// `push` and `pop` into a list part of an aggregate root charge the part count of each
/// container node on the path, after the element and before a held root (section 5.4). The
/// totals and the `S015` positions are those of the Lean guards for `Agg.pathWidth`.
#[test]
fn a_push_into_a_list_part_charges_the_part_count_of_each_node_on_the_path() {
    let run = 700_000_600;
    let list_part = |ev: &mut Evaluator<'_>, p: PathId, t: TyId| with_list(ev, p, t, None, &[]);
    let tuple2 = "(UInt[8], List[UInt[8]])";
    let src = assign_in(tuple2, "x.1.push(5);");
    let ok = run_f(&src, run, 1_000_000, list_part);
    assert!(ok.ends_with(" | 15"), "{ok}");
    assert_eq!(run_f(&src, run + 1, 11, list_part), "S015 3:3");
    assert_eq!(run_f(&src, run + 2, 10, list_part), "S015 2:3");

    let wide = |ev: &mut Evaluator<'_>, p: PathId, t: TyId| with_list(ev, p, t, Some(true), &[7]);
    let tuple3 = "(UInt[8], Bool, List[UInt[8]])";
    let src = assign_in(tuple3, "x.2.push(5);");
    let ok = run_f(&src, run + 3, 1_000_000, wide);
    assert!(ok.ends_with(" | 16"), "{ok}");
    assert_eq!(run_f(&src, run + 4, 12, wide), "S015 3:3");
    assert_eq!(run_f(&src, run + 5, 11, wide), "S015 2:3");
    let src = assign_in(tuple3, "let y = x.2.pop();");
    let ok = run_f(&src, run + 6, 1_000_000, wide);
    assert!(ok.ends_with(" | 12"), "{ok}");

    let nested = |ev: &mut Evaluator<'_>, p: PathId, t: TyId| {
        let u8t = ev.tys.mk(Ty::UInt(8));
        let list = ev.tys.list(u8t);
        let inner = ev.tys.tuple(vec![u8t, list]);
        let a = leaf_x(ev, p, 0);
        let empty = Agg::Static(Value::List(u8t, Vec::new()));
        let part = Agg::node(&ev.graph, &ev.tys, inner, vec![a, empty]);
        let part = part.unwrap_or_else(|| panic!("a node"));
        node(ev, t, vec![part, Agg::Static(Value::Bool(true))])
    };
    let src = assign_in("((UInt[8], List[UInt[8]]), Bool)", "x.0.1.push(5);");
    let ok = run_f(&src, run + 7, 1_000_000, nested);
    assert!(ok.ends_with(" | 18"), "{ok}");
    assert_eq!(run_f(&src, run + 8, 14, nested), "S015 3:3");
    assert_eq!(run_f(&src, run + 9, 13, nested), "S015 2:3");
}

const PS: &str = "struct P(comptime W: Nat) { a: UInt[W], b: Bool }\n";

fn module_with(item: &str) -> String {
    format!("{PS}{item}")
}

/// A constructor argument is in a data context, so a register reads (section 9.2). A literal
/// element is a raw context: a register there is `S010`. A module argument is a static position,
/// so an aggregate with a hardware leaf there is `S011` at the statement, also in a literal that
/// waits for its type. The totals include the lowering.
#[test]
fn a_constructor_reads_a_register_and_a_module_argument_is_static() {
    let record = module_with("module M() {\n  input x: UInt[8];\n  let r = P[8](x, true);\n}\n");
    assert_eq!(lowered_cost(&record, "M"), "total 101\nM 73\n");
    let read = module_with(
        "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n  reg q: UInt[8] = 0;\n  \
         let r = P[8](q, true);\n  q := x;\n  y := r.a;\n}\n",
    );
    assert!(
        cost(&read, "M").starts_with("total"),
        "{}",
        cost(&read, "M")
    );
    let arg = |t: &str, a: &str| {
        format!("module C(comptime p: {t}) {{\n}}\nmodule M() {{\n  input x: UInt[8];\n{a}}}\n")
    };
    let tuple = arg(
        "(UInt[8], Int)",
        "  let a = (x, 1);\n  instance c = C(a);\n",
    );
    assert_eq!(cost(&tuple, "M"), "S011 6:3");
    let waits = arg(
        "([Bool; 0], UInt[8])",
        "  let h = x;\n  instance c = C(([], h));\n",
    );
    assert_eq!(cost(&waits, "M"), "S011 6:3");
    let fine = arg("(UInt[8], Int)", "  instance c = C((3, 1));\n");
    assert!(cost(&fine, "M").starts_with("total"));
}

/// Each new aggregate node checks its depth at its node (`S015`).
#[test]
fn a_new_aggregate_node_checks_its_depth() {
    let hw = |body: &str| {
        format!(
            "module M(comptime N: Nat) {{\n  input x: UInt[8];\n  output y: UInt[8];\n  \
             reg r: UInt[8] = 0;\n{body}\n  r := x;\n  y := r;\n}}\n"
        )
    };
    let array = hw("  let t = [[x]];");
    assert_eq!(cost_depth(&array, "M(1)", 2), "S015 5:11");
    assert!(cost_depth(&array, "M(1)", 3).starts_with("total"));
    let tuple = hw("  let t = ((x,),);");
    assert_eq!(cost_depth(&tuple, "M(1)", 2), "S015 5:11");
    assert!(cost_depth(&tuple, "M(1)", 3).starts_with("total"));
}

/// The aggregate root `(UInt[8], List[Type])` with the list `[Type UInt[8], Type [[UInt[8]; 1]; 1]]`.
fn type_list(ev: &mut Evaluator<'_>, p: PathId, t: TyId) -> Val {
    let a = leaf_x(ev, p, 0);
    let u8t = ev.tys.mk(Ty::UInt(8));
    let one = ev.tys.array(u8t, crate::int::Int::from_u64(1));
    let deep = ev.tys.array(one, crate::int::Int::from_u64(1));
    let ty = ev.tys.mk(Ty::Type);
    let list = Value::List(ty, vec![Value::Type(u8t), Value::Type(deep)]);
    node(ev, t, vec![a, Agg::Static(list)])
}

/// A `pop` of an element deeper than the element type can lower the depth of the list, so it
/// charges the size of the root after the part counts and builds each node on the path again.
/// The totals and the `S015` positions are those of the Lean guards for `Agg.change`.
#[test]
fn a_pop_of_a_deep_element_charges_the_root_and_a_shallow_pop_does_not() {
    let run = 700_000_700;
    let src = assign_in("(UInt[8], List[Type])", "let y = x.1.pop();");
    let ok = run_f(&src, run, 1_000_000, type_list);
    assert!(ok.ends_with(" | 27"), "{ok}");
    assert_eq!(run_f(&src, run + 1, 23, type_list), "S015 3:3");
    assert_eq!(run_f(&src, run + 2, 22, type_list), "S015 2:11");
    let two = assign_in(
        "(UInt[8], List[Type])",
        "let y = x.1.pop(); let z = x.1.pop();",
    );
    let ok = run_f(&two, run + 3, 1_000_000, type_list);
    assert!(ok.ends_with(" | 35"), "{ok}");
}

/// The refresh of a push keeps the depth of the root exact, and a deep pop finds it again. The
/// totals are those of the elaboration alone; with the lowering they are 147 and 132, as in Lean.
#[test]
fn the_stored_depth_of_a_root_stays_exact_after_a_push_and_a_deep_pop() {
    let body = |pop: &str| {
        format!(
            "module M() domains() {{\n    input a: UInt[8];\n    output y: UInt[8];\n    \
             let mut t = (a, list(Type));\n    t.1.push([[UInt[8]; 1]; 1]);\n    {pop}\n    \
             let u = (t,);\n    y := a;\n}}\n"
        )
    };
    assert_eq!(
        cost_depth(&body("let k = t.1.pop();"), "M()", 5),
        "total 123\nM 97\n"
    );
    assert_eq!(cost_depth(&body(""), "M()", 5), "S015 7:13");
    assert_eq!(cost_depth(&body(""), "M()", 6), "total 108\nM 82\n");
}

/// An index after a selector waits at a static part of an aggregate root, so a mutation inside
/// the index holds the root local and charges its size, as Lean does (section 5.4). The totals
/// are those of the Lean evaluator for the same module.
#[test]
fn an_index_at_a_static_part_of_an_aggregate_root_holds_the_root() {
    let module = |sel: &str, inside: &str| {
        format!(
            "comptime fn bumpl(mut x: List[Nat]) -> Nat {{ x.push(9); return 0; }}\n\
             module M() domains() {{\n    input a: UInt[8];\n    output y: UInt[8];\n    \
             let mut t = (a, list(Nat), [1, 2], [(0, a, [3, 4])]);\n    t.1.push(4);\n    \
             t.1.push(5);\n    let k = t.{sel}[{inside}];\n    y := t.0;\n}}\n"
        )
    };
    assert_eq!(
        lowered_cost(&module("1", "t.1.pop() - 4"), "M()"),
        "total 180\nM 152\n"
    );
    assert_eq!(
        lowered_cost(&module("2", "(t.1.push(1), 0).1"), "M()"),
        "total 184\nM 156\n"
    );
    assert_eq!(
        lowered_cost(&module("1", "bumpl(t.1)"), "M()"),
        "total 229\nM 201\n"
    );
}

/// The message of the first error of the module `M` with the statement `s` in its body.
fn message_of(s: &str) -> String {
    let src = format!(
        "module M() domains() {{\n    input a: UInt[8];\n    output y: UInt[8];\n    {s}\n    y := a;\n}}\n"
    );
    let file = crate::tests_elab::load(&src).unwrap_or_else(|e| panic!("{e}"));
    match crate::elaborate_with(
        &file,
        "M()",
        parse::DEFAULT_SYNTAX_DEPTH,
        crate::Budget::default(),
        crate::names::sha16,
    ) {
        Ok(Err(e)) => format!("{} {}", e.code, e.message),
        _ => "no error".to_owned(),
    }
}

/// An operand that is a hardware aggregate prints as `hardware T` in each message, and an
/// operator rejects it as Lean does: as no data operand, never as a static `Bool`.
#[test]
fn an_aggregate_operand_prints_its_type_and_no_operator_accepts_it() {
    let t = "hardware (UInt[8], Int)";
    let cases = [
        (
            "let s = str((a, 1));",
            format!("`str` needs an Int, not {t}"),
        ),
        (
            "let s = str(a);",
            "`str` needs an Int, not hardware UInt[8]".to_owned(),
        ),
        (
            "let s = a << (a, 1);",
            format!("a shift count is UInt or a static Int, not {t}"),
        ),
        ("let s = (a, 1) << a;", format!("`<<` does not accept {t}")),
        ("let s = !(a, 1);", format!("`!` does not accept {t}")),
        ("let s = -(a, 1);", format!("`-` does not accept {t}")),
        (
            "let s = (a, 1) & 3;",
            format!("expected data operands, not {t} and Int"),
        ),
        (
            "let s = (a, 1) && true;",
            format!("expected data operands, not {t} and Bool"),
        ),
        (
            "let s = 1 + (a, 1);",
            "`+` accepts only Int and Nat; hardware has `+%`, `-%`, and `*%`".to_owned(),
        ),
    ];
    for (s, message) in cases {
        assert_eq!(message_of(s), format!("S010 {message}"), "{s}");
    }
}

/// A later index of a segment holds the aggregate root too, when the steps before it lead to a
/// static part: the path is followed to the index, not only up to the first index. The totals
/// and the `S015` positions are those of the Lean evaluator for the same module.
#[test]
fn a_later_index_after_an_index_of_an_aggregate_root_holds_the_root() {
    let module = |base: &str| {
        format!(
            "comptime fn bumpl(mut x: List[Nat]) -> Nat {{ x.push(9); return 0; }}\n\
             module M() domains() {{\n    input a: UInt[8];\n    output y: UInt[8];\n    \
             let mut t = (a, list(Nat), [1, 2], [(0, a, [3, 4])]);\n    t.1.push(4);\n    \
             t.1.push(5);\n    let k = {base};\n    y := t.0;\n}}\n"
        )
    };
    let pushed = module("t.3[0].2[(t.1.push(1), 0).1]");
    assert_eq!(lowered_cost(&pushed, "M()"), "total 188\nM 160\n");
    assert_eq!(cost_fuel(&pushed, "M()", 148), "S015 8:23");
    assert_eq!(cost_fuel(&pushed, "M()", 154), "S015 8:36");
    assert_eq!(
        lowered_cost(&module("t.3[0].2[t.1.pop() - 4]"), "M()"),
        "total 184\nM 156\n"
    );
    assert_eq!(
        lowered_cost(&module("t.3[(0, bumpl(t.1)).0].2[bumpl(t.1)]"), "M()"),
        "total 305\nM 277\n"
    );
}
