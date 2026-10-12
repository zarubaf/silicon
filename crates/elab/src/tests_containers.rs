// SPDX-License-Identifier: Apache-2.0
//! The container cases of `Silicon.Source.Test.Eval` and `Silicon.Source.Test.Elab` in Lean:
//! the literals, the typed uses, the index, the selector, `len`, `==`, the depth bound, the
//! places, the arguments of an instantiation, and the nested doubling of section 11.3. The
//! charges are exact: the cost is the number, this fuel passes, and one unit less gives
//! `S015`.

use crate::names::sha16;
use crate::tests::{cost, exact, message, out, path_steps, type_work};
use crate::tests_elab::{cost as top_cost, cost_fuel, order};
use std::fmt::Write;

/// The result of `eval` with the default budgets.
fn o(src: &str, expr: &str) -> String {
    out(src, expr, 100_000_000, 1000)
}

fn depth(src: &str, expr: &str, depth: u64) -> String {
    out(src, expr, 100_000_000, depth)
}

fn typed(ty: &str, v: &str) -> String {
    format!("fn f() -> Int {{ let a: {ty} = {v}; return 0; }}")
}

fn body(s: &str) -> String {
    format!("fn f() -> Int {{ {s} }}")
}

#[test]
fn literals() {
    assert_eq!(o("", "()"), "(unit)");
    assert_eq!(o("", "(1,)"), "(tuple ((int 1)))");
    assert_eq!(o("", "(1, true)"), "(tuple ((int 1) (bool true)))");
    assert_eq!(o("", "[1, 2]"), "(array int ((int 1) (int 2)))");
    assert_eq!(
        o("", "[[1, 2], [3, 4]]"),
        "(array (array int 2) ((array int ((int 1) (int 2))) (array int ((int 3) (int 4)))))"
    );
    exact("", "()", 2);
    exact("", "(1, true)", 8);
    exact("", "[1, 2]", 8);
}

#[test]
fn the_elements_take_their_common_type() {
    assert_eq!(
        o("", "[1, UInt[8](2)]"),
        "(array (uint 8) ((uint 8 1) (uint 8 2)))"
    );
    exact("", "[1, UInt[8](2)]", 20);
    assert_eq!(o("", "[1, true]"), "S010 1:1");
    assert_eq!(o("", "[[1], [2, 3]]"), "S010 1:1");
    assert_eq!(o("", "[UInt[8](1), UInt[16](2)]"), "S010 1:1");
    assert_eq!(o("", "[(\"a\", 1)]"), "S010 1:1");
    assert_eq!(o("", "[300, UInt[8](1)]"), "S012 1:1");
}

#[test]
fn an_empty_array_takes_its_type_at_a_typed_use() {
    let empty = "fn f(x: [UInt[8]; 0]) -> Int { return len(x); }\n\
        fn g(comptime x: [Bool; 0]) -> Int { return len(x); }\n\
        fn h() -> [Bool; 0] { return []; }\n\
        const E: [Bool; 0] = [];";
    assert_eq!(o(empty, "f([])"), "(int 0)");
    assert_eq!(o(empty, "g([])"), "(int 0)");
    assert_eq!(o(empty, "h()"), "(array bool ())");
    assert_eq!(o(empty, "E"), "(array bool ())");
    assert_eq!(o("", "[]"), "S010 1:1");
    assert_eq!(o("", "[[]]"), "S010 1:2");
    assert_eq!(o("", "len([])"), "S010 1:5");
    assert_eq!(o("", "[] == []"), "S010 1:1");
    assert_eq!(
        o("fn f() -> Int { let a = []; return 0; }", "f()"),
        "S010 1:25"
    );
    assert_eq!(o("fn f() -> Int { []; return 0; }", "f()"), "S010 1:17");
    assert_eq!(
        o("fn f() -> Int { let a: [Bool; 1] = []; return 0; }", "f()"),
        "S010 1:17"
    );
}

#[test]
fn a_typed_use_converts_each_element() {
    assert_eq!(
        cost(&typed("[UInt[8]; 2]", "[1, 2]"), "f()"),
        cost("fn f() -> Int { let a = [1, 2]; return 0; }", "f()") + 13 + 6
    );
    let get = "fn f(a: [UInt[8]; 2]) -> UInt[8] { return a[1]; }";
    assert_eq!(o(get, "f([1, 2])"), "(uint 8 2)");
    assert_eq!(o(get, "f([1, 256])"), "S012 1:1");
    assert_eq!(o(get, "f([1, 2, 3])"), "S010 1:1");
    assert_eq!(
        o(
            "fn f() -> [Nat; 2] { let a: [Nat; 2] = [1, 2]; return a; }",
            "f()"
        ),
        "(array nat ((int 1) (int 2)))"
    );
    assert_eq!(o(&typed("[Nat; 2]", "[1, -1]"), "f()"), "S012 1:17");
    assert_eq!(o(&typed("(UInt[8], Bool)", "(1, true)"), "f()"), "(int 0)");
    assert_eq!(o(&typed("(UInt[8], Bool)", "(1, 2)"), "f()"), "S010 1:17");
    assert_eq!(o(&typed("()", "()"), "f()"), "(int 0)");
    assert_eq!(o(&typed("Unit", "()"), "f()"), "(int 0)");
}

#[test]
fn a_unit_part_keeps_its_value() {
    assert_eq!(
        o(
            "fn f() -> (Nat, ()) { let x: (Nat, ()) = (1, ()); return x; }",
            "f()"
        ),
        "(tuple ((int 1) (unit)))"
    );
    assert_eq!(o(&typed("((), Nat)", "((), 1)"), "f()"), "(int 0)");
    assert_eq!(o(&typed("[(Nat, ()); 1]", "[(1, ())]"), "f()"), "(int 0)");
    let unit_arg = "module C(comptime A: ([Nat; 2], ())) {\n  output y: Bool;\n  y := true;\n}\n\
        module M() {\n  output y: Bool;\n  instance c = C(([1, 2], ()));\n  y := c.y;\n}\n";
    assert!(top_cost(unit_arg, "M()").starts_with("total"));
    assert_eq!(
        o(
            "fn f() -> Int { let mut a: [Int; 1] = [1]; a = [2]; return a[0]; }",
            "f()"
        ),
        "(int 2)"
    );
}

#[test]
fn a_container_type_checks_its_length_and_depth() {
    assert_eq!(o(&typed("[Bool; -1]", "[]"), "f()"), "S012 1:31");
    assert_eq!(o(&typed("[Bool; true]", "[]"), "f()"), "S010 1:31");
    let nested = typed("[[Bool; 1]; 1]", "[[true]]");
    assert_eq!(depth(&nested, "f()", 3), "(int 0)");
    assert_eq!(depth(&nested, "f()", 2), "S015 1:24");
    let tuple = typed("([Bool; 1],)", "([true],)");
    assert_eq!(depth(&tuple, "f()", 2), "S015 1:24");
}

#[test]
fn the_index_and_the_selector_refer_to_an_element() {
    assert_eq!(o("", "[1, 2][1]"), "(int 2)");
    assert_eq!(o("", "(1, true)[1]"), "(bool true)");
    assert_eq!(o("", "(1, 2).1"), "(int 2)");
    assert_eq!(o("", "(1, 2).0x1"), "(int 2)");
    assert_eq!(o("", "len([1, 2, 3])"), "(int 3)");
    exact("", "[1, 2][0]", 11);
    exact("", "(1, 2).0", 9);
    exact("", "len([1, 2])", 10);
    assert_eq!(o("", "[1, 2][2]"), "S013 1:8");
    assert_eq!(o("", "[1, 2][-1]"), "S013 1:8");
    assert_eq!(o("", "(1, 2).2"), "S013 1:8");
    assert_eq!(o("", "[1, 2][true]"), "S010 1:8");
    assert_eq!(o("", "[1, 2][0, 1]"), "S010 1:1");
    assert_eq!(o("", "[1, 2].0"), "S010 1:1");
    assert_eq!(o("", "1[0]"), "S010 1:1");
    assert_eq!(o("", "len(1)"), "S010 1:1");
}

#[test]
fn a_binding_of_an_element_copies_it() {
    assert_eq!(
        cost(
            "fn f() -> Int { let a = [[1, 2]]; let b = a[0]; return 0; }",
            "f()"
        ),
        cost(
            "fn f() -> Int { let a = [[1, 2]]; let b = [1, 2]; return 0; }",
            "f()"
        ) - 8
            + 4
            + 3
    );
}

#[test]
fn equality_needs_a_common_type_for_each_pair() {
    assert_eq!(o("", "[1, 2] == [1, 2]"), "(bool true)");
    assert_eq!(o("", "[1, 2] != [1, 3]"), "(bool true)");
    assert_eq!(o("", "() == ()"), "(bool true)");
    assert_eq!(o("", "(1, (2, 3)) == (1, (2, 4))"), "(bool false)");
    assert_eq!(o("", "(\"a\", 1) == (\"a\", 1)"), "(bool true)");
    assert_eq!(o("", "[1, 2] == [UInt[8](1), 2]"), "(bool true)");
    exact("", "[1, 2] == [1, 2]", 23);
    assert_eq!(o("", "[300] == [UInt[8](1)]"), "S012 1:1");
    assert_eq!(o("", "[1] == [1, 2]"), "S010 1:1");
    assert_eq!(o("", "(1,) == (1, 2)"), "S010 1:1");
    assert_eq!(o("", "[1] == (1,)"), "S010 1:1");
    assert_eq!(o("", "[1] == 1"), "S010 1:1");
    assert_eq!(o("", "[1] < [2]"), "S010 1:1");
    assert_eq!(o("", "() >= ()"), "S010 1:1");
    assert_eq!(o("", "[1] + [2]"), "S010 1:1");
}

#[test]
fn a_new_container_checks_the_nesting_depth() {
    let array = "fn f() -> Int { let a = [[[1]]]; return 0; }";
    assert_eq!(depth(array, "f()", 4), "(int 0)");
    assert_eq!(depth(array, "f()", 3), "S015 1:25");
    let tuple = "fn f() -> Int { let a = (((1,),),); return 0; }";
    assert_eq!(depth(tuple, "f()", 3), "S015 1:25");
}

/// A module that binds the container `body` in its first statements.
fn hw(body: &str) -> String {
    format!(
        "module M(comptime N: Nat) {{\n  input x: UInt[8];\n  output y: UInt[8];\n  \
         reg r: UInt[8] = 0;\n{body}\n  r := x;\n  y := r;\n}}\n"
    )
}

#[test]
fn a_container_holds_only_static_values() {
    let top = |body: &str, arg: &str| top_cost(&hw(body), arg);
    assert_eq!(top("  let t = (1, x);", "M(1)"), "S010 5:15");
    assert_eq!(top("  let t = [r];", "M(1)"), "S010 5:12");
    assert_eq!(
        top("  let h = x +% 1;\n  let u = [1, 2][h];", "M(1)"),
        "S011 6:18"
    );
    assert_eq!(
        top("  let h = x +% 1;\n  let u: [Int; h] = [1];", "M(1)"),
        "S011 6:16"
    );
    assert_eq!(top("  let u = x.0;", "M(1)"), "S010 5:11");
    assert_eq!(top("  let u = len(x);", "M(1)"), "S010 5:11");
    assert_eq!(top("  let t = [1, 2] == x;", "M(1)"), "S010 5:11");
    assert_eq!(
        top("  let t = [1, 2];\n  let u = t[N];", "M(2)"),
        "S013 6:13"
    );
    assert!(top("  let t = [1, 2];\n  let u = t[N];", "M(1)").starts_with("total"));
}

/// The nested doubling of section 11.3: making `a_k` charges `2^(k + 2) - 1`. Each `let`
/// adds 4 units: the statement, the literal, and the two names. There is no clock: the test
/// reads the charges.
fn doubling(k: u32) -> String {
    let mut src = "fn d() -> Int {\n  let a0 = [0, 0];\n".to_owned();
    for i in 1..=k {
        writeln!(src, "  let a{i} = [a{}, a{}];", i - 1, i - 1).unwrap();
    }
    src.push_str("  return 0;\n}");
    src
}

#[test]
fn the_nested_doubling_charges_two_to_the_k() {
    exact(&doubling(0), "d()", 17);
    for k in 0..6u32 {
        let step = (1u64 << (k + 3)) - 1 + 4;
        assert_eq!(
            cost(&doubling(k + 1), "d()"),
            cost(&doubling(k), "d()") + step,
            "k = {k}"
        );
    }
    assert_eq!(out(&doubling(20), "d()", 1_000_000, 1000), "S015 19:13");
}

#[test]
fn the_nested_doubling_in_a_module() {
    let module = |k: u32| {
        let mut src = "module T() {\n  let a0 = [0, 0];\n".to_owned();
        for i in 1..=k {
            writeln!(src, "  let a{i} = [a{}, a{}];", i - 1, i - 1).unwrap();
        }
        src.push_str("}\n");
        src
    };
    assert_eq!(cost_fuel(&module(20), "T", 1_000_000), "S015 19:13");
    assert!(cost_fuel(&module(16), "T", 1_000_000).starts_with("total"));
}

#[test]
fn the_type_flows_into_the_elements_of_a_literal() {
    assert_eq!(
        o(
            "fn f() -> [[Bool; 0]; 1] { let x: [[Bool; 0]; 1] = [[]]; return x; }",
            "f()"
        ),
        "(array (array bool 0) ((array bool ())))"
    );
    assert_eq!(
        o("fn f() -> ([Bool; 0], Int) { return ([], 1); }", "f()"),
        "(tuple ((array bool ()) (int 1)))"
    );
    assert_eq!(
        o(
            "fn g(x: [[Bool; 0]; 2]) -> Int { return len(x); }",
            "g([[], []])"
        ),
        "(int 2)"
    );
    assert_eq!(
        o(
            "fn f() -> Int { let x: [Bool; 0] = [[]]; return 0; }",
            "f()"
        ),
        "S010 1:17"
    );
    assert_eq!(
        o("fn f() -> Int { let x = ([], 1); return 0; }", "f()"),
        "S010 1:26"
    );
    assert_eq!(o("", "[1, []]"), "S010 1:5");
}

#[test]
fn an_assignment_replaces_the_selected_part() {
    assert_eq!(
        o(&body("let mut a = [1, 2]; a[0] = 5; return a[0];"), "f()"),
        "(int 5)"
    );
    assert_eq!(
        o(
            "fn f() -> [[Int; 2]; 2] { let mut a = [[1, 2], [3, 4]]; a[1][0] = 9; return a; }",
            "f()"
        ),
        "(array (array int 2) ((array int ((int 1) (int 2))) (array int ((int 9) (int 4)))))"
    );
    assert_eq!(
        o(
            "fn f() -> (Int, (Bool, Int)) { let mut a = (1, (true, 2)); a.1.0 = false; \
             a.1.1 = 7; return a; }",
            "f()"
        ),
        "(tuple ((int 1) (tuple ((bool false) (int 7)))))"
    );
    assert_eq!(
        o(
            "fn f() -> [(Int, Int); 1] { let mut a = [(1, 2)]; a[0].1 = 5; return a; }",
            "f()"
        ),
        "(array (tuple (int int)) ((tuple ((int 1) (int 5)))))"
    );
    assert_eq!(
        o(
            "fn f() -> [[Int; 2]; 1] { let mut a = [[1, 2]]; let b = a; a[0][0] = 9; return b; }",
            "f()"
        ),
        "(array (array int 2) ((array int ((int 1) (int 2)))))"
    );
    assert_eq!(
        o(
            "fn f() -> Int { let mut x: [[Bool; 0]; 1] = [[]]; x[0] = []; return len(x[0]); }",
            "f()"
        ),
        "(int 0)"
    );
}

#[test]
fn the_indices_of_a_place_evaluate_before_the_right_side() {
    let at = |s: &str| o(&body(s), "f()");
    assert_eq!(
        at("let mut a = [[1, 2]]; a[1 / 0][0] = 1 / 0; return 0;"),
        "S013 1:41"
    );
    assert_eq!(
        at("let mut a = [[1, 2]]; a[0][1 / 0] = 1 / 0; return 0;"),
        "S013 1:44"
    );
    assert_eq!(
        at("let mut a = [[1, 2]]; a[0][5] = 1 / 0; return 0;"),
        "S013 1:44"
    );
    assert_eq!(
        at("let mut a = [[1, 2]]; a[0][0] = 1 / 0; return 0;"),
        "S013 1:49"
    );
    assert_eq!(at("let mut a = (1, 2); a.2 = 3; return 0;"), "S013 1:39");
    assert_eq!(
        at("let mut a: [UInt[8]; 2] = [1, 2]; a[0] = 256; return 0;"),
        "S012 1:51"
    );
    assert_eq!(
        at("let mut a: [UInt[8]; 2] = [1, 2]; a[0] = true; return 0;"),
        "S010 1:51"
    );
    assert_eq!(at("let a = [1, 2]; a[0] = 3; return 0;"), "S010 1:33");
    assert_eq!(
        at("let mut a = [1, 2]; a[0, 1] = 3; return 0;"),
        "S010 1:37"
    );
    assert_eq!(at("let mut a = 1; a[0] = 3; return 0;"), "S010 1:32");
}

/// Each step of the place charges 1 at its node. The update copies only the containers on
/// its path, so it charges nothing more. The statement and the step `[0]` charge 1 each, and
/// the index `0` and the right side `5` charge 2 each.
#[test]
fn an_update_charges_nothing_more() {
    assert_eq!(
        cost(&body("let mut a = [1, 2]; a[0] = 5; return 0;"), "f()"),
        cost(&body("let mut a = [1, 2]; return 0;"), "f()") + 6
    );
    assert_eq!(
        cost(
            &body("let mut a = [[1, 2]]; let b = [3, 4]; a[0] = b; return 0;"),
            "f()"
        ),
        cost(
            &body("let mut a = [[1, 2]]; let b = [3, 4]; return 0;"),
            "f()"
        ) + 1
            + 1
            + 2
            + 1
            + 3
    );
}

/// Each selector `.N` of a place charges 1: the statement, the three steps, and the right side.
#[test]
fn each_step_of_a_place_charges() {
    assert_eq!(
        cost(
            &body("let mut a = ((1, (2, 3)), 4); a.0.1.0 = 5; return 0;"),
            "f()"
        ),
        cost(&body("let mut a = ((1, (2, 3)), 4); return 0;"), "f()") + 1 + 3 + 2
    );
    // The step `[1]` charges at its node `1:39`, after the index `0` at `1:41`.
    let src = body("let mut a = [[1, 2]]; a[0][1] = 5; return 0;");
    let used = cost(&src, "f()");
    assert_eq!(out(&src, "f()", used - 9, 1000), "S015 1:39");
    assert_eq!(out(&src, "f()", used - 10, 1000), "S015 1:41");
}

/// A failed check of a step comes before each error of a later step, as in Lean, although the
/// checks run after the indices.
#[test]
fn a_failed_step_comes_before_a_later_index() {
    let at = |s: &str| o(&body(s), "f()");
    assert_eq!(
        at("let mut a = [[1, 2]]; a[5][1 / 0] = 1; return 0;"),
        "S013 1:41"
    );
    assert_eq!(
        at("let mut a = [[1, 2]]; a[0].0[1 / 0] = 1; return 0;"),
        "S010 1:39"
    );
    // This fuel runs out at the charge of the step `[0]` after `[5]`, and `[5]` fails first.
    let fuel = cost(&body("let mut a = [[1, 2]]; return 0;"), "f()");
    let good = body("let mut a = [[1, 2]]; a[0][0] = 1; return 0;");
    assert_eq!(out(&good, "f()", fuel, 1000), "S015 1:39");
    let bad = body("let mut a = [[1, 2]]; a[5][0] = 1; return 0;");
    assert_eq!(out(&bad, "f()", fuel, 1000), "S013 1:41");
}

/// A tuple of depth `d` with the selector place `.0` of depth `d`.
fn deep(d: usize) -> (String, String) {
    let mut lit = "0".to_owned();
    for _ in 0..d {
        lit = format!("({lit}, 0)");
    }
    (lit, format!("a{}", ".0".repeat(d)))
}

/// An update of a place of depth `d` walks its path once: `d` steps, not one walk from the
/// root for each step.
#[test]
fn a_deep_update_walks_its_path_once() {
    let steps = |d: usize, updates: usize| {
        let (lit, place) = deep(d);
        let src = body(&format!(
            "let mut a = {lit}; {} return 0;",
            format!("{place} = 1; ").repeat(updates)
        ));
        path_steps(&src, "f()")
    };
    let d = 400;
    let each = (steps(d, 30) - steps(d, 10)) / 20;
    assert!(each <= 2 * d as u64, "{each} steps for a depth of {d}");
    let index = |updates: usize| {
        let src = body(&format!(
            "let mut a = [[[[1]]]]; {} return 0;",
            "a[0][0][0][0] = 2; ".repeat(updates)
        ));
        path_steps(&src, "f()")
    };
    assert!(index(20) - index(10) <= 10 * 2 * 4);
}

/// A read of a place of depth `d` walks its path a constant number of times: once for its
/// checks and once for each use of its result. Thus it makes `O(d)` steps, not one walk from
/// the root for each step.
#[test]
fn a_deep_read_walks_its_path_once() {
    let steps = |d: usize, reads: usize| {
        let (lit, place) = deep(d);
        let src = body(&format!(
            "let a = {lit}; let mut s = 0; {} return s;",
            format!("s = s + {place}; ").repeat(reads)
        ));
        path_steps(&src, "f()")
    };
    let d = 400;
    let each = (steps(d, 30) - steps(d, 10)) / 20;
    assert!(each <= 4 * d as u64, "{each} steps for a depth of {d}");
    let index = |reads: usize| {
        let src = body(&format!(
            "let a = [[[[1]]]]; let mut s = 0; {} return s;",
            "s = s + a[0][0][0][0]; ".repeat(reads)
        ));
        path_steps(&src, "f()")
    };
    assert!(index(20) - index(10) <= 10 * 4 * 4);
}

/// A read checks each step before the index of the next step, as in Lean, although the checks
/// run after the indices.
#[test]
fn a_read_checks_each_step_before_a_later_index() {
    let at = |s: &str| o(&body(s), "f()");
    assert_eq!(at("let a = [[1, 2]]; return a[5][1 / 0];"), "S013 1:44");
    assert_eq!(at("let a = [[1, 2]]; return a[0].0[1 / 0];"), "S010 1:42");
    assert_eq!(at("let a = [[1, 2]]; return a[0][1 / 0];"), "S013 1:47");
    assert_eq!(at("let a = [[1, 2]]; return a[0, 1][0];"), "S010 1:42");
    assert_eq!(at("let a = [[1, 2]]; return a[0][0, 1];"), "S010 1:42");
}

/// A local whose tuple holds a string has no type, so the update of an element finds the
/// type of the element. It finds it once, so an update of depth `d` does work in `d`, not one
/// walk of the subtree at each step.
#[test]
fn a_deep_update_of_a_tuple_with_a_string_types_its_element_once() {
    let work = |d: usize, updates: usize| {
        let mut lit = "(\"s\", 0)".to_owned();
        for _ in 1..d {
            lit = format!("({lit}, 0)");
        }
        let place = format!("a{}.1", ".0".repeat(d - 1));
        let src = body(&format!(
            "let mut a = {lit}; {} return 0;",
            format!("{place} = 1; ").repeat(updates)
        ));
        type_work(&src, "f()")
    };
    let d = 400;
    let each = (work(d, 30) - work(d, 10)) / 20;
    assert!(each <= 4 * d as u64, "{each} for a depth of {d}");
}

/// A message prints at most 256 bits of the length of an array type, and at most 1024 bytes
/// of the text of a type, also when the last piece of the text goes past the limit.
#[test]
fn a_message_bounds_the_text_of_a_type() {
    let big = message(
        "fn f() -> Int { let a: [Int; 1 << 1000000] = 0; return 0; }",
        "f()",
    );
    assert_eq!(
        big,
        "expected [Int; an integer of 1000001 bits], but the value is Int"
    );
    // The text of the type has 1015 bytes before its last piece `; 1000000]`, which goes
    // past the limit.
    let wide = format!("[({}); 1000000]", vec!["UInt[65536]"; 78].join(", "));
    let text = message(
        &format!("fn f() -> Int {{ let a: {wide} = 0; return 0; }}"),
        "f()",
    );
    let ty = text
        .strip_prefix("expected ")
        .and_then(|t| t.split(", but the value is").next())
        .unwrap_or_default();
    assert_eq!(ty.len(), 1024 + 3, "{text}");
    assert!(ty.ends_with("..."), "{text}");
}

/// An instance argument that waits for its type makes each argument take its value in the
/// scope of the module. A reference argument stays a reference until the instance statement
/// pays the sizes, so 1,000 references to an array of 1,000 elements copy nothing before
/// `S015`.
#[test]
fn a_module_argument_copies_after_its_charge() {
    let refs = vec!["a"; 1000].join(", ");
    let params = (0..1000)
        .map(|k| format!("comptime x{k}: [Int; 1000]"))
        .collect::<Vec<_>>()
        .join(", ");
    let zeros = vec!["0"; 1000].join(", ");
    let src = format!(
        "const a: [Int; 1000] = [{zeros}];\n\
         module C({params}, comptime e: [Bool; 0]) {{\n}}\n\
         module T() {{\n  instance c = C({refs}, []);\n}}\n"
    );
    // The arguments and the constant cost far less than this fuel, and their copies far more.
    let fuel = 100_003;
    assert!(cost_fuel(&src, "T", fuel).starts_with("S015"));
    let copies = crate::eval::COPIES
        .lock()
        .map(|c| c.get(&fuel).copied())
        .ok()
        .flatten();
    assert_eq!(copies, Some(0));
}

fn container(ty: &str, arg: &str) -> String {
    format!("module C(comptime xs: {ty}) {{\n}}\nmodule T() {{\n  instance a = C({arg});\n}}\n")
}

#[test]
fn a_container_argument_gives_the_digest_name() {
    assert_eq!(
        order(&container("[UInt[8]; 2]", "[1, 2]"), "T"),
        [
            format!(
                "C$0h{}",
                sha16("(instantiation root C ((array int ((int 1) (int 2)))))")
            ),
            "T".to_owned()
        ]
    );
    assert_eq!(
        order(&container("[Bool; 0]", "[]"), "T"),
        [
            format!("C$0h{}", sha16("(instantiation root C ((array bool ())))")),
            "T".to_owned()
        ]
    );
    assert_eq!(
        order(&container("([Bool; 0], Int)", "([], 1)"), "T"),
        [
            format!(
                "C$0h{}",
                sha16("(instantiation root C ((tuple ((array bool ()) (int 1)))))")
            ),
            "T".to_owned()
        ]
    );
    assert_eq!(top_cost(&container("[Bool; 0]", "[[]]"), "T"), "S010 4:3");
    let sized = "module C(comptime n: Nat, comptime xs: [[Bool; 0]; n]) {\n}\n\
        module T() {\n  instance a = C(2, [[], []]);\n}\n";
    assert!(top_cost(sized, "T").starts_with("total"));
}

/// The units of `T` in the output of `cost`.
fn units(lines: &str) -> u64 {
    lines
        .lines()
        .find_map(|l| l.strip_prefix("T "))
        .and_then(|n| n.parse().ok())
        .unwrap_or(0)
}

/// The serialization of a container charges 1 for each container node, then its bytes. The
/// parent pays it. `[[1, 2]]` costs `T` 31 units more than `[1, 2]`: the outer literal charges
/// 1 for its node and 4 for its size, the copy adds 1, the walk 1, and the serialization 24
/// bytes. The totals with the lowering are 173 and 204 in Lean, and the driver prints them.
#[test]
fn the_serialization_of_a_container_charges_each_node() {
    let flat = units(&top_cost(&container("[UInt[8]; 2]", "[1, 2]"), "T"));
    let nested = units(&top_cost(&container("[[UInt[8]; 2]; 1]", "[[1, 2]]"), "T"));
    assert_eq!(flat, 90);
    assert_eq!(nested - flat, 31);
}

#[test]
fn a_part_of_a_resource_is_not_a_target() {
    assert_eq!(
        top_cost(
            "module M() domains() {\n  wire w: UInt[8];\n  w.0 := 1;\n}\n",
            "M"
        ),
        "S017 3:3"
    );
    assert_eq!(
        top_cost(
            "module M() domains() {\n  wire w: UInt[8];\n  w[1 / 0] := 1;\n}\n",
            "M"
        ),
        "S017 3:3"
    );
    assert_eq!(
        top_cost(
            "module C() {\n  input a: Bool;\n}\nmodule M() {\n  instance c = C();\n  c.a[0] := true;\n}\n",
            "M"
        ),
        "S017 6:3"
    );
}

/// A tuple type or literal of `n` elements of `Int`.
fn wide(n: usize, item: &str) -> String {
    format!("({})", vec![item; n].join(", "))
}

/// The type work is the lookups of types, 1 plus the number of parts of each one. An id is a
/// plain copy, so the tests below count the lookups and not the time.
#[test]
fn a_type_is_a_copy_of_an_id() {
    fn copy<T: Copy>() {}
    copy::<crate::types::TyId>();
}

/// An update `a.0 = 1` in a wide tuple does not walk the type of the tuple: 500 more updates
/// make no lookup of a type.
#[test]
fn an_update_in_a_wide_tuple_builds_no_type() {
    let work = |updates: usize| {
        let src = body(&format!(
            "let mut a = {}; {} return a.0;",
            wide(400, "0"),
            "a.0 = 1; ".repeat(updates)
        ));
        type_work(&src, "f()")
    };
    assert_eq!(work(550), work(50));
}

/// The nested doubling of an array whose element type is wide copies the element type as an
/// id: each level looks up a constant number of types, and the width counts once.
#[test]
fn a_doubling_with_a_wide_element_type_builds_one_type_per_level() {
    let work = |width: usize, levels: usize| {
        let mut lets = String::new();
        let mut last = "e".to_owned();
        for k in 1..=levels {
            writeln!(lets, "let a{k} = [{last}, {last}];").unwrap();
            last = format!("a{k}");
        }
        let src = body(&format!(
            "let e: [{}; 0] = []; {lets} return len({last});",
            wide(width, "Int")
        ));
        type_work(&src, "f()")
    };
    let (narrow, wider) = (work(300, 6), work(300, 12));
    assert!(wider - narrow <= 8 * 6, "{narrow} {wider}");
    let (small, large) = (work(100, 8), work(700, 8));
    assert!(large - small <= 4 * 600 + 64, "{small} {large}");
}
