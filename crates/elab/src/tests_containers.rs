// SPDX-License-Identifier: Apache-2.0
//! The container cases of `Silicon.Source.Test.Eval` and `Silicon.Source.Test.Elab` in Lean:
//! the literals, the typed uses, the index, the selector, `len`, `==`, the depth bound, the
//! places, the arguments of an instantiation, and the nested doubling of section 11.3. The
//! charges are exact: the cost is the number, this fuel passes, and one unit less gives
//! `S015`.

use crate::names::sha16;
use crate::tests::{cost, exact, out};
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

#[test]
fn an_update_charges_nothing_more() {
    assert_eq!(
        cost(&body("let mut a = [1, 2]; a[0] = 5; return 0;"), "f()"),
        cost(&body("let mut a = [1, 2]; return 0;"), "f()") + 5
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
            + 2
            + 1
            + 3
    );
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
