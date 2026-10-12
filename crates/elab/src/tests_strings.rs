// SPDX-License-Identifier: Apache-2.0
//! The string and list cases of `Silicon.Source.Test.Eval` in Lean: the types `String` and
//! `List[T]`, the string operations, the list functions, the receiver calls, and the `mut`
//! formals. The charges are exact: the cost is the number, this fuel passes, and one unit less
//! gives `S015`. The tests of the work count steps and copies and not the time.

use crate::counters::{JOINED, WALKED, get};
use crate::eval::{COPIES, COUNTS, Counts};
use crate::tests::{cost, exact, out, path_steps};
use std::sync::atomic::Ordering;

/// The result of `eval` with the default budgets.
fn o(src: &str, expr: &str) -> String {
    out(src, expr, 100_000_000, 1000)
}

fn depth(src: &str, expr: &str, depth: u64) -> String {
    out(src, expr, 100_000_000, depth)
}

#[test]
fn the_types_string_and_list() {
    assert_eq!(o("", "String"), "(type string)");
    assert_eq!(o("", "List[Int]"), "(type (list int))");
    exact("", "List[Int]", 5);
    assert_eq!(o("", "List"), "S007 1:1");
    assert_eq!(o("", "List[1]"), "S010 1:1");
    assert_eq!(depth("", "List[List[Int]]", 2), "S015 1:1");
    assert_eq!(
        o("", "[(\"a\", 1)]"),
        "(array (tuple (string int)) ((tuple ((string \"a\") (int 1)))))"
    );
}

/// The copies of the run with the fuel `fuel`, and the counts of its work.
fn work(fuel: u64) -> (u64, Counts) {
    let copies = COPIES
        .lock()
        .ok()
        .and_then(|c| c.get(&fuel).copied())
        .unwrap_or(u64::MAX);
    let counts = COUNTS
        .lock()
        .ok()
        .and_then(|c| c.get(&fuel).copied())
        .unwrap_or_default();
    (copies, counts)
}

/// `+` joins two strings and charges the sum of their sizes: 1 for the node, 4 for each
/// literal, and 6 for the join. No ordering takes a string.
#[test]
fn the_join_and_the_comparison_of_strings() {
    assert_eq!(o("", "\"ab\" + \"cd\""), "(string \"abcd\")");
    exact("", "\"ab\" + \"cd\"", 15);
    assert_eq!(o("", "\"a\" == \"a\""), "(bool true)");
    assert_eq!(o("", "\"a\" != \"b\""), "(bool true)");
    assert_eq!(o("", "\"a\" < \"b\""), "S010 1:1");
    assert_eq!(o("", "\"a\" * \"b\""), "S010 1:1");
    assert_eq!(o("", "\"a\" + 1"), "S010 1:1");
    let join = "comptime fn f(s: String) -> String { return s + \"!\"; }";
    assert_eq!(o(join, "f(\"a\")"), "(string \"a!\")");
    let local = "comptime fn f() -> String { let mut s = \"a\"; s = s + \"b\"; return s; }";
    assert_eq!(o(local, "f()"), "(string \"ab\")");
    let wrong = "comptime fn f() -> String { let s: String = 1; return s; }";
    assert_eq!(o(wrong, "f()"), "S010 1:29");
}

/// `s[i]` gives a string with the scalar `i` of `s`. It charges the size of `s` after the type
/// of the index and before its range. The units are 1 for the node, 7 for the literal, 2 for
/// the index, and 6 for the scan. Thus a fuel of 11 fails at the charge, and 12 reaches the
/// range check.
#[test]
fn the_index_of_a_string() {
    assert_eq!(o("", "\"h\u{e9}llo\"[1]"), "(string \"\u{e9}\")");
    exact("", "\"h\u{e9}llo\"[1]", 16);
    assert_eq!(o("", "\"abc\"[UInt[8](2)]"), "(string \"c\")");
    assert_eq!(o("", "\"abc\"[3]"), "S013 1:7");
    assert_eq!(o("", "\"abc\"[-1]"), "S013 1:7");
    assert_eq!(o("", "\"abc\"[true]"), "S010 1:7");
    assert_eq!(out("", "\"abc\"[5]", 11, 1000), "S015 1:1");
    assert_eq!(out("", "\"abc\"[5]", 12, 1000), "S013 1:7");
    // The result is a new string, which an index takes again.
    assert_eq!(o("", "\"abc\"[1][0]"), "(string \"b\")");
    assert_eq!(o("", "\"abc\"[1][1]"), "S013 1:10");
    assert_eq!(o("", "(\"ab\", 1).0[1]"), "(string \"b\")");
}

/// The scan of a string charges before the next index evaluates. The expected errors are those
/// of the Lean evaluator: the fuel 17 pays the first scan and stops in the second index, at its
/// sum, and not at the second scan.
#[test]
fn the_scan_of_a_string_charges_before_the_next_index() {
    let expr = "\"abc\"[0][1 + 1]";
    for (fuel, error) in [
        (14, "S015 1:10"),
        (16, "S015 1:14"),
        (17, "S015 1:14"),
        (18, "S015 1:10"),
        (20, "S015 1:1"),
        (22, "S013 1:10"),
    ] {
        assert_eq!(out("", expr, fuel, 1000), error, "{fuel}");
    }
}

/// `len(s)` counts the scalars and charges the size of `s` before the scan.
#[test]
fn the_length_of_a_string() {
    assert_eq!(o("", "len(\"h\u{e9}llo\")"), "(int 5)");
    assert_eq!(o("", "len(\"\")"), "(int 0)");
    exact("", "len(\"abc\")", 11);
}

/// `str(n)` gives the decimal form of an `Int`. It charges the copy of `n`, the square of its
/// size, and the size of the result. Thus `str(-5)` charges 4 for `-5`, then 1, 1, and 3.
#[test]
fn the_decimal_form_of_an_integer() {
    assert_eq!(o("", "str(-5)"), "(string \"-5\")");
    exact("", "str(-5)", 11);
    assert_eq!(o("", "str(1 << 64)"), "(string \"18446744073709551616\")");
    let shift = cost("", "1 << 64");
    exact("", "str(1 << 64)", shift + 2 + 2 + 4 + 21);
    assert_eq!(o("", "str(UInt[8](1))"), "S010 1:1");
    assert_eq!(o("", "str(\"a\")"), "S010 1:1");
}

/// B6: `str(n)` pays the square of the size of `n` before it converts. A fuel that cannot pay
/// it converts no digit, and one that can makes the digits and then stops at the result.
#[test]
fn the_conversion_of_an_integer_follows_its_charge() {
    let expr = "str(1 << 2560)";
    // The node, the callee, the operand, the copy of the operand, and the square of its size.
    let before = 2 + cost("", "1 << 2560") + 41;
    let (fuel, paid) = (before + 41 * 41 - 1, before + 41 * 41);
    assert!(out("", expr, fuel, 1000).starts_with("S015"));
    assert_eq!(work(fuel).1.converted, 0);
    assert!(out("", expr, paid, 1000).starts_with("S015"));
    assert_eq!(work(paid).1.converted, 771);
}

/// B6: a string with more bytes than 4 times the fuel cannot pay its scan, and the charge
/// fails from its byte length without a scan. Another string scans in the size of its charge.
#[test]
fn the_scan_of_a_string_follows_its_charge() {
    let text = "a".repeat(10_000);
    let src = format!("fn f() -> Int {{ let s = \"{text}\"; return len(s); }}");
    let full = cost(&src, "f()");
    assert!(full > 10_001);
    // The scan is the second last charge: the size of the string, then the result.
    let (short, enough) = (full - 7502, full - 7501);
    assert!(out(&src, "f()", short, 1000).starts_with("S015"));
    assert_eq!(work(short).1.scanned, 0);
    assert!(out(&src, "f()", enough, 1000).starts_with("S015"));
    assert_eq!(work(enough).1.scanned, 10_000);
}

/// B7: `s = s + t` in a loop joins into one new string for each step, which is the whole of its
/// copy. The accumulator is read in place, so nothing copies a reference, and the cost grows by
/// the size of the new string: its second difference is a constant.
#[test]
fn a_join_in_a_loop_makes_one_string_for_each_step() {
    let steps = |n: u64| {
        let src = format!(
            "comptime fn f() -> Int {{ let mut s = \"\"; \
             comptime for i in 0..{n} {{ s = s + \"ab\"; }} return len(s); }}"
        );
        (cost(&src, "f()"), src)
    };
    let (c10, _) = steps(10);
    let (c11, _) = steps(11);
    let (c12, src) = steps(12);
    assert_eq!(c12 - c11 - (c11 - c10), 2);
    let fuel = 5_000_000 + 12;
    assert_eq!(out(&src, "f()", fuel, 1000), "(int 24)");
    assert_eq!(work(fuel).0, 0);
}

/// `list(T)` makes an empty list. It charges its node, the callee, the copy of `T`, and 1 for
/// the list.
#[test]
fn the_empty_list() {
    assert_eq!(o("", "list(Int)"), "(list int ())");
    exact("", "list(Int)", 5);
    assert_eq!(o("", "list(1)"), "S010 1:1");
    assert_eq!(depth("", "list(List[Int])", 2), "S015 1:1");
}

/// The list functions on a `let mut` place, each on its own line.
const LISTS: &str = "comptime fn f() -> List[Int] { let mut xs = list(Int); push(xs, 1); push(xs, 2); \
    return xs; }\n\
    comptime fn g() -> Int { let mut xs = list(Int); push(xs, 7); return pop(xs); }\n\
    comptime fn h() -> Int { let mut xs = list(Int); return pop(xs); }\n\
    comptime fn i() -> List[Int] { let mut xs = f(); xs[0] = 5; return xs; }\n\
    comptime fn u() -> List[UInt[8]] { let mut xs = list(UInt[8]); push(xs, 1); return xs; }\n\
    comptime fn v() -> Int { let mut xs = list(UInt[8]); push(xs, 300); return 0; }\n\
    comptime fn w() -> Int { let mut xs = list(Int); push(xs, true); return 0; }\n\
    comptime fn a() -> Int { let mut x = 1; push(x, 1); return 0; }\n\
    comptime fn t() -> (List[Int], Int) { let mut t = (list(Int), 1); push(t.0, 3); return t; }\n\
    comptime fn d() -> Int { let mut xs = list(Type); push(xs, List[List[Int]]); return 0; }\n\
    comptime fn e() -> List[[Int; 0]] { let mut xs = list([Int; 0]); push(xs, []); return xs; }\n";

/// `push` and `pop` change the list place. `pop` of an empty list is `S013` at the call.
/// `push` makes the typed use of its element, and a value that does not fit is `S012` at the
/// call. The source skips the pre-check where it names `S008`, so the cases run on the checked
/// part only.
#[test]
fn push_and_pop() {
    assert_eq!(o(LISTS, "f()"), "(list int ((int 1) (int 2)))");
    assert_eq!(o(LISTS, "g()"), "(int 7)");
    assert_eq!(o(LISTS, "h()"), "S013 3:57");
    assert_eq!(o(LISTS, "u()"), "(list (uint 8) ((uint 8 1)))");
    assert_eq!(o(LISTS, "v()"), "S012 6:54");
    assert_eq!(o(LISTS, "w()"), "S010 7:50");
    assert_eq!(o(LISTS, "a()"), "S010 8:41");
    assert_eq!(o(LISTS, "t()"), "(tuple ((list int ((int 3))) (int 1)))");
    assert_eq!(o(LISTS, "e()"), "(list (array int 0) ((array int ())))");
}

/// `f()` costs 31 units: the call 2, its result type 5, its body block 1, the `let` 6, each
/// `push` 6, and the `return` 5. Each `push` costs its statement 1, its node 1, its callee 1,
/// the literal 2, and the size of the element 1.
#[test]
fn the_charges_of_push_and_pop() {
    exact(LISTS, "f()", 31);
    exact(LISTS, "g()", 21);
}

/// The new depth of a list comes from the element alone.
#[test]
fn the_depth_of_a_push() {
    assert_eq!(depth(LISTS, "d()", 3), "S015 10:51");
    assert_eq!(depth(LISTS, "d()", 4), "(int 0)");
    // The root counts the steps of the place: the list is two tuples deep, so the push makes the
    // root 5 deep.
    let deep = "comptime fn d() -> Int { let mut t = ((list(Type),),); \
        push(t.0.0, List[Int]); return 0; }\n";
    assert_eq!(depth(deep, "d()", 5), "(int 0)");
    assert_eq!(depth(deep, "d()", 4), "S015 1:56");
}

/// `len` and an index refer to a list, and an index of a list is also a step of a place.
#[test]
fn the_index_and_the_length_of_a_list() {
    assert_eq!(o(LISTS, "len(f())"), "(int 2)");
    assert_eq!(o(LISTS, "f()[1]"), "(int 2)");
    assert_eq!(o(LISTS, "f()[2]"), "S013 1:5");
    assert_eq!(o(LISTS, "i()"), "(list int ((int 5) (int 2)))");
}

/// `==` on two lists joins their element types. Two lists of different lengths are unequal.
/// No ordering takes a list. An array of lists joins the list types.
#[test]
fn the_equality_of_lists() {
    assert_eq!(o(LISTS, "f() == f()"), "(bool true)");
    assert_eq!(o(LISTS, "f() == list(Int)"), "(bool false)");
    assert_eq!(o(LISTS, "f() == u()"), "(bool false)");
    assert_eq!(o(LISTS, "list(Int) == list(Bool)"), "S010 1:1");
    assert_eq!(o(LISTS, "f() < f()"), "S010 1:1");
    assert_eq!(
        o(LISTS, "[f(), list(Int)]"),
        "(array (list int) ((list int ((int 1) (int 2))) (list int ())))"
    );
}

/// B1: a join makes its string after its charge. The fuel 14 cannot pay the join, which is the
/// last charge of 15, and so no byte joins.
#[test]
fn a_join_follows_its_charge() {
    JOINED.store(0, Ordering::Relaxed);
    assert!(out("", "\"ab\" + \"cd\"", 14, 1000).starts_with("S015"));
    assert_eq!(get(&JOINED), 0);
    assert_eq!(out("", "\"ab\" + \"cd\"", 15, 1000), "(string \"abcd\")");
    assert_eq!(get(&JOINED), 4);
}

/// The list `f` that pushes `n` integers, then pops them.
fn pushes(n: u64) -> String {
    format!(
        "comptime fn f() -> Int {{ let mut xs = list(Int); \
         comptime for i in 0..{n} {{ push(xs, i); }} \
         comptime for i in 0..{n} {{ let y = pop(xs); }} return 0; }}"
    )
}

/// B5: a push reads the depth of its element and the length of its place path, and no walk
/// enters the list. The nodes that the walks visit grow in the number of pushes, not in the
/// square of it.
#[test]
fn a_push_does_not_walk_the_list() {
    let walked = |n: u64| {
        let src = pushes(n);
        WALKED.store(0, Ordering::Relaxed);
        assert_eq!(out(&src, "f()", 100_000_000, 1000), "(int 0)");
        get(&WALKED)
    };
    let (small, large) = (walked(200), walked(400));
    assert!(
        large < 5 * small / 2,
        "{small} nodes for 200 pushes, {large} for 400"
    );
}

/// B4: a push or a pop changes its list in one walk down the path of the place, so the steps
/// follow the length of the path and not the length of the list, and nothing copies the list.
#[test]
fn a_push_and_a_pop_walk_their_path_once() {
    let steps = |depth: usize, n: u64| {
        let (open, close) = ("(".repeat(depth), ",)".repeat(depth));
        let place = format!("t{}", ".0".repeat(depth));
        let src = format!(
            "comptime fn f() -> Int {{ let mut t = {open}list(Int){close}; \
             comptime for i in 0..{n} {{ push({place}, i); }} \
             comptime for i in 0..{n} {{ let y = pop({place}); }} return 0; }}"
        );
        path_steps(&src, "f()")
    };
    let depth = 40usize;
    let each = (steps(depth, 30) - steps(depth, 10)) / 40;
    assert!(
        each <= 2 * depth as u64 + 2,
        "{each} steps for a depth of {depth}"
    );
}

/// B2: an element that a reference names copies after its charge. A fuel that cannot pay the
/// size of the element copies nothing, and a fuel that can copies the element once.
#[test]
fn a_pushed_element_copies_after_its_charge() {
    let zeros = vec!["0"; 1000].join(", ");
    let src = format!(
        "const big: [Int; 1000] = [{zeros}];\n\
         comptime fn f() -> Int {{ let mut xs = list([Int; 1000]); push(xs, big); return 0; }}"
    );
    let full = cost(&src, "f()");
    // The size of the element, 1,001, is the charge before the last 4 units.
    let short = full - 500;
    assert!(out(&src, "f()", short, 1000).starts_with("S015"));
    assert_eq!(work(short).0, 0);
    assert_eq!(out(&src, "f()", full, 1000), "(int 0)");
    assert_eq!(work(full).0, 1001);
}

/// A receiver call binds its receiver at the first parameter without `comptime`, and it
/// charges as its plain call. The receiver evaluates first, so its `S013` comes before the
/// `S013` of the argument. The prelude functions take a receiver too.
const CALLS: &str = "fn f(comptime n: Int, x: Int) -> Int { return n * 10 + x; }\n\
    fn g() -> Int { let a = 3; return a.f(7); }\n\
    fn h() -> Int { let a = 3; return f(7, a); }\n\
    fn p() -> Int { return [1][5].f(1 / 0); }\n\
    fn q() -> Int { let mut xs = list(Int); xs.push(4); xs.push(5); let y = xs.pop(); \
    return y + xs.len(); }\n\
    fn r() -> UInt[4] { return UInt[8](3).resize(UInt[4]); }\n\
    fn s() -> String { return 12.str(); }\n";

#[test]
fn a_receiver_call_binds_at_the_first_parameter_without_comptime() {
    assert_eq!(o(CALLS, "g()"), "(int 73)");
    assert_eq!(cost(CALLS, "g()"), cost(CALLS, "h()"));
    assert_eq!(o(CALLS, "p()"), "S013 4:28");
    assert_eq!(o(CALLS, "q()"), "(int 6)");
    assert_eq!(o(CALLS, "r()"), "(uint 4 3)");
    assert_eq!(o(CALLS, "s()"), "(string \"12\")");
}

/// A `mut` actual copies its place into the formal. At the return, the final value of the formal
/// goes back into the place, also through steps of the place and through a receiver. The place
/// has the type of the formal, else `S010` at the call. A `comptime fn` writes back its static
/// value.
const MUTS: &str = "fn inc(mut x: Int) -> () { x = x + 1; return (); }\n\
    fn two(mut x: Int, mut y: [Int; 2]) -> Int { x = x + y[0]; y[1] = 9; return x; }\n\
    comptime fn ct(mut x: Int) -> Int { x = 2; return 0; }\n\
    fn k() -> Int { let mut a = 1; inc(a); a.inc(); return a; }\n\
    fn l() -> [Int; 2] { let mut a = [1, 2]; inc(a[1]); return a; }\n\
    fn m() -> Int { let mut a: Nat = 1; inc(a); return a; }\n\
    fn o() -> (Int, [Int; 2]) { let mut a = 5; let mut b = [1, 2]; let r = two(a, b); \
    return (a, b); }\n\
    fn u() -> Int { let mut a = 1; let z = ct(a); return a; }\n";

#[test]
fn a_mut_actual_goes_back_into_its_place() {
    assert_eq!(o(MUTS, "k()"), "(int 3)");
    assert_eq!(o(MUTS, "l()"), "(array int ((int 1) (int 3)))");
    assert_eq!(o(MUTS, "m()"), "S010 6:37");
    assert_eq!(
        o(MUTS, "o()"),
        "(tuple ((int 6) (array int ((int 1) (int 9)))))"
    );
    assert_eq!(o(MUTS, "u()"), "(int 2)");
}

/// A `mut` actual charges the copy in and the write-back, but its root name charges no node. With
/// a value of size 2, the call thus costs one unit more than the call with a copy only.
#[test]
fn the_charges_of_a_mut_formal() {
    let keep = "fn keep(mut x: Int) -> () { return (); }\n\
        fn id(x: Int) -> () { return (); }\n\
        fn a() -> Int { let mut a = 18446744073709551616; keep(a); return 0; }\n\
        fn b() -> Int { let mut a = 18446744073709551616; id(a); return 0; }\n";
    assert_eq!(cost(keep, "a()"), cost(keep, "b()") + 1);
}

/// B2: a `mut` actual copies its place into the formal after the charge of its size, and the
/// write-back moves the final value and copies nothing. A fuel that cannot pay the copy copies
/// nothing, and a fuel that can copies the array once.
#[test]
fn a_mut_actual_copies_in_after_its_charge_and_writes_back_by_a_move() {
    let zeros = vec!["0"; 1000].join(", ");
    let src = format!(
        "fn touch(mut a: [Int; 1000]) -> () {{ return (); }}\n\
         fn f() -> Int {{ let mut xs: [Int; 1000] = [{zeros}]; touch(xs); return 0; }}"
    );
    let full = cost(&src, "f()");
    // The copy-in is the first charge of the call, of 1,001 units. The call costs the write-back
    // of 1,001 more, and a few units for the call and the return.
    let short = full - 1_001 - 1_001 + 500;
    assert!(out(&src, "f()", short, 1000).starts_with("S015"));
    assert_eq!(work(short).0, 0);
    assert_eq!(out(&src, "f()", full, 1000), "(int 0)");
    assert_eq!(work(full).0, 1001);
}
