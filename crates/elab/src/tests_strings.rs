// SPDX-License-Identifier: Apache-2.0
//! The string and list cases of `Silicon.Source.Test.Eval` in Lean: the types `String` and
//! `List[T]`, the string operations, the list functions, the receiver calls, and the `mut`
//! formals. The charges are exact: the cost is the number, this fuel passes, and one unit less
//! gives `S015`. The tests of the work count steps and copies and not the time.

use crate::eval::{COPIES, COUNTS, Counts};
use crate::tests::{cost, exact, out};

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
