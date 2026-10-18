// SPDX-License-Identifier: Apache-2.0
//! The records of `diagnostic` (sections 5.4, 6.2, and 8.2), as in `Silicon.Source.Test.Elab` in
//! Lean. Each case lists the records and the outcome of the elaboration at some fuels: the
//! full budget, and the fuels at the borders of the charges of the last calls, where the charge
//! of a call stops at its exact unit. The values are those of the Lean binary `silicon-check
//! observe`. The lowering that follows the elaboration is not part of these cases, so an
//! `S015` of the lowering reads as `ok`.

use crate::tests_elab::load;
use crate::{Budget, observe_with};

/// The records of `src` with the top `top`, then `ok` or the code and the position of the first
/// error. An `S015` also has its message, which names the unit that did not fit.
fn observed(src: &str, top: &str, fuel: Option<u64>, depth: Option<u64>) -> (Vec<String>, String) {
    let file = load(src).unwrap();
    let budget = Budget {
        fuel: fuel.unwrap_or(Budget::default().fuel),
        depth: depth.unwrap_or(Budget::default().depth),
    };
    let Ok(done) = observe_with(
        &file,
        top,
        parse::DEFAULT_SYNTAX_DEPTH,
        budget,
        crate::names::sha16,
    ) else {
        panic!("the top selection must be valid")
    };
    let status = match done.outcome {
        Ok(_) => "ok".to_owned(),
        Err(e) if e.code == crate::Code::S015 => {
            format!("{} {}:{} {}", e.code, e.pos.line, e.pos.col, e.message)
        }
        Err(e) => format!("{} {}:{}", e.code, e.pos.line, e.pos.col),
    };
    (done.records, status)
}

/// Each case is the fuel (`None` for the full budget), the records, and the outcome.
type Case<'a> = (Option<u64>, &'a [&'a str], &'a str);

fn check(src: &str, top: &str, depth: Option<u64>, cases: &[Case<'_>]) {
    for &(fuel, records, status) in cases {
        let (got, outcome) = observed(src, top, fuel, depth);
        let got: Vec<&str> = got.iter().map(String::as_str).collect();
        assert_eq!(
            (got.as_slice(), outcome.as_str()),
            (records, status),
            "{fuel:?}"
        );
    }
}

/// A static integer: the node and the name, the copies, the measure charge, and the bytes.
#[test]
fn a_static_integer() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"depth\", 16);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &["(record 5 3 M () (string \"depth\") (int 16))"],
                "ok",
            ),
            (
                Some(63),
                &[],
                "S015 5:3 the fuel cannot pay 43 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(105),
                &[],
                "S015 5:3 the fuel cannot pay 43 unit(s); 42 remain; raise --fuel",
            ),
            (
                Some(106),
                &["(record 5 3 M () (string \"depth\") (int 16))"],
                "S015 6:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(107),
                &["(record 5 3 M () (string \"depth\") (int 16))"],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(108),
                &["(record 5 3 M () (string \"depth\") (int 16))"],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(109),
                &["(record 5 3 M () (string \"depth\") (int 16))"],
                "S015 6:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(110),
                &["(record 5 3 M () (string \"depth\") (int 16))"],
                "S015 6:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(111),
                &["(record 5 3 M () (string \"depth\") (int 16))"],
                "ok",
            ),
        ],
    );
}

/// The measure charge of an integer is the square of its size.
#[test]
fn a_large_integer_pays_the_square_of_its_size() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"n\", 123456789012345678901234567890123456789);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &["(record 5 3 M () (string \"n\") (int 123456789012345678901234567890123456789))"],
                "ok",
            ),
            (
                Some(60),
                &[],
                "S015 5:3 the fuel cannot pay 76 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(135),
                &[],
                "S015 5:3 the fuel cannot pay 76 unit(s); 75 remain; raise --fuel",
            ),
            (
                Some(136),
                &["(record 5 3 M () (string \"n\") (int 123456789012345678901234567890123456789))"],
                "S015 6:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(137),
                &["(record 5 3 M () (string \"n\") (int 123456789012345678901234567890123456789))"],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(138),
                &["(record 5 3 M () (string \"n\") (int 123456789012345678901234567890123456789))"],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(139),
                &["(record 5 3 M () (string \"n\") (int 123456789012345678901234567890123456789))"],
                "S015 6:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(140),
                &["(record 5 3 M () (string \"n\") (int 123456789012345678901234567890123456789))"],
                "S015 6:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(141),
                &["(record 5 3 M () (string \"n\") (int 123456789012345678901234567890123456789))"],
                "ok",
            ),
        ],
    );
}

/// A static container charges 1 for each container and the square for each integer.
#[test]
fn static_containers_pay_one_for_each_container() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"t\", (1, \"x\", [true, false], ((), -3)));
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 5 3 M () (string \"t\") (tuple ((int 1) (string \"x\") (array bool ((bool true) (bool false))) (tuple ((unit) (int -3))))))",
                ],
                "ok",
            ),
            (
                Some(100),
                &[],
                "S015 5:3 the fuel cannot pay 127 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(226),
                &[],
                "S015 5:3 the fuel cannot pay 127 unit(s); 126 remain; raise --fuel",
            ),
            (
                Some(227),
                &[
                    "(record 5 3 M () (string \"t\") (tuple ((int 1) (string \"x\") (array bool ((bool true) (bool false))) (tuple ((unit) (int -3))))))",
                ],
                "S015 6:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(228),
                &[
                    "(record 5 3 M () (string \"t\") (tuple ((int 1) (string \"x\") (array bool ((bool true) (bool false))) (tuple ((unit) (int -3))))))",
                ],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(229),
                &[
                    "(record 5 3 M () (string \"t\") (tuple ((int 1) (string \"x\") (array bool ((bool true) (bool false))) (tuple ((unit) (int -3))))))",
                ],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(230),
                &[
                    "(record 5 3 M () (string \"t\") (tuple ((int 1) (string \"x\") (array bool ((bool true) (bool false))) (tuple ((unit) (int -3))))))",
                ],
                "S015 6:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(231),
                &[
                    "(record 5 3 M () (string \"t\") (tuple ((int 1) (string \"x\") (array bool ((bool true) (bool false))) (tuple ((unit) (int -3))))))",
                ],
                "S015 6:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(232),
                &[
                    "(record 5 3 M () (string \"t\") (tuple ((int 1) (string \"x\") (array bool ((bool true) (bool false))) (tuple ((unit) (int -3))))))",
                ],
                "ok",
            ),
        ],
    );
}

/// The message is the canonical string with its escapes.
#[test]
fn a_message_is_quoted() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"a\\\"b\\\\c\\nd é☃\", 1);
  diagnostic(\"\", ());
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))",
                    "(record 6 3 M () (string \"\") (unit))",
                ],
                "ok",
            ),
            (
                Some(135),
                &["(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))"],
                "S015 6:3 the fuel cannot pay 36 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(170),
                &["(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))"],
                "S015 6:3 the fuel cannot pay 36 unit(s); 35 remain; raise --fuel",
            ),
            (
                Some(171),
                &[
                    "(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))",
                    "(record 6 3 M () (string \"\") (unit))",
                ],
                "S015 7:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(172),
                &[
                    "(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))",
                    "(record 6 3 M () (string \"\") (unit))",
                ],
                "S015 7:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(173),
                &[
                    "(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))",
                    "(record 6 3 M () (string \"\") (unit))",
                ],
                "S015 7:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(174),
                &[
                    "(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))",
                    "(record 6 3 M () (string \"\") (unit))",
                ],
                "S015 7:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(175),
                &[
                    "(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))",
                    "(record 6 3 M () (string \"\") (unit))",
                ],
                "S015 7:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(176),
                &[
                    "(record 5 3 M () (string \"a\\\"b\\\\c\\nd é☃\") (int 1))",
                    "(record 6 3 M () (string \"\") (unit))",
                ],
                "ok",
            ),
        ],
    );
}

/// A hardware scalar is `(hw <type>)`, and a tuple charges 1 and its static part 1.
#[test]
fn a_hardware_scalar_and_tuple() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"s\", d);
  diagnostic(\"t\", (d, 1, c));
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 5 3 M () (string \"s\") (hw (uint 8)))",
                    "(record 6 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))",
                ],
                "ok",
            ),
            (
                Some(120),
                &["(record 5 3 M () (string \"s\") (hw (uint 8)))"],
                "S015 6:3 the fuel cannot pay 72 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(191),
                &["(record 5 3 M () (string \"s\") (hw (uint 8)))"],
                "S015 6:3 the fuel cannot pay 72 unit(s); 71 remain; raise --fuel",
            ),
            (
                Some(192),
                &[
                    "(record 5 3 M () (string \"s\") (hw (uint 8)))",
                    "(record 6 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))",
                ],
                "S015 7:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(193),
                &[
                    "(record 5 3 M () (string \"s\") (hw (uint 8)))",
                    "(record 6 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))",
                ],
                "S015 7:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(194),
                &[
                    "(record 5 3 M () (string \"s\") (hw (uint 8)))",
                    "(record 6 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))",
                ],
                "S015 7:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(195),
                &[
                    "(record 5 3 M () (string \"s\") (hw (uint 8)))",
                    "(record 6 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))",
                ],
                "S015 7:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(196),
                &[
                    "(record 5 3 M () (string \"s\") (hw (uint 8)))",
                    "(record 6 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))",
                ],
                "S015 7:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(197),
                &[
                    "(record 5 3 M () (string \"s\") (hw (uint 8)))",
                    "(record 6 3 M () (string \"t\") (tuple ((hw (uint 8)) (int 1) (hw bool))))",
                ],
                "ok",
            ),
        ],
    );
}

/// Nested aggregates with hardware and static leaves.
#[test]
fn nested_hardware_aggregates() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"n\", ((d, 2), [c, c], ((), \"x\")));
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 5 3 M () (string \"n\") (tuple ((tuple ((hw (uint 8)) (int 2))) (array bool ((hw bool) (hw bool))) (tuple ((unit) (string \"x\"))))))",
                ],
                "ok",
            ),
            (
                Some(102),
                &[],
                "S015 5:3 the fuel cannot pay 137 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(238),
                &[],
                "S015 5:3 the fuel cannot pay 137 unit(s); 136 remain; raise --fuel",
            ),
            (
                Some(239),
                &[
                    "(record 5 3 M () (string \"n\") (tuple ((tuple ((hw (uint 8)) (int 2))) (array bool ((hw bool) (hw bool))) (tuple ((unit) (string \"x\"))))))",
                ],
                "S015 6:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(240),
                &[
                    "(record 5 3 M () (string \"n\") (tuple ((tuple ((hw (uint 8)) (int 2))) (array bool ((hw bool) (hw bool))) (tuple ((unit) (string \"x\"))))))",
                ],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(241),
                &[
                    "(record 5 3 M () (string \"n\") (tuple ((tuple ((hw (uint 8)) (int 2))) (array bool ((hw bool) (hw bool))) (tuple ((unit) (string \"x\"))))))",
                ],
                "S015 6:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(242),
                &[
                    "(record 5 3 M () (string \"n\") (tuple ((tuple ((hw (uint 8)) (int 2))) (array bool ((hw bool) (hw bool))) (tuple ((unit) (string \"x\"))))))",
                ],
                "S015 6:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(243),
                &[
                    "(record 5 3 M () (string \"n\") (tuple ((tuple ((hw (uint 8)) (int 2))) (array bool ((hw bool) (hw bool))) (tuple ((unit) (string \"x\"))))))",
                ],
                "S015 6:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(244),
                &[
                    "(record 5 3 M () (string \"n\") (tuple ((tuple ((hw (uint 8)) (int 2))) (array bool ((hw bool) (hw bool))) (tuple ((unit) (string \"x\"))))))",
                ],
                "ok",
            ),
        ],
    );
}

/// A reference renders from its type: a part without a hardware leaf is its static zero.
#[test]
fn a_reference_renders_from_its_type() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  input a: (UInt[8], [Bool; 0], ());
  input v: [UInt[4]; 3];
  output o: UInt[8];
  diagnostic(\"a\", a);
  diagnostic(\"v\", v);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                    "(record 8 3 M () (string \"v\") (array (uint 4) ((hw (uint 4)) (hw (uint 4)) (hw (uint 4)))))",
                ],
                "ok",
            ),
            (
                Some(208),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                ],
                "S015 8:3 the fuel cannot pay 91 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(298),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                ],
                "S015 8:3 the fuel cannot pay 91 unit(s); 90 remain; raise --fuel",
            ),
            (
                Some(299),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                    "(record 8 3 M () (string \"v\") (array (uint 4) ((hw (uint 4)) (hw (uint 4)) (hw (uint 4)))))",
                ],
                "S015 9:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(300),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                    "(record 8 3 M () (string \"v\") (array (uint 4) ((hw (uint 4)) (hw (uint 4)) (hw (uint 4)))))",
                ],
                "S015 9:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(301),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                    "(record 8 3 M () (string \"v\") (array (uint 4) ((hw (uint 4)) (hw (uint 4)) (hw (uint 4)))))",
                ],
                "S015 9:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(302),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                    "(record 8 3 M () (string \"v\") (array (uint 4) ((hw (uint 4)) (hw (uint 4)) (hw (uint 4)))))",
                ],
                "S015 9:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(303),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                    "(record 8 3 M () (string \"v\") (array (uint 4) ((hw (uint 4)) (hw (uint 4)) (hw (uint 4)))))",
                ],
                "S015 9:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(304),
                &[
                    "(record 7 3 M () (string \"a\") (tuple ((hw (uint 8)) (array bool ()) (unit))))",
                    "(record 8 3 M () (string \"v\") (array (uint 4) ((hw (uint 4)) (hw (uint 4)) (hw (uint 4)))))",
                ],
                "ok",
            ),
        ],
    );
}

/// A reference of 40 tuples charges 1 for the array and 1 for each tuple.
#[test]
fn a_wide_reference_charges_each_container_once() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  input big: [(UInt[1],); 40];
  output o: UInt[8];
  diagnostic(\"big\", big);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 6 3 M () (string \"big\") (array (tuple ((uint 1))) ((tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))))))",
                ],
                "ok",
            ),
            (
                Some(934),
                &[],
                "S015 6:3 the fuel cannot pay 1021 unit(s); 726 remain; raise --fuel",
            ),
            (
                Some(1228),
                &[],
                "S015 6:3 the fuel cannot pay 1021 unit(s); 1020 remain; raise --fuel",
            ),
            (
                Some(1229),
                &[
                    "(record 6 3 M () (string \"big\") (array (tuple ((uint 1))) ((tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))))))",
                ],
                "S015 7:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(1230),
                &[
                    "(record 6 3 M () (string \"big\") (array (tuple ((uint 1))) ((tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))))))",
                ],
                "S015 7:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(1231),
                &[
                    "(record 6 3 M () (string \"big\") (array (tuple ((uint 1))) ((tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))))))",
                ],
                "S015 7:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(1232),
                &[
                    "(record 6 3 M () (string \"big\") (array (tuple ((uint 1))) ((tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))))))",
                ],
                "S015 7:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(1233),
                &[
                    "(record 6 3 M () (string \"big\") (array (tuple ((uint 1))) ((tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))))))",
                ],
                "S015 7:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(1234),
                &[
                    "(record 6 3 M () (string \"big\") (array (tuple ((uint 1))) ((tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))) (tuple ((hw (uint 1)))))))",
                ],
                "ok",
            ),
        ],
    );
}

/// A reference to a struct renders as a record of its type.
#[test]
fn a_struct_reference_names_its_type() {
    let src = "struct H { x: UInt[4], y: Bool }
struct G(comptime W: Nat) { x: UInt[W], y: Bool }
module M() {
  input c: Bool;
  input d: UInt[8];
  input h: H;
  input g: G[4];
  output o: UInt[8];
  diagnostic(\"h\", h);
  diagnostic(\"g\", g);
  diagnostic(\"x\", h.x);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                    "(record 11 3 M () (string \"x\") (hw (uint 4)))",
                ],
                "ok",
            ),
            (
                Some(305),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                ],
                "S015 11:3 the fuel cannot pay 45 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(349),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                ],
                "S015 11:3 the fuel cannot pay 45 unit(s); 44 remain; raise --fuel",
            ),
            (
                Some(350),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                    "(record 11 3 M () (string \"x\") (hw (uint 4)))",
                ],
                "S015 12:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(351),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                    "(record 11 3 M () (string \"x\") (hw (uint 4)))",
                ],
                "S015 12:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(352),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                    "(record 11 3 M () (string \"x\") (hw (uint 4)))",
                ],
                "S015 12:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(353),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                    "(record 11 3 M () (string \"x\") (hw (uint 4)))",
                ],
                "S015 12:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(354),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                    "(record 11 3 M () (string \"x\") (hw (uint 4)))",
                ],
                "S015 12:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(355),
                &[
                    "(record 9 3 M () (string \"h\") (record (struct root H ()) ((hw (uint 4)) (hw bool))))",
                    "(record 10 3 M () (string \"g\") (record (struct root G ((int 4))) ((hw (uint 4)) (hw bool))))",
                    "(record 11 3 M () (string \"x\") (hw (uint 4)))",
                ],
                "ok",
            ),
        ],
    );
}

/// Each handle kind renders with its type and core name; a handle has no measure charge.
#[test]
#[allow(clippy::too_many_lines)]
fn each_handle_renders_by_its_kind() {
    let src = "module C() {
  input a: Bool;
  output q: Bool;
  q := a;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  reg r: UInt[8] = 0;
  r := d;
  wire w: (Bool, UInt[2]);
  w := (c, 1);
  mem m: [UInt[8]; 4];
  write_port(m, 0, d, c);
  let k = read_port(m, 0, c);
  instance u = C();
  u.a := c;
  output o: UInt[8];
  diagnostic(\"r\", r);
  diagnostic(\"w\", w);
  diagnostic(\"o\", o);
  diagnostic(\"m\", m);
  diagnostic(\"u\", u);
  diagnostic(\"i\", u.a);
  diagnostic(\"q\", u.q);
  diagnostic(\"clk\", clock);
  diagnostic(\"k\", k);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                    "(record 27 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (uint 8)))) ((hw (uint 8)) (hw bool))))",
                ],
                "ok",
            ),
            (
                Some(695),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                ],
                "S015 27:3 the fuel cannot pay 114 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(808),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                ],
                "S015 27:3 the fuel cannot pay 114 unit(s); 113 remain; raise --fuel",
            ),
            (
                Some(809),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                    "(record 27 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (uint 8)))) ((hw (uint 8)) (hw bool))))",
                ],
                "S015 28:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(810),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                    "(record 27 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (uint 8)))) ((hw (uint 8)) (hw bool))))",
                ],
                "S015 28:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(811),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                    "(record 27 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (uint 8)))) ((hw (uint 8)) (hw bool))))",
                ],
                "S015 28:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(812),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                    "(record 27 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (uint 8)))) ((hw (uint 8)) (hw bool))))",
                ],
                "S015 28:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(813),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                    "(record 27 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (uint 8)))) ((hw (uint 8)) (hw bool))))",
                ],
                "S015 28:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(814),
                &[
                    "(record 19 3 M () (string \"r\") (reg (uint 8) r))",
                    "(record 20 3 M () (string \"w\") (wire (tuple (bool (uint 2))) w))",
                    "(record 21 3 M () (string \"o\") (output (uint 8) o))",
                    "(record 22 3 M () (string \"m\") (mem (array (uint 8) 4) m))",
                    "(record 23 3 M () (string \"u\") (instance C u))",
                    "(record 24 3 M () (string \"i\") (input bool u a))",
                    "(record 25 3 M () (string \"q\") (hw bool))",
                    "(record 26 3 M () (string \"clk\") (domain clock))",
                    "(record 27 3 M () (string \"k\") (record (struct prelude ReadResponse ((type (uint 8)))) ((hw (uint 8)) (hw bool))))",
                ],
                "ok",
            ),
        ],
    );
}

/// A value that waits for its type is S010 at the call, after the message.
#[test]
fn a_value_that_waits_is_s010_at_the_call() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"one\", 1);
  diagnostic(\"s\", []);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[(
            None,
            &["(record 5 3 M () (string \"one\") (int 1))"],
            "S010 6:3",
        )],
    );
}

/// The message `[]` is S010 at the call.
#[test]
fn a_message_that_waits_is_s010_at_the_call() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic([], 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S010 5:3")]);
}

/// A nested literal with `[]` waits too.
#[test]
fn a_nested_empty_array_waits() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"s\", [1, []]);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S010 5:3")]);
}

/// The message is a String: an Int is S010 after the records before it.
#[test]
fn an_int_message_is_s010() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"a\", 1);
  diagnostic(5, 1);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[(
            None,
            &["(record 5 3 M () (string \"a\") (int 1))"],
            "S010 6:3",
        )],
    );
}

/// A hardware message is S011.
#[test]
fn a_hardware_message_is_s011() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(d, 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S011 5:3")]);
}

/// A register as the message is hardware: S011.
#[test]
fn a_register_message_is_s011() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  reg r: UInt[8] = 0;
  r := d;
  output o: UInt[8];
  diagnostic(r, 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S011 7:3")]);
}

/// A wire with an empty type as the message is S011 by the handle check, with no read.
#[test]
fn an_empty_wire_message_is_s011() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  wire ew: [Bool; 0];
  ew := [];
  output o: UInt[8];
  diagnostic(ew, 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S011 7:3")]);
}

/// A child input as the message is S017.
#[test]
fn a_child_input_message_is_s017() {
    let src = "module C() {
  input a: Bool;
  output q: Bool;
  q := a;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  instance u = C();
  u.a := c;
  output o: UInt[8];
  diagnostic(u.a, 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S017 12:3")]);
}

/// A memory as the message is S010.
#[test]
fn a_memory_message_is_s010() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  mem m: [UInt[8]; 4];
  write_port(m, 0, d, c);
  let k = read_port(m, 0, c);
  output o: UInt[8];
  diagnostic(m, 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S010 8:3")]);
}

/// An instance as the message is S010.
#[test]
fn an_instance_message_is_s010() {
    let src = "module C() {
  input a: Bool;
  output q: Bool;
  q := a;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  instance u = C();
  u.a := c;
  output o: UInt[8];
  diagnostic(u, 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S010 12:3")]);
}

/// A domain as the message is S010.
#[test]
fn a_domain_message_is_s010() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(clock, 1);
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S010 5:3")]);
}

/// A graph effect in a hardware arm is S016, also through a helper and before the message check.
#[test]
fn a_hardware_arm_has_no_graph_effect() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  let z = if (c) { diagnostic(5, 1) } else { 0 };
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S016 5:20")]);
}

/// The helper makes the call in the arm.
#[test]
fn a_helper_in_a_hardware_arm_is_s016() {
    let src = "fn id(x: Nat) -> Nat {
    diagnostic(\"id\", x);
    return x;
}
fn l1(x: Nat) -> Nat {
    diagnostic(\"l1\", x);
    return x;
}
fn l2(x: Nat) -> Nat {
    let f = l1;
    return f(x);
}
fn l3(x: Nat) -> Nat {
    return x.l2();
}
fn sf() -> Nat {
    diagnostic(\"sf\", 3);
    return 3;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  let z = if (c) { id(2) } else { 0 };
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S016 2:5")]);
}

/// A type argument that calls a function with a record is S016.
#[test]
fn a_structural_context_has_no_graph_effect() {
    let src = "fn id(x: Nat) -> Nat {
    diagnostic(\"id\", x);
    return x;
}
fn l1(x: Nat) -> Nat {
    diagnostic(\"l1\", x);
    return x;
}
fn l2(x: Nat) -> Nat {
    let f = l1;
    return f(x);
}
fn l3(x: Nat) -> Nat {
    return x.l2();
}
fn sf() -> Nat {
    diagnostic(\"sf\", 3);
    return 3;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  let x: UInt[sf()] = 0;
  o := 0;
}
";
    check(src, "M()", None, &[(None, &[], "S016 17:5")]);
}

/// Frames through a call, a function value, and a receiver call.
#[test]
#[allow(clippy::too_many_lines)]
fn frames_name_the_callers_outermost_first() {
    let src = "fn id(x: Nat) -> Nat {
    diagnostic(\"id\", x);
    return x;
}
fn l1(x: Nat) -> Nat {
    diagnostic(\"l1\", x);
    return x;
}
fn l2(x: Nat) -> Nat {
    let f = l1;
    return f(x);
}
fn l3(x: Nat) -> Nat {
    return x.l2();
}
fn sf() -> Nat {
    diagnostic(\"sf\", 3);
    return 3;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  let z = l3(4);
  diagnostic(\"m\", z);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                    "(record 25 3 M () (string \"m\") (int 4))",
                ],
                "ok",
            ),
            (
                Some(190),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                ],
                "S015 25:3 the fuel cannot pay 39 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(228),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                ],
                "S015 25:3 the fuel cannot pay 39 unit(s); 38 remain; raise --fuel",
            ),
            (
                Some(229),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                    "(record 25 3 M () (string \"m\") (int 4))",
                ],
                "S015 26:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(230),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                    "(record 25 3 M () (string \"m\") (int 4))",
                ],
                "S015 26:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(231),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                    "(record 25 3 M () (string \"m\") (int 4))",
                ],
                "S015 26:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(232),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                    "(record 25 3 M () (string \"m\") (int 4))",
                ],
                "S015 26:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(233),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                    "(record 25 3 M () (string \"m\") (int 4))",
                ],
                "S015 26:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(234),
                &[
                    "(record 6 5 M ((call l3 24 11) (call l2 14 12) (call l1 11 12)) (string \"l1\") (int 4))",
                    "(record 25 3 M () (string \"m\") (int 4))",
                ],
                "ok",
            ),
        ],
    );
}

/// A child names its own instantiation and has no frames of the parent.
#[test]
#[allow(clippy::too_many_lines)]
fn a_child_runs_before_the_rest_of_its_parent() {
    let src = "module C(comptime W: Nat) {
  input a: Bool;
  output q: Bool;
  diagnostic(\"child\", id(W));
  q := a;
}
fn id(x: Nat) -> Nat {
    diagnostic(\"id\", x);
    return x;
}
fn l1(x: Nat) -> Nat {
    diagnostic(\"l1\", x);
    return x;
}
fn l2(x: Nat) -> Nat {
    let f = l1;
    return f(x);
}
fn l3(x: Nat) -> Nat {
    return x.l2();
}
fn sf() -> Nat {
    diagnostic(\"sf\", 3);
    return 3;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  instance u = C(3);
  u.a := c;
  output o: UInt[8];
  diagnostic(\"p\", id(1));
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                    "(record 32 3 M () (string \"p\") (int 1))",
                ],
                "ok",
            ),
            (
                Some(323),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                ],
                "S015 32:3 the fuel cannot pay 39 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(361),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                ],
                "S015 32:3 the fuel cannot pay 39 unit(s); 38 remain; raise --fuel",
            ),
            (
                Some(362),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                    "(record 32 3 M () (string \"p\") (int 1))",
                ],
                "S015 33:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(363),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                    "(record 32 3 M () (string \"p\") (int 1))",
                ],
                "S015 33:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(364),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                    "(record 32 3 M () (string \"p\") (int 1))",
                ],
                "S015 33:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(365),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                    "(record 32 3 M () (string \"p\") (int 1))",
                ],
                "S015 33:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(366),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                    "(record 32 3 M () (string \"p\") (int 1))",
                ],
                "S015 33:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(367),
                &[
                    "(record 8 5 C$3 ((call id 4 23)) (string \"id\") (int 3))",
                    "(record 4 3 C$3 () (string \"child\") (int 3))",
                    "(record 8 5 M ((call id 32 19)) (string \"id\") (int 1))",
                    "(record 32 3 M () (string \"p\") (int 1))",
                ],
                "ok",
            ),
        ],
    );
}

/// Two instances of one instantiation give one record.
#[test]
fn a_done_instantiation_makes_no_second_record() {
    let src = "module C(comptime W: Nat) {
  input a: Bool;
  output q: Bool;
  diagnostic(\"child\", W);
  q := a;
}
module M() {
  input c: Bool;
  input d: UInt[8];
  instance u = C(8);
  u.a := c;
  instance v = C(8);
  v.a := c;
  instance s = C(2);
  s.a := c;
  output o: UInt[8];
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "ok",
            ),
            (
                Some(312),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "S015 16:13 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(313),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "S015 16:13 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(314),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "S015 17:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(315),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "S015 17:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(316),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "S015 17:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(317),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "S015 17:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(318),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "S015 17:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(319),
                &[
                    "(record 4 3 C$8 () (string \"child\") (int 8))",
                    "(record 4 3 C$2 () (string \"child\") (int 2))",
                ],
                "ok",
            ),
        ],
    );
}

/// One record for each iteration, at one position.
#[test]
fn a_loop_makes_a_record_for_each_iteration() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  comptime for i in 0..3 {
    diagnostic(\"i\", i);
  }
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[
            (
                None,
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                    "(record 6 5 M () (string \"i\") (int 2))",
                ],
                "ok",
            ),
            (
                Some(165),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                ],
                "S015 6:5 the fuel cannot pay 38 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(202),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                ],
                "S015 6:5 the fuel cannot pay 38 unit(s); 37 remain; raise --fuel",
            ),
            (
                Some(203),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                    "(record 6 5 M () (string \"i\") (int 2))",
                ],
                "S015 8:3 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(204),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                    "(record 6 5 M () (string \"i\") (int 2))",
                ],
                "S015 8:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(205),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                    "(record 6 5 M () (string \"i\") (int 2))",
                ],
                "S015 8:8 the fuel cannot pay 1 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(206),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                    "(record 6 5 M () (string \"i\") (int 2))",
                ],
                "S015 8:3 the fuel cannot pay 2 unit(s); 0 remain; raise --fuel",
            ),
            (
                Some(207),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                    "(record 6 5 M () (string \"i\") (int 2))",
                ],
                "S015 8:3 the fuel cannot pay 2 unit(s); 1 remain; raise --fuel",
            ),
            (
                Some(208),
                &[
                    "(record 6 5 M () (string \"i\") (int 0))",
                    "(record 6 5 M () (string \"i\") (int 1))",
                    "(record 6 5 M () (string \"i\") (int 2))",
                ],
                "ok",
            ),
        ],
    );
}

/// An error after two records keeps them.
#[test]
fn records_before_an_error_stay() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  diagnostic(\"a\", 1);
  diagnostic(\"b\", (d, 2));
  static_assert(false, \"stop\");
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[(
            None,
            &[
                "(record 5 3 M () (string \"a\") (int 1))",
                "(record 6 3 M () (string \"b\") (tuple ((hw (uint 8)) (int 2))))",
            ],
            "S014 7:3",
        )],
    );
}

/// The S018 of an undriven register waits for the end of the body.
#[test]
fn a_missing_binding_at_the_end_keeps_the_records() {
    let src = "module M() {
  input c: Bool;
  input d: UInt[8];
  reg r: UInt[8] = 0;
  output o: UInt[8];
  diagnostic(\"a\", 1);
  o := 0;
}
";
    check(
        src,
        "M()",
        None,
        &[(
            None,
            &["(record 6 3 M () (string \"a\") (int 1))"],
            "S018 4:3",
        )],
    );
}

/// The depth limit is S015 with the records before it.
#[test]
fn a_deep_recursion_makes_deep_frames() {
    let src = "fn rec(n: Nat) -> Nat {
  diagnostic(\"rec\", n);
  return if (n == 0) { 0 } else { rec(n - 1) };
}
module M() {
  input c: Bool;
  input d: UInt[8];
  output o: UInt[8];
  rec(5);
  o := 0;
}
";
    check(
        src,
        "M()",
        Some(4),
        &[(
            None,
            &[
                "(record 2 3 M ((call rec 9 3)) (string \"rec\") (int 5))",
                "(record 2 3 M ((call rec 9 3) (call rec 3 35)) (string \"rec\") (int 4))",
                "(record 2 3 M ((call rec 9 3) (call rec 3 35) (call rec 3 35)) (string \"rec\") (int 3))",
            ],
            "S015 3:35 the nesting depth goes above 4; raise --depth",
        )],
    );
}

const EVAL_PRE: &str = "struct Q { a: UInt[4], b: Int }
fn id(x: Nat) -> Nat {
    diagnostic(\"id\", x);
    return x;
}
fn l1(x: Nat) -> Nat {
    diagnostic(\"l1\", (x, x));
    return x;
}
fn l2(x: Nat) -> Nat {
    let f = l1;
    return f(x) + id(x);
}
fn l3(x: Nat) -> Nat {
    return x.l2();
}
const nb: Int = 123456789012345678901234567890123456789;
";

/// `eval` prints no record, but each call charges as in an elaboration, with the emitted name
/// `-` and the frames in the measured line. The units are those of the Lean binary: the
/// smallest fuel that passes is the used fuel plus the length of the result.
#[test]
fn eval_charges_the_records_it_does_not_print() {
    let used = |expr: &str, want: &str, units: u64| {
        let (text, got) = crate::tests::run(EVAL_PRE, expr, 1_000_000, 1000);
        assert_eq!((text.as_str(), got), (want, units), "{expr}");
    };
    used("diagnostic(\"x\", 1)", "(unit)", 49);
    used("id(3)", "(int 3)", 76);
    used("l3(2)", "(int 4)", 270);
    used("\"m\".diagnostic(Q(1, 2))", "(unit)", 125);
    used("diagnostic(\"a\", (1, \"x\", [nb, 1]))", "(unit)", 178);
    let (_, got) = crate::tests::run(EVAL_PRE, "id(3)", 75, 1000);
    assert_eq!(got, 0, "one unit less stops the call");
    let (text, _) = crate::tests::run(EVAL_PRE, "diagnostic(\"s\", [])", 1_000_000, 1000);
    assert_eq!(text, "S010 1:1");
}

/// The message of the first error of the module `M` in `src`.
fn said(src: &str) -> String {
    let file = load(src).unwrap();
    let done = observe_with(
        &file,
        "M()",
        parse::DEFAULT_SYNTAX_DEPTH,
        Budget::default(),
        crate::names::sha16,
    );
    match done {
        Ok(crate::Observed {
            outcome: Err(e), ..
        }) => e.message,
        _ => "ok".to_owned(),
    }
}

fn with_ports(ports: &str, body: &str, items: &str) -> String {
    format!(
        "{items}module M() {{\n  input c: Bool;\n  input d: UInt[8];\n{ports}  output o: UInt[8];\n{body}  o := 0;\n}}\n"
    )
}

const CHILD: &str = "module C() {\n  input a: Bool;\n  output q: Bool;\n  q := a;\n}\n";
const MEMORY: &str =
    "  mem m: [UInt[8]; 4];\n  write_port(m, 0, d, c);\n  let k = read_port(m, 0, c);\n";

/// The messages equal those of Lean, and each error is at the call.
#[test]
fn the_messages_of_diagnostic_equal_those_of_lean() {
    let body = |b: &str| with_ports("", b, "");
    assert_eq!(
        said(&body(
            "  let z = if (c) { diagnostic(\"a\", 1) } else { 0 };\n"
        )),
        "a hardware arm has no graph effect such as `diagnostic`"
    );
    assert_eq!(
        said(&with_ports(
            "",
            "  let x: UInt[sf()] = 0;\n",
            "fn sf() -> Nat {\n  diagnostic(\"sf\", 3);\n  return 3;\n}\n"
        )),
        "a type or a constant has no graph effect such as `diagnostic`; call it before and use the result"
    );
    assert_eq!(
        said(&body("  diagnostic(5, 1);\n")),
        "the message of `diagnostic` is a String, not Int"
    );
    assert_eq!(
        said(&body("  diagnostic(d, 1);\n")),
        "the message of `diagnostic` is a static String, not hardware UInt[8]"
    );
    assert_eq!(
        said(&with_ports(
            "  reg r: UInt[8] = 0;\n  r := d;\n",
            "  diagnostic(r, 1);\n",
            ""
        )),
        "the message of `diagnostic` is a static String, not a register"
    );
    let child = "  instance u = C();\n  u.a := c;\n";
    assert_eq!(
        said(&with_ports(child, "  diagnostic(u.a, 1);\n", CHILD)),
        "the input `a` of `u` is a target only; read the value that you bind to it"
    );
    assert_eq!(
        said(&with_ports(child, "  diagnostic(u, 1);\n", CHILD)),
        "`u` is an instance, not data; read its outputs as `u.q`"
    );
    assert_eq!(
        said(&with_ports(MEMORY, "  diagnostic(m, 1);\n", "")),
        "`m` is a memory, not data; read a word with `read_port`"
    );
    assert_eq!(
        said(&body("  diagnostic(clock, 1);\n")),
        "a domain is not data"
    );
    assert_eq!(
        said(&body("  diagnostic(\"s\", []);\n")),
        "the value of `diagnostic` needs a type; `[]` without a type"
    );
    assert_eq!(
        said(&body("  diagnostic([], 1);\n")),
        "the message of `diagnostic` is a String, not `[]` without a type"
    );
    assert_eq!(
        said(&body("  diagnostic(\"s\", [1, []]);\n")),
        "the value of `diagnostic` needs a type; an array literal with `[]` without a type"
    );
}

/// A module `M` with the extra ports `ports` and the body `body`, over the enum `Op`.
fn enum_module(ports: &str, body: &str, extra: &str) -> String {
    format!(
        "{extra}module M() {{\n  input d: UInt[8];\n{ports}  output o: Bool;\n{body}  o := true;\n}}\n"
    )
}

/// A hardware enum renders as `(enum <type> <tag> <payload>)`: a static tag is an integer, and a
/// hardware leaf is `(hw (uint ..))`. A reference of an enum type renders each leaf as a
/// hardware leaf, and an empty payload has no part.
#[test]
fn an_enum_renders_as_its_tag_and_its_payload() {
    let op = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n";
    let reference = enum_module("  input a: Op;\n", "  diagnostic(\"r\", a);\n", op);
    check(
        &reference,
        "M",
        None,
        &[(
            None,
            &[
                "(record 6 3 M () (string \"r\") (enum (enum root Op ()) (hw (uint 2)) (hw (uint 8))))",
            ],
            "ok",
        )],
    );
    let hardware = enum_module("", "  diagnostic(\"h\", Op::Load(d));\n", op);
    check(
        &hardware,
        "M",
        None,
        &[(
            None,
            &["(record 5 3 M () (string \"h\") (enum (enum root Op ()) 1 (hw (uint 8))))"],
            "ok",
        )],
    );
    let flag = enum_module(
        "  input a: F;\n",
        "  diagnostic(\"r\", a);\n",
        "enum F: UInt[1] { A = 0 }\n",
    );
    check(
        &flag,
        "M",
        None,
        &[(
            None,
            &["(record 6 3 M () (string \"r\") (enum (enum root F ()) (hw (uint 1))))"],
            "ok",
        )],
    );
    let fixed = enum_module("", "  diagnostic(\"s\", Op::Load(3));\n", op);
    check(
        &fixed,
        "M",
        None,
        &[(
            None,
            &["(record 5 3 M () (string \"s\") (enum (enum root Op ()) 1 (uint 8 3)))"],
            "ok",
        )],
    );
}
