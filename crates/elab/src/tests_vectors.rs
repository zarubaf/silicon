// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Vectors` in Lean: the port schema, the values of each
//! type, the faults of an input line, and runs of the counter and of registers with a nonzero
//! reset value.

use crate::tests_elab::load;
use crate::types::Ty;
use crate::{Budget, Failure, check, elaborate};
use core_ir::interp::Sim;
use core_ir::vectors::inputs;

/// The schema and the checked design of `src` with the top `top`, or the code and the
/// position of the first error.
fn setup(src: &str, top: &str) -> Result<(crate::vectors::Schema, core_ir::typed::Design), String> {
    let file = load(src)?;
    let at = |e: crate::Error| format!("{} {}:{}", e.code, e.pos.line, e.pos.col);
    let budget = Budget::default();
    let design = match elaborate(&file, top, parse::DEFAULT_SYNTAX_DEPTH, budget).unwrap() {
        Ok(d) => d,
        Err(e) => return Err(at(e)),
    };
    let lowered = match design.lower().unwrap() {
        Ok(l) => l,
        Err(Failure::Source(e)) => return Err(at(e)),
        Err(Failure::Defect(m)) => panic!("{m}"),
    };
    let typed = match check(&lowered.design) {
        Ok(t) => t,
        Err(Failure::Source(e)) => return Err(at(e)),
        Err(Failure::Defect(m)) => panic!("{m}"),
    };
    let schema = design.schema().unwrap();
    assert!(schema.fits(&lowered.design));
    Ok((schema, typed))
}

/// The output lines of `run` for the input lines `lines`, from the zero state. A fault of an
/// input line gives its message instead.
fn run(src: &str, top: &str, lines: &[&str]) -> String {
    let (schema, typed) = match setup(src, top) {
        Ok(s) => s,
        Err(e) => return e,
    };
    let module = &typed.modules()[typed.top().index()];
    let mut values = Vec::new();
    for line in lines {
        match schema.parse_line(line) {
            Ok(v) => values.push(inputs(module, v).unwrap()),
            Err(m) => return m,
        }
    }
    let mut sim = Sim::new(&typed).unwrap();
    let mut out = String::new();
    for v in &values {
        out.push_str(&schema.print_line(sim.step(v).values()));
    }
    out
}

type Pairs = Vec<(String, String)>;

/// The source names and the core names of the schema.
fn names(src: &str, top: &str) -> (Pairs, Pairs) {
    let (s, _) = setup(src, top).unwrap();
    let pair = |e: &crate::vectors::Entry| (e.name.clone(), e.core.clone());
    (
        s.inputs.iter().map(pair).collect(),
        s.outputs.iter().map(pair).collect(),
    )
}

fn pairs(xs: &[(&str, &str)]) -> Pairs {
    xs.iter()
        .map(|(a, b)| ((*a).to_owned(), (*b).to_owned()))
        .collect()
}

fn text(lines: &[&str]) -> String {
    let mut out = String::new();
    for l in lines {
        out.push_str(l);
        out.push('\n');
    }
    out
}

const PORTS: &str = "module P() {\n  input zz: Bool;\n  input add: UInt[4];\n  input a_b: Bool;\n  \
    output y: UInt[4];\n  output mux: Bool;\n  y := add;\n  mux := zz && a_b;\n}\n";

const COMB: &str =
    "module C() domains() {\n  input a: SInt[4];\n  output b: SInt[4];\n  b := -a;\n}\n";

/// The reset comes first, then the inputs in byte order of their names. A keyword port keeps
/// its source name in a vector, and its core name has `$0k`.
#[test]
fn the_port_schema() {
    assert_eq!(
        names(PORTS, "P"),
        (
            pairs(&[
                ("clock$0rst", "clock$0rst"),
                ("a_b", "a_b"),
                ("add", "add$0k"),
                ("zz", "zz")
            ]),
            pairs(&[("mux", "mux$0k"), ("y", "y")])
        )
    );
    assert_eq!(
        run(
            PORTS,
            "P",
            &["in=(clock$0rst false a_b true add 9 zz true)"]
        ),
        "out=(mux true y 9)\n"
    );
    assert_eq!(
        names(COMB, "C"),
        (pairs(&[("a", "a")]), pairs(&[("b", "b")]))
    );
    assert_eq!(
        run(
            COMB,
            "C",
            &[
                "in=(a -8)",
                "in=(a 7)",
                "in=(a 0)",
                "in=(a -0)",
                "in=(a -1)"
            ]
        ),
        text(&[
            "out=(b -8)",
            "out=(b -7)",
            "out=(b 0)",
            "out=(b 0)",
            "out=(b 1)"
        ])
    );
}

/// The core value of a source value, as a number, or `None`.
fn value(t: &Ty, v: &str) -> Option<String> {
    super::vectors::parse_value("x", t, v)
        .ok()
        .map(|b| crate::int::constant(&b).to_string())
}

/// The values of each type. An input value can have leading zeros.
#[test]
fn the_values_of_each_type() {
    let cases: [(Ty, &str, Option<&str>); 16] = [
        (Ty::Bool, "true", Some("1")),
        (Ty::Bool, "false", Some("0")),
        (Ty::Bool, "1", None),
        (Ty::UInt(8), "255", Some("255")),
        (Ty::UInt(8), "007", Some("7")),
        (Ty::UInt(8), "256", None),
        (Ty::UInt(8), "-1", None),
        (Ty::UInt(8), "+1", None),
        (Ty::SInt(8), "-128", Some("128")),
        (Ty::SInt(8), "-1", Some("255")),
        (Ty::SInt(8), "127", Some("127")),
        (Ty::SInt(8), "128", None),
        (Ty::SInt(8), "-129", None),
        (Ty::SInt(8), "-", None),
        (Ty::SInt(1), "-1", Some("1")),
        (Ty::SInt(1), "1", None),
    ];
    for (t, v, want) in cases {
        assert_eq!(value(&t, v).as_deref(), want, "{v}");
    }
    let bits = |w: u32, v: u32| core_ir::Bits::new(w, v.into()).unwrap();
    let texts = [
        super::vectors::value_text(&Ty::Bool, &bits(1, 1)),
        super::vectors::value_text(&Ty::UInt(8), &bits(8, 255)),
        super::vectors::value_text(&Ty::SInt(8), &bits(8, 255)),
        super::vectors::value_text(&Ty::SInt(8), &bits(8, 128)),
        super::vectors::value_text(&Ty::SInt(8), &bits(8, 127)),
    ];
    assert_eq!(texts, ["true", "255", "-1", "-128", "127"]);
}

/// The faults of an input line, with the tokenization of a core vector.
#[test]
fn the_faults_of_an_input_line() {
    for (line, want) in [
        ("in=(a 1", "expected in=(...)"),
        ("in=()", "missing input"),
        ("in=(a 1 b 2)", "extra input tokens"),
        ("in=(b 1)", "expected input a"),
        ("in=(a 1)\r", "invalid input line ending"),
        ("in=(a 8)", "input a exceeds its width"),
    ] {
        assert_eq!(run(COMB, "C", &[line]), want, "{line}");
    }
    assert_eq!(
        run(
            PORTS,
            "P",
            &["in=(clock$0rst false add 1 a_b true zz true)"]
        ),
        "expected input a_b"
    );
    assert_eq!(
        run(PORTS, "P", &["in=(a_b true add 1 zz true)"]),
        "expected input clock$0rst"
    );
    assert_eq!(
        run(
            PORTS,
            "P",
            &[" in=(\tclock$0rst  false a_b false add 1 zz false ) "]
        ),
        "out=(mux false y 1)\n"
    );
}

const COUNTER: &str = "module Counter(comptime W: Nat) {\n    input enable: Bool;\n    \
    output value: UInt[W];\n    output full: Bool;\n    reg count: UInt[W] = 0;\n    \
    count := if (enable) { count +% 1 } else { count };\n    value := count;\n    \
    full := count == UInt[W]((1 << W) - 1);\n}\n\
    module Main() {\n    input enable: Bool;\n    output value: UInt[4];\n    \
    instance counter = Counter(4);\n    counter.enable := enable;\n    \
    value := counter.value;\n}\n";

/// The counter counts after its reset and wraps at its width. As a child of `Main`, it gets
/// the reset of the domain.
#[test]
fn the_counter_runs() {
    let on = "in=(clock$0rst false enable true)";
    let off = "in=(clock$0rst false enable false)";
    assert_eq!(
        run(
            COUNTER,
            "Counter(2)",
            &["in=(clock$0rst true enable true)", on, on, off, on, on, on]
        ),
        text(&[
            "out=(full false value 0)",
            "out=(full false value 0)",
            "out=(full false value 1)",
            "out=(full false value 2)",
            "out=(full false value 2)",
            "out=(full true value 3)",
            "out=(full false value 0)"
        ])
    );
    assert_eq!(
        run(
            COUNTER,
            "Main",
            &["in=(clock$0rst true enable true)", on, on]
        ),
        text(&["out=(value 0)", "out=(value 0)", "out=(value 1)"])
    );
}

/// Before the first reset edge, each register has the value 0 of the test convention. After
/// it, `r` has its reset value 42, and `q` of type `SInt[8]` has -1.
#[test]
fn registers_with_a_nonzero_reset_value() {
    let regs = "module Regs() {\n  input load: Bool;\n  output u: UInt[8];\n  output s: SInt[8];\n  \
                reg r: UInt[8] = 42;\n  reg q: SInt[8] = -1;\n  \
                r := if (load) { r +% 1 } else { r };\n  q := if (load) { q -% 1 } else { q };\n  \
                u := r;\n  s := q;\n}\n";
    assert_eq!(
        run(
            regs,
            "Regs",
            &[
                "in=(clock$0rst false load true)",
                "in=(clock$0rst false load false)",
                "in=(clock$0rst true load true)",
                "in=(clock$0rst false load false)",
                "in=(clock$0rst false load true)",
                "in=(clock$0rst false load true)"
            ]
        ),
        text(&[
            "out=(s 0 u 0)",
            "out=(s -1 u 1)",
            "out=(s -1 u 1)",
            "out=(s -1 u 42)",
            "out=(s -1 u 42)",
            "out=(s -2 u 43)"
        ])
    );
    assert_eq!(
        run(
            "module R() domains() {\n  reg r: Bool = false;\n}\n",
            "R",
            &[]
        ),
        "S017 2:3"
    );
}
