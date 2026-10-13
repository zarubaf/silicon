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

const LEAF_PORTS: &str = "struct S { a: Bool, b: UInt[4] }\n\
    struct P { hdr: (UInt[4], Bool), data: [S; 2] }\n\
    module L() domains() {\n  input xs: [UInt[4]; 2];\n  input t: (Bool, SInt[4]);\n  \
    input add: S;\n  input pkt: P;\n  output y: P;\n  output mux: [Bool; 1];\n  \
    y := pkt;\n  mux := [add.a];\n}\n";

/// One entry for each leaf of a port, in packing order: `.k` for an array or tuple element,
/// and a keyword port with leaves keeps its source name and has no `0k`.
#[test]
fn the_schema_has_one_entry_for_each_leaf() {
    assert_eq!(
        names(LEAF_PORTS, "L"),
        (
            pairs(&[
                ("add.a", "add$a"),
                ("add.b", "add$b"),
                ("pkt.hdr.0", "pkt$hdr$0e"),
                ("pkt.hdr.1", "pkt$hdr$1e"),
                ("pkt.data.0.a", "pkt$data$0e$a"),
                ("pkt.data.0.b", "pkt$data$0e$b"),
                ("pkt.data.1.a", "pkt$data$1e$a"),
                ("pkt.data.1.b", "pkt$data$1e$b"),
                ("t.0", "t$0e"),
                ("t.1", "t$1e"),
                ("xs.0", "xs$0e"),
                ("xs.1", "xs$1e"),
            ]),
            pairs(&[
                ("mux.0", "mux$0e"),
                ("y.hdr.0", "y$hdr$0e"),
                ("y.hdr.1", "y$hdr$1e"),
                ("y.data.0.a", "y$data$0e$a"),
                ("y.data.0.b", "y$data$0e$b"),
                ("y.data.1.a", "y$data$1e$a"),
                ("y.data.1.b", "y$data$1e$b"),
            ]),
        )
    );
}

const EMPTY_PORTS: &str = "struct E { a: Bool, z: (), e: [Bool; 0], c: (UInt[2], ()) }\n\
    module M() {\n  input u: ();\n  input n: [UInt[8]; 0];\n  input p: E;\n  \
    output o: ();\n  output y: E;\n  o := ();\n  y := p;\n}\n";

/// An empty port and an empty leaf have no entry, and the other fields keep their order.
#[test]
fn an_empty_port_and_an_empty_leaf_have_no_entry() {
    assert_eq!(
        names(EMPTY_PORTS, "M"),
        (
            pairs(&[
                ("clock$0rst", "clock$0rst"),
                ("p.a", "p$a"),
                ("p.c.0", "p$c$0e")
            ]),
            pairs(&[("y.a", "y$a"), ("y.c.0", "y$c$0e")]),
        )
    );
    assert_eq!(
        run(
            EMPTY_PORTS,
            "M",
            &["in=(clock$0rst false p.a true p.c.0 2)"]
        ),
        "out=(y.a true y.c.0 2)\n"
    );
    assert_eq!(
        run(
            EMPTY_PORTS,
            "M",
            &["in=(clock$0rst false p$a true p.c.0 2)"]
        ),
        "expected input p.a"
    );
}

const AGG_RUN: &str = "struct R { n: UInt[4], s: SInt[4], f: Bool }\n\
    module A() {\n  input t: (UInt[4], UInt[4]);\n  input v: R;\n  \
    output swap: (UInt[4], UInt[4]);\n  output q: R;\n  output eq: Bool;\n  \
    reg r: R = R(5, -2, true);\n  r := v;\n  swap := (t.1, t.0);\n  q := r;\n  eq := r == v;\n}\n";

/// A vector runs through an aggregate design by leaf.
#[test]
fn a_vector_runs_through_an_aggregate_design() {
    assert_eq!(
        run(
            AGG_RUN,
            "A",
            &[
                "in=(clock$0rst true t.0 1 t.1 2 v.n 3 v.s -4 v.f false)",
                "in=(clock$0rst false t.0 9 t.1 0 v.n 3 v.s -4 v.f false)",
                "in=(clock$0rst false t.0 9 t.1 0 v.n 7 v.s 7 v.f true)",
                "in=(clock$0rst false t.0 9 t.1 0 v.n 7 v.s 7 v.f true)"
            ]
        ),
        text(&[
            "out=(eq false q.n 0 q.s 0 q.f false swap.0 2 swap.1 1)",
            "out=(eq false q.n 5 q.s -2 q.f true swap.0 0 swap.1 9)",
            "out=(eq false q.n 3 q.s -4 q.f false swap.0 0 swap.1 9)",
            "out=(eq true q.n 7 q.s 7 q.f true swap.0 0 swap.1 9)"
        ])
    );
    assert_eq!(
        run(
            AGG_RUN,
            "A",
            &["in=(clock$0rst true t.0 1 t.1 2 v.n 3 v.s -9 v.f false)"]
        ),
        "input v.s exceeds its width"
    );
}
