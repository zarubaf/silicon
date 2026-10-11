// SPDX-License-Identifier: Apache-2.0
//! Tests of the interpreter and of the `in=` and `out=` vector format.

use core_ir::Bits;
use core_ir::check::check;
use core_ir::diag::ErrorCode;
use core_ir::interp::{Outputs, Sim};
use core_ir::text::parse;
use core_ir::typed;
use core_ir::vectors::{VectorError, inputs, parse_input, print_output};

fn design(src: &str) -> typed::Design {
    let Ok(ast) = parse(src) else {
        panic!("the source must parse");
    };
    match check(&ast) {
        Ok(design) => design,
        Err(d) => panic!("the design must check: {d}"),
    }
}

fn top(design: &typed::Design) -> &typed::Module {
    &design.modules()[design.top().index()]
}

/// Runs one input line per cycle and returns the printed output lines.
fn run(src: &str, lines: &[&str]) -> Vec<String> {
    let design = design(src);
    let Ok(mut sim) = Sim::new(&design) else {
        panic!("the design must have no extern");
    };
    lines
        .iter()
        .map(|line| {
            let inputs = match parse_input(line, top(&design)) {
                Ok(inputs) => inputs,
                Err(e) => panic!("{line:?}: {e}"),
            };
            print_output(top(&design), &sim.step(&inputs))
        })
        .collect()
}

const COUNTER: &str = "\
(design counter
  (module counter
    (input clk clock)
    (input rst (bits 1))
    (input en (bits 1))
    (output q (bits 8))
    (reg r (bits 8) clk (reset sync rst (const 8 0)))
    (let inc (bits 8) (add r (const 8 1)))
    (next r (mux en inc r))
    (assign q r)))
";

/// Inputs built from values equal those of the same input line, and the outputs give their
/// values in port order.
#[test]
fn inputs_from_values_equal_a_parsed_line() {
    let design = design(COUNTER);
    let top = top(&design);
    let bits = |w: u32, v: u32| Bits::new(w, v.into()).unwrap();
    let built = inputs(top, vec![bits(1, 0), bits(1, 1)]).unwrap();
    assert_eq!(
        Some(built.clone()),
        parse_input("in=(rst 0 en 1)", top).ok()
    );
    assert!(inputs(top, vec![bits(1, 0)]).is_none());
    assert!(inputs(top, vec![bits(1, 0), bits(2, 1)]).is_none());
    let mut sim = Sim::new(&design).unwrap();
    assert_eq!(sim.step(&built).values(), [bits(8, 0)]);
    assert_eq!(sim.step(&built).values(), [bits(8, 1)]);
}

#[test]
fn the_counter_counts_from_zero() {
    let lines = ["in=(rst 0 en 1)"; 4];
    assert_eq!(
        run(COUNTER, &lines),
        ["out=(q 0)\n", "out=(q 1)\n", "out=(q 2)\n", "out=(q 3)\n"]
    );
}

#[test]
fn a_reset_clears_the_register_for_the_next_cycle() {
    let lines = [
        "in=(rst 0 en 1)",
        "in=(rst 0 en 1)",
        "in=(rst 1 en 1)",
        "in=(rst 0 en 1)",
        "in=(rst 0 en 0)",
    ];
    assert_eq!(
        run(COUNTER, &lines),
        [
            "out=(q 0)\n",
            "out=(q 1)\n",
            "out=(q 2)\n",
            "out=(q 0)\n",
            "out=(q 1)\n"
        ]
    );
}

const MEMORY: &str = "\
(design top
  (module top
    (input clk clock)
    (input wa (bits 4))
    (input wd (bits 8))
    (input we (bits 1))
    (input ra (bits 4))
    (output rd (bits 8))
    (mem m (bits 8) 12 clk)
    (write m 0 wa wd we)
    (assign rd (read m ra))))
";

#[test]
fn memory_out_of_range() {
    let lines = [
        "in=(wa 1 wd 5 we 1 ra 1)",
        "in=(wa 13 wd 7 we 1 ra 1)",
        "in=(wa 0 wd 0 we 0 ra 13)",
        "in=(wa 0 wd 0 we 0 ra 1)",
    ];
    assert_eq!(
        run(MEMORY, &lines),
        [
            "out=(rd 0)\n",
            "out=(rd 5)\n",
            "out=(rd 0)\n",
            "out=(rd 5)\n"
        ]
    );
}

#[test]
fn a_write_with_enable_zero_does_nothing() {
    let lines = [
        "in=(wa 3 wd 9 we 1 ra 3)",
        "in=(wa 3 wd 4 we 0 ra 3)",
        "in=(wa 0 wd 0 we 0 ra 3)",
    ];
    assert_eq!(
        run(MEMORY, &lines),
        ["out=(rd 0)\n", "out=(rd 9)\n", "out=(rd 9)\n"]
    );
}

#[test]
fn the_higher_write_port_wins_at_one_address() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (input a (bits 2))
    (output rd (bits 8))
    (mem m (bits 8) 4 clk)
    (write m 1 a (const 8 9) (const 1 1))
    (write m 0 a (const 8 3) (const 1 1))
    (assign rd (read m a))))
";
    assert_eq!(
        run(src, &["in=(a 2)", "in=(a 2)"]),
        ["out=(rd 0)\n", "out=(rd 9)\n"]
    );
}

#[test]
fn an_instance_output_feeds_its_own_input() {
    // `x` does not depend on `b`, so `u.x` can drive `b`. The register `r`
    // holds `b` for one cycle. The child `k` has no inputs at all.
    let src = "\
(design top
  (module konst
    (output c (bits 8))
    (assign c (const 8 40)))
  (module child
    (input clk clock)
    (input a (bits 8))
    (input b (bits 8))
    (output x (bits 8))
    (output y (bits 8))
    (reg r (bits 8) clk)
    (next r b)
    (assign x (add a (const 8 1)))
    (assign y r))
  (module top
    (input clk clock)
    (input i (bits 8))
    (output o (bits 8))
    (output p (bits 8))
    (inst k konst)
    (inst u child (clk clk) (a (add i k.c)) (b u.x))
    (assign o u.y)
    (assign p u.x)))
";
    assert_eq!(
        run(src, &["in=(i 1)", "in=(i 2)", "in=(i 3)"]),
        ["out=(o 0 p 42)\n", "out=(o 42 p 43)\n", "out=(o 43 p 44)\n"]
    );
}

#[test]
fn nested_instances_keep_their_own_state() {
    let src = "\
(design top
  (module delay
    (input clk clock)
    (input d (bits 4))
    (output q (bits 4))
    (reg r (bits 4) clk)
    (next r d)
    (assign q r))
  (module twice
    (input clk clock)
    (input d (bits 4))
    (output q (bits 4))
    (inst first delay (clk clk) (d d))
    (inst second delay (clk clk) (d first.q))
    (assign q second.q))
  (module top
    (input clk clock)
    (input d (bits 4))
    (output q (bits 4))
    (inst t twice (clk clk) (d d))
    (assign q t.q)))
";
    assert_eq!(
        run(src, &["in=(d 5)", "in=(d 6)", "in=(d 7)", "in=(d 8)"]),
        ["out=(q 0)\n", "out=(q 0)\n", "out=(q 5)\n", "out=(q 6)\n"]
    );
}

#[test]
fn an_extern_gives_e014_at_the_first_extern() {
    let src = "\
(design top
  (module top
    (input a (bits 4))
    (output b (bits 4))
    (inst u late (a a))
    (assign b u.b))
  (extern early
    (input a (bits 4))
    (output b (bits 4))
    (deps b (a)))
  (extern late
    (input a (bits 4))
    (output b (bits 4))
    (deps b (a))))
";
    let design = design(src);
    let Err(d) = Sim::new(&design) else {
        panic!("E014 expected");
    };
    assert_eq!((d.code, d.span.line, d.span.col), (ErrorCode::E014, 7, 3));
    assert_eq!(d.to_string(), "error[E014]: 7:3: no environment for extern");
}

const PORTS: &str = "\
(design top
  (module top
    (input clk clock)
    (input a (bits 1))
    (input x (bits 40))
    (output p (bits 1))
    (output q (bits 40))
    (assign p a)
    (assign q x)))
";

#[test]
fn input_lines_allow_spaces_tabs_and_leading_zeros() {
    let lines = [
        "in=(a 1 x 1099511627775)",
        " \tin=( a\t001   x 1099511627775 )\t ",
    ];
    assert_eq!(run(PORTS, &lines), ["out=(p 1 q 1099511627775)\n"; 2]);
}

#[test]
fn faulty_input_lines_are_usage_errors() {
    let design = design(PORTS);
    let cases = [
        ("", VectorError::Syntax),
        ("in=(a 1 x 0)\r", VectorError::Syntax),
        ("in= (a 1 x 0)", VectorError::Syntax),
        ("in=(a 1 x 0", VectorError::Syntax),
        ("in=(a 1 x 0))", VectorError::Syntax),
        ("in=(a 1 x)", VectorError::Syntax),
        ("in=(a 1 x -1)", VectorError::Syntax),
        ("in=(a 1 x 0) x", VectorError::Syntax),
        ("in=(a 1 x 0x1)", VectorError::Syntax),
        ("in=(a 1)", VectorError::Missing("x".into())),
        ("in=(a 1 x 0 y 0)", VectorError::Extra("y".into())),
        ("in=(a 1 y 0)", VectorError::Unknown("y".into())),
        ("in=(x 0 a 1)", VectorError::OutOfOrder("x".into())),
        ("in=(a 1 a 1)", VectorError::OutOfOrder("a".into())),
        ("in=(a 2 x 0)", VectorError::TooWide("a".into())),
        ("in=(a 0 x 1099511627776)", VectorError::TooWide("x".into())),
    ];
    for (line, error) in cases {
        assert_eq!(parse_input(line, top(&design)), Err(error), "{line:?}");
    }
}

#[test]
fn a_top_without_outputs_prints_an_empty_list() {
    let src = "\
(design top
  (module top
    (input a (bits 1))))
";
    assert_eq!(run(src, &["in=(a 1)", "in=( a 0 )"]), ["out=()\n"; 2]);
}

#[test]
fn a_top_without_inputs_reads_an_empty_list() {
    let src = "\
(design top
  (module top
    (output c (bits 3))
    (assign c (const 3 0))))
";
    assert_eq!(run(src, &["in=()", "in=( )"]), ["out=(c 0)\n"; 2]);
}

/// A chain of `depth` instances above a counter. Module `m{k}` runs `m{k-1}`.
fn deep_chain(depth: usize) -> String {
    use std::fmt::Write;
    let mut src = format!(
        "(design m{depth}\n  (module m0\n    (input clk clock)\n    (input a (bits 8))\n    (output q (bits 8))\n    (reg r (bits 8) clk)\n    (next r (add r a))\n    (assign q r))\n"
    );
    for k in 1..=depth {
        let j = k - 1;
        // Writing to a `String` cannot fail.
        let _ = writeln!(
            src,
            "  (module m{k}\n    (input clk clock)\n    (input a (bits 8))\n    (output q (bits 8))\n    (inst u m{j} (clk clk) (a a))\n    (assign q u.q))"
        );
    }
    src.push_str(")\n");
    src
}

#[test]
fn a_deep_instance_chain_runs_on_a_small_stack() {
    let src = deep_chain(20_000);
    let run_chain = move || run(&src, &["in=(a 1)"; 3]);
    let thread = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(run_chain)
        .expect("the thread starts");
    let lines = thread
        .join()
        .expect("the chain runs without a stack overflow");
    assert_eq!(lines, ["out=(q 0)\n", "out=(q 1)\n", "out=(q 2)\n"]);
}

#[test]
fn a_value_reads_an_output_of_its_module() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (input a (bits 1))
    (input b (bits 1))
    (output q (bits 2))
    (output p (bits 1))
    (reg r (bits 1) clk)
    (next r p)
    (assign q (concat p r))
    (assign p (and a b))))
";
    let lines = ["in=(a 1 b 1)", "in=(a 0 b 1)", "in=(a 1 b 1)"];
    assert_eq!(
        run(src, &lines),
        ["out=(q 2 p 1)\n", "out=(q 1 p 0)\n", "out=(q 2 p 1)\n"]
    );
}

#[test]
fn an_unused_extern_fails_before_a_wide_hierarchy_expands() {
    use std::fmt::Write;
    let mut src = String::from(
        "(design m40\n  (extern ext\n    (input a (bits 1))\n    (output b (bits 1))\n    (deps b (a)))\n  (module m0\n    (input a (bits 1))\n    (output q (bits 1))\n    (assign q a))\n",
    );
    for k in 1..=40 {
        let j = k - 1;
        // Writing to a `String` cannot fail.
        let _ = writeln!(
            src,
            "  (module m{k}\n    (input a (bits 1))\n    (output q (bits 1))\n    (inst u m{j} (a a))\n    (inst v m{j} (a a))\n    (assign q (and u.q v.q)))"
        );
    }
    src.push_str(")\n");
    let design = design(&src);
    let Err(d) = Sim::new(&design) else {
        panic!("E014 expected");
    };
    assert_eq!((d.code, d.span.line, d.span.col), (ErrorCode::E014, 2, 3));
}

#[test]
fn the_vectors_of_another_simulator_go_through_the_same_format() {
    let design = design(
        "(design t (module t (input a (bits 4)) (input b (bits 70)) \
         (output q (bits 4)) (output w (bits 70)) (assign q a) (assign w b)))",
    );
    let Ok(inputs) = parse_input("in=(a 9 b 1180591620717411303423)", top(&design)) else {
        panic!("the line must parse");
    };
    let values: Vec<String> = inputs
        .values()
        .iter()
        .map(|v| v.to_biguint().to_string())
        .collect();
    assert_eq!(values, ["9", "1180591620717411303423"]);
    let outputs = Outputs::new(inputs.values().to_vec());
    assert_eq!(
        print_output(top(&design), &outputs),
        "out=(q 9 w 1180591620717411303423)\n"
    );
}
