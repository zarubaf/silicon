//! Tests of the checker passes 1 to 7: the code and the position of each error.

use core_ir::check::check;
use core_ir::diag::{Diagnostic, ErrorCode};
use core_ir::text::parse;
use core_ir::typed;

fn run(src: &str) -> Result<typed::Design, Diagnostic> {
    let Ok(design) = parse(src) else {
        panic!("the source must parse");
    };
    check(&design)
}

fn expect(src: &str, code: ErrorCode, line: u32, col: u32) {
    let Err(d) = run(src) else {
        panic!("{code} expected, but the design checks");
    };
    assert_eq!((d.code, d.span.line, d.span.col), (code, line, col), "{d}");
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

const EVERY_FORM: &str = "\
(design top
  (extern ext
    (input a (bits 4))
    (output b (bits 4))
    (deps b (a)))
  (module top
    (input clk clock)
    (input a (bits 4))
    (output o (bits 8))
    (mem m (bits 4) 12 clk)
    (write m 0 (extract a 0 4) (not a) (icmp ult a a))
    (inst u ext (a a))
    (let x (bits 8) (concat (read m a) (replicate u.b 1)))
    (let y (bits 8) (shrs x (const 8 1)))
    (assign o y)))
";

#[test]
fn well_formed_designs_check() {
    let counter = run(COUNTER).expect("counter checks");
    let top = &counter.modules[counter.top.index()];
    assert_eq!(top.name, "counter");
    assert!(top.has_clock);
    assert_eq!(top.regs.len(), 1);
    run(EVERY_FORM).expect("every form checks");
}

#[test]
fn e002_duplicate_name() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let a (bits 1) (const 1 0))
    (let a (bits 1) (const 1 1))
    (assign q a)))
";
    expect(src, ErrorCode::E002, 5, 10);
}

#[test]
fn e002_module_and_extern_share_a_scope() {
    let src = "\
(design top
  (extern top
    (output o (bits 1)) (deps o ()))
  (module top
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E002, 4, 11);
}

#[test]
fn e003_unknown_name() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q missing)))
";
    expect(src, ErrorCode::E003, 4, 15);
}

#[test]
fn e003_top_must_name_a_module() {
    let src = "\
(design nope
  (module top
    (output q (bits 1))
    (assign q missing)))
";
    expect(src, ErrorCode::E003, 1, 9);
}

#[test]
fn e003_unknown_instance_output() {
    let src = "\
(design top
  (module child
    (output o (bits 1))
    (assign o (const 1 0)))
  (module top
    (output q (bits 1))
    (inst u child)
    (assign q u.p)))
";
    expect(src, ErrorCode::E003, 8, 15);
}

#[test]
fn e005_declared_width_over_the_limit() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let a (bits 65537) (const 1 0))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E005, 4, 5);
}

#[test]
fn e005_width_at_the_limit_is_fine() {
    let src = "\
(design top
  (module top
    (input a (bits 65536))
    (output q (bits 65536))
    (assign q a)))
";
    run(src).expect("a 65536-bit port checks");
}

#[test]
fn e005_zero_width_port() {
    let src = "\
(design top
  (module top
    (output q (bits 0))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E005, 3, 5);
}

#[test]
fn e005_memory_depth_over_the_limit() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output q (bits 1))
    (mem m (bits 1) 16777217 clk)
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E005, 5, 5);
}

#[test]
fn e005_constant_does_not_fit() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q (const 1 2))))
";
    expect(src, ErrorCode::E005, 4, 15);
}

#[test]
fn e005_replication_count_zero() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q (replicate (const 1 0) 0))))
";
    expect(src, ErrorCode::E005, 4, 15);
}

#[test]
fn e009_clock_read_by_a_value() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output q (bits 1))
    (let a (bits 1) clk)
    (assign q a)))
";
    expect(src, ErrorCode::E009, 5, 21);
}

#[test]
fn e009_second_clock_input() {
    let src = "\
(design top
  (module top
    (input c1 clock)
    (input c2 clock)
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E009, 4, 5);
}

#[test]
fn e009_register_names_a_non_clock() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (input d (bits 1))
    (output q (bits 1))
    (reg r (bits 1) d)
    (next r d)
    (assign q r)))
";
    expect(src, ErrorCode::E009, 6, 5);
}

#[test]
fn e011_missing_instance_input() {
    let src = "\
(design top
  (module child
    (input a (bits 1))
    (output o (bits 1))
    (assign o a))
  (module top
    (output q (bits 1))
    (inst u child)
    (assign q u.o)))
";
    expect(src, ErrorCode::E011, 8, 5);
}

#[test]
fn e011_input_connected_twice() {
    let src = "\
(design top
  (module child
    (input a (bits 1))
    (output o (bits 1))
    (assign o a))
  (module top
    (output q (bits 1))
    (inst u child (a (const 1 0)) (a (const 1 1)))
    (assign q u.o)))
";
    expect(src, ErrorCode::E011, 8, 35);
}

#[test]
fn e011_clock_input_needs_a_clock() {
    let src = "\
(design top
  (module child
    (input clk clock)
    (output o (bits 1))
    (assign o (const 1 0)))
  (module top
    (input clk clock)
    (output q (bits 1))
    (inst u child (clk (const 1 0)))
    (assign q u.o)))
";
    expect(src, ErrorCode::E011, 9, 19);
}

#[test]
fn e013_deps_name_an_unknown_input() {
    let src = "\
(design top
  (extern ext
    (input a (bits 1))
    (output o (bits 1))
    (deps o (nope)))
  (module top
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E013, 5, 5);
}

#[test]
fn e013_output_without_deps() {
    let src = "\
(design top
  (extern ext
    (input a (bits 1))
    (output o (bits 1)))
  (module top
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E013, 4, 5);
}

#[test]
fn e004_operand_widths_differ() {
    let src = "\
(design top
  (module top
    (output q (bits 4))
    (assign q (add (const 4 1) (const 3 1)))))
";
    expect(src, ErrorCode::E004, 4, 15);
}

#[test]
fn e004_target_width_differs() {
    let src = "\
(design top
  (module top
    (output q (bits 4))
    (let a (bits 3) (const 4 1))
    (assign q (const 4 1))))
";
    expect(src, ErrorCode::E004, 4, 5);
}

#[test]
fn e004_concat_over_the_limit() {
    let src = "\
(design top
  (module top
    (input a (bits 40000))
    (output q (bits 1))
    (let x (bits 1) (extract (concat a a) 0 1))
    (assign q x)))
";
    expect(src, ErrorCode::E004, 5, 30);
}

#[test]
fn e004_replicate_over_the_limit() {
    let src = "\
(design top
  (module top
    (input a (bits 40000))
    (output q (bits 1))
    (let x (bits 1) (extract (replicate a 2) 0 1))
    (assign q x)))
";
    expect(src, ErrorCode::E004, 5, 30);
}

#[test]
fn e004_memory_address_width() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (input a (bits 3))
    (output q (bits 1))
    (mem m (bits 1) 12 clk)
    (assign q (read m a))))
";
    expect(src, ErrorCode::E004, 7, 15);
}

#[test]
fn e004_extract_out_of_range() {
    let src = "\
(design top
  (module top
    (input a (bits 4))
    (output q (bits 2))
    (assign q (extract a 3 2))))
";
    expect(src, ErrorCode::E004, 5, 15);
}

#[test]
fn earlier_pass_wins() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let a (bits 1) (const 1 0))
    (let b (bits 1) (const 1 0))
    (let c (bits 1) (const 1 0))
    (let d (bits 1) (const 1 0))
    (let h (bits 1) (const 1 0))
    (assign q missing)
    (let e (bits 1) (const 1 0))
    (let f (bits 1) (const 1 0))
    (let a (bits 1) (const 1 0))))
";
    expect(src, ErrorCode::E002, 12, 10);
}

#[test]
fn lowest_position_within_a_pass() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let a (bits 1) second)
    (assign q first)
    (let b (bits 1) third)))
";
    expect(src, ErrorCode::E003, 4, 21);
}

#[test]
fn pass_8_register_without_next() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output q (bits 1))
    (reg r (bits 1) clk)
    (assign q r)))
";
    expect(src, ErrorCode::E006, 5, 5);
}

#[test]
fn pass_8_output_assigned_twice() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q (const 1 0))
    (assign q (const 1 1))))
";
    expect(src, ErrorCode::E007, 5, 5);
}

#[test]
fn pass_8_write_port_gap() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output q (bits 1))
    (mem m (bits 1) 2 clk)
    (write m 1 (const 1 0) (const 1 0) (const 1 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E012, 5, 5);
}
