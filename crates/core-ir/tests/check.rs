//! Tests of the checker: the code and the position of each error, the
//! schedule, the port dependencies, and the module order.

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
    expect(src, ErrorCode::E005, 4, 18);
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
    expect(src, ErrorCode::E005, 3, 21);
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
    expect(src, ErrorCode::E005, 5, 21);
}

#[test]
fn e005_constant_does_not_fit() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q (const 1 2))))
";
    expect(src, ErrorCode::E005, 4, 24);
}

#[test]
fn e005_replication_count_zero() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q (replicate (const 1 0) 0))))
";
    expect(src, ErrorCode::E005, 4, 38);
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
fn e003_register_clock_is_not_a_clock_input() {
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
    expect(src, ErrorCode::E003, 6, 21);
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
    expect(src, ErrorCode::E011, 9, 24);
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
    expect(src, ErrorCode::E013, 5, 14);
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
    expect(src, ErrorCode::E013, 4, 13);
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

#[test]
fn e002_reserved_prefix() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let silicon_x (bits 1) (const 1 0))
    (assign q silicon_x)))
";
    expect(src, ErrorCode::E002, 4, 10);
}

#[test]
fn e003_next_of_a_non_register() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let a (bits 1) (const 1 0))
    (next a a)
    (assign q a)))
";
    expect(src, ErrorCode::E003, 5, 11);
}

#[test]
fn e003_assign_of_a_non_output() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let a (bits 1) (const 1 0))
    (assign a a)
    (assign q a)))
";
    expect(src, ErrorCode::E003, 5, 13);
}

#[test]
fn e003_connection_to_a_port_that_is_not_an_input() {
    let src = "\
(design top
  (module child
    (output o (bits 1))
    (assign o (const 1 0)))
  (module top
    (output q (bits 1))
    (inst u child (o (const 1 0)))
    (assign q u.o)))
";
    expect(src, ErrorCode::E003, 7, 20);
}

#[test]
fn e003_in_a_connection_beats_e011() {
    let src = "\
(design top
  (module child
    (input clk clock)
    (output o (bits 1))
    (assign o (const 1 0)))
  (module top
    (output q (bits 1))
    (inst u child (clk missing))
    (assign q u.o)))
";
    expect(src, ErrorCode::E003, 8, 24);
}

#[test]
fn e005_extract_of_zero_bits() {
    let src = "\
(design top
  (module top
    (input a (bits 4))
    (output q (bits 1))
    (assign q (extract a 0 0))))
";
    expect(src, ErrorCode::E005, 5, 28);
}

#[test]
fn e009_clock_output_port() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output c clock)
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E009, 4, 5);
}

#[test]
fn e009_read_of_a_clock_output_of_a_child() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (inst u child)
    (let a (bits 1) u.c)
    (assign q a))
  (module child
    (output c clock)
    (output o (bits 1))
    (assign o (const 1 0))))
";
    expect(src, ErrorCode::E009, 5, 21);
}

#[test]
fn e009_clock_name_connected_to_a_bits_input() {
    let src = "\
(design top
  (module child
    (input a (bits 1))
    (output o (bits 1))
    (assign o a))
  (module top
    (input clk clock)
    (output q (bits 1))
    (inst u child (a clk))
    (assign q u.o)))
";
    expect(src, ErrorCode::E009, 9, 22);
}

#[test]
fn e009_clock_inside_a_clock_connection_expression() {
    let src = "\
(design top
  (module child
    (input c clock)
    (output o (bits 1))
    (assign o (const 1 0)))
  (module top
    (input clk clock)
    (output q (bits 1))
    (inst u child (c (not clk)))
    (assign q u.o)))
";
    expect(src, ErrorCode::E009, 9, 27);
}

#[test]
fn a_clock_name_connects_to_a_clock_input() {
    let src = "\
(design top
  (module child
    (input c clock)
    (output o (bits 1))
    (assign o (const 1 0)))
  (module top
    (input clk clock)
    (output q (bits 1))
    (inst u child (c clk))
    (assign q u.o)))
";
    let design = run(src).expect("the clock connection checks");
    assert!(
        design
            .modules
            .iter()
            .all(|m| m.insts.iter().all(|i| i.inputs.is_empty()))
    );
}

#[test]
fn e013_duplicate_input_in_a_deps_list() {
    let src = "\
(design top
  (extern ext
    (input a (bits 1))
    (output o (bits 1))
    (deps o (a a)))
  (module top
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E013, 5, 16);
}

#[test]
fn e013_clock_input_in_a_deps_list() {
    let src = "\
(design top
  (extern ext
    (input c clock)
    (output o (bits 1))
    (deps o (c)))
  (module top
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E013, 5, 14);
}

#[test]
fn e013_second_deps_entry_is_at_its_output_name() {
    let src = "\
(design top
  (extern ext
    (input a (bits 1))
    (output o (bits 1))
    (deps o (a))
    (deps o (a)))
  (module top
    (output q (bits 1))
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E013, 6, 11);
}

#[test]
fn e009_assign_to_a_clock_output_is_reported_at_the_port() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output c clock)
    (output q (bits 1))
    (assign c clk)
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E009, 4, 5);
}

#[test]
fn e009_clock_read_in_an_assign_before_a_let() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output q (bits 1))
    (assign q clk)
    (let a (bits 1) clk)))
";
    expect(src, ErrorCode::E009, 5, 15);
}

/// One statement of each kind. The last `clk` of each reads the clock.
const CLOCK_READS: [&str; 7] = [
    "(let x (bits 1) clk)",
    "(reg s (bits 1) clk (reset sync clk (const 1 0)))",
    "(next r clk)",
    "(assign q clk)",
    "(write m 0 (const 1 0) (const 1 0) clk)",
    "(inst u child (c clk) (a clk))",
    "(inst v child (a (const 1 0)) (c (not clk)))",
];

#[test]
fn e009_lowest_clock_read_across_statement_kinds() {
    for first in CLOCK_READS {
        for second in CLOCK_READS.into_iter().filter(|s| *s != first) {
            let src = format!(
                "\
(design top
  (module child
    (input a (bits 1))
    (input c clock)
    (output o (bits 1))
    (assign o a))
  (module top
    (input clk clock)
    (output q (bits 1))
    (reg r (bits 1) clk)
    (mem m (bits 1) 2 clk)
    {first}
    {second}))
"
            );
            let Some(at) = first.rfind("clk") else {
                panic!("each statement reads the clock");
            };
            let col = 5 + u32::try_from(at).expect("a short line");
            expect(&src, ErrorCode::E009, 12, col);
        }
    }
}

#[test]
fn e005_lowest_constant_across_statement_kinds() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q (const 1 2))
    (let a (bits 1) (const 1 3))))
";
    expect(src, ErrorCode::E005, 4, 24);
}

#[test]
fn e010_instance_cycle_is_at_its_lowest_inst() {
    let src = "\
(design top
  (module b
    (output q (bits 1))
    (inst u a)
    (assign q u.q))
  (module a
    (output q (bits 1))
    (inst v b)
    (assign q v.q))
  (module top
    (output q (bits 1))
    (inst w a)
    (assign q w.q)))
";
    expect(src, ErrorCode::E010, 4, 5);
}

#[test]
fn e010_module_instantiates_itself() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q (const 1 0))
    (inst u top)))
";
    expect(src, ErrorCode::E010, 5, 5);
}

#[test]
fn e010_comes_before_e008() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let a (bits 1) a)
    (inst u loop)
    (assign q a))
  (module loop
    (output q (bits 1))
    (inst u loop)
    (assign q u.q)))
";
    expect(src, ErrorCode::E010, 9, 5);
}

#[test]
fn e008_let_cycle_is_at_its_lowest_node() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (assign q x)
    (let y (bits 1) (not x))
    (let x (bits 1) (and y (const 1 0)))))
";
    expect(src, ErrorCode::E008, 5, 5);
}

#[test]
fn e008_lowest_node_across_cycles() {
    let src = "\
(design top
  (module top
    (output q (bits 1))
    (let c (bits 1) d)
    (let a (bits 1) b)
    (let b (bits 1) a)
    (let d (bits 1) c)
    (assign q (const 1 0))))
";
    expect(src, ErrorCode::E008, 4, 5);
}

#[test]
fn e008_read_address_reads_itself() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output q (bits 1))
    (mem m (bits 1) 2 clk)
    (write m 0 (const 1 0) (const 1 0) (const 1 0))
    (let a (bits 1) (read m a))
    (assign q a)))
";
    expect(src, ErrorCode::E008, 7, 5);
}

#[test]
fn a_register_breaks_a_loop() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (output q (bits 1))
    (reg r (bits 1) clk)
    (let x (bits 1) (not r))
    (next r x)
    (assign q x)))
";
    run(src).expect("a register read makes no edge");
}

#[test]
fn memory_contents_break_a_loop() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (input a (bits 1))
    (output q (bits 1))
    (mem m (bits 1) 2 clk)
    (let x (bits 1) (read m a))
    (write m 0 a x (const 1 1))
    (assign q x)))
";
    run(src).expect("the stored contents make no edge");
}

/// A child whose output `q` reads its input `a` in the same cycle.
const PASS_THROUGH: &str = "\
  (module child
    (input a (bits 1))
    (output q (bits 1))
    (assign q (not a)))
";

#[test]
fn loop_through_one_instance_fails() {
    let src = format!(
        "\
(design top
{PASS_THROUGH}  (module top
    (output q (bits 1))
    (inst u child (a u.q))
    (assign q u.q)))
"
    );
    expect(&src, ErrorCode::E008, 8, 5);
}

#[test]
fn e008_feedback_through_a_child_memory_address() {
    let src = "\
(design top
  (module child
    (input clk clock)
    (input a (bits 1))
    (output q (bits 1))
    (mem m (bits 1) 2 clk)
    (write m 0 (const 1 0) (const 1 0) (const 1 0))
    (assign q (read m a)))
  (module top
    (input clk clock)
    (output q (bits 1))
    (let x (bits 1) u.q)
    (inst u child (clk clk) (a x))
    (assign q x)))
";
    expect(src, ErrorCode::E008, 12, 5);
}

#[test]
fn e008_loop_through_an_extern() {
    let src = "\
(design top
  (extern ext
    (input a (bits 1))
    (output b (bits 1))
    (deps b (a)))
  (module top
    (output q (bits 1))
    (inst u ext (a u.b))
    (assign q u.b)))
";
    expect(src, ErrorCode::E008, 8, 5);
}

#[test]
fn an_extern_without_deps_breaks_a_loop() {
    let src = "\
(design top
  (extern ext
    (input a (bits 1))
    (output b (bits 1))
    (deps b ()))
  (module top
    (output q (bits 1))
    (inst u ext (a u.b))
    (assign q u.b)))
";
    run(src).expect("an output outside the deps makes no edge");
}

#[test]
fn sibling_handshake_passes() {
    let src = "\
(design top
  (module child
    (input clk clock)
    (input valid (bits 1))
    (output ready (bits 1))
    (reg r (bits 1) clk)
    (next r valid)
    (assign ready r))
  (module top
    (input clk clock)
    (output q (bits 1))
    (inst u child (clk clk) (valid v.ready))
    (inst v child (clk clk) (valid u.ready))
    (assign q (and u.ready v.ready))))
";
    let design = run(src).expect("the handshake has no combinational loop");
    let child = &design.modules[0];
    assert_eq!(child.name, "child");
    assert_eq!(child.deps, vec![vec![]]);
}

fn reads(expr: &typed::Expr, out: &mut Vec<typed::Node>) {
    use typed::{Expr, Node};
    match expr {
        Expr::Let(l) => out.push(Node::Let(*l)),
        Expr::InstOut(u, o) => out.push(Node::InstOut(*u, *o)),
        Expr::Input(_) | Expr::Reg(_) | Expr::Const(_) => {}
        Expr::Un(_, a) | Expr::Extract(a, ..) | Expr::Replicate(a, _) | Expr::Read(_, a) => {
            reads(a, out);
        }
        Expr::Bin(_, a, b) | Expr::Icmp(_, a, b) => {
            reads(a, out);
            reads(b, out);
        }
        Expr::Mux(a, b, c) => {
            reads(a, out);
            reads(b, out);
            reads(c, out);
        }
    }
}

fn callee_deps(design: &typed::Design, callee: typed::Callee) -> &typed::Deps {
    match callee {
        typed::Callee::Module(m) => &design.modules[m.index()].deps,
        typed::Callee::Extern(e) => &design.externs[e.index()].deps,
    }
}

/// Each module comes after its children, and its schedule has each node once,
/// after every node that it reads.
fn assert_well_ordered(design: &typed::Design) {
    use typed::Node;
    for (index, module) in design.modules.iter().enumerate() {
        let mut nodes = module.lets.len() + module.outputs.len();
        for inst in &module.insts {
            if let typed::Callee::Module(m) = inst.callee {
                assert!(m.index() < index, "a child comes first");
            }
            nodes += callee_deps(design, inst.callee).len();
        }
        assert_eq!(module.schedule.len(), nodes, "each node once");
        for (at, node) in module.schedule.iter().enumerate() {
            let mut read = Vec::new();
            match *node {
                Node::Let(l) => reads(&module.lets[l.index()].expr, &mut read),
                Node::Output(o) => reads(&module.assigns[o.index()], &mut read),
                Node::InstOut(u, q) => {
                    let inst = &module.insts[u.index()];
                    for i in &callee_deps(design, inst.callee)[q.index()] {
                        reads(&inst.inputs[i.index()], &mut read);
                    }
                }
            }
            assert_eq!(module.schedule.iter().filter(|n| *n == node).count(), 1);
            for r in read {
                let before = module.schedule.iter().position(|n| *n == r);
                assert!(before.is_some_and(|b| b < at), "{r:?} before {node:?}");
            }
        }
    }
}

#[test]
fn schedules_and_module_order() {
    let src = "\
(design top
  (module top
    (input clk clock)
    (input a (bits 1))
    (output q (bits 1))
    (output p (bits 1))
    (let z (bits 1) (and y u.q))
    (let y (bits 1) (or x a))
    (inst u mid (clk clk) (a y))
    (let x (bits 1) (not a))
    (assign q z)
    (assign p x))
  (module mid
    (input clk clock)
    (input a (bits 1))
    (output q (bits 1))
    (inst v child (a a))
    (inst w handshake (clk clk) (valid v.q))
    (assign q (xor v.q w.ready)))
  (module handshake
    (input clk clock)
    (input valid (bits 1))
    (output ready (bits 1))
    (reg r (bits 1) clk)
    (next r valid)
    (assign ready r))
"
    .to_owned()
        + PASS_THROUGH
        + ")\n";
    let design = run(&src).expect("the design checks");
    assert_well_ordered(&design);
    assert_eq!(design.modules[design.top.index()].name, "top");
    let names: Vec<&str> = design.modules.iter().map(|m| m.name.as_str()).collect();
    assert_eq!(names.len(), 4);
    let mid = design
        .modules
        .iter()
        .find(|m| m.name == "mid")
        .expect("mid");
    assert_eq!(mid.deps.len(), 1);
    assert_eq!(mid.deps[0].len(), 1, "mid.q reads mid.a through v");
    let top = &design.modules[design.top.index()];
    assert_eq!(top.deps.iter().map(Vec::len).collect::<Vec<_>>(), [1, 1]);
}

#[test]
fn every_form_and_handshake_are_well_ordered() {
    assert_well_ordered(&run(EVERY_FORM).expect("every form checks"));
    assert_well_ordered(&run(COUNTER).expect("counter checks"));
}

/// A 2-wide chain of the given depth. An exponential search over the paths
/// does not finish.
fn wide_chain(depth: usize) -> String {
    let lets = (1..=depth)
        .map(|k| {
            let j = k - 1;
            format!(
                "    (let a{k} (bits 1) (and a{j} b{j}))\n    (let b{k} (bits 1) (or a{j} b{j}))\n"
            )
        })
        .collect::<Vec<_>>()
        .concat();
    format!(
        "(design top\n  (module top\n    (input a0 (bits 1))\n    (input b0 (bits 1))\n    (output q (bits 1))\n{lets}    (assign q (xor a{depth} b{depth}))))\n"
    )
}

fn indices(deps: &typed::Deps) -> Vec<Vec<usize>> {
    deps.iter()
        .map(|d| d.iter().map(|i| i.index()).collect())
        .collect()
}

#[test]
fn deep_two_wide_chain_is_fast() {
    let design = run(&wide_chain(40)).expect("the chain checks");
    assert_eq!(indices(&design.modules[0].deps), [[0, 1]]);
}

#[test]
fn deep_two_wide_chain_cycle_is_fast() {
    let src = wide_chain(40).replace("(and a0 b0)", "(and a0 a40)");
    expect(&src, ErrorCode::E008, 6, 5);
}

#[test]
fn deep_two_wide_hierarchy_is_fast() {
    use std::fmt::Write;
    let mut src = String::from(
        "(design m40\n  (module m0\n    (input a (bits 1))\n    (input b (bits 1))\n    (output q (bits 1))\n    (assign q (and a b)))\n",
    );
    for k in 1..=40 {
        let j = k - 1;
        writeln!(
            src,
            "  (module m{k}\n    (input a (bits 1))\n    (input b (bits 1))\n    (output q (bits 1))\n    (inst u m{j} (a a) (b b))\n    (inst v m{j} (a u.q) (b b))\n    (assign q (or u.q v.q)))"
        )
        .expect("write");
    }
    src.push_str(")\n");
    let design = run(&src).expect("the hierarchy checks");
    assert_well_ordered(&design);
    let top = &design.modules[design.top.index()];
    assert_eq!(top.name, "m40");
    assert_eq!(indices(&top.deps), [[0, 1]]);
}
