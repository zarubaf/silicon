//! Tests of the `.sil` parser, printer, and canonical form.

use core_ir::diag::{Diagnostic, ErrorCode, Span};
use core_ir::text::{canonicalize, parse, print};

const COUNTER: &str = "\
; an 8-bit counter
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

fn err(src: &str) -> Diagnostic {
    let Err(d) = parse(src) else {
        panic!("source must not parse");
    };
    d
}

#[test]
fn counter_parses() {
    let design = parse(COUNTER).expect("counter parses");
    assert_eq!(design.top.text, "counter");
    assert_eq!(design.top.span, Span { line: 2, col: 9 });
    assert_eq!(design.items.len(), 1);
}

#[test]
fn print_matches_the_spec_layout() {
    let design = parse(COUNTER).expect("counter parses");
    let expected = COUNTER.split_once('\n').expect("comment line").1;
    assert_eq!(print(&design), expected);
}

#[test]
fn parse_print_round_trips_up_to_spans() {
    for src in [COUNTER, EVERY_FORM] {
        let design = parse(src).expect("source parses");
        let again = parse(&print(&design)).expect("printed text parses");
        assert_eq!(design.without_spans(), again.without_spans());
    }
}

#[test]
fn keyword_as_a_name_is_e001() {
    let d = err("(design add)");
    assert_eq!(d.code, ErrorCode::E001);
    assert_eq!(d.span, Span { line: 1, col: 9 });
    // A statement outside a module fails at its keyword.
    let d = err("(let add (bits 1) (const 1 0))");
    assert_eq!(
        (d.code, d.span),
        (ErrorCode::E001, Span { line: 1, col: 2 })
    );
}

#[test]
fn keyword_as_a_module_name_is_e001() {
    let d = err("(design top\n  (module mux))");
    assert_eq!(
        (d.code, d.span),
        (ErrorCode::E001, Span { line: 2, col: 11 })
    );
}

#[test]
fn missing_paren_is_e001_at_the_end() {
    let d = err("(design top\n  (module top");
    assert_eq!(d.code, ErrorCode::E001);
    assert_eq!(d.span, Span { line: 2, col: 14 });
}

#[test]
fn unmatched_close_is_e001() {
    let d = err("(design top))");
    assert_eq!(
        (d.code, d.span),
        (ErrorCode::E001, Span { line: 1, col: 13 })
    );
}

#[test]
fn wrong_shape_is_e001_at_the_first_bad_token() {
    let d = err("(design top\n  (module top (input a (bits x))))");
    assert_eq!(
        (d.code, d.span),
        (ErrorCode::E001, Span { line: 2, col: 30 })
    );
}

#[test]
fn bad_character_is_e001() {
    let d = err("(design top #)");
    assert_eq!(
        (d.code, d.span),
        (ErrorCode::E001, Span { line: 1, col: 13 })
    );
}

#[test]
fn deep_nesting_is_an_error_not_a_crash() {
    let d = err(&"(".repeat(100_000));
    assert_eq!(d.code, ErrorCode::E001);
}

#[test]
fn diagnostic_display_matches_the_cli_contract() {
    let d = Diagnostic {
        code: ErrorCode::E004,
        span: Span { line: 12, col: 5 },
        message: "width mismatch".to_string(),
    };
    assert_eq!(d.to_string(), "error[E004]: 12:5: width mismatch");
}

#[test]
fn canonicalize_sorts_items_and_statements() {
    let src = "\
(design b
  (module b
    (input clk clock)
    (output o (bits 1))
    (assign o z)
    (write m 1 a a a)
    (write m 0 a a a)
    (next r2 a)
    (next r1 a)
    (let z (bits 1) a)
    (let a (bits 1) r1)
    (inst i2 b)
    (inst i1 b)
    (mem m (bits 1) 2 clk)
    (reg r2 (bits 1) clk)
    (reg r1 (bits 1) clk))
  (module a))
";
    let expected = "\
(design b
  (module a)
  (module b
    (input clk clock)
    (output o (bits 1))
    (reg r1 (bits 1) clk)
    (reg r2 (bits 1) clk)
    (mem m (bits 1) 2 clk)
    (inst i1 b)
    (inst i2 b)
    (let a (bits 1) r1)
    (let z (bits 1) a)
    (next r1 a)
    (next r2 a)
    (write m 0 a a a)
    (write m 1 a a a)
    (assign o z)))
";
    let design = parse(src).expect("parses");
    assert_eq!(print(&canonicalize(&design)), expected);
}

#[test]
fn counter_canonical_snapshot() {
    let design = parse(COUNTER).expect("counter parses");
    insta::assert_snapshot!(print(&canonicalize(&design)));
}
