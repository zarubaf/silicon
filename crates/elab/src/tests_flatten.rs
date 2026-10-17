// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Flatten` in Lean: the exact canonical `.sil` text of
//! small designs and of each operator row of section 7.4, the temporaries with the effective
//! height, `S020` with its position, and the charges of the lowering.

use crate::tests_elab::load;
use crate::{Abort, Budget, Design, Failure, Lowered, check, elaborate};
use core_ir::text::{canonicalize, parse, print};

/// The elaboration of `src` with the top `top` and the fuel `fuel`, and its lowering. An error
/// gives its code and its position.
pub(crate) fn lowered(src: &str, top: &str, fuel: u64) -> Result<(Design, Lowered), String> {
    let file = load(src)?;
    let budget = Budget {
        fuel,
        ..Budget::default()
    };
    let at = |e: crate::Error| format!("{} {}:{}", e.code, e.pos.line, e.pos.col);
    let design = match elaborate(&file, top, parse::DEFAULT_SYNTAX_DEPTH, budget) {
        Ok(Ok(d)) => d,
        Ok(Err(e)) => return Err(at(e)),
        Err(Abort::Usage(_)) => return Err("usage".to_owned()),
        Err(Abort::Stack(e)) => panic!("{e}"),
    };
    match design.lower().unwrap() {
        Ok(l) => Ok((design, l)),
        Err(Failure::Source(e)) => Err(at(e)),
        Err(Failure::Defect(m)) => Err(format!("defect {m}")),
    }
}

/// The result of `elab`: the canonical `.sil` text, or the code and the position of the
/// error.
pub(crate) fn sil_fuel(src: &str, top: &str, fuel: u64) -> String {
    match lowered(src, top, fuel) {
        Ok((_, l)) => match check(&l.design) {
            Ok(_) => print(&canonicalize(&l.design)),
            Err(Failure::Source(e)) => format!("{} {}:{}", e.code, e.pos.line, e.pos.col),
            Err(Failure::Defect(m)) => format!("defect {m}"),
        },
        Err(e) => e,
    }
}

pub(crate) fn sil(src: &str, top: &str) -> String {
    sil_fuel(src, top, Budget::default().fuel)
}

/// The output of `cost` with the lowering, or the code and the position of the first error.
pub(crate) fn lowered_cost(src: &str, top: &str) -> String {
    match lowered(src, top, Budget::default().fuel) {
        Ok((_, l)) => l.cost(),
        Err(e) => e,
    }
}

/// The fuel of the elaboration with the lowering.
pub(crate) fn total(src: &str, top: &str) -> u64 {
    lowered(src, top, Budget::default().fuel).unwrap().1.used()
}

/// The fuel of the elaboration alone.
pub(crate) fn elab_used(src: &str, top: &str) -> u64 {
    lowered(src, top, Budget::default().fuel).unwrap().0.used()
}

pub(crate) fn text<S: AsRef<str>>(lines: &[S]) -> String {
    let mut out = String::new();
    for l in lines {
        out.push_str(l.as_ref());
        out.push('\n');
    }
    out
}

/// The text re-parses and passes the core checker.
pub(crate) fn valid(s: &str) -> bool {
    parse(s).is_ok_and(|d| core_ir::check::check(&d).is_ok())
}

const COUNTER: &str = "module Counter(comptime W: Nat) {\n    input enable: Bool;\n    \
    output value: UInt[W];\n    output full: Bool;\n    reg count: UInt[W] = 0;\n    \
    count := if (enable) { count +% 1 } else { count };\n    value := count;\n    \
    full := count == UInt[W]((1 << W) - 1);\n}\n";

fn counter() -> String {
    COUNTER.to_owned()
        + "module Main() {\n    input enable: Bool;\n    output value: UInt[4];\n    \
           instance counter = Counter(4);\n    counter.enable := enable;\n    \
           value := counter.value;\n}\n"
}

fn two_counters() -> String {
    COUNTER.to_owned()
        + "module Main() {\n    input enable: Bool;\n    output value: UInt[4];\n    \
           instance a = Counter(4);\n    instance b = Counter(2);\n    a.enable := enable;\n    \
           b.enable := !enable;\n    value := a.value;\n}\n"
}

#[test]
fn the_counter() {
    assert_eq!(
        sil(&counter(), "Counter(4)"),
        text(&[
            "(design Counter$4",
            "  (module Counter$4",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input enable (bits 1))",
            "    (output full (bits 1))",
            "    (output value (bits 4))",
            "    (reg count (bits 4) clock$0clk (reset sync clock$0rst (const 4 0)))",
            "    (next count (mux enable (add count (const 4 1)) count))",
            "    (assign full (icmp eq count (const 4 15)))",
            "    (assign value count)))"
        ])
    );
}

#[test]
fn two_instantiations_of_one_module() {
    assert_eq!(
        sil(&two_counters(), "Main"),
        text(&[
            "(design Main",
            "  (module Counter$2",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input enable (bits 1))",
            "    (output full (bits 1))",
            "    (output value (bits 2))",
            "    (reg count (bits 2) clock$0clk (reset sync clock$0rst (const 2 0)))",
            "    (next count (mux enable (add count (const 2 1)) count))",
            "    (assign full (icmp eq count (const 2 3)))",
            "    (assign value count))",
            "  (module Counter$4",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input enable (bits 1))",
            "    (output full (bits 1))",
            "    (output value (bits 4))",
            "    (reg count (bits 4) clock$0clk (reset sync clock$0rst (const 4 0)))",
            "    (next count (mux enable (add count (const 4 1)) count))",
            "    (assign full (icmp eq count (const 4 15)))",
            "    (assign value count))",
            "  (module Main",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input enable (bits 1))",
            "    (output value (bits 4))",
            "    (inst a Counter$4 (clock$0clk clock$0clk) (clock$0rst clock$0rst) (enable enable))",
            "    (inst b Counter$2 (clock$0clk clock$0clk) (clock$0rst clock$0rst) \
             (enable (xor enable (const 1 1))))",
            "    (assign value a.value)))"
        ])
    );
}

const UNROLL: &str = "module R(comptime N: Nat) {\n  input x: UInt[4];\n  input e: Bool;\n  \
    output y: UInt[4];\n  let mut acc = x;\n  comptime for i in 0..N {\n    \
    reg r: UInt[4] = i;\n    r := if (e) { acc } else { r };\n    acc = acc +% r;\n  }\n  \
    y := acc;\n}\n";

#[test]
fn a_loop_unrolls_into_loop_frames() {
    assert_eq!(
        sil(UNROLL, "R(2)"),
        text(&[
            "(design R$2",
            "  (module R$2",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input e (bits 1))",
            "    (input x (bits 4))",
            "    (output y (bits 4))",
            "    (reg i$0$r (bits 4) clock$0clk (reset sync clock$0rst (const 4 0)))",
            "    (reg i$1$r (bits 4) clock$0clk (reset sync clock$0rst (const 4 1)))",
            "    (let acc (bits 4) x)",
            "    (let i$0$acc (bits 4) (add acc i$0$r))",
            "    (let i$1$acc (bits 4) (add i$0$acc i$1$r))",
            "    (next i$0$r (mux e acc i$0$r))",
            "    (next i$1$r (mux e i$0$acc i$1$r))",
            "    (assign y i$1$acc)))"
        ])
    );
}

const OPS: &str = "module C() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := !a;\n}\n\
    module M() {\n  input x: UInt[8];\n  input s: SInt[8];\n  input c: UInt[3];\n  \
    input e: Bool;\n  output y: UInt[8];\n  output z: SInt[16];\n  output b: Bool;\n  \
    let w = (x +% 1) -% (x *% 3) & ~x | (x ^ 255);\n  let v = -s >> c;\n  \
    let n = if (e) { 2 } else { 2 };\n  let k = if (e) { 1 } else { x << n };\n  instance u = C();\n  let h = u.a;\n  \
    h := e && x < 5 || s >= -1 && x != w;\n  \
    y := if (u.q) { k } else { reinterpret(UInt[8], s) };\n  z := resize(SInt[16], v);\n  \
    b := if (e) { true } else { false };\n}\n";

#[test]
fn the_operator_rows() {
    assert_eq!(
        sil(OPS, "M"),
        text(&[
            "(design M",
            "  (module C",
            "    (input a (bits 1))",
            "    (output q (bits 1))",
            "    (assign q (xor a (const 1 1))))",
            "  (module M",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input c (bits 3))",
            "    (input e (bits 1))",
            "    (input s (bits 8))",
            "    (input x (bits 8))",
            "    (output b (bits 1))",
            "    (output y (bits 8))",
            "    (output z (bits 16))",
            "    (inst u C (a (or (and e (icmp ult x (const 8 5))) \
             (and (icmp sge s (const 8 255)) (icmp ne x w)))))",
            "    (let k (bits 8) (mux e (const 8 1) (shl x (const 8 2))))",
            "    (let v (bits 8) (shrs (sub (const 8 0) s) (concat (const 5 0) c)))",
            "    (let w (bits 8) (or (and (sub (add x (const 8 1)) (mul x (const 8 3))) (not x)) \
             (xor x (const 8 255))))",
            "    (assign b (mux e (const 1 1) (const 1 0)))",
            "    (assign y (mux u.q k s))",
            "    (assign z (concat (replicate (extract v 7 1) 8) v))))"
        ])
    );
}

const OPS2: &str = "module P() domains() {\n  input a: SInt[8];\n}\n\
    module N() domains() {\n  input x: UInt[4];\n  input y: UInt[4];\n  input c: UInt[8];\n  \
    input s: SInt[4];\n  input e: Bool;\n  output a: UInt[4];\n  output b: UInt[4];\n  \
    output d: SInt[4];\n  output f: UInt[2];\n  output g: UInt[8];\n  output h: Bool;\n  \
    output i: UInt[4];\n  a := (x +% y) << (c ^ 1);\n  b := x >> c;\n  \
    d := (s +% 1) >> (c +% 2);\n  f := resize(UInt[2], x);\n  g := resize(UInt[8], x +% y);\n  \
    h := !e && x <= y || x > y && s < 1 || s <= s && s > s;\n  i := x << y;\n  \
    instance u = P();\n  u.a := resize(SInt[8], s +% 1);\n}\n";

#[test]
fn the_wide_counts_and_the_temporaries() {
    assert_eq!(
        sil(OPS2, "N"),
        text(&[
            "(design N",
            "  (module N",
            "    (input c (bits 8))",
            "    (input e (bits 1))",
            "    (input s (bits 4))",
            "    (input x (bits 4))",
            "    (input y (bits 4))",
            "    (output a (bits 4))",
            "    (output b (bits 4))",
            "    (output d (bits 4))",
            "    (output f (bits 2))",
            "    (output g (bits 8))",
            "    (output h (bits 1))",
            "    (output i (bits 4))",
            "    (inst u P (a (concat (replicate (extract u$a$0t 3 1) 4) u$a$0t)))",
            "    (let a$0t (bits 8) (xor c (const 8 1)))",
            "    (let d$0t (bits 4) (add s (const 4 1)))",
            "    (let d$1t (bits 8) (add c (const 8 2)))",
            "    (let u$a$0t (bits 4) (add s (const 4 1)))",
            "    (assign a (mux (icmp uge a$0t (const 8 4)) (const 4 0) \
             (shl (add x y) (extract a$0t 0 4))))",
            "    (assign b (mux (icmp uge c (const 8 4)) (const 4 0) (shru x (extract c 0 4))))",
            "    (assign d (mux (icmp uge d$1t (const 8 4)) (shrs d$0t (const 4 3)) \
             (shrs d$0t (extract d$1t 0 4))))",
            "    (assign f (extract x 0 2))",
            "    (assign g (concat (const 4 0) (add x y)))",
            "    (assign h (or (or (and (xor e (const 1 1)) (icmp ule x y)) \
             (and (icmp ugt x y) (icmp slt s (const 4 1)))) (and (icmp sle s s) (icmp sgt s s))))",
            "    (assign i (shl x y)))",
            "  (module P",
            "    (input a (bits 8))))"
        ])
    );
}

fn shifts() -> String {
    let mut e = "x".to_owned();
    for _ in 0..30 {
        e = format!("({e} >> c)");
    }
    format!(
        "module S() {{\n  input x: SInt[1];\n  input c: UInt[2];\n  output y: SInt[1];\n  \
         y := {e};\n}}\n"
    )
}

/// The case of section 11.3: each source shift gives exactly 2 `shrs`, and each inner shift
/// is a temporary, so the output stays linear.
#[test]
fn nested_shifts_stay_linear() {
    let out = sil(&shifts(), "S");
    assert_eq!(out.matches("shrs").count(), 60);
    assert_eq!(out.matches("(let y$").count(), 29);
}

/// `S020` is at the cycle node with the lowest source position.
#[test]
fn a_combinational_cycle() {
    let wires = "module M() {\n  input a: Bool;\n  output y: Bool;\n  wire w: Bool;\n  \
                 wire v: Bool;\n  v := w && a;\n  w := v || a;\n  y := w;\n}\n";
    assert_eq!(sil(wires, "M"), "S020 6:3");
    let through = "module P() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := a;\n}\n\
                   module T() domains() {\n  output y: Bool;\n  instance u = P();\n  \
                   u.a := u.q;\n  y := u.q;\n}\n";
    assert_eq!(sil(through, "T"), "S020 8:3");
}

const SMALL: &str = "module M() {\n  input a: UInt[2];\n  input b: UInt[2];\n  \
    input c: UInt[3];\n  output y: UInt[2];\n  y := (a +% b) << (c ^ 1);\n}\n";

/// `SMALL` lowers with 58 units, and each unit is needed.
#[test]
fn the_charges_of_the_lowering() {
    let units = total(SMALL, "M");
    assert_eq!(units, elab_used(SMALL, "M") + 58);
    assert!(sil_fuel(SMALL, "M", units).starts_with("(design "));
    assert_eq!(sil_fuel(SMALL, "M", units - 1), "S015 1:1");
    assert_eq!(sil_fuel(SMALL, "M", elab_used(SMALL, "M") + 24), "S015 3:3");
}

/// Each field of a core name charges its bytes. A port name of 100 bytes occurs twice.
#[test]
fn a_name_pays_its_bytes() {
    let named = |x: &str| {
        format!("module M() domains() {{\n  input a: Bool;\n  output {x}: Bool;\n  {x} := a;\n}}\n")
    };
    let lowering = |src: &str| total(src, "M") - elab_used(src, "M");
    assert_eq!(
        lowering(&named(&"q".repeat(100))),
        lowering(&named("q")) + 198
    );
}

/// A loop value is a made integer field, and it charges the square of its size in each name.
#[test]
fn a_big_loop_value_pays_its_digits() {
    let src = "module M() {\n  input x: Bool;\n  output y: Bool;\n  \
               comptime for i in (1 << 100000)..(1 << 100000) + 1 {\n    let t = x;\n    \
               y := t;\n  }\n}\n";
    assert!(total(src, "M") > elab_used(src, "M") + 2 * 1563 * 1563);
}

fn chain(k: usize, e: &str) -> String {
    let mut e = e.to_owned();
    for _ in 0..k {
        e = format!("({e} +% x)");
    }
    e
}

fn core_chain(k: usize, e: &str) -> String {
    let mut e = e.to_owned();
    for _ in 0..k {
        e = format!("(add {e} x)");
    }
    e
}

fn high(k: usize) -> String {
    format!(
        "module D() domains() {{\n  input x: UInt[8];\n  output y: UInt[8];\n  y := {};\n}}\n",
        chain(k, "x")
    )
}

fn deep_text(lets: &[String], y: &str) -> String {
    let mut lines = vec![
        "(design D".to_owned(),
        "  (module D".to_owned(),
        "    (input x (bits 8))".to_owned(),
        "    (output y (bits 8))".to_owned(),
    ];
    lines.extend(lets.iter().cloned());
    lines.push(format!("    (assign y {y})))"));
    text(&lines)
}

/// A node whose effective height reaches 64 binds to a temporary of the effective height 1.
/// The value of a statement does not bind, so each 63 additions bind one temporary.
#[test]
fn the_effective_height() {
    let t0 = format!("    (let y$0t (bits 8) {})", core_chain(63, "x"));
    let t1 = format!("    (let y$1t (bits 8) {})", core_chain(63, "y$0t"));
    assert_eq!(sil(&high(63), "D"), deep_text(&[], &core_chain(63, "x")));
    assert_eq!(
        sil(&high(64), "D"),
        deep_text(std::slice::from_ref(&t0), &core_chain(1, "y$0t"))
    );
    assert_eq!(
        sil(&high(127), "D"),
        deep_text(&[t0.clone(), t1.clone()], &core_chain(1, "y$1t"))
    );
    assert_eq!(
        sil(&high(128), "D"),
        deep_text(&[t0, t1], &core_chain(2, "y$1t"))
    );
}

/// A 4096-high source expression binds 64 temporaries and lowers to valid text.
#[test]
fn the_highest_expression() {
    let out = sil(&high(4095), "D");
    assert_eq!(out.matches("(let y$").count(), 64);
    assert!(valid(&out));
}

/// A spine of `n` additions whose step `i` adds the chain of `sib(i)` additions.
fn branchy(n: usize, sib: impl Fn(usize) -> usize) -> String {
    let mut e = "x".to_owned();
    for i in 0..n {
        e = format!("({e} +% {})", chain(sib(i), "x"));
    }
    format!("module D() domains() {{\n  input x: UInt[8];\n  output y: UInt[8];\n  y := {e};\n}}\n")
}

/// The height of the sibling at each step of a spine.
type Sibling = fn(usize) -> usize;

fn skip(i: usize) -> usize {
    match i {
        61 => 64,
        123 => 128,
        185 => 192,
        247 => 256,
        _ => 0,
    }
}

/// A taller sibling lifts the height of the spine past a multiple of 64. The effective height
/// still binds each 63 levels of the spine, so each shape lowers to valid text.
#[test]
fn a_branching_spine() {
    assert!(valid(&sil(&branchy(257, skip), "D")));
    let shapes: [(usize, Sibling); 5] = [
        (300, |i| i % 70),
        (300, |i| i * 7 % 130),
        (260, |i| (i * 37) % 66),
        (200, |i| if i % 2 == 0 { 63 } else { 64 }),
        (257, |i| skip(i) + i % 3),
    ];
    for (n, f) in shapes {
        assert!(valid(&sil(&branchy(n, f), "D")), "{n}");
    }
}

/// A core error other than `E008` in a lowered design is a defect.
#[test]
fn another_core_error_is_a_defect() {
    let broken = text(&[
        "(design D",
        "  (module D",
        "    (output y (bits 8))",
        "    (assign y z)))",
    ]);
    let design = parse(&broken).unwrap();
    assert!(matches!(check(&design), Err(Failure::Defect(m)) if m.starts_with("error[")));
}

/// Each design of these tests that elaborates also passes the core checker.
#[test]
fn each_design_passes_the_core_checker() {
    for (src, top) in [
        (counter(), "Main"),
        (OPS.to_owned(), "M"),
        (OPS2.to_owned(), "N"),
        (UNROLL.to_owned(), "R(3)"),
        (shifts(), "S"),
        (SMALL.to_owned(), "M"),
    ] {
        assert!(sil(&src, top).starts_with("(design "), "{top}");
    }
}

/// A name refers to a core name, so its hardware value has the size of a finite value of its
/// type (section 5.4). Each copy of a `UInt[256]` name charges 4, and each copy of a `UInt[64]`
/// name 1. The binding of `p`, the binding of `x`, and the `:=` of `y` copy a name.
fn copies(w: u32) -> String {
    format!(
        "module M() {{\n  input p: UInt[{w}];\n  output q: UInt[{w}];\n  let x = p;\n  let y = x;\n  q := y;\n}}\n"
    )
}

#[test]
fn a_copy_of_a_wide_name_charges_its_width() {
    assert_eq!(total(&copies(256), "M"), total(&copies(64), "M") + 9);
    assert_eq!(total(&copies(256), "M"), 99);
    assert!(!sil_fuel(&copies(256), "M", 99).starts_with("S015"));
    assert!(sil_fuel(&copies(256), "M", 98).starts_with("S015"));
}

/// A static container of `Bool`, `UInt`, or `SInt` in a hardware aggregate has hardware leaves in
/// its type only. A read of it, with an index that changes a sibling, holds the root like the
/// read of any static part, so the fuel equals that of Lean. The totals are those of
/// `silicon-check cost`.
#[test]
fn a_static_container_with_leaf_types_holds_the_root() {
    let body = |decl: &str, root: &str, read: &str, out: &str| {
        format!(
            "module M() domains() {{ input a: UInt[8]; output y: UInt[8]; {decl} let mut t = {root}; let k = {read}; y := {out}; }}\n"
        )
    };
    let cases = [
        (
            body(
                "",
                "(a, list(Nat), [(false, true)])",
                "t.2[0][(t.1.push(1), 0).1]",
                "t.0",
            ),
            122,
        ),
        (
            body(
                "let s: [UInt[8]; 2] = [1, 2];",
                "(a, list(Nat), s)",
                "t.2[(t.1.push(1), 0).1]",
                "t.0",
            ),
            136,
        ),
        (
            body(
                "let s: (SInt[4], [SInt[4]; 2]) = (-1, [2, -3]);",
                "(a, list(Nat), s)",
                "t.2.1[(t.1.push(1), 0).1]",
                "t.0",
            ),
            183,
        ),
        (
            body(
                "let s: [[(Bool, UInt[2]); 1]; 1] = [[(true, 2)]];",
                "(list(Nat), (a, ((s, a), a)))",
                "t.1.1.0.0[0][(t.0.push(1), 0).1].0",
                "a",
            ),
            254,
        ),
    ];
    for (src, units) in cases {
        assert_eq!(total(&src, "M"), units, "{src}");
        assert!(!sil_fuel(&src, "M", units).starts_with("S015"), "{src}");
        assert!(sil_fuel(&src, "M", units - 1).starts_with("S015"), "{src}");
    }
}

/// The `let` lines of the canonical text of `src`.
pub(crate) fn enum_lets(src: &str) -> Vec<String> {
    sil(src, "M")
        .lines()
        .filter(|l| l.starts_with("    (let "))
        .map(str::to_owned)
        .collect()
}

/// The module `M` with the enum `Op` and the hardware inputs `x`, `c`, `y`, and `e`.
pub(crate) fn op_module(body: &str) -> String {
    format!(
        "enum Op: UInt[2] {{ Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }}\n\
         module M() {{\n  input x: UInt[8];\n  input c: Bool;\n  input y: UInt[4];\n  \
         input e: Op;\n  output o: Bool;\n{body}  o := true;\n}}\n"
    )
}

/// The constructor of a hardware enum (section 7.4). The static tag needs no statement. The
/// payload is the `concat` chain of its leaves, the first leaf in the low bits, inside zero
/// high bits when the leaves are narrower than `P`. One leaf of `P` bits is that leaf.
#[test]
fn a_hardware_constructor_lowers_to_a_concat_chain() {
    let lets = |body: &str| enum_lets(&op_module(body));
    assert_eq!(
        lets("  let a = Op::Load(x);\n"),
        ["    (let a$payload (bits 8) x)"]
    );
    assert_eq!(
        lets("  let a = Op::Pair(c, y);\n"),
        ["    (let a$payload (bits 8) (concat (const 3 0) (concat y c)))"]
    );
    // The units of the lowering alone.
    let units = |body: &str| total(&op_module(body), "M") - elab_used(&op_module(body), "M");
    assert_eq!(
        units("  let a = Op::Pair(c, y);\n"),
        units("  let a = Op::Load(x);\n") + 5
    );
    assert_eq!(
        lets("  let a = if (c) { Op::Load(x) } else { Op::Pair(c, y) };\n"),
        [
            "    (let a$payload (bits 8) (mux c x (concat (const 3 0) (concat y c))))",
            "    (let a$tag (bits 2) (mux c (const 2 1) (const 2 2)))"
        ]
    );
}

/// A payload of 70 leaves is one `concat` chain. The loop builds it from the first leaf, and the
/// chain so far binds to a temporary when its height reaches 64.
#[test]
fn a_wide_pack_binds_a_temporary_at_the_height_64() {
    let src = "enum W: UInt[1] { A([Bool; 70]) = 1 }\nmodule M() {\n  input x: [Bool; 70];\n  \
               output o: Bool;\n  let a = W::A(x);\n  o := true;\n}\n";
    let lets = enum_lets(src);
    assert_eq!(lets.len(), 2, "{lets:?}");
    let mut high = "a$payload$0t".to_owned();
    for k in 64..=69 {
        high = format!("(concat x${k}e {high})");
    }
    assert_eq!(lets[0], format!("    (let a$payload (bits 70) {high})"));
    let mut low = "x$0e".to_owned();
    for k in 1..=63 {
        low = format!("(concat x${k}e {low})");
    }
    assert_eq!(lets[1], format!("    (let a$payload$0t (bits 64) {low})"));
}

/// `reinterpret` between an enum and its bits (section 7.4). The pack is `(concat payload
/// tag)`. The unpack is `(extract b 0 W)` and `(extract b W P)`. Both leaves refer to a core
/// name `b`. Another `b` binds to one temporary of the leaf statement that lowers first.
#[test]
fn reinterpret_lowers_to_concat_and_extract() {
    let lets = |body: &str| enum_lets(&op_module(body));
    assert_eq!(
        lets("  let d = Op::Pair(c, y);\n  let a = reinterpret(UInt[10], d);\n"),
        [
            "    (let a (bits 10) (concat d$payload (const 2 2)))",
            "    (let d$payload (bits 8) (concat (const 3 0) (concat y c)))"
        ]
    );
    assert_eq!(
        lets("  let b = resize(UInt[10], x);\n  let a = reinterpret(Op, b);\n"),
        [
            "    (let a$payload (bits 8) (extract b 2 8))",
            "    (let a$tag (bits 2) (extract b 0 2))",
            "    (let b (bits 10) (concat (const 2 0) x))"
        ]
    );
    assert_eq!(
        lets("  let a = reinterpret(Op, resize(UInt[10], x));\n"),
        [
            "    (let a$payload (bits 8) (extract a$tag$0t 2 8))",
            "    (let a$tag (bits 2) (extract a$tag$0t 0 2))",
            "    (let a$tag$0t (bits 10) (concat (const 2 0) x))"
        ]
    );
    assert_eq!(
        lets("  let a = reinterpret(UInt[10], reinterpret(Op, resize(UInt[10], x)));\n"),
        [
            "    (let a (bits 10) (concat (extract a$0t 2 8) (extract a$0t 0 2)))",
            "    (let a$0t (bits 10) (concat (const 2 0) x))"
        ]
    );
}

/// `k` nested round trips bind `k` more temporaries, one for each shared operand. Each level adds
/// 21 units. The output and the charge thus stay linear, where copies would give `2^k` nodes.
#[test]
fn nested_round_trips_stay_linear() {
    let trips = |k: usize| {
        let mut e = "reinterpret(Op, resize(UInt[10], x))".to_owned();
        for _ in 0..k {
            e = format!("reinterpret(Op, reinterpret(UInt[10], {e}))");
        }
        op_module(&format!("  let a = {e};\n"))
    };
    for k in 0..20 {
        assert_eq!(enum_lets(&trips(k)).len(), k + 3, "{k}");
        let lowering = |k: usize| total(&trips(k), "M") - elab_used(&trips(k), "M");
        assert_eq!(lowering(k + 1), lowering(k) + 21, "{k}");
    }
}

/// With `P` 0, a conversion makes no core node: the unpack is `b`, and the pack is the tag.
#[test]
fn a_conversion_with_an_empty_payload_makes_no_node() {
    let src = "enum E: UInt[2] { A = 0, B = 1 }\nmodule M() {\n  input c: Bool;\n  input e: E;\n  \
               input u: UInt[2];\n  output o: Bool;\n  let a = reinterpret(E, u +% 1);\n  \
               let b = reinterpret(UInt[2], a);\n  o := true;\n}\n";
    assert_eq!(
        enum_lets(src),
        [
            "    (let a$tag (bits 2) (add u (const 2 1)))",
            "    (let b (bits 2) a$tag)"
        ]
    );
}

/// An enum port, register, wire, and child port has the two leaves `tag` and `payload`, in this
/// order, and an empty payload gives only `tag` (section 7.5). A register resets each leaf to
/// that leaf of its reset value. An enum field of a record adds its two leaves at its place.
#[test]
fn an_enum_has_the_leaves_tag_and_payload() {
    let src = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\n\
               enum F: UInt[1] { A = 0, B = 1 }\n\
               struct S { f: Op, g: Bool }\nmodule C() {\n  input a: Op;\n  output b: Op;\n  \
               b := a;\n}\nmodule M() {\n  input i: Op;\n  input s: S;\n  input x: UInt[8];\n  \
               input z: F;\n  output o: Op;\n  output q: Op;\n  output t: S;\n  output y: F;\n  \
               reg r: Op = Op::Load(7);\n  r := Op::Load(x);\n  wire w: Op;\n  w := i;\n  \
               instance c = C();\n  c.a := r;\n  o := w;\n  q := c.b;\n  t := s;\n  y := z;\n}\n";
    assert_eq!(
        sil(src, "M"),
        text(&[
            "(design M",
            "  (module C",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input a$tag (bits 2))",
            "    (input a$payload (bits 8))",
            "    (output b$tag (bits 2))",
            "    (output b$payload (bits 8))",
            "    (assign b$payload a$payload)",
            "    (assign b$tag a$tag))",
            "  (module M",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input i$tag (bits 2))",
            "    (input i$payload (bits 8))",
            "    (input s$f$tag (bits 2))",
            "    (input s$f$payload (bits 8))",
            "    (input s$g (bits 1))",
            "    (input x (bits 8))",
            "    (input z$tag (bits 1))",
            "    (output o$tag (bits 2))",
            "    (output o$payload (bits 8))",
            "    (output q$tag (bits 2))",
            "    (output q$payload (bits 8))",
            "    (output t$f$tag (bits 2))",
            "    (output t$f$payload (bits 8))",
            "    (output t$g (bits 1))",
            "    (output y$tag (bits 1))",
            "    (reg r$payload (bits 8) clock$0clk (reset sync clock$0rst (const 8 7)))",
            "    (reg r$tag (bits 2) clock$0clk (reset sync clock$0rst (const 2 1)))",
            "    (inst c C (clock$0clk clock$0clk) (clock$0rst clock$0rst) (a$tag r$tag) \
             (a$payload r$payload))",
            "    (let w$payload (bits 8) i$payload)",
            "    (let w$tag (bits 2) i$tag)",
            "    (next r$payload x)",
            "    (next r$tag (const 2 1))",
            "    (assign o$payload w$payload)",
            "    (assign o$tag w$tag)",
            "    (assign q$payload c.b$payload)",
            "    (assign q$tag c.b$tag)",
            "    (assign t$f$payload s$f$payload)",
            "    (assign t$f$tag s$f$tag)",
            "    (assign t$g s$g)",
            "    (assign y$tag z$tag)))"
        ])
    );
}

/// An enum memory word packs its leaves, `tag` in the low bits (section 7.6). The `data` of the
/// response is a reference to the word, so its leaves are `extract` nodes at the offsets 0 and
/// `W`. An enum field of a word starts at the offset of its field, here 1 after the `Bool`.
#[test]
fn an_enum_memory_word_packs_the_tag_in_the_low_bits() {
    let src = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\nmodule M() {\n  input a: UInt[2];\n  \
               input c: Bool;\n  input d: Op;\n  output o: Op;\n  output t: UInt[10];\n  \
               mem m: [Op; 4];\n  let k = read_port(m, a, c);\n  write_port(m, a, d, c);\n  \
               o := k.data;\n  t := reinterpret(UInt[10], k.data);\n}\n";
    assert_eq!(
        sil(src, "M"),
        text(&[
            "(design M",
            "  (module M",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input a (bits 2))",
            "    (input c (bits 1))",
            "    (input d$tag (bits 2))",
            "    (input d$payload (bits 8))",
            "    (output o$tag (bits 2))",
            "    (output o$payload (bits 8))",
            "    (output t (bits 10))",
            "    (reg m$0rdata (bits 10) clock$0clk (reset sync clock$0rst (const 10 0)))",
            "    (reg m$0rvalid (bits 1) clock$0clk (reset sync clock$0rst (const 1 0)))",
            "    (mem m (bits 10) 4 clock$0clk)",
            "    (let k$data$payload (bits 8) (extract m$0rdata 2 8))",
            "    (let k$data$tag (bits 2) (extract m$0rdata 0 2))",
            "    (let k$valid (bits 1) m$0rvalid)",
            "    (let m$0raddr (bits 2) a)",
            "    (let m$0ren (bits 1) c)",
            "    (next m$0rdata (mux m$0ren (read m m$0raddr) m$0rdata))",
            "    (next m$0rvalid (and m$0ren (const 1 1)))",
            "    (write m 0 a (concat d$payload d$tag) (and c (xor clock$0rst (const 1 1))))",
            "    (assign o$payload k$data$payload)",
            "    (assign o$tag k$data$tag)",
            "    (assign t (concat k$data$payload k$data$tag))))"
        ])
    );
    let field = "enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1 }\nstruct S { b: Bool, f: Op }\n\
                 module M() {\n  input c: Bool;\n  input d: S;\n  output o: S;\n  mem m: [S; 2];\n  \
                 let k = read_port(m, 0, c);\n  write_port(m, 0, d, c);\n  o := k.data;\n}\n";
    let lets: Vec<String> = sil(field, "M")
        .lines()
        .filter(|l| l.starts_with("    (let k$data"))
        .map(str::to_owned)
        .collect();
    assert_eq!(
        lets,
        [
            "    (let k$data$b (bits 1) (extract m$0rdata 0 1))",
            "    (let k$data$f$payload (bits 8) (extract m$0rdata 3 8))",
            "    (let k$data$f$tag (bits 2) (extract m$0rdata 1 2))"
        ]
    );
}
