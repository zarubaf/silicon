// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Elab` in Lean, and the cases of the top selection of
//! `Silicon.Source.Test.Eval`: the table of instantiations, the depth-first order, the charges
//! of `instance` statements, each check for each instantiation at its position, and the core
//! names of section 7.3.
//!
//! The Lean `cost` adds the charges of the lowering, which a later part of #72 brings. The
//! numbers here are those of Lean `Elab.elaborate` and `Elab.costLines` alone.

use crate::names::sha16;
use crate::{Abort, Budget, Design, elaborate_with};
use std::fmt::Write;

/// A test digest function that maps each serialization to one digest.
fn collide(_: &str) -> String {
    "0000000000000000".to_owned()
}

/// The checked file of `src`, or the code and the position of the first error before
/// elaboration.
pub(crate) fn load(src: &str) -> Result<resolve::Resolved, String> {
    let at = |code: &dyn std::fmt::Display, pos: parse::ast::Pos| {
        format!("{code} {}:{}", pos.line, pos.col)
    };
    let parsed = parse::parse(src).unwrap();
    if let Some(e) = parsed.errors().first() {
        return Err(at(&e.code, e.pos));
    }
    let file = match resolve::resolve(parsed) {
        Ok(file) => file,
        Err(resolve::Failed::Names(e)) => return Err(at(&e[0].code, e[0].pos)),
        Err(resolve::Failed::Parse(_) | resolve::Failed::Stack(_)) => panic!("no resolve"),
    };
    match typeck::check(file) {
        Ok(file) => Ok(file),
        Err(typeck::Failed::Errors(e)) => Err(at(&e[0].code, e[0].pos)),
        Err(typeck::Failed::Stack(e)) => panic!("{e}"),
    }
}

/// The elaboration of `src` with the top selection `top`, or the code and the position of
/// the first error, or `usage`.
fn run(
    src: &str,
    top: &str,
    fuel: u64,
    depth: u64,
    digest: fn(&str) -> String,
) -> Result<Design, String> {
    let file = load(src)?;
    let budget = Budget { fuel, depth };
    match elaborate_with(&file, top, parse::DEFAULT_SYNTAX_DEPTH, budget, digest) {
        Ok(Ok(d)) => Ok(d),
        Ok(Err(e)) => Err(format!("{} {}:{}", e.code, e.pos.line, e.pos.col)),
        Err(Abort::Usage(_)) => Err("usage".to_owned()),
        Err(Abort::Stack(e)) => panic!("{e}"),
    }
}

/// The output of `cost`, or the code and the position of the first error.
fn cost_with(src: &str, top: &str, fuel: u64, depth: u64, digest: fn(&str) -> String) -> String {
    match run(src, top, fuel, depth, digest) {
        Ok(d) => d.cost(),
        Err(e) => e,
    }
}

pub(crate) fn cost(src: &str, top: &str) -> String {
    let b = Budget::default();
    cost_with(src, top, b.fuel, b.depth, sha16)
}

pub(crate) fn cost_fuel(src: &str, top: &str, fuel: u64) -> String {
    cost_with(src, top, fuel, Budget::default().depth, sha16)
}

/// `ok` with the units of the elaboration alone at the fuel `fuel` and the depth `depth`, or the
/// code and the position of the first error.
pub(crate) fn elab_only(src: &str, top: &str, fuel: u64, depth: u64) -> String {
    match run(src, top, fuel, depth, sha16) {
        Ok(d) => format!("ok {}", d.used()),
        Err(e) => e,
    }
}

pub(crate) fn cost_depth(src: &str, top: &str, depth: u64) -> String {
    cost_with(src, top, Budget::default().fuel, depth, sha16)
}

pub(crate) fn design(src: &str, top: &str) -> Design {
    let b = Budget::default();
    run(src, top, b.fuel, b.depth, sha16).unwrap()
}

/// The total fuel of `cost`.
pub(crate) fn total(src: &str, top: &str) -> u64 {
    design(src, top).used()
}

/// The cost is `units`. This fuel passes, and one unit less gives `S015`.
fn exact(src: &str, top: &str, units: u64) {
    assert_eq!(total(src, top), units);
    assert!(cost_fuel(src, top, units).starts_with("total"));
    assert!(cost_fuel(src, top, units - 1).starts_with("S015"));
}

/// The emitted names in the order in which the instantiations finish.
pub(crate) fn order(src: &str, top: &str) -> Vec<String> {
    design(src, top).order()
}

/// The core names of the named bindings, the registers, the wires, and the children of `m`.
pub(crate) fn names(src: &str, top: &str, m: &str) -> Vec<String> {
    design(src, top).core_names(m).unwrap()
}

/// The counter of the v0.1 README, with a parent.
const COUNTER: &str = "module Counter(comptime W: Nat) {
    input enable: Bool;
    output value: UInt[W];
    output full: Bool;
    reg count: UInt[W] = 0;
    count := if (enable) { count +% 1 } else { count };
    value := count;
    full := count == UInt[W]((1 << W) - 1);
}
module Main() {
    input enable: Bool;
    output value: UInt[4];
    instance counter = Counter(4);
    counter.enable := enable;
    value := counter.value;
}
";

#[test]
fn the_counter() {
    assert_eq!(cost(COUNTER, "Main"), "total 168\nCounter$4 66\nMain 70\n");
    exact(COUNTER, "Main", 168);
    assert_eq!(cost(COUNTER, "Counter(8)"), "total 118\nCounter$8 66\n");
    assert_eq!(order(COUNTER, "Main"), ["Counter$4", "Main"]);
}

const LEAF: &str = "module C(comptime n: Nat) {\n}\n";

/// A child finishes before its parent. A repeated `InstantiationId` elaborates once. Its
/// `instance` statement charges 1, and its argument charges 2 for the node and the literal,
/// Its parameter type `Nat` charges 1, and the recursive size 1. Its serialization charges 1 for
/// the decimal form and 32 for its bytes. These are 38 units. The child pays nothing for its
/// parameter.
#[test]
fn the_table_of_instantiations() {
    let one = format!("{LEAF}module T() {{\n  instance a = C(5);\n}}\n");
    let two = format!("{LEAF}module T() {{\n  instance a = C(5);\n  instance b = C(5);\n}}\n");
    let other = format!("{LEAF}module T() {{\n  instance a = C(5);\n  instance b = C(6);\n}}\n");
    assert_eq!(total(&two, "T"), total(&one, "T") + 38);
    assert_eq!(order(&two, "T"), ["C$5", "T"]);
    assert_eq!(order(&other, "T"), ["C$5", "C$6", "T"]);
    assert_eq!(cost(&other, "T"), "total 111\nC$5 1\nC$6 1\nT 83\n");
}

/// An instantiation that depends on itself is `S019` at its `instance` statement.
#[test]
fn a_cycle_of_instantiations() {
    let self_dep = "module M(comptime d: Nat) {\n  instance a = M(d);\n}\n";
    let cycle = "module A(comptime d: Nat) {\n  instance b = B(d);\n}\n\
                 module B(comptime d: Nat) {\n  instance a = A(d);\n}\n";
    assert_eq!(cost(self_dep, "M(3)"), "S019 2:3");
    assert_eq!(cost(cycle, "A(1)"), "S019 5:3");
}

/// Two identities that share an emitted name are `S019` at the `instance` statement of the
/// second. A test digest function makes all digests equal.
#[test]
fn two_identities_share_a_digest() {
    let src = "module M(comptime x: [UInt[8]; 1]) {\n}\n\
               module T() {\n  instance a = M([1]);\n  instance b = M([2]);\n}\n";
    assert!(cost(src, "T").starts_with("total"));
    let b = Budget::default();
    assert_eq!(cost_with(src, "T", b.fuel, b.depth, collide), "S019 5:3");
    assert_eq!(
        order(src, "T"),
        [
            format!(
                "M$0h{}",
                sha16("(instantiation root M ((array (uint 8) ((uint 8 1)))))")
            ),
            format!(
                "M$0h{}",
                sha16("(instantiation root M ((array (uint 8) ((uint 8 2)))))")
            ),
            "T".to_owned()
        ]
    );
}

/// An emitted name is taken when its instantiation starts. A descendant that shares the
/// emitted name of an active ancestor is thus `S019` at its own `instance` statement.
#[test]
fn a_name_is_taken_at_the_start() {
    let src = "module M(comptime x: [UInt[8]; 1]) {\n\
               \x20 comptime if (x[0] == UInt[8](1)) { instance a = M([0]); }\n}\n\
               module T() {\n  instance b = M([1]);\n}\n";
    assert!(cost(src, "T").starts_with("total"));
    let b = Budget::default();
    assert_eq!(cost_with(src, "T", b.fuel, b.depth, collide), "S019 2:38");
}

/// A serialization charges its length in bytes, and an emitted name too. A module with a long
/// name thus pays for each new instantiation, and 1000 of them fail with `S015` under a small
/// fuel. A short name passes with the same fuel.
#[test]
fn a_long_name_pays_for_each_instantiation() {
    let src = |n: &str| {
        format!(
            "module {n}(comptime i: Int) {{\n}}\nmodule T() {{\n  comptime for i in 0..1000 {{\n\
             \x20   instance u = {n}(i);\n  }}\n}}\n"
        )
    };
    assert_eq!(
        cost_fuel(&src(&"a".repeat(100_000)), "T", 1_000_000),
        "S015 5:5"
    );
    assert!(cost_fuel(&src("L"), "T", 1_000_000).starts_with("total"));
}

/// The decimal form of an integer in a serialization charges the square of its size. The
/// argument `1 << 1000000` has the size 15626, so its serialization fails before it runs.
#[test]
fn a_big_argument_pays_its_decimal_form() {
    let src = "module M(comptime x: Int) {\n}\nmodule T() {\n  instance u = M(1 << 1000000);\n}\n";
    assert_eq!(cost_fuel(src, "T", 10_000_000), "S015 4:3");
}

/// A child with a free input is `S018` at its `instance` statement. The counts select the
/// first such child, so a module with 8000 inputs and 8000 children returns fast.
#[test]
fn the_first_child_with_a_free_input() {
    let n = 8000;
    let mut src = "module W() {\n".to_owned();
    for j in 0..n {
        writeln!(src, "  input i{j}: Bool;").unwrap();
    }
    write!(
        src,
        "}}\nmodule T() {{\n  comptime for k in 0..{n} {{\n    instance u = W();\n  }}\n}}\n"
    )
    .unwrap();
    let start = std::time::Instant::now();
    assert_eq!(cost_fuel(&src, "T", 1_000_000), "S018 8005:5");
    assert!(start.elapsed() < std::time::Duration::from_secs(10));
}

const BRANCH: &str = "module M(comptime d: Nat, comptime id: Nat) {
  output o: Bool;
  comptime if (d == 0) { o := true; } else {
    instance a = M(d - 1, 2 * id);
    instance b = M(d - 1, 2 * id + 1);
    o := a.o && b.o;
  }
}
";

const SHARED: &str = "module M(comptime d: Nat) {
  output o: Bool;
  comptime if (d == 0) { o := true; } else {
    instance a = M(d - 1);
    instance b = M(d - 1);
    o := a.o && b.o;
  }
}
";

/// The branching hierarchy of section 11.3 with `d = 10`: 2047 instantiations.
#[test]
fn the_branching_hierarchy() {
    assert_eq!(order(BRANCH, "M(10, 0)").len(), 2047);
    assert_eq!(total(BRANCH, "M(10, 0)"), 175_878);
    exact(BRANCH, "M(10, 0)", 175_878);
    let lines = cost(BRANCH, "M(10, 0)");
    assert!(lines.starts_with("total 175878\nM$0$0 14\nM$0$1 14\nM$0$10 14\n"));
}

/// The shared hierarchy of section 11.3 with `d = 30`: 31 instantiations, linear in `d`.
#[test]
fn the_shared_hierarchy() {
    assert_eq!(order(SHARED, "M(30)").len(), 31);
    exact(SHARED, "M(30)", 3326);
    assert_eq!(
        total(SHARED, "M(30)") - total(SHARED, "M(29)"),
        total(SHARED, "M(20)") - total(SHARED, "M(19)")
    );
    assert_eq!(total(SHARED, "M(30)") - total(SHARED, "M(29)"), 110);
}

const CHAIN: &str = "module Chain(comptime d: Nat) {
  comptime if (d > 0) { instance c = Chain(d - 1); }
}
";

/// A deep child first and a shallow child later, and the reverse order. The top and the
/// chain `Chain(5)` to `Chain(0)` nest 7 levels. In the reverse order, `Chain(3)` nests 5
/// levels first. Then `Chain(5)` and `Chain(4)` nest 3 levels, and `Chain(3)` is done.
#[test]
fn the_nesting_depth_of_instantiations() {
    let deep_first =
        format!("{CHAIN}module Top() {{\n  instance a = Chain(5);\n  instance b = Chain(3);\n}}\n");
    let shallow_first =
        format!("{CHAIN}module Top() {{\n  instance a = Chain(3);\n  instance b = Chain(5);\n}}\n");
    assert!(cost_depth(&deep_first, "Top", 7).starts_with("total"));
    assert_eq!(cost_depth(&deep_first, "Top", 6), "S015 2:25");
    assert!(cost_depth(&shallow_first, "Top", 5).starts_with("total"));
    assert_eq!(cost_depth(&shallow_first, "Top", 4), "S015 2:25");
    assert_eq!(total(&deep_first, "Top"), total(&shallow_first, "Top"));
    assert_eq!(total(&deep_first, "Top"), 440);
}

/// A deep chain of instantiations runs a group of levels on each thread, so a large nesting
/// depth needs no large stack. Deep blocks around the `instance` statement too.
#[test]
fn a_deep_chain_of_instantiations() {
    let src = "module C(comptime d: Nat) {\n  output o: Bool;\n\
               \x20 comptime if (d > 0) { instance c = C(d - 1); o := c.o; } else { o := true; }\n}\n";
    assert!(cost_depth(src, "C(20000)", 30_000).starts_with("total 1337842\n"));
    assert_eq!(cost_depth(src, "C(20000)", 20_000), "S015 3:25");
    let blocks = format!(
        "module C(comptime d: Nat) {{\n  output o: Bool;\n  {}comptime if (d > 0) {{ \
         instance c = C(d - 1); o := c.o; }} else {{ o := true; }}{}\n}}\n",
        "{ ".repeat(1000),
        " }".repeat(1000)
    );
    assert!(cost(&blocks, "C(300)").starts_with("total 320038\n"));
}

/// The core names of section 7.3: loop frames, call frames, versions, and the result role.
#[test]
fn the_core_names() {
    let helpers = "fn add(comptime W: Nat, a: UInt[W], b: UInt[W]) -> UInt[W] {
  let t = a +% b;
  return t;
}
module M() {
  input x: UInt[8];
  output y: UInt[8];
  let s = add(8, x, 1);
  comptime for i in 0..2 {
    let z = add(8, s, i);
    reg r: Bool = false;
    r := true;
  }
  { let s = x; }
  let mut q = x;
  q = q +% 1;
  instance u = Leaf();
  y := s;
}
module Leaf() {
}
";
    assert_eq!(
        names(helpers, "M", "M"),
        [
            "add$0c$a",
            "add$0c$t",
            "add$0c$0ret",
            "s",
            "i$0$add$1c$a",
            "i$0$add$1c$t",
            "i$0$add$1c$0ret",
            "i$0$z",
            "i$1$add$1c$a",
            "i$1$add$1c$t",
            "i$1$add$1c$0ret",
            "i$1$z",
            "s$1v",
            "q",
            "q$1v",
            "i$0$r",
            "i$1$r",
            "u"
        ]
    );
    assert_eq!(cost(helpers, "M"), "total 238\nLeaf 1\nM 211\n");
}

/// A static value gets no core name. A user name equal to a core keyword gets `0k`.
#[test]
fn a_keyword_gets_its_escape() {
    let src = "module next() {
  input add: Bool;
  output bits: Bool;
  let design = add;
  let k = 5;
  wire inst: Bool;
  inst := design;
  bits := inst;
}
";
    assert_eq!(names(src, "next", "next$0k"), ["design$0k", "inst$0k"]);
    assert_eq!(cost(src, "next"), "total 54\nnext$0k 19\n");
}

/// Each hardware operator of slice 1, a hardware `if` with static arms, a hardware shift
/// count, the conversions, and a child input through a handle alias. A hardware `if` with two
/// equal static `Int` arms gives the static value (F19), here the static shift count `n`.
#[test]
fn the_hardware_operators() {
    let src = "module C() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := !a;\n}
module M() {
  input x: UInt[8];\n  input s: SInt[8];\n  input c: UInt[3];\n  input e: Bool;
  output y: UInt[8];\n  output z: SInt[16];\n  output b: Bool;
  let w = (x +% 1) -% (x *% 3) & ~x | (x ^ 255);
  let v = -s >> c;
  let n = if (e) { 2 } else { 2 };
  let k = if (e) { 1 } else { x << n };
  instance u = C();
  let h = u.a;
  h := e && x < 5 || s >= -1 && x != w;
  y := if (u.q) { k } else { reinterpret(UInt[8], s) };
  z := resize(SInt[16], v);
  b := if (e) { true } else { false };
}
";
    assert_eq!(order(src, "M"), ["C", "M"]);
    assert_eq!(names(src, "M", "M"), ["w", "v", "k", "u"]);
    exact(src, "M", 276);
    assert_eq!(cost(src, "M"), "total 276\nC 10\nM 240\n");
}

/// The module of the F19 cases: a hardware `if` in the body.
fn arms(body: &str) -> String {
    format!("module T() {{\n  input c: Bool;\n  output o: UInt[8];\n{body}  o := 0;\n}}\n")
}

/// F19: a hardware `if` with two static arms of a type that is not hardware data is a static
/// pair. It charges as a static equality, the sum of the sizes. Thus `if (c) { 3 } else { 3 }`
/// charges 6 more than `3`. Equal arms give the static value, and different arms are `S011` at
/// the `if`. An `Int` arm and a `Bool` arm have no join, so they are `S010`. Two arms of type
/// `()` give `()`.
#[test]
fn a_hardware_if_with_static_arms_is_a_static_pair() {
    let if_3 = total(&arms("  let k = if (c) { 3 } else { 3 };\n"), "T");
    assert_eq!(if_3, total(&arms("  let k = 3;\n"), "T") + 6);
    for equal in [
        "  let k = if (c) { \"a\" } else { \"a\" };\n",
        "  let k = if (c) { () } else { () };\n",
    ] {
        assert!(cost(&arms(equal), "T").starts_with("total"), "{equal}");
    }
    let cases = [
        ("  let k = if (c) { 3 } else { 4 };\n", "S011 4:11"),
        (
            "  let k = if (c) { UInt[8] } else { UInt[4] };\n",
            "S011 4:11",
        ),
        ("  let k = if (c) { 3 } else { true };\n", "S010 4:11"),
    ];
    for (body, code) in cases {
        assert_eq!(cost(&arms(body), "T"), code, "{body}");
    }
}

/// A hardware function: its arguments, its versions, and its result get core names in the
/// call frame, and the operand trees of each call are shared.
#[test]
fn a_hardware_function() {
    let src = "fn inc(a: UInt[8]) -> UInt[8] { let mut t = a; t = t +% 1; t = t +% 1; return t; }
module M() {
  input x: UInt[8];
  output y: UInt[8];
  let a = inc(x);
  let b = inc(inc(a));
  y := b;
}
";
    exact(src, "M", 174);
    assert_eq!(
        names(src, "M", "M"),
        [
            "inc$0c$a",
            "inc$0c$t",
            "inc$0c$t$1v",
            "inc$0c$t$2v",
            "inc$0c$0ret",
            "a",
            "inc$2c$a",
            "inc$2c$t",
            "inc$2c$t$1v",
            "inc$2c$t$2v",
            "inc$2c$0ret",
            "inc$1c$a",
            "inc$1c$t",
            "inc$1c$t$1v",
            "inc$1c$t$2v",
            "inc$1c$0ret",
            "b"
        ]
    );
}

/// Each case is a source, a top selection, and the code and the position of its first error.
fn errors(cases: &[(&str, &str, &str)]) {
    for (src, top, want) in cases {
        assert_eq!(cost(src, top), *want, "{src}");
    }
}

/// Two ports with one name are `S019`, also from a loop and after a binding of the name.
#[test]
fn two_ports_with_one_name() {
    errors(&[
        (
            "module M() {\n  comptime for i in 0..2 {\n    input x: Bool;\n  }\n}\n",
            "M",
            "S019 3:5",
        ),
        (
            "module M() {\n  input y: Bool;\n  let x = y;\n  { input x: Bool; }\n}\n",
            "M",
            "S019 4:5",
        ),
    ]);
}

/// `S010`: a port type is hardware data, operands have one type, and a binding has its type.
#[test]
fn the_type_rule() {
    errors(&[
        ("module M() {\n  input x: Nat;\n}\n", "M", "S010 2:3"),
        (
            "module M() {\n  input x: UInt[8];\n  input z: UInt[4];\n  output y: UInt[8];\n  y := x +% z;\n}\n",
            "M",
            "S010 5:8",
        ),
        (
            "module M() {\n  output y: UInt[8];\n  y := true;\n}\n",
            "M",
            "S010 3:3",
        ),
        (
            "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n  y := x + 1;\n}\n",
            "M",
            "S010 4:8",
        ),
        (
            "module M() {\n  input x: UInt[8];\n  output y: Bool;\n  y := x && true;\n}\n",
            "M",
            "S010 4:8",
        ),
        (
            "module M() {\n  input e: Bool;\n  input x: UInt[8];\n  output y: UInt[8];\n  y := if (e) { x } else { true };\n}\n",
            "M",
            "S010 5:8",
        ),
        (
            "module M() {\n  input c: UInt[2];\n  output y: Bool;\n  y := if (c) { true } else { false };\n}\n",
            "M",
            "S010 4:8",
        ),
        (
            "module M() {\n  input x: UInt[8];\n  input c: SInt[3];\n  output y: UInt[8];\n  y := x << c;\n}\n",
            "M",
            "S010 5:8",
        ),
        (
            "module C() domains() {\n  output a: Bool;\n  a := true;\n}\nmodule M() domains() {\n  output y: Bool;\n  instance c = C();\n  y := c.b;\n}\n",
            "M",
            "S010 8:8",
        ),
        (
            "module M() {\n  output y: Bool;\n  y := clock;\n}\n",
            "M",
            "S010 3:3",
        ),
        (
            "fn f(a: Bool) -> Bool { comptime if (false) { return a; } }\nmodule M() {\n  input x: Bool;\n  output y: Bool;\n  y := f(x);\n}\n",
            "M",
            "S010 5:8",
        ),
        (
            "module M() {\n  wire w: Bool;\n  reg r: Bool = false;\n  let mut h = w;\n  h = r;\n}\n",
            "M",
            "S010 5:3",
        ),
        (
            "module C(comptime n: Nat) {\n}\nmodule M() {\n  instance c = C(true);\n}\n",
            "M",
            "S010 4:3",
        ),
    ]);
}

/// `S011`: a static position gets a static value. The pre-check already rejects a port name
/// in a static position with `S005`, so these cases use a `let` binding of a port.
#[test]
fn the_stage_rule() {
    errors(&[
        (
            "module M() {\n  input x: Bool;\n  comptime if (x) { }\n}\n",
            "M",
            "S005 3:16",
        ),
        (
            "module M() {\n  input x: Bool;\n  let a = x;\n  comptime if (a) { }\n}\n",
            "M",
            "S011 4:3",
        ),
        (
            "module M() {\n  input x: Bool;\n  let a = x;\n  reg r: Bool = a;\n  r := a;\n}\n",
            "M",
            "S011 4:3",
        ),
        (
            "comptime fn f(b: Bool) -> Bool { return b; }\nmodule M() {\n  input x: Bool;\n  output y: Bool;\n  let a = x;\n  y := f(a);\n}\n",
            "M",
            "S011 6:8",
        ),
        (
            "module C(comptime n: Nat) {\n}\nmodule M() {\n  input x: Bool;\n  let a = x;\n  instance c = C(a);\n}\n",
            "M",
            "S011 6:3",
        ),
        (
            "module M() {\n  input x: UInt[8];\n  let a = x;\n  comptime for i in 0..a { }\n}\n",
            "M",
            "S011 4:3",
        ),
    ]);
}

/// `S012`: a value fits its type. `S013`: a negative shift count. `S014`: an assertion.
#[test]
fn the_fit_rule_the_faults_and_the_assertions() {
    errors(&[
        (
            "module M() {\n  reg r: UInt[4] = 16;\n  r := r;\n}\n",
            "M",
            "S012 2:3",
        ),
        (
            "module M() {\n  output y: UInt[8];\n  y := 300;\n}\n",
            "M",
            "S012 3:3",
        ),
        (
            "module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n  y := x << -1;\n}\n",
            "M",
            "S013 4:8",
        ),
        (
            "module M() {\n  static_assert(1 == 2, \"no\");\n}\n",
            "M",
            "S014 2:3",
        ),
    ]);
}

/// `S017`: the resource rule.
#[test]
fn the_resource_rule() {
    errors(&[
        (
            "module M() {\n  input x: Bool;\n  x := true;\n}\n",
            "M",
            "S017 3:3",
        ),
        (
            "module M() domains() {\n  reg r: Bool = false;\n}\n",
            "M",
            "S017 2:3",
        ),
        (
            "module C() {\n}\nmodule M() domains() {\n  instance c = C();\n}\n",
            "M",
            "S017 4:3",
        ),
        (
            "module C() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := a;\n}\nmodule M() domains() {\n  output y: Bool;\n  instance c = C();\n  c.a := false;\n  c.q := true;\n  y := c.q;\n}\n",
            "M",
            "S017 10:3",
        ),
        (
            "module C() domains() {\n  input a: Bool;\n}\nmodule M() domains() {\n  output y: Bool;\n  instance c = C();\n  c.a := false;\n  y := c.a;\n}\n",
            "M",
            "S017 8:3",
        ),
        (
            "module C() domains() {\n  input a: Bool;\n  input b: UInt[4];\n}\nmodule M() domains() {\n  instance c = C();\n  let p = c.b;\n  p := 3;\n  c.a := p;\n}\n",
            "M",
            "S017 9:3",
        ),
    ]);
}

/// `S018`: each resource has exactly one binding. The errors wait for the end of the body and
/// compete by position. A missing binding is at the declaration, and a missing child input
/// is at the `instance` statement.
#[test]
fn the_binding_rule() {
    errors(&[
        (
            "module M() {\n  output y: Bool;\n  y := true;\n  y := false;\n}\n",
            "M",
            "S018 4:3",
        ),
        ("module M() {\n  wire w: Bool;\n}\n", "M", "S018 2:3"),
        (
            "module M() {\n  output y: Bool;\n  wire w: Bool;\n  w := y;\n  w := y;\n}\n",
            "M",
            "S018 2:3",
        ),
        (
            "module C() domains() {\n  input a: Bool;\n}\nmodule M() domains() {\n  instance c = C();\n}\n",
            "M",
            "S018 5:3",
        ),
        (
            "module C() domains() {\n  input a: Bool;\n}\nmodule M() domains() {\n  instance c = C();\n  c.a := true;\n  c.a := false;\n}\n",
            "M",
            "S018 7:3",
        ),
        (
            "module M() {\n  output y: Bool;\n  comptime for i in 0..2 {\n    y := true;\n  }\n}\n",
            "M",
            "S018 4:5",
        ),
        (
            "module C() domains() {\n  input a: Bool;\n  input b: Bool;\n}\nmodule M() domains() {\n  comptime for i in 0..3 {\n    instance c = C();\n    c.a := true;\n    comptime if (i != 1) { c.b := false; }\n  }\n}\n",
            "M",
            "S018 7:5",
        ),
    ]);
}

/// An error in the body comes before an `S018` of the same body. A child finishes first.
#[test]
fn the_order_of_the_binding_rule() {
    errors(&[
        (
            "module M() {\n  wire w: Bool;\n  output y: UInt[8];\n  y := true;\n}\n",
            "M",
            "S010 4:3",
        ),
        (
            "module C() {\n  output q: Bool;\n}\nmodule M() {\n  output y: UInt[8];\n  instance c = C();\n  y := true;\n}\n",
            "M",
            "S018 2:3",
        ),
    ]);
}

/// The top selection: its arguments with their `instance` charge, its serialization of 50
/// bytes, and its emitted name of 12 bytes. Then its instantiation charges its parameter types
/// and its body.
#[test]
fn the_top_selection() {
    let src = "module Counter(comptime W: Nat, comptime E: Bool) {\n}";
    assert_eq!(cost(src, "Counter(8, true)"), "total 72\nCounter$8$1b 1\n");
    exact(src, "Counter(8, true)", 72);
    assert_eq!(cost_fuel(src, "Counter(8, true)", 5), "S015 1:45");
    assert_eq!(cost(src, "Counter(-1, true)"), "S012 1:1");
    assert_eq!(cost(src, "Counter(8, 1)"), "S010 1:1");
    assert_eq!(cost(src, "Counter(8)"), "S007 1:1");
    assert_eq!(cost_depth(src, "Counter(8, true)", 0), "S015 1:1");
    assert_eq!(cost(src, "Counter(8 + 1, true)"), "usage");
    assert_eq!(cost(src, "Nope(8)"), "usage");
    let neg = "module M(comptime s: Int) {\n}\n";
    exact(neg, "M(-12345678901234567890123)", 95);
    assert_eq!(cost(neg, "M(\"x\")"), "S010 1:1");
}

/// A chain of 300 acyclic constants in a parameter type. The top selection nests one level
/// more than the constants: the depth 301 passes, and 300 gives `S015`.
#[test]
fn the_top_selection_nests_one_level() {
    let mut src = "const C0: Nat = 0;\n".to_owned();
    for k in 1..300 {
        writeln!(src, "const C{k}: Nat = C{} + 1;", k - 1).unwrap();
    }
    src.push_str("module Top(comptime x: UInt[C299 + 1]) {\n}\n");
    assert_eq!(cost_depth(&src, "Top(5)", 301), "total 2189\nTop$5 1\n");
    assert_eq!(cost_depth(&src, "Top(5)", 300), "S015 2:17");
}

/// The emitted names of digest arguments, of a keyword module, and at the 64-byte limit.
#[test]
fn the_emitted_names_of_a_design() {
    let src = "module M(comptime s: Int, comptime t: Bool) {\n}\nmodule add() {\n}\n\
               module T() {\n  instance a = M(1 << 300, true);\n  instance b = M(-7, false);\n\
               \x20 instance c = add();\n}\n";
    let d = design(src, "T");
    let digest = sha16(&format!(
        "(instantiation root M ((int {}) (bool true)))",
        crate::int::Int::from_u64(1).shl(300)
    ));
    assert_eq!(
        d.order(),
        [
            format!("M$0h{digest}"),
            "M$7n$0b".to_owned(),
            "add$0k".to_owned(),
            "T".to_owned()
        ]
    );
    let long = |n: usize| format!("module {}() {{\n}}\n", "a".repeat(n));
    assert_eq!(order(&long(64), &"a".repeat(64)), ["a".repeat(64)]);
    assert!(order(&long(65), &"a".repeat(65))[0].starts_with(&format!("{}$0h", "a".repeat(65))));
}

/// A list holds no hardware value: `S011` at the element. A hardware arm cannot `push` or `pop`
/// a binding from before the arm: `S016` at the call. A function that the arm calls can change
/// its own list.
fn arm_lists(body: &str) -> String {
    format!(
        "fn g() -> UInt[8] {{ let mut ys = list(UInt[8]); push(ys, 1); return pop(ys); }}\n\
         module T() {{\n  input c: Bool;\n  output o: UInt[8];\n{body}}}\n"
    )
}

#[test]
fn a_list_holds_no_hardware_and_a_hardware_arm_cannot_change_one() {
    let at = |body: &str| cost(&arm_lists(body), "T");
    assert_eq!(
        at("  let mut xs = list(Bool);\n  push(xs, c);\n  o := 0;\n"),
        "S011 6:12"
    );
    assert_eq!(
        at("  let mut xs = list(Bool);\n  push(xs, true);\n  xs[0] = c;\n  o := 0;\n"),
        "S011 7:11"
    );
    assert_eq!(
        at(
            "  let mut xs = list(UInt[8]);\n  push(xs, 1);\n  o := if (c) { pop(xs) } else { 2 };\n"
        ),
        "S016 7:17"
    );
    assert_eq!(
        at(
            "  let mut xs = list(UInt[8]);\n  push(xs, 1);\n  o := if (c) { 3 } else { pop(xs) };\n"
        ),
        "S016 7:28"
    );
    assert_eq!(
        at("  let mut xs = list(UInt[8]);\n  o := if (c) { push(xs, 1) } else { 2 };\n"),
        "S016 6:17"
    );
    assert!(at("  o := if (c) { g() } else { 2 };\n").starts_with("total"));
}

/// A hardware write-back gives the caller root its next version after the result of the call.
/// The write-backs run in the order of the parameters. A write-back of a binding from before a
/// hardware arm is `S016` at the call. A function that the arm calls can pass its own binding.
fn muts(body: &str) -> String {
    format!(
        "fn inc(mut a: UInt[8]) -> () {{ a = a +% 1; return (); }}\n\
         fn swap(mut a: UInt[8], mut b: UInt[8]) -> UInt[8] {{ let t = a; a = b; b = t; return t; }}\n\
         fn own() -> UInt[8] {{ let mut z: UInt[8] = 1; inc(z); return z; }}\n\
         module M() {{\n  input c: Bool;\n  input x: UInt[8];\n  input w: UInt[8];\n\
         \x20 output y: UInt[8];\n{body}}}\n"
    )
}

#[test]
fn a_hardware_write_back_binds_the_next_version() {
    let at = |body: &str| names(&muts(body), "M", "M");
    assert_eq!(
        at("  let mut q = x;\n  inc(q);\n  y := q;\n"),
        ["q", "inc$0c$a", "inc$0c$a$1v", "q$1v"]
    );
    assert_eq!(
        at("  let mut q = x;\n  q.inc();\n  q.inc();\n  y := q;\n"),
        [
            "q",
            "inc$0c$a",
            "inc$0c$a$1v",
            "q$1v",
            "inc$1c$a",
            "inc$1c$a$1v",
            "q$2v"
        ]
    );
    assert_eq!(
        at("  let mut q = x;\n  let mut r = w;\n  let s = swap(q, r);\n  y := q +% r;\n"),
        [
            "q",
            "r",
            "swap$0c$a",
            "swap$0c$b",
            "swap$0c$t",
            "swap$0c$a$1v",
            "swap$0c$b$1v",
            "swap$0c$0ret",
            "q$1v",
            "r$1v",
            "s"
        ]
    );
    let cost_of = |body: &str| cost(&muts(body), "M");
    assert_eq!(
        cost_of("  let mut q = x;\n  let mut r = w;\n  y := if (c) { swap(q, r) } else { 0 };\n"),
        "S016 11:17"
    );
    assert!(cost_of("  y := if (c) { own() } else { 0 };\n").starts_with("total"));
    assert_eq!(
        cost_of("  let mut q: UInt[4] = 1;\n  inc(q);\n  y := 0;\n"),
        "S010 10:3"
    );
    assert!(cost_of("  let mut q = [UInt[8](1)];\n  inc(q[0]);\n  y := 0;\n").starts_with("total"));
}

/// The call sites count the call nodes in pre-order (decision F18). The constructor call
/// `T()(1)` has two call nodes at one position, so the later call of `add` has the site 2. A
/// receiver call has its own site at its receiver.
#[test]
fn the_call_sites_count_in_pre_order() {
    let src = "comptime fn T() -> Type { return UInt[8]; }\n\
        fn add(a: UInt[8], b: UInt[8]) -> UInt[8] { return a +% b; }\n\
        module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n\
        \x20 let a = T()(1);\n  let s = add(x, a);\n  y := s.add(a);\n}\n";
    assert_eq!(
        names(src, "M", "M"),
        ["add$2c$a", "add$2c$0ret", "s", "add$3c$a", "add$3c$0ret"]
    );
}

/// B10: a body with many calls numbers them in one pre-order pass of the resolver, so the last
/// call has the site of its rank, and the elaboration looks each site up by its node.
#[test]
fn many_call_sites_keep_their_pre_order_numbers() {
    let calls = 1500;
    let mut body = String::new();
    for k in 0..calls {
        writeln!(body, "  let a{k} = add(x, x);").unwrap();
    }
    let src = format!(
        "fn add(a: UInt[8], b: UInt[8]) -> UInt[8] {{ return a +% b; }}\n\
         module M() {{\n  input x: UInt[8];\n  output y: UInt[8];\n{body}  y := a0;\n}}\n"
    );
    let got = names(&src, "M", "M");
    assert_eq!(got.len(), 4 * calls);
    let last = format!("add${}c$0ret", calls - 1);
    assert!(got.contains(&last), "{last}");
}

/// B9: a list argument is measured, then its length is charged, and only then does its text
/// exist. A fuel that cannot pay the length writes no byte, and a fuel that can writes the whole
/// text once.
#[test]
fn a_list_argument_is_measured_and_charged_before_it_is_written() {
    use crate::counters::of;
    let make = |instance: &str| {
        format!(
            "module C(comptime xs: List[Int]) {{\n}}\n\
             module M() {{\n  let mut xs = list(Int);\n\
             \x20 comptime for i in 0..60 {{ xs.push(i); }}\n{instance}}}\n"
        )
    };
    let (with, without) = (make("  instance c = C(xs);\n"), make(""));
    let before = total(&without, "M");
    let items: Vec<String> = (0..60).map(|i| format!("(int {i})")).collect();
    let text = format!("(list int ({}))", items.join(" "));
    let total = total(&with, "M");
    let written = |fuel: u64| {
        let _ = cost_fuel(&with, "M", fuel);
        of(fuel).serialized
    };
    // The text is a length charge away from the fuel before the instance statement.
    let first = (0..=total).find(|&fuel| written(fuel) > 0).unwrap_or(total);
    assert!(first >= before + text.len() as u64, "{first} {before}");
    assert_eq!(written(first), text.len() as u64);
    assert_eq!(written(first - 1), 0);
}

/// The module `C` with the parameter type `ty`, and a top that instantiates it with `a` and `b`.
fn two_arguments(ty: &str, a: &str, b: &str) -> String {
    format!(
        "module C(comptime x: {ty}) {{\n}}\nmodule T() {{\n  instance a = C({a});\n  \
         instance b = C({b});\n}}\n"
    )
}

/// The `InstantiationId` holds the arguments after their typed use (section 7.1). `C(1)` and
/// `C(UInt[8](1))` give one instantiation, and so do `[1, 2]` and `[UInt[8](1), UInt[8](2)]`
/// at `[UInt[8]; 2]`. Two arguments of type `Nat` that differ give two.
#[test]
fn converted_arguments_give_one_instantiation() {
    let one = |ty: &str, a: &str, b: &str| order(&two_arguments(ty, a, b), "T").len();
    assert_eq!(one("UInt[8]", "1", "UInt[8](1)"), 2);
    assert_eq!(one("UInt[8]", "UInt[8](1)", "1"), 2);
    assert_eq!(one("[UInt[8]; 2]", "[1, 2]", "[UInt[8](1), UInt[8](2)]"), 2);
    assert_eq!(one("[UInt[8]; 2]", "[UInt[8](1), UInt[8](2)]", "[1, 2]"), 2);
    assert_eq!(one("[Nat; 2]", "[1, 2]", "[1, 2]"), 2);
    assert_eq!(one("UInt[8]", "1", "2"), 3);
}

/// `C(1)` that reaches `C(UInt[8](1))` reaches itself: `S019` at the inner statement.
#[test]
fn a_converted_instantiation_depends_on_itself() {
    let src = "module C(comptime x: UInt[8]) {\n  instance a = C(UInt[8](1));\n}\n";
    assert_eq!(cost(src, "C(1)"), "S019 2:3");
}

/// A failed typed use is at the statement, before `S017`.
#[test]
fn a_failed_typed_use_comes_before_s017() {
    let comb = |arg: &str| {
        format!(
            "module Clocked(comptime n: UInt[8]) {{\n}}\n\
             module Comb() domains() {{\n  instance u = Clocked({arg});\n}}\n"
        )
    };
    assert_eq!(cost(&comb("300"), "Comb"), "S012 4:3");
    assert_eq!(cost(&comb("3"), "Comb"), "S017 4:3");
    assert_eq!(cost(&comb("true"), "Comb"), "S010 4:3");
}

/// The typed use nests one level at each `instance` statement, also at a repeat of a done
/// instantiation. `Leaf()` in `Wrap` is a repeat at the depth 3.
#[test]
fn the_typed_use_of_a_repeat_nests_one_level() {
    let src = "module Leaf() {\n}\nmodule Wrap() {\n  instance c = Leaf();\n}\n\
               module Top() {\n  instance a = Leaf();\n  instance b = Wrap();\n}\n";
    assert!(cost_depth(src, "Top", 3).starts_with("total"));
    assert_eq!(cost_depth(src, "Top", 2), "S015 4:3");
}

/// The counts of the work of an elaboration with the fuel budget `fuel`.
fn counted(src: &str, fuel: u64) -> [u64; 6] {
    assert!(cost_fuel(src, "T", fuel).starts_with("total"));
    let c = crate::counters::of(fuel);
    [
        c.walked,
        c.typed,
        c.nodes,
        c.compared,
        c.table,
        c.serialized,
    ]
}

/// A repeat of an instantiation with a container argument does work linear in the size of the
/// argument: the typed use of `k` repeats walks and converts the `n` elements `k` times, and
/// nothing else grows with `n * k`. The argument is the constant `XS` of the type `ty`. The
/// typed use either keeps the value of the caller or converts it.
fn repeat_work(family: u64, ty: &str) {
    let source = |n: usize, k: usize| {
        let elems = vec!["1"; n].join(", ");
        let mut src = format!(
            "const XS: [{ty}; {n}] = [{elems}];\nmodule C(comptime xs: [UInt[8]; {n}]) {{\n}}\n\
             module T() {{\n"
        );
        for j in 0..k {
            writeln!(src, "  instance c{j} = C(XS);").unwrap();
        }
        src.push_str("}\n");
        src
    };
    let at = |n: usize, k: usize| {
        let fuel = 600_000_000 + family * 1_000_000 + (n as u64) * 1000 + k as u64;
        counted(&source(n, k), fuel)
    };
    // The work of ten more repeats, for three sizes.
    let growth = |n: usize| {
        let (low, high) = (at(n, 10), at(n, 20));
        let (more, top) = (at(n, 40), at(n, 80));
        let mut d = [0; 6];
        for m in 0..6 {
            // Each repeat costs the same: the growth is linear in `k`.
            assert_eq!(top[m] - more[m], 2 * (more[m] - high[m]), "count {m} in k");
            assert_eq!(more[m] - high[m], 2 * (high[m] - low[m]), "count {m} in k");
            d[m] = high[m] - low[m];
        }
        d
    };
    let (d1, d2, d4) = (growth(50), growth(100), growth(200));
    for m in 0..6 {
        // Each repeat costs a constant plus a multiple of `n`: linear in the size.
        assert_eq!(d4[m] - d2[m], 2 * (d2[m] - d1[m]), "count {m} in n");
    }
    assert!(
        d4.iter().sum::<u64>() > d1.iter().sum::<u64>(),
        "{d1:?} {d4:?}"
    );
}

#[test]
fn a_repeat_with_a_container_argument_does_linear_work() {
    repeat_work(1, "UInt[8]");
    repeat_work(2, "Int");
}
