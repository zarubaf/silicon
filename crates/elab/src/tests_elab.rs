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
fn load(src: &str) -> Result<resolve::Resolved, String> {
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

fn cost(src: &str, top: &str) -> String {
    let b = Budget::default();
    cost_with(src, top, b.fuel, b.depth, sha16)
}

fn cost_fuel(src: &str, top: &str, fuel: u64) -> String {
    cost_with(src, top, fuel, Budget::default().depth, sha16)
}

fn cost_depth(src: &str, top: &str, depth: u64) -> String {
    cost_with(src, top, Budget::default().fuel, depth, sha16)
}

fn design(src: &str, top: &str) -> Design {
    let b = Budget::default();
    run(src, top, b.fuel, b.depth, sha16).unwrap()
}

/// The total fuel of `cost`.
fn total(src: &str, top: &str) -> u64 {
    design(src, top).used()
}

/// The cost is `units`. This fuel passes, and one unit less gives `S015`.
fn exact(src: &str, top: &str, units: u64) {
    assert_eq!(total(src, top), units);
    assert!(cost_fuel(src, top, units).starts_with("total"));
    assert!(cost_fuel(src, top, units - 1).starts_with("S015"));
}

/// The emitted names in the order in which the instantiations finish.
fn order(src: &str, top: &str) -> Vec<String> {
    design(src, top).order()
}

/// The core names of the named bindings, the registers, the wires, and the children of `m`.
fn names(src: &str, top: &str, m: &str) -> Vec<String> {
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
    assert_eq!(cost(COUNTER, "Main"), "total 168\nCounter$4 67\nMain 69\n");
    exact(COUNTER, "Main", 168);
    assert_eq!(cost(COUNTER, "Counter(8)"), "total 118\nCounter$8 67\n");
    assert_eq!(order(COUNTER, "Main"), ["Counter$4", "Main"]);
}

const LEAF: &str = "module C(comptime n: Nat) {\n}\n";

/// A child finishes before its parent. A repeated `InstantiationId` elaborates once. Its
/// `instance` statement charges 1, and its argument charges 2 for the node and the literal,
/// and 1 for the recursive size. Its serialization charges 1 for the decimal form and 32 for
/// its bytes. These are 37 units.
#[test]
fn the_table_of_instantiations() {
    let one = format!("{LEAF}module T() {{\n  instance a = C(5);\n}}\n");
    let two = format!("{LEAF}module T() {{\n  instance a = C(5);\n  instance b = C(5);\n}}\n");
    let other = format!("{LEAF}module T() {{\n  instance a = C(5);\n  instance b = C(6);\n}}\n");
    assert_eq!(total(&two, "T"), total(&one, "T") + 37);
    assert_eq!(order(&two, "T"), ["C$5", "T"]);
    assert_eq!(order(&other, "T"), ["C$5", "C$6", "T"]);
    assert_eq!(cost(&other, "T"), "total 111\nC$5 2\nC$6 2\nT 81\n");
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
    let src = "module M(comptime x: UInt[8]) {\n}\n\
               module T() {\n  instance a = M(UInt[8](1));\n  instance b = M(UInt[8](2));\n}\n";
    assert!(cost(src, "T").starts_with("total"));
    let b = Budget::default();
    assert_eq!(cost_with(src, "T", b.fuel, b.depth, collide), "S019 5:3");
    assert_eq!(
        order(src, "T"),
        [
            format!("M$0h{}", sha16("(instantiation root M ((uint 8 1)))")),
            format!("M$0h{}", sha16("(instantiation root M ((uint 8 2)))")),
            "T".to_owned()
        ]
    );
}

/// An emitted name is taken when its instantiation starts. A descendant that shares the
/// emitted name of an active ancestor is thus `S019` at its own `instance` statement.
#[test]
fn a_name_is_taken_at_the_start() {
    let src = "module M(comptime x: UInt[8]) {\n\
               \x20 comptime if (x == UInt[8](1)) { instance a = M(UInt[8](0)); }\n}\n\
               module T() {\n  instance b = M(UInt[8](1));\n}\n";
    assert!(cost(src, "T").starts_with("total"));
    let b = Budget::default();
    assert_eq!(cost_with(src, "T", b.fuel, b.depth, collide), "S019 2:35");
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
    assert!(lines.starts_with("total 175878\nM$0$0 16\nM$0$1 16\nM$0$10 16\n"));
}

/// The shared hierarchy of section 11.3 with `d = 30`: 31 instantiations, linear in `d`.
#[test]
fn the_shared_hierarchy() {
    assert_eq!(order(SHARED, "M(30)").len(), 31);
    exact(SHARED, "M(30)", 3296);
    assert_eq!(
        total(SHARED, "M(30)") - total(SHARED, "M(29)"),
        total(SHARED, "M(20)") - total(SHARED, "M(19)")
    );
    assert_eq!(total(SHARED, "M(30)") - total(SHARED, "M(29)"), 109);
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
    assert_eq!(total(&deep_first, "Top"), 439);
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
/// count, the conversions, and a child input through a handle alias.
#[test]
fn the_hardware_operators() {
    let src = "module C() domains() {\n  input a: Bool;\n  output q: Bool;\n  q := !a;\n}
module M() {
  input x: UInt[8];\n  input s: SInt[8];\n  input c: UInt[3];\n  input e: Bool;
  output y: UInt[8];\n  output z: SInt[16];\n  output b: Bool;
  let w = (x +% 1) -% (x *% 3) & ~x | (x ^ 255);
  let v = -s >> c;
  let k = if (e) { 1 } else { x << 2 };
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
    exact(src, "M", 268);
    assert_eq!(cost(src, "M"), "total 268\nC 10\nM 232\n");
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
    assert_eq!(cost(src, "Counter(8, true)"), "total 72\nCounter$8$1b 3\n");
    exact(src, "Counter(8, true)", 72);
    assert_eq!(cost_fuel(src, "Counter(8, true)", 5), "S015 1:1");
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
    assert_eq!(cost_depth(&src, "Top(5)", 301), "total 2156\nTop$5 2113\n");
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
