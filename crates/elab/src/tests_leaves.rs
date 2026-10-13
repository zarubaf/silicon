// SPDX-License-Identifier: Apache-2.0
//! The cases of the lowering by leaf in `Silicon.Source.Test.Flatten` in Lean (section 7 of the
//! front-end spec): the names of the leaves, the charge of each leaf, the shared condition across
//! leaf statements and modules, the empty resources, the cycles of one leaf, and the chain of an
//! aggregate `==` that lowers in a loop.

use crate::counters;
use crate::hw::Op;
use crate::int::Int;
use crate::tests_flatten::{elab_used, sil, sil_fuel, text, total, valid};
use crate::types::{Ty, Types};
use crate::{Budget, elaborate};
use core_ir::text::print;
use parse::ast::BinOp;

/// Each leaf of an aggregate lowers to one core node with the leaf name of section 7.3. The
/// leaves of a port follow in packing order, so `p$xs$0e` comes before `p$b`. A register leaf
/// takes its reset constant from the leaf of its value. A named binding takes one version for
/// all its leaves. A call result names its leaves after `0ret`, and a static leaf lowers to a
/// constant.
#[test]
fn each_leaf_lowers_to_one_node_with_its_name() {
    let src = "struct S { xs: [UInt[8]; 2], b: Bool }\n\
        fn f(x: UInt[8]) -> (UInt[8], Bool) {\n  return (x, true);\n}\n\
        module M() {\n  input p: S;\n  input a: UInt[8];\n  output y: S;\n  \
        output z: (UInt[8], Bool);\n  reg r: [UInt[4]; 3] = [1, 2, 3];\n  r := r;\n  \
        let mut q = p;\n  q = S([a, a], p.b);\n  y := q;\n  z := f(a);\n}\n";
    assert_eq!(
        sil(src, "M"),
        text(&[
            "(design M",
            "  (module M",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (input a (bits 8))",
            "    (input p$xs$0e (bits 8))",
            "    (input p$xs$1e (bits 8))",
            "    (input p$b (bits 1))",
            "    (output y$xs$0e (bits 8))",
            "    (output y$xs$1e (bits 8))",
            "    (output y$b (bits 1))",
            "    (output z$0e (bits 8))",
            "    (output z$1e (bits 1))",
            "    (reg r$0e (bits 4) clock$0clk (reset sync clock$0rst (const 4 1)))",
            "    (reg r$1e (bits 4) clock$0clk (reset sync clock$0rst (const 4 2)))",
            "    (reg r$2e (bits 4) clock$0clk (reset sync clock$0rst (const 4 3)))",
            "    (let f$1c$0ret$0e (bits 8) f$1c$x)",
            "    (let f$1c$x (bits 8) a)",
            "    (let q$1v$b (bits 1) p$b)",
            "    (let q$1v$xs$0e (bits 8) a)",
            "    (let q$1v$xs$1e (bits 8) a)",
            "    (let q$b (bits 1) p$b)",
            "    (let q$xs$0e (bits 8) p$xs$0e)",
            "    (let q$xs$1e (bits 8) p$xs$1e)",
            "    (next r$0e r$0e)",
            "    (next r$1e r$1e)",
            "    (next r$2e r$2e)",
            "    (assign y$b q$1v$b)",
            "    (assign y$xs$0e q$1v$xs$0e)",
            "    (assign y$xs$1e q$1v$xs$1e)",
            "    (assign z$0e f$1c$0ret$0e)",
            "    (assign z$1e (const 1 1))))"
        ])
    );
}

/// A struct skips its empty fields. The other fields keep their names and their order.
#[test]
fn a_struct_skips_its_empty_fields() {
    let src = "struct E { a: Bool, z: (), e: [Bool; 0], c: UInt[2] }\n\
        module M() domains() {\n  input p: E;\n  output y: E;\n  y := p;\n}\n";
    assert_eq!(
        sil(src, "M"),
        text(&[
            "(design M",
            "  (module M",
            "    (input p$a (bits 1))",
            "    (input p$c (bits 2))",
            "    (output y$a (bits 1))",
            "    (output y$c (bits 2))",
            "    (assign y$a p$a)",
            "    (assign y$c p$c)))"
        ])
    );
}

/// Each leaf of a port charges 1 for its node, then the bytes of its name, before it exists. A
/// leaf of `x: [Bool; 3]` charges 3: its node, `x`, and `<k>e`. An empty port charges nothing.
/// The walk makes no list of the leaves, so a port with 2^40 leaves is `S015` at its
/// declaration.
#[test]
fn each_leaf_of_a_port_charges_before_it_exists() {
    let port = |n: &str| format!("module M() domains() {{\n  input x: [Bool; {n}];\n}}\n");
    let lowering = |src: &str| total(src, "M") - elab_used(src, "M");
    assert_eq!(lowering(&port("3")), lowering(&port("0")) + 9);
    assert_eq!(
        lowering(&port("0")),
        lowering("module M() domains() {\n}\n")
    );
    assert_eq!(sil_fuel(&port("1 << 40"), "M", 10000), "S015 2:3");
}

/// The condition of an aggregate `if` binds once to a temporary of the leaf statement that
/// lowers first. The second leaf statement refers to it, also in a child connection:
/// `u$a$0e$0t`. The table of shared conditions starts empty in each module, so `C` and `M` each
/// bind their own. A child output of an aggregate type lowers to one reference for each leaf.
#[test]
fn a_shared_condition_works_across_leaf_statements_and_modules() {
    let src = "module C() domains() {\n  input c: Bool;\n  input a: (Bool, Bool);\n  \
        output q: (Bool, Bool);\n  q := if (!c) { a } else { (c, c) };\n}\n\
        module M() domains() {\n  input c: Bool;\n  input d: Bool;\n  input a: (Bool, Bool);\n  \
        output y: (Bool, Bool);\n  output z: (Bool, Bool);\n  instance u = C();\n  \
        u.c := c;\n  u.a := if (c && d) { a } else { (d, d) };\n  \
        y := if (c || d) { a } else { u.q };\n  z := u.q;\n}\n";
    assert_eq!(
        sil(src, "M"),
        text(&[
            "(design M",
            "  (module C",
            "    (input a$0e (bits 1))",
            "    (input a$1e (bits 1))",
            "    (input c (bits 1))",
            "    (output q$0e (bits 1))",
            "    (output q$1e (bits 1))",
            "    (let q$0e$0t (bits 1) (xor c (const 1 1)))",
            "    (assign q$0e (mux q$0e$0t a$0e c))",
            "    (assign q$1e (mux q$0e$0t a$1e c)))",
            "  (module M",
            "    (input a$0e (bits 1))",
            "    (input a$1e (bits 1))",
            "    (input c (bits 1))",
            "    (input d (bits 1))",
            "    (output y$0e (bits 1))",
            "    (output y$1e (bits 1))",
            "    (output z$0e (bits 1))",
            "    (output z$1e (bits 1))",
            "    (inst u C (a$0e (mux u$a$0e$0t a$0e d)) (a$1e (mux u$a$0e$0t a$1e d)) (c c))",
            "    (let u$a$0e$0t (bits 1) (and c d))",
            "    (let y$0e$0t (bits 1) (or c d))",
            "    (assign y$0e (mux y$0e$0t a$0e u.q$0e))",
            "    (assign y$1e (mux y$0e$0t a$1e u.q$1e))",
            "    (assign z$0e u.q$0e)",
            "    (assign z$1e u.q$1e)))"
        ])
    );
}

/// An empty port, register, wire, and child port lower to no core node. Each still has its one
/// binding. A combinational child keeps its empty module.
#[test]
fn an_empty_resource_lowers_to_nothing() {
    let src = "module C() domains() {\n  input p: ();\n  output q: [Bool; 0];\n  q := [];\n}\n\
        module M() {\n  input e: [(); 4];\n  output o: [(); 4];\n  reg r: [Bool; 0] = [];\n  \
        wire w: ((), [UInt[8]; 0]);\n  instance u = C();\n  u.p := ();\n  o := e;\n  r := r;\n  \
        w := ((), []);\n}\n";
    assert_eq!(
        sil(src, "M"),
        text(&[
            "(design M",
            "  (module C)",
            "  (module M",
            "    (input clock$0clk clock)",
            "    (input clock$0rst (bits 1))",
            "    (inst u C)))"
        ])
    );
}

/// A cycle through one leaf is `S020` at the binding (section 7.5). A dependency between two
/// different leaves of one wire is not a cycle.
#[test]
fn a_cycle_through_one_leaf_is_s020() {
    let wire2 = |v: &str| {
        format!(
            "module M() domains() {{\n  input c: Bool;\n  wire w: (Bool, Bool);\n  \
             w := {v};\n  output y: Bool;\n  y := w.1;\n}}\n"
        )
    };
    assert_eq!(
        sil(&wire2("(c, w.0)"), "M"),
        text(&[
            "(design M",
            "  (module M",
            "    (input c (bits 1))",
            "    (output y (bits 1))",
            "    (let w$0e (bits 1) c)",
            "    (let w$1e (bits 1) w$0e)",
            "    (assign y w$1e)))"
        ])
    );
    assert_eq!(sil(&wire2("(w.0, c)"), "M"), "S020 4:3");
    assert_eq!(sil(&wire2("(w.1, w.0)"), "M"), "S020 4:3");
}

/// The chain of `==` on an aggregate is as long as its leaf count. Its left spine lowers in a
/// loop, so a long chain needs no deep recursion.
#[test]
fn a_long_equality_chain_lowers() {
    let eq = |n: usize| {
        format!(
            "module M() domains() {{\n  input a: [Bool; {n}];\n  input b: [Bool; {n}];\n  \
             output y: Bool;\n  y := a == b;\n}}\n"
        )
    };
    assert!(valid(&sil(&eq(2048), "M")));
}

/// The chain of 10^5 links of `and` binds one temporary for each 63 links by the height rule,
/// and the lowering needs a stack for the right operands only: the height that sizes its stack
/// does not grow with the chain.
#[test]
fn a_chain_of_100000_links_lowers_in_a_loop() {
    let src = "module T() domains() {\n  input a: Bool;\n  input b: Bool;\n  \
        output y: Bool;\n  output z: Bool;\n  y := a;\n  z := b;\n}\n";
    let file = crate::tests_elab::load(src).unwrap();
    let Ok(Ok(mut d)) = elaborate(&file, "T", parse::DEFAULT_SYNTAX_DEPTH, Budget::default())
    else {
        panic!("elaboration failed");
    };
    let top = d.top;
    let value = |d: &crate::Design, k: usize| match d.insts[top].body.binds[k].value {
        crate::agg::Agg::Hw(h) => h,
        _ => panic!("a scalar binding holds a hardware value"),
    };
    let (a, b) = (value(&d, 0), value(&d, 1));
    let pos = d.insts[top].body.binds[0].pos;
    let mut chain = a;
    for _ in 0..100_000 {
        chain = d
            .graph
            .mk(pos, Ty::Bool, Op::Bin(BinOp::And), vec![chain, b]);
    }
    d.insts[top].body.binds[0].value = crate::agg::Agg::Hw(chain);
    assert!(d.graph.height() < 8, "{}", d.graph.height());
    let lowered = d.lower().unwrap().unwrap();
    let out = print(&lowered.design);
    assert_eq!(out.matches("(let ").count(), 1587);
}

/// The walk over the leaves of a type visits a part with leaves, and nothing else: the parts
/// of a tuple come from the metadata, so a tuple of 1000 empty parts and a `Bool` takes two
/// steps, and an array of 2^40 empty parts takes one.
#[test]
fn the_walk_over_leaves_skips_the_empty_parts() {
    use crate::layout::{Env, Shapes, for_each_leaf};
    fn run(
        fuel: u64,
        tys: &mut Types,
        make: impl FnOnce(&mut Types) -> crate::types::TyId,
    ) -> (u64, u64) {
        let root = make(tys);
        counters::start(fuel);
        let mut shapes = Shapes::default();
        let mut seen = 0;
        let env = Env {
            tys,
            order: &[],
            texts: &[],
        };
        let done: Result<(), ()> = for_each_leaf(
            env,
            &mut shapes,
            root,
            (),
            |(), _, _, _, _| (),
            |_| (),
            |_, _, ()| {
                seen += 1;
                Ok(())
            },
        );
        assert!(done.is_ok());
        (seen, counters::of(fuel).leaves)
    }
    let big = |t: &mut Types| {
        let unit = t.mk(Ty::Unit);
        t.array(unit, Int::from_u64(1).shl(40))
    };
    let tuple = |t: &mut Types| {
        let unit = t.mk(Ty::Unit);
        let mut parts = vec![unit; 1000];
        parts.push(t.mk(Ty::Bool));
        t.tuple(parts)
    };
    let nested = |t: &mut Types| {
        let empty = big(t);
        let flag = t.mk(Ty::Bool);
        let pair = t.tuple(vec![empty, flag]);
        t.array(pair, Int::from_u64(100))
    };
    let mut tys = Types::default();
    assert_eq!(run(710_000_001, &mut tys, big), (0, 1));
    assert_eq!(run(710_000_002, &mut tys, tuple), (1, 2));
    assert_eq!(run(710_000_003, &mut tys, nested), (100, 201));
}

/// A selection of a hardware aggregate normalizes an empty part before the next index
/// evaluates, so the zero size of `p.1` is paid before `1 + 0` (Lean `Eval.eval` of `.index`).
/// With 74 units, the size of the empty array (11) is the unit that fails. With 75, it is paid
/// and the index fails on its first unit.
#[test]
fn an_empty_part_is_paid_before_the_next_index() {
    let src = "module M() domains() { input p: (Bool, [(); 10]); let w = p[1][1 + 0]; }\n";
    assert_eq!(sil_fuel(src, "M", 64), "S015 1:59");
    assert_eq!(sil_fuel(src, "M", 74), "S015 1:59");
    assert_eq!(sil_fuel(src, "M", 75), "S015 1:64");
}

/// The same order holds for a chain of selections and indices on a tuple with empty subparts.
#[test]
fn an_empty_part_in_a_chain_is_paid_before_each_index() {
    let src =
        "module M() domains() { input p: (Bool, [[(); 2]; 2]); let w = p.1[1 + 0][1 + 0]; }\n";
    assert_eq!(sil_fuel(src, "M", 36), "S015 1:41");
    assert_eq!(sil_fuel(src, "M", 42), "S015 1:50");
    assert_eq!(sil_fuel(src, "M", 44), "S015 1:40");
}

/// A place pays the zero size of an empty part before the next step charges (Lean `placeAt`).
/// The size of the array `[(); 10]` is 11. With 75 units it fails at that unit, and with 87
/// and 94 the later steps and the index charge in turn.
#[test]
fn a_place_pays_an_empty_part_before_the_next_step() {
    let src =
        "module M() domains() { input p: (Bool, [(); 10]); let mut v = p; v.1[1 + 0] = (); }\n";
    assert_eq!(sil_fuel(src, "M", 75), "S015 1:66");
    assert_eq!(sil_fuel(src, "M", 87), "S015 1:70");
    assert_eq!(sil_fuel(src, "M", 94), "S015 1:79");
}
