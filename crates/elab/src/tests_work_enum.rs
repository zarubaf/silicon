// SPDX-License-Identifier: Apache-2.0
//! The work of the enum constructors, the packs, `reinterpret`, the lowering of a pack, and the
//! layout of enums, as the work bound of design section 5.5 states it for the Rust front end.
//! A static pack writes each leaf into one bit buffer, and a hardware pack walks the leaves of
//! its parts once with its own stack, so the work follows the charged copies and never the
//! product of the leaves and the width. The tests count the steps of the walks and not the
//! time.

use crate::counters::{Counts, of};
use crate::tests_elab::load;
use crate::{Abort, Budget, elaborate};
use std::fmt::Write;

/// The counts of the elaboration with the lowering of the module `M` of `src`, and the units
/// that the whole run charged. The key makes the fuel budget of the run unique, so it keys the
/// counters.
struct Run {
    counts: Counts,
    units: u64,
}

fn run(key: u64, depth: u64, src: &str) -> Run {
    let fuel = 950_000_000 + key;
    let file = load(src).unwrap();
    let budget = Budget { fuel, depth };
    let design = match elaborate(&file, "M", parse::DEFAULT_SYNTAX_DEPTH, budget) {
        Ok(Ok(design)) => design,
        Ok(Err(e)) => panic!("{} {}:{} {}", e.code, e.pos.line, e.pos.col, e.message),
        Err(Abort::Usage(m)) => panic!("{m}"),
        Err(Abort::Stack(e)) => panic!("{e}"),
    };
    let lowered = design.lower().unwrap().ok().unwrap();
    Run {
        counts: of(fuel),
        units: lowered.used(),
    }
}

/// W5. A static constructor with `n` `Bool` leaves writes each leaf into one bit buffer: one
/// step for each leaf, and no step reads an earlier leaf. The work is not the leaves times the
/// words of the payload.
#[test]
fn w5_a_static_constructor_writes_one_step_for_each_leaf() {
    let steps = |n: u64, key: u64| {
        let src = format!(
            "enum E: UInt[1] {{ A([Bool; {n}]) = 0 }}\n\
             module M() {{\n  output y: E;\n  y := E::A([Bool; {n}]());\n}}\n"
        );
        run(key, 1000, &src).counts.packed
    };
    assert_eq!(steps(1024, 1), 1024);
    assert_eq!(steps(2048, 2), 2048);
    assert_eq!(steps(65536, 3), 65536);
}

/// W6. A hardware constructor from a register with `n` leaves visits the root and each leaf once.
/// A payload that nests 3000 deep takes the same walk, and the walk keeps its own stack.
#[test]
fn w6_a_hardware_constructor_walks_each_part_once() {
    let steps = |n: u64, key: u64| {
        let src = format!(
            "enum E: UInt[1] {{ A([UInt[8]; {n}]) = 0 }}\n\
             module M() {{\n  input x: [UInt[8]; {n}];\n  output y: E;\n  \
             reg r: [UInt[8]; {n}] = [UInt[8]; {n}]();\n  r := x;\n  y := E::A(r);\n}}\n"
        );
        run(key, 1000, &src).counts.packed
    };
    assert_eq!((steps(256, 10), steps(512, 11)), (257, 513));
    let depth = 3000;
    let mut src = "type T0 = UInt[8];\n".to_owned();
    for k in 1..=depth {
        writeln!(src, "type T{k} = (T{},);", k - 1).unwrap();
    }
    write!(
        src,
        "enum E: UInt[1] {{ A(T{depth}) = 0 }}\n\
         module M() {{\n  input x: T{depth};\n  output y: E;\n  y := E::A(x);\n}}\n"
    )
    .unwrap();
    assert_eq!(run(12, 10_000, &src).counts.packed, depth + 1);
}

/// W7. `k` constructors of one local copy it `k` times, and each copy is paid: the copied
/// size is `k` times the size of the local.
#[test]
fn w7_k_constructors_of_one_local_copy_it_k_times() {
    let copies = |n: u64, k: u64, key: u64| {
        let mut body = String::new();
        for i in 0..k {
            writeln!(body, "  let e{i} = E::A(l);").unwrap();
        }
        let src = format!(
            "enum E: UInt[1] {{ A([UInt[8]; {n}]) = 0 }}\n\
             module M() {{\n  output y: E;\n  let l = [UInt[8]; {n}]();\n{body}  y := e0;\n}}\n"
        );
        run(key, 1000, &src).counts.copies
    };
    let (four, eight, sixteen) = (copies(64, 4, 20), copies(64, 8, 21), copies(64, 16, 22));
    assert_eq!(sixteen - eight, 2 * (eight - four));
    let (wide, wider) = (copies(128, 4, 23), copies(256, 4, 24));
    assert_eq!(wider - wide, 2 * (wide - four));
}

/// W8. `reinterpret` both ways, nested `k` deep, charges a constant for each level: the mark of
/// the shared operand pays for its operand once, and a value that holds it counts a core name.
#[test]
fn w8_nested_reinterpret_is_linear() {
    let units = |k: u64, key: u64| {
        let mut e = "x".to_owned();
        for _ in 0..k {
            e = format!("reinterpret(UInt[10], reinterpret(Op, {e}))");
        }
        let src = format!(
            "enum Op: UInt[2] {{ Add = 0, Load(UInt[8]) = 1 }}\n\
             module M() {{\n  input x: UInt[10];\n  output y: UInt[10];\n  y := {e};\n}}\n"
        );
        let r = run(key, 1000, &src);
        (r.units, r.counts.paths)
    };
    let step = |k: u64, key: u64| {
        let (a, b) = (units(k + 1, key), units(k, key + 100));
        (a.0 - b.0, a.1 - b.1)
    };
    let first = step(1, 30);
    for k in 2..24 {
        assert_eq!(step(k, 100 + 2 * k), first, "{k}");
    }
}

/// W9. The lowering of a pack of `n` leaves builds its `concat` chain in a loop: one step for each
/// leaf after the first, and the chain binds a temporary at the height 64.
#[test]
fn w9_the_lowering_of_a_wide_pack_is_a_loop() {
    let chained = |n: u64, key: u64| {
        let src = format!(
            "enum E: UInt[1] {{ A([UInt[1]; {n}]) = 0 }}\n\
             module M() {{\n  input x: [UInt[1]; {n}];\n  output y: E;\n  y := E::A(x);\n}}\n"
        );
        run(key, 1000, &src).counts.chained
    };
    assert_eq!(chained(1024, 50), 1023);
    assert_eq!(chained(65536, 51), 65535);
}

/// W10. The layout of `n` enums visits two leaves for each enum, and no more.
#[test]
fn w10_the_layout_of_enums_is_per_leaf() {
    let leaves = |n: u64, key: u64| {
        let src = format!(
            "enum Op: UInt[2] {{ Add = 0, Load(UInt[8]) = 1 }}\n\
             module M() {{\n  input a: [Op; {n}];\n  output y: [Op; {n}];\n  y := a;\n}}\n"
        );
        run(key, 1000, &src).counts.leaves
    };
    let (a, b, c) = (leaves(1024, 60), leaves(2048, 61), leaves(4096, 62));
    assert_eq!(c - b, 2 * (b - a));
    assert_eq!(c, 9 * 4096 + 3);
    assert_eq!(leaves(65536, 63), 9 * 65536 + 3);
}
