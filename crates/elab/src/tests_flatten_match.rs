// SPDX-License-Identifier: Apache-2.0
//! The lowering of a hardware `match` in `Silicon.Source.Test.Flatten` and `Test.Elab` in Lean
//! (design section 7.4): the AND-OR form of each result leaf, the marks that bind in the first
//! leaf statement, the order of the temporaries, and the two chains that build in a loop.

use crate::Budget;
use crate::counters::of;
use crate::tests_flatten::{elab_used, enum_lets, op_module, total};
use std::fmt::Write as _;

/// The `let` lines of the module `M` with the statements `body`.
fn op_lets(body: &str) -> Vec<String> {
    enum_lets(&op_module(body))
}

/// The units of the lowering of the module `M` with the statements `body`.
fn op_units(body: &str) -> u64 {
    total(&op_module(body), "M") - elab_used(&op_module(body), "M")
}

/// A hardware `match` is a parallel AND-OR mux (section 7.4). Each result leaf of width `w` is
/// `(or (and (replicate s_0 w) v_0) ...)`. Over `Bool`, the selects are `icmp eq` nodes of one
/// use, so they stay inline. The row charges 10 more than the `mux` of an `if`. The `or`,
/// `replicate`, and `and` nodes charge 5, and the two selects 4 each. The `mux` charges 1 and the
/// condition 2.
#[test]
fn a_match_is_a_parallel_and_or_mux() {
    assert_eq!(
        op_lets("  let a = match (c) { true => x, false => x +% 1 };\n"),
        [
            "    (let a (bits 8) (or (and (replicate (icmp eq c (const 1 1)) 8) x) \
             (and (replicate (icmp eq c (const 1 0)) 8) (add x (const 8 1)))))"
        ]
    );
    assert_eq!(
        op_units("  let a = match (c) { true => x, false => x +% 1 };\n"),
        op_units("  let a = if (c) { x } else { x +% 1 };\n") + 10
    );
}

/// An integer scrutinee with `_`. Each select has two uses, so it binds to a temporary of the
/// first statement that lowers it, in arm order. The select of `_` is
/// `(xor (or s_0 s_1) (const 1 1))`. A static value of an arm is a constant.
#[test]
fn an_integer_scrutinee_binds_its_selects_in_arm_order() {
    assert_eq!(
        op_lets("  let a = match (x) { 0 => y, 1 => y +% 1, _ => 3 };\n"),
        [
            "    (let a (bits 4) (or (or (and (replicate a$0t 4) y) \
             (and (replicate a$1t 4) (add y (const 4 1)))) \
             (and (replicate (xor (or a$0t a$1t) (const 1 1)) 4) (const 4 3))))",
            "    (let a$0t (bits 1) (icmp eq x (const 8 0)))",
            "    (let a$1t (bits 1) (icmp eq x (const 8 1)))"
        ]
    );
}

/// An enum scrutinee with binders. The selects compare the `tag` leaf, and each binder is an
/// `extract` of the `payload` leaf, bound as a `let`.
#[test]
fn an_enum_scrutinee_compares_the_tag_and_extracts_the_payload() {
    assert_eq!(
        op_lets(
            "  let a = match (e) { Op::Load(v) => v, \
             Op::Pair(b, z) => resize(UInt[8], z), _ => 0 };\n"
        ),
        [
            "    (let a (bits 8) (or (or (and (replicate a$0t 8) v) \
             (and (replicate a$1t 8) (concat (const 4 0) z))) \
             (and (replicate (xor (or a$0t a$1t) (const 1 1)) 8) (const 8 0))))",
            "    (let a$0t (bits 1) (icmp eq e$tag (const 2 1)))",
            "    (let a$1t (bits 1) (icmp eq e$tag (const 2 2)))",
            "    (let b (bits 1) (extract e$payload 0 1))",
            "    (let v (bits 8) (extract e$payload 0 8))",
            "    (let z (bits 4) (extract e$payload 1 4))"
        ]
    );
}

/// A result of two leaves. The marks bind in the first leaf statement in the order of section
/// 7.4. The select `s_0` binds first, then the select of `_`, which refers to it. The second leaf
/// statement refers to both.
#[test]
fn the_marks_bind_in_the_first_leaf_statement() {
    assert_eq!(
        op_lets("  let a = match (c) { true => (x, y), _ => (x +% 1, y) };\n"),
        [
            "    (let a$0e (bits 8) (or (and (replicate a$0e$0t 8) x) \
             (and (replicate a$0e$1t 8) (add x (const 8 1)))))",
            "    (let a$0e$0t (bits 1) (icmp eq c (const 1 1)))",
            "    (let a$0e$1t (bits 1) (xor a$0e$0t (const 1 1)))",
            "    (let a$1e (bits 4) (or (and (replicate a$0e$0t 4) y) \
             (and (replicate a$0e$1t 4) y)))"
        ]
    );
}

/// `k` nested `match (match (c) { .. }) { true => c, _ => x == 0 }` add one temporary and 24 units
/// for each level, so the output and the charge stay linear.
#[test]
fn nested_matches_add_one_temporary_and_a_constant_for_each_level() {
    let nest = |k: usize| {
        let mut e = "c".to_owned();
        for _ in 0..k {
            e = format!("match ({e}) {{ true => c, _ => x == 0 }}");
        }
        format!("  let a = {e};\n")
    };
    for k in 1..=20 {
        assert_eq!(op_lets(&nest(k)).len(), k + 1, "{k}");
    }
    for k in 1..=20 {
        assert_eq!(op_units(&nest(k + 1)), op_units(&nest(k)) + 24, "{k}");
    }
}

/// The `or` chain of `terms`, built from the left.
fn ors(terms: &[String]) -> String {
    let mut chain = terms[0].clone();
    for term in &terms[1..] {
        chain = format!("(or {chain} {term})");
    }
    chain
}

/// The term `(and (replicate a$<i>t 4) y)` of the arm `i`.
fn term(i: usize) -> String {
    format!("(and (replicate a${i}t 4) y)")
}

fn temp(i: usize) -> String {
    format!("a${i}t")
}

/// A `match` of 70 arms. Both chains build in a loop. The `or` chain of the select of `_` binds
/// `a$69t` when its height reaches 64, after `s_63`. The chain of the result binds `a$70t` after
/// the arm 61, where an `and` term has the height 3.
#[test]
fn a_match_of_70_arms_binds_both_chains_at_the_height_64() {
    let mut arms = String::new();
    for i in 0..69 {
        write!(arms, "{i} => y, ").unwrap();
    }
    let lets = op_lets(&format!("  let a = match (x) {{ {arms}_ => 0 }};\n"));
    assert_eq!(lets.len(), 72);
    let mut chain: Vec<String> = vec![temp(70)];
    chain.extend((62..69).map(term));
    let mut wild: Vec<String> = vec![temp(69)];
    wild.extend((64..69).map(temp));
    chain.push(format!(
        "(and (replicate (xor {} (const 1 1)) 4) (const 4 0))",
        ors(&wild)
    ));
    assert!(lets.contains(&format!("    (let a (bits 4) {})", ors(&chain))));
    let selects: Vec<String> = (0..64).map(temp).collect();
    assert!(lets.contains(&format!("    (let a$69t (bits 1) {})", ors(&selects))));
    let terms: Vec<String> = (0..62).map(term).collect();
    assert!(lets.contains(&format!("    (let a$70t (bits 4) {})", ors(&terms))));
}

/// The binding order in one arm. In 65 arms, the value of arm 62 has the height 63, so its `and`
/// node binds `a$65t` before the chain of arms 0 to 61 binds `a$66t`. The `or` chain of the 64
/// selects before `_` reaches the height 64 at its end, so it binds `a$64t` before the `xor`.
#[test]
fn the_and_node_of_an_arm_binds_before_the_chain_that_it_joins() {
    let mut adds = "y".to_owned();
    for _ in 0..62 {
        adds.push_str(" +% 1");
    }
    let mut arms = String::new();
    for i in 0..64 {
        if i == 62 {
            write!(arms, "62 => {adds}, ").unwrap();
        } else {
            write!(arms, "{i} => y, ").unwrap();
        }
    }
    let lets = op_lets(&format!("  let a = match (x) {{ {arms}_ => 0 }};\n"));
    assert!(
        lets.contains(
            &"    (let a (bits 4) (or (or (or a$66t a$65t) (and (replicate a$63t 4) y)) \
         (and (replicate (xor a$64t (const 1 1)) 4) (const 4 0))))"
                .to_owned()
        )
    );
    let selects: Vec<String> = (0..64).map(temp).collect();
    assert!(lets.contains(&format!("    (let a$64t (bits 1) {})", ors(&selects))));
    assert!(
        lets.iter()
            .any(|l| l.starts_with("    (let a$65t (bits 4) (and (replicate a$62t 4) (add"))
    );
    let terms: Vec<String> = (0..62).map(term).collect();
    assert!(lets.contains(&format!("    (let a$66t (bits 4) {})", ors(&terms))));
}

/// W8. The lowering of a `match` with `m` arms and `L` leaves builds each chain in a loop: one
/// step for each arm of each leaf, and one for each select of `_`. No recursion follows `m`.
#[test]
fn w8_the_lowering_of_a_wide_match_is_a_loop() {
    let steps = |bits: u32, key: u64| {
        let m = 1u64 << bits;
        let mut arms = String::new();
        for i in 0..m {
            write!(arms, "{i} => a, ").unwrap();
        }
        let src = format!(
            "module M() {{\n  input s: UInt[{bits}];\n  input a: [UInt[8]; 64];\n  \
             output y: [UInt[8]; 64];\n  y := match (s) {{ {arms} }};\n}}\n"
        );
        let fuel = 980_000_000 + key;
        let budget = Budget {
            fuel,
            ..Budget::default()
        };
        let file = crate::tests_elab::load(&src).unwrap();
        let Ok(Ok(design)) = crate::elaborate(&file, "M", parse::DEFAULT_SYNTAX_DEPTH, budget)
        else {
            panic!("the elaboration must succeed")
        };
        assert!(design.lower().unwrap().is_ok());
        of(fuel).chained
    };
    // The select of each arm lowers once, in the first leaf statement.
    assert_eq!(steps(10, 1), 1024 * 64);
    assert_eq!(steps(11, 2), 2048 * 64);
    assert_eq!(steps(12, 3), 4096 * 64);
}
