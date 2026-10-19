// SPDX-License-Identifier: Apache-2.0
//! The structural contexts of section 9.4, as in `Silicon.Source.Test.Elab` in Lean. Each sets a
//! guard of the kind structural at the current depth. A `push`, a `pop`, or a `mut` write-back
//! of a binding from before the context is `S016` at the call. A helper that the context calls
//! can change its own locals. The values are those of the Lean binary, and each `S016` text is
//! pinned in full.

use crate::tests_elab::{elab_only, load};
use crate::{Budget, elaborate_with};

const PRE: &str = "struct P(comptime W: Nat) { a: UInt[W] }\n\
    fn f(mut n: Int) -> Int { n = n + 1; return n; }\n\
    fn h() -> Nat { let mut ys = list(Nat); push(ys, 4); return pop(ys); }\n";

fn module(body: &str) -> String {
    format!(
        "{PRE}module M() {{\n  input c: Bool;\n  input a: UInt[2];\n  input d: UInt[8];\n  \
         output o: UInt[8];\n  let mut xs = list(Nat);\n  push(xs, 2);\n  push(xs, 3);\n  \
         let mut n = 3;\n{body}  o := 0;\n}}\n"
    )
}

/// The result of `body` in the module `M`, with the functions `fs` before it.
fn run(body: &str, fs: &str) -> String {
    let b = Budget::default();
    elab_only(&format!("{fs}{}", module(body)), "M", b.fuel, b.depth)
}

/// The message of the first error of `src` with the top `M`, or `ok`.
fn said(src: &str) -> String {
    let file = load(src).unwrap();
    match elaborate_with(
        &file,
        "M",
        parse::DEFAULT_SYNTAX_DEPTH,
        Budget::default(),
        crate::names::sha16,
    ) {
        Ok(Ok(_)) => "ok".to_owned(),
        Ok(Err(e)) => e.message,
        Err(_) => "usage".to_owned(),
    }
}

/// A module with a memory `q`, a port call, an alias `k`, and `rest`.
fn with_memory(write: bool, rest: &str) -> String {
    let port = if write {
        "  write_port(q, a, d, c);\n"
    } else {
        "  let r = read_port(q, a, c);\n"
    };
    module(&format!(
        "  mem q: [UInt[8]; 4];\n{port}  let k = q;\n{rest}"
    ))
}

#[test]
fn a_mutation_in_a_type_annotation_is_s016() {
    let at = |body: &str| run(body, "");
    assert_eq!(
        at("  let x: [Bool; pop(xs)] = [false, false, false];\n"),
        "S016 13:17"
    );
    assert_eq!(at("  let x: UInt[f(n)] = 0;\n"), "S016 13:15");
    assert_eq!(at("  wire w: UInt[pop(xs)];\n  w := 0;\n"), "S016 13:16");
    assert_eq!(at("  reg r: UInt[pop(xs)] = 0;\n  r := r;\n"), "S016 13:15");
    assert_eq!(
        run(
            "  let z = g(xs, 1);\n",
            "fn g(mut ys: List[Nat], b: UInt[pop(ys)]) -> Nat { return 1; }\n"
        ),
        "S016 1:33"
    );
    assert_eq!(
        run(
            "  let z = g(xs);\n",
            "fn g(mut ys: List[Nat]) -> UInt[pop(ys)] { return 1; }\n"
        ),
        "S016 1:33"
    );
}

#[test]
fn a_mutation_in_a_form_that_makes_a_type_is_s016() {
    let at = |body: &str| run(body, "");
    assert_eq!(at("  let x = UInt[pop(xs)](0);\n"), "S016 13:16");
    assert_eq!(at("  let x = UInt[xs.pop()](0);\n"), "S016 13:16");
    assert_eq!(at("  let t = [Bool; push(xs, 4)];\n"), "S016 13:18");
    assert_eq!(at("  let t = fn (UInt[pop(xs)]) -> Bool;\n"), "S016 13:20");
    assert_eq!(at("  type T = UInt[pop(xs)];\n"), "S016 13:17");
}

#[test]
fn a_mutation_in_a_struct_use_or_a_memory_is_s016() {
    let at = |body: &str| run(body, "");
    assert_eq!(at("  let t = P[pop(xs)];\n"), "S016 13:13");
    assert_eq!(at("  let x: P[f(n)] = P[4](1);\n"), "S016 13:12");
    assert_eq!(at("  mem q: [UInt[pop(xs)]; 4];\n"), "S016 13:16");
    assert_eq!(at("  mem q: [UInt[8]; pop(xs)];\n"), "S016 13:20");
    assert_eq!(at("  mem q: [UInt[8]; f(n)];\n"), "S016 13:20");
}

#[test]
fn a_helper_changes_its_own_locals_and_other_forms_are_not_structural() {
    let at = |body: &str| run(body, "");
    assert_eq!(at("  let x: UInt[h()] = 0;\n"), "ok 106");
    assert_eq!(at("  let x = UInt[8](pop(xs));\n"), "ok 90");
    assert_eq!(at("  comptime if (pop(xs) == 3) {}\n"), "ok 86");
    assert_eq!(at("  comptime for i in 0..pop(xs) {}\n"), "ok 90");
    assert_eq!(
        run(
            "  let z = cf();\n  let w: UInt[cf()] = 0;\n",
            "comptime fn cf() -> Nat { let mut ys = list(Nat); push(ys, 4); return pop(ys); }\n"
        ),
        "ok 128"
    );
}

#[test]
fn a_constant_at_its_first_use_in_an_arm_runs_its_helper() {
    let k = "const K: Nat = h();\n";
    assert_eq!(
        run("  let z = if (c) { UInt[8](K) } else { 0 };\n", k),
        "ok 120"
    );
    assert_eq!(
        run("  let z = if (c) { UInt[K](1) } else { 0 };\n", k),
        "ok 120"
    );
}

#[test]
fn the_innermost_guard_wins() {
    assert_eq!(
        run("  let z = if (c) { pop(xs) } else { 0 };\n", ""),
        "S016 13:20"
    );
    assert_eq!(
        said(&module(
            "  let z = if (c) { UInt[pop(xs)](0) } else { 0 };\n"
        )),
        "a type or a constant cannot change `xs`; change `xs` before it, keep the result in a \
         `let`, and use that name here"
    );
}

#[test]
fn the_other_effects_in_a_type_expression() {
    let at = |body: &str, fs: &str| run(body, fs);
    let ty = "  let x: UInt[g()] = 0;\n";
    assert_eq!(
        at(ty, "fn g() -> Nat { reg r: UInt[8] = 0; return 1; }\n"),
        "S016 1:17"
    );
    assert_eq!(
        at(ty, "fn g() -> Nat { mem q: [UInt[8]; 4]; return 1; }\n"),
        "S016 1:17"
    );
    assert_eq!(
        at(
            ty,
            "comptime fn g() -> Nat { reg r: UInt[8] = 0; return 1; }\n"
        ),
        "S006 1:26"
    );
    assert_eq!(
        at(
            ty,
            "comptime fn g() -> Nat { mem q: [UInt[8]; 4]; return 1; }\n"
        ),
        "S006 1:26"
    );
    let g1 = "  let x: UInt[g(1)] = 0;\n";
    assert_eq!(
        at(g1, "fn g(x: UInt[8]) -> Nat { x := 1; return 1; }\n"),
        "S016 1:27"
    );
    assert_eq!(
        at(
            g1,
            "comptime fn g(x: UInt[8]) -> Nat { x := 1; return 1; }\n"
        ),
        "S006 1:36"
    );
}

#[test]
fn a_port_call_in_a_structural_context_is_s016() {
    let at = |write: bool, rest: &str| {
        let b = Budget::default();
        elab_only(&with_memory(write, rest), "M", b.fuel, b.depth)
    };
    assert_eq!(
        at(true, "  let x: UInt[read_port(k, 0, true)] = 0;\n"),
        "S016 16:15"
    );
    assert_eq!(
        at(false, "  mem q2: [UInt[8]; write_port(k, 0, 1, true)];\n"),
        "S016 16:21"
    );
    assert_eq!(
        at(false, "  let t = [Bool; k.write_port(0, 1, true)];\n"),
        "S016 16:18"
    );
    assert_eq!(
        at(true, "  let x: UInt[read_port(q, 0, true)] = 0;\n"),
        "S005 16:25"
    );
}

/// Each normative text of `S016` (section 9.4), in full.
#[test]
fn each_text_of_s016_is_pinned_in_full() {
    assert_eq!(
        said(&module(
            "  let x: [Bool; pop(xs)] = [false, false, false];\n"
        )),
        "a type or a constant cannot change `xs`; change `xs` before it, keep the result in a \
         `let`, and use that name here"
    );
    assert_eq!(
        said(&module("  let x: UInt[f(n)] = 0;\n")),
        "a type or a constant cannot change `n`; change `n` before it, keep the result in a \
         `let`, and use that name here"
    );
    assert_eq!(
        said(&with_memory(
            true,
            "  let x: UInt[read_port(k, 0, true)] = 0;\n"
        )),
        "a type or a constant has no graph effect such as `read_port`; call it before and use \
         the result"
    );
    assert_eq!(
        said(&module("  let z = if (c) { pop(xs) } else { 0 };\n")),
        "a hardware arm cannot change `xs`, a binding from before the arm; change `xs` before \
         the `if` or `match`, and use the result in the arm"
    );
    assert_eq!(
        said(&with_memory(
            true,
            "  let z = if (c) { read_port(q, a, c) } else { 0 };\n"
        )),
        "a hardware arm has no graph effect such as `read_port`; call `read_port` before the `if` \
         or `match`, and use its result in the arm"
    );
}
