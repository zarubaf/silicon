// SPDX-License-Identifier: Apache-2.0
//! The call cases of `Silicon.Source.Test.Eval` and `Test.Elab` in Lean: a call through a
//! function value with its charges, its number of arguments, its callee rule, its `mut` actuals,
//! and the wait of its callee, then the windows of the `mut` actuals at run time (`S008`).

use crate::counters::of;
use crate::tests::{cost, out};
use crate::tests_elab::{cost as elab_cost, names, total};
use crate::{Budget, eval};

fn o(src: &str, expr: &str) -> String {
    out(src, expr, 100_000_000, 1000)
}

fn with(src: &str, expr: &str, fuel: u64) -> String {
    out(src, expr, fuel, 1000)
}

const VIA_FNS: &str = "fn id(x: Bool) -> Bool { return x; }\n\
    fn two(a: Int, b: Int) -> Int { return a - b; }\n\
    fn inc(mut x: Int) -> Int { x = x + 1; return x; }\n\
    comptime fn c(x: Int) -> Int { return x + 1; }\n\
    fn sf(mut h: fn (Bool) -> Bool) -> Bool { h = id; return true; }\n\
    fn st(mut t: Type) -> Nat { t = Bool; return 0; }\n\
    fn ap(h: fn (Bool) -> Bool, x: Bool) -> Bool { return h(x); }\n";

fn call_in(s: &str) -> String {
    format!("{VIA_FNS}fn f() -> Int {{ {s} }}")
}

/// A call through a function value evaluates its callee once, then runs as a call of its item.
/// The callee charges as an expression, and no function name charges.
#[test]
fn a_call_through_a_value_charges_as_a_named_call() {
    let fl = "fn g() -> Bool { return true; }\nfn f() -> Bool { let x = g; return x(); }";
    assert_eq!(o(fl, "f()"), "(bool true)");
    assert_eq!(
        o(&call_in("let f = two; return f(5, 2);"), "f()"),
        "(int 3)"
    );
    assert_eq!(
        cost(&call_in("let f = two; return f(5, 2);"), "f()"),
        cost(&call_in("let f = two; return two(5, 2);"), "f()")
    );
    assert_eq!(o(VIA_FNS, "ap(id, false)"), "(bool false)");
    assert_eq!(
        o(&call_in("let fs = [two, two]; return fs[1](7, 1);"), "f()"),
        "(int 6)"
    );
    assert_eq!(o(VIA_FNS, "(two)(1, 1)"), "(int 0)");
}

/// The number of arguments is `S007` at the call, after the charge of the callee and before
/// the arguments: `error` does not run.
#[test]
fn the_number_of_arguments_of_a_value() {
    let few = call_in("let f = two; return f(5);");
    assert_eq!(o(&few, "f()"), "S007 8:37");
    assert_eq!(
        o(
            &call_in("let f = two; return f(5, 2, error(\"x\"));"),
            "f()"
        ),
        "S007 8:37"
    );
    assert_eq!(with(&few, "f()", 16), "S007 8:37");
    assert_eq!(with(&few, "f()", 15), "S015 8:37");
}

/// A callee that is neither a function nor a type is `S010` at the call. The type rule of the
/// arguments holds as at a named call, and a `comptime fn` runs through its value.
#[test]
fn the_callee_rule_and_the_types_of_the_arguments() {
    assert_eq!(o(&call_in("let f = 3; return f(5);"), "f()"), "S010 8:35");
    assert_eq!(o(&call_in("return (1)(5);"), "f()"), "S010 8:24");
    assert_eq!(
        o(&call_in("let f = two; return f(true, 1);"), "f()"),
        "S010 8:37"
    );
    assert_eq!(o(&call_in("let f = c; return f(5);"), "f()"), "(int 6)");
}

/// The `mut` marks of the function type select the `mut` actuals. The write-back runs as at a
/// named call, with the same charges. A `mut` actual that is not a place is `S008`.
#[test]
fn the_mut_actuals_of_a_value() {
    let by = |s: &str| call_in(&format!("let f = inc; let mut a = 1; {s}"));
    let named = |s: &str| call_in(&format!("let f = inc; let mut a = 1; {s}"));
    assert_eq!(
        o(&by("let r = f(a); return a * 10 + r;"), "f()"),
        "(int 22)"
    );
    assert_eq!(
        cost(&by("let r = f(a); return a;"), "f()"),
        cost(&named("let r = inc(a); return a;"), "f()")
    );
    assert_eq!(o(&call_in("let f = inc; return f(3);"), "f()"), "S008 8:39");
}

/// The callee waits while the arguments evaluate. A write-back to the local of the callee thus
/// charges the size of the local: 1 for a function, 2 for `UInt[8]`. Another callee local is
/// not held, so its call charges 1 or 2 less.
#[test]
fn the_callee_waits_while_the_arguments_evaluate() {
    let c = |s: &str| cost(&call_in(s), "f()");
    assert_eq!(
        c("let mut f = id; let b = f(sf(f)); return 0;")
            - c("let mut f = id; let b = sf(f); return 0;"),
        c("let mut f = id; let mut e = id; let b = e(sf(f)); return 0;")
            - c("let mut f = id; let mut e = id; let b = sf(f); return 0;")
            + 1
    );
    assert_eq!(
        c("let mut T = UInt[8]; let v = T(st(T)); return 0;")
            - c("let mut T = UInt[8]; let v = st(T); return 0;"),
        c("let mut T = UInt[8]; let mut S = UInt[8]; let v = S(st(T)); return 0;")
            - c("let mut T = UInt[8]; let mut S = UInt[8]; let v = st(T); return 0;")
            + 2
    );
}

const VIA_HW: &str = "fn inc(mut a: UInt[8]) -> () { a = a +% 1; return (); }\n\
    fn swap(mut a: UInt[8], mut b: UInt[8]) -> UInt[8] { let t = a; a = b; b = t; return t; }\n\
    comptime fn cc(a: UInt[8]) -> UInt[8] { return a; }\n\
    module M() {\n  input c: Bool;\n  input x: UInt[8];\n  input w: UInt[8];\n\
    \x20 output y: UInt[8];\n  let f = swap;\n  let mut q = x;\n  let mut r = w;\n";

fn via_hw(body: &str) -> String {
    format!("{VIA_HW}{body}}}\n")
}

/// A call through a value gives the call frame of its item and the site of the call, so the
/// names and the charges equal those of a named call. A `comptime fn` runs in the static mode.
#[test]
fn a_call_through_a_value_names_its_frame_like_a_named_call() {
    let body = "  let s = f(q, r);\n  y := q +% r;\n";
    let named = "  let s = swap(q, r);\n  y := q +% r;\n";
    assert_eq!(
        names(&via_hw(body), "M", "M"),
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
    assert_eq!(
        names(&via_hw(body), "M", "M"),
        names(&via_hw(named), "M", "M")
    );
    assert_eq!(total(&via_hw(body), "M"), total(&via_hw(named), "M"));
    assert_eq!(
        names(
            &via_hw("  let g = inc;\n  g(q);\n  g(q);\n  y := q;\n"),
            "M",
            "M"
        ),
        [
            "q",
            "r",
            "inc$0c$a",
            "inc$0c$a$1v",
            "q$1v",
            "inc$1c$a",
            "inc$1c$a$1v",
            "q$2v"
        ]
    );
    assert_eq!(
        elab_cost(
            &via_hw("  let g = inc;\n  y := if (c) { g(q) } else { 0 };\n"),
            "M"
        ),
        "S016 13:17"
    );
    assert_eq!(
        elab_cost(&via_hw("  let g = cc;\n  y := g(x);\n"), "M"),
        "S011 13:8"
    );
    assert!(elab_cost(&via_hw("  let g = cc;\n  y := g(3);\n"), "M").starts_with("total"));
}

fn windows(s: &str) -> String {
    format!(
        "fn mo(mut a: List[Int]) -> Int {{ return a.len(); }}\n\
         fn mt(mut a: List[Int], mut b: List[Int]) -> Int {{ return 0; }}\n\
         fn mp(mut a: List[Int], b: Int) -> Int {{ return b; }}\n\
         fn mu(mut a: List[Int], b: ()) -> Int {{ return 0; }}\n\
         fn mq(b: Int, mut a: List[Int]) -> Int {{ return b; }}\n\
         fn mr(mut a: List[Int]) -> Int {{ let h = mo; a.push(7); return h(a); }}\n\
         fn f() -> Int {{\nlet mut xs = list(Int); xs.push(1); xs.push(2); \
         let mut ys = list(Int);\n\
         let vo = mo; let vt = mt; let vp = mp; let vu = mu; let vq = mq; let vr = mr;\n\
         {s}\nreturn xs.len() * 10 + ys.len();\n}}"
    )
}

/// The value of `f()` without pass 4: pass 5 alone then decides `S008`.
fn late(src: &str) -> String {
    let depth_n = parse::DEFAULT_SYNTAX_DEPTH;
    let at = |code: &dyn std::fmt::Display, pos: parse::ast::Pos| {
        format!("{code} {}:{}", pos.line, pos.col)
    };
    let parsed = parse::parse_with_depth(src, depth_n).unwrap();
    let Ok(file) = resolve::resolve(parsed) else {
        panic!("the source must resolve")
    };
    let e = parse::parse_expr("f()", depth_n).unwrap().unwrap();
    let e = resolve::resolve_expr(&file, e).unwrap().unwrap();
    match eval(&file, &e, Budget::default()).unwrap() {
        Ok((done, _)) => done.serialize(),
        Err(e) => at(&e.code, e.pos),
    }
}

/// `S008` at run time (section 9.1). The `mut` marks of a call through a function value are
/// known only in pass 5. A `mut` actual whose root is pending in a window of the same frame is
/// `S008` at the start of the actual. Pass 4 accepts each of these programs.
#[test]
fn a_root_in_a_window_is_pending() {
    let s008 = |body: &str, at: &str| assert_eq!(o(&windows(body), "f()"), format!("S008 {at}"));
    s008("vp(xs, xs.pop());", "10:8");
    s008("vp(xs, pop(xs));", "10:12");
    s008("vu(xs, xs.push(1));", "10:8");
    s008("vu(xs, push(xs, 1));", "10:13");
    s008("vt(xs, xs);", "10:8");
    // A `push` or a named call opens a window, and a call through a value in it conflicts.
    s008("xs.push(vo(xs));", "10:12");
    s008("push(xs, vo(xs));", "10:13");
    s008("mp(xs, vo(xs));", "10:11");
    s008("mp(xs, mp(ys, vo(xs)));", "10:18");
    // A call through a value opens a window, and a named call or `pop` in it conflicts.
    s008("vp(xs, mo(xs));", "10:11");
    s008("vp(xs, vp(ys, xs.pop()));", "10:15");
    // An assignment opens a window for the indices of its place and its right side.
    s008("xs[vo(xs) - 1] = 5;", "10:7");
    s008("xs[0] = vo(xs);", "10:12");
}

/// A root is pending only in its window, and only in its frame. An argument before the `mut`
/// actual, a call that ends before it, a read, and another root do not conflict. The callee
/// `mr` changes its own `mut` formal while the root `xs` of the caller is pending.
#[test]
fn a_root_is_pending_only_in_its_window_and_frame() {
    let run = |body: &str| o(&windows(body), "f()");
    assert_eq!(run("vp(xs, ys.pop());"), "S013 10:8");
    assert_eq!(run("ys.push(3); vp(xs, ys.pop());"), "(int 20)");
    assert_eq!(run("vq(xs.pop(), xs);"), "(int 10)");
    assert_eq!(
        run("let a = mo(ys) + vo(xs) + vp(xs, xs.len());"),
        "(int 20)"
    );
    assert_eq!(run("vt(xs, ys); vt(ys, xs);"), "(int 20)");
    assert_eq!(run("let a = vp(xs, vr(ys));"), "(int 21)");
    assert_eq!(run("ys.push(vo(xs)); xs[vo(ys) - 1] = 5;"), "(int 21)");
}

/// The windows have no charge: a call through a value charges as the named call.
#[test]
fn the_windows_have_no_charge() {
    assert_eq!(
        cost(&windows("let a = vp(xs, 1);"), "f()"),
        cost(&windows("let a = mp(xs, 1);"), "f()")
    );
}

/// Pass 4 and pass 5 agree on the calls of function items. A program that pass 4 rejects gives
/// the same error in pass 5 alone, and the call through the value gives it too. A program that
/// pass 4 accepts runs the same in pass 5 alone.
#[test]
fn pass_four_and_pass_five_agree() {
    let agree = |named: &str, value: &str, want: &str| {
        assert_eq!(o(&windows(named), "f()"), want, "{named}");
        assert_eq!(late(&windows(named)), want, "{named} late");
        assert_eq!(o(&windows(value), "f()"), want, "{value}");
    };
    agree("mp(xs, xs.pop());", "vp(xs, xs.pop());", "S008 10:8");
    agree("mt(xs, xs);", "vt(xs, xs);", "S008 10:8");
    agree("mu(xs, push(xs, 1));", "vu(xs, push(xs, 1));", "S008 10:13");
    agree("mp(xs, mo(xs));", "vp(xs, vo(xs));", "S008 10:11");
    agree("mq(xs.pop(), xs);", "vq(xs.pop(), xs);", "(int 10)");
    agree(
        "mt(xs, ys); mt(ys, xs);",
        "vt(xs, ys); vt(ys, xs);",
        "(int 20)",
    );
    for (body, at) in [
        ("xs.push(xs.pop());", "10:9"),
        ("xs[0] = xs.pop();", "10:9"),
        ("xs[xs.pop()] = 1;", "10:4"),
    ] {
        let want = format!("S008 {at}");
        assert_eq!(o(&windows(body), "f()"), want, "{body}");
        assert_eq!(late(&windows(body)), want, "{body} late");
    }
}

/// The windows that a run opened and closed, for a fuel that no other test uses.
fn windows_of(src: &str, fuel: u64) -> u64 {
    let _ = with(src, "f()", fuel);
    of(fuel).windows
}

/// A call through one value, `n` times, opens and closes the window of its `mut` actual, and
/// the fuel grows by a fixed step for each call: the lookup of the item by the value has no
/// charge and no walk.
#[test]
fn many_calls_through_one_value_grow_linearly() {
    let src = |n: usize| {
        let calls = "f(a); ".repeat(n);
        call_in(&format!("let f = inc; let mut a = 1; {calls}return a;"))
    };
    let counts: Vec<u64> = [0, 10, 20, 40]
        .iter()
        .zip(7_000_001u64..)
        .map(|(&n, fuel)| windows_of(&src(n), fuel))
        .collect();
    // The window of the actual and the window of the assignment in the callee.
    assert_eq!(counts, [0, 40, 80, 160]);
    let used: Vec<u64> = [0, 10, 20, 40]
        .iter()
        .map(|&n| cost(&src(n), "f()"))
        .collect();
    assert_eq!(used[2] - used[1], used[1] - used[0]);
    assert_eq!(used[3] - used[2], 2 * (used[2] - used[1]));
}

/// A call with `k` `mut` actuals on `k` distinct roots opens `k` windows and closes them after
/// the last argument, so the work is `2k` for the call and the fuel grows by a fixed step for
/// each actual.
#[test]
fn many_mut_actuals_on_distinct_roots_grow_linearly() {
    let src = |k: usize| {
        let params: Vec<String> = (0..k).map(|i| format!("mut p{i}: Int")).collect();
        let locals = (0..k)
            .map(|i| format!("let mut x{i} = {i};"))
            .collect::<Vec<_>>()
            .join(" ");
        let args: Vec<String> = (0..k).map(|i| format!("x{i}")).collect();
        format!(
            "fn many({}) -> Int {{ return 0; }}\nfn f() -> Int {{ let v = many; {locals}\
             return v({}); }}",
            params.join(", "),
            args.join(", ")
        )
    };
    let counts: Vec<u64> = [10, 20, 40]
        .iter()
        .zip(7_100_001u64..)
        .map(|(&k, fuel)| windows_of(&src(k), fuel))
        .collect();
    assert_eq!(counts, [20, 40, 80]);
    let used: Vec<u64> = [10, 20, 40].iter().map(|&k| cost(&src(k), "f()")).collect();
    assert_eq!(used[2] - used[1], 2 * (used[1] - used[0]));
}

/// A call through a value in a frame while a window of that frame is open: the windows follow
/// the frames and do not copy. Each of the `n + 1` frames of a recursion through a value opens
/// one window of its own `x` while the next frame runs, so a root of a frame does not conflict
/// with the same local of another frame, and the work is `2 (n + 1)` and not more.
#[test]
fn nested_calls_through_values_keep_one_window_for_each_frame() {
    let src = "fn tk(mut a: Int, b: Nat) -> Nat { return b; }\n\
        fn r(n: Nat) -> Nat {\n  let mut x = 0;\n  let f = r;\n  let t = tk;\n  \
        return t(x, if (n == 0) { 0 } else { f(n - 1) });\n}";
    let counts: Vec<u64> = [10u64, 20, 40]
        .iter()
        .zip(7_200_001u64..)
        .map(|(&n, fuel)| {
            let _ = with(src, &format!("r({n})"), fuel);
            of(fuel).windows
        })
        .collect();
    assert_eq!(counts, [22, 42, 82]);
    let used: Vec<u64> = [10, 20, 40]
        .iter()
        .map(|n| cost(src, &format!("r({n})")))
        .collect();
    assert_eq!(used[2] - used[1], 2 * (used[1] - used[0]));
}
