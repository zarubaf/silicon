// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::program::{Place, Radix, SBin};
use num_bigint::BigInt;
use proptest::strategy::ValueTree;
use proptest::test_runner::TestRunner;
use std::collections::{BTreeMap, BTreeSet};

fn tapes(count: usize) -> Vec<Vec<u32>> {
    let mut runner = TestRunner::deterministic();
    let strategy = vec(any::<u32>(), 0..4096);
    (0..count)
        .filter_map(|_| strategy.new_tree(&mut runner).ok().map(|t| t.current()))
        .collect()
}

#[test]
fn an_empty_tape_gives_the_smallest_program() {
    let p = build(vec![]).unwrap();
    assert_eq!(
        p.text(),
        "module M0() domains() {\n    output o0: Bool;\n    o0 := false;\n}\n"
    );
    assert_eq!(p.top(), "M0()");
    assert_eq!(p.probe(), ("0".to_owned(), "(int 0)".to_owned()));
    let ports = Ports {
        clocked: false,
        inputs: vec![],
        outputs: vec![("o0".to_owned(), Scalar::Bool)],
    };
    assert_eq!(p.ports(), &ports);
}

#[test]
fn the_same_tape_gives_the_same_program() {
    let mut x: u32 = 12345;
    let tape: Vec<u32> = (0..512)
        .map(|_| {
            x = x.wrapping_mul(1_103_515_245).wrapping_add(12345);
            x
        })
        .collect();
    assert_eq!(
        build(tape.clone()).unwrap().text(),
        build(tape).unwrap().text()
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn programs_lex(p in typed()) {
        let p = p.map_err(|e| TestCaseError::fail(e.to_string()))?;
        let lexed = syntax::lex(&p.text(), 4096);
        prop_assert!(lexed.errors.is_empty(), "{:?}", lexed.errors);
    }
}

/// The statements of a body, with those of nested frames.
fn stmts_of_body(body: &[Stmt]) -> Vec<&Stmt> {
    let mut out = Vec::new();
    for s in body {
        out.push(s);
        match s {
            Stmt::If(_, t, e) => {
                out.extend(stmts_of_body(t));
                out.extend(stmts_of_body(e.as_deref().unwrap_or_default()));
            }
            Stmt::For(_, _, _, b) => out.extend(stmts_of_body(b)),
            _ => {}
        }
    }
    out
}

fn stmts_of(items: &[Item]) -> Vec<&Stmt> {
    let mut out = Vec::new();
    for item in items {
        match item {
            Item::Module { body, .. } | Item::Helper { body, .. } => {
                out.extend(stmts_of_body(body));
            }
            _ => {}
        }
    }
    out
}

fn hexprs_of<'a>(s: &'a Stmt, out: &mut Vec<&'a HExpr>) {
    fn walk<'a>(e: &'a HExpr, out: &mut Vec<&'a HExpr>) {
        out.push(e);
        match e {
            HExpr::Unary(_, a) | HExpr::Resize(_, a) | HExpr::Reinterpret(_, a) => walk(a, out),
            HExpr::Binary(_, a, b) => {
                walk(a, out);
                walk(b, out);
            }
            HExpr::If(c, t, e) => {
                walk(c, out);
                walk(t, out);
                walk(e, out);
            }
            HExpr::Call(_, args) => args.iter().for_each(|a| walk(a, out)),
            _ => {}
        }
    }
    match s {
        Stmt::Let { value, .. } | Stmt::Assign(_, value) | Stmt::Connect(_, value) => {
            walk(value, out);
        }
        _ => {}
    }
}

fn calls_of(name: &str, e: &SExpr) -> usize {
    match e {
        SExpr::Call(f, args) => {
            usize::from(f == name) + args.iter().map(|a| calls_of(name, a)).sum::<usize>()
        }
        SExpr::Unary(_, a) => calls_of(name, a),
        SExpr::Binary(_, a, b) => calls_of(name, a) + calls_of(name, b),
        SExpr::If(c, t, e) => calls_of(name, c) + calls_of(name, t) + calls_of(name, e),
        _ => 0,
    }
}

/// The slice-1 forms of a program.
fn features(p: &Program, contexts: usize) -> BTreeSet<&'static str> {
    let text = p.text();
    let mut seen: BTreeSet<&'static str> = [
        "comptime fn",
        "comptime for",
        "error(\"dead\")",
        "const ",
        "static_assert(",
        "reg ",
        "wire ",
        "instance ",
        "let mut ",
        "SInt[",
        "resize(",
        "reinterpret(",
        "0x",
        "0b",
    ]
    .into_iter()
    .filter(|f| text.contains(f))
    .collect();
    if text.contains(" in (-") {
        seen.insert("negative loop bound");
    }
    for item in &p.items {
        if let Item::ComptimeFn(f) = item
            && calls_of(&f.name, &f.step) == 2
        {
            seen.insert("two self calls");
        }
    }
    let stmts = stmts_of(&p.items);
    let mut hexprs = Vec::new();
    for s in &stmts {
        hexprs_of(s, &mut hexprs);
        match s {
            Stmt::For(_, _, _, b) if b.iter().any(|s| matches!(s, Stmt::For(..))) => {
                seen.insert("nested comptime for");
            }
            Stmt::If(_, _, Some(_)) => {
                seen.insert("comptime if with else");
            }
            Stmt::StaticLet(..) => {
                seen.insert("static let");
            }
            Stmt::Input(_, Ty::Bool) => {
                seen.insert("Bool input");
            }
            _ => {}
        }
        let ty = match s {
            Stmt::Input(_, t) | Stmt::Output(_, t) | Stmt::Reg(_, t, _) | Stmt::Wire(_, t) => {
                Some(t)
            }
            _ => None,
        };
        if let Some(Ty::UInt(w) | Ty::SInt(w)) = ty
            && !matches!(w, SExpr::Int(..))
        {
            seen.insert("width that is not a literal");
        }
    }
    for e in hexprs {
        match e {
            HExpr::Call(..) => {
                seen.insert("helper call");
            }
            HExpr::If(..) => {
                seen.insert("hardware if");
            }
            _ => {}
        }
    }
    if p.ports.clocked {
        seen.insert("clocked top");
    }
    if contexts >= 2 {
        seen.insert("two contexts");
    }
    seen
}

#[test]
fn programs_cover_slice_1() {
    let want: BTreeSet<&str> = [
        "comptime fn",
        "two self calls",
        "comptime for",
        "negative loop bound",
        "nested comptime for",
        "comptime if with else",
        "error(\"dead\")",
        "const ",
        "static_assert(",
        "helper call",
        "reg ",
        "wire ",
        "instance ",
        "let mut ",
        "static let",
        "SInt[",
        "resize(",
        "reinterpret(",
        "width that is not a literal",
        "hardware if",
        "0x",
        "0b",
        "clocked top",
        "Bool input",
        "two contexts",
    ]
    .into_iter()
    .collect();
    let mut seen = BTreeSet::new();
    let mut total = Stats::default();
    let mut shape = Shape::default();
    for tape in tapes(400) {
        let mut b = Builder::new(tape);
        let p = b.program();
        assert!(p.is_ok(), "a program faults: {p:?}");
        let contexts = b.contexts.iter().map(Vec::len).max().unwrap_or(0);
        if let Ok(p) = p {
            seen.extend(features(&p, contexts));
            shape.add(&p, contexts);
        }
        total.widths += b.stats.widths;
        total.width_fallbacks += b.stats.width_fallbacks;
        total.calls += b.stats.calls;
        total.call_fallbacks += b.stats.call_fallbacks;
    }
    let missing: Vec<&&str> = want.difference(&seen).collect();
    assert!(missing.is_empty(), "missing forms: {missing:?}");
    assert!(
        total.width_fallbacks * 2 < total.widths,
        "width fallbacks: {total:?}"
    );
    assert!(
        total.call_fallbacks * 5 < total.calls,
        "call fallbacks: {total:?}"
    );
    // The run oracle tests hardware only if outputs read names, and the
    // twin is tested by hierarchy, contexts, and calls.
    assert!(shape.reading * 4 >= shape.outputs * 3, "{shape:?}");
    assert!(shape.modules * 5 >= 400 * 2, "{shape:?}");
    assert!(shape.deep * 20 >= 400 * 3, "{shape:?}");
    assert!(shape.calls * 10 >= 400 * 3, "{shape:?}");
    assert!(shape.contexts * 10 >= 400, "{shape:?}");
}

/// The mean program stays near the size of the slice-1 programs (2457
/// bytes over these 256 tapes before containers): at most 50% more.
#[test]
fn the_mean_program_stays_small() {
    const TAPES: usize = 256;
    let total: usize = tapes(TAPES)
        .into_iter()
        .filter_map(|tape| build(tape).ok())
        .map(|p| p.text().len())
        .sum();
    assert!(total / TAPES <= 3700, "the mean is {} bytes", total / TAPES);
}

/// The most levels of container types in `t`.
fn levels(t: &STy) -> u32 {
    match t {
        STy::Tuple(ts) => 1 + ts.iter().map(levels).max().unwrap_or(0),
        STy::Array(t, _) => 1 + levels(t),
        _ => 0,
    }
}

/// The forms of the static containers that a program holds, by name.
fn static_forms(s: &Stats) -> [(&'static str, bool); 32] {
    [
        ("tuple", s.tuples > 0),
        ("array", s.arrays > 0),
        ("selector", s.selects > 0),
        ("index", s.indexes > 0),
        ("len", s.lens > 0),
        ("record", s.records > 0),
        ("zero", s.zeros > 0),
        ("field", s.fields > 0),
        ("data_bits", s.data_bits > 0),
        ("str(n)", s.str_of > 0),
        ("join", s.joins > 0),
        ("scalar of a string", s.scalars > 0),
        ("len of a string", s.str_lens > 0),
        ("string equality", s.str_eqs > 0),
        ("list builder call", s.list_calls > 0),
        ("push", s.pushes > 0),
        ("pop", s.pops > 0),
        ("index of a list", s.list_indexes > 0),
        ("len of a list", s.list_lens > 0),
        ("static mut call", s.mut_calls > 0),
        ("hardware mut call", s.hw_mut_calls > 0),
        ("hardware mut receiver", s.hw_mut_receivers > 0),
        ("function value", s.fn_values > 0),
        ("function value with a mut formal", s.mut_values > 0),
        ("function value of a helper", s.hw_values > 0),
        ("call through a function value", s.value_calls > 0),
        ("mut call through a function value", s.mut_value_calls > 0),
        ("helper call through a function value", s.hw_value_calls > 0),
        ("function as a module argument", s.fn_arguments > 0),
        ("diagnostic statement", s.diagnostics > 0),
        ("effectful function", s.effectful_fns > 0),
        ("call of an effectful function", s.effectful_calls > 0),
    ]
}

/// The positions of each form and those that took a fallback.
fn fallback_pairs(s: &Stats) -> [(&'static str, u32, u32); 8] {
    [
        ("container leaf", s.leaves, s.leaf_fallbacks),
        ("index", s.indexes, s.index_fallbacks),
        ("type argument", s.arguments, s.argument_fallbacks),
        ("list call", s.list_calls, s.list_call_fallbacks),
        ("push", s.pushes + s.push_fallbacks, s.push_fallbacks),
        (
            "mut call",
            s.mut_calls + s.mut_call_fallbacks,
            s.mut_call_fallbacks,
        ),
        ("hardware mut call", s.hw_mut_calls, 0),
        (
            "call through a function value",
            s.value_calls,
            s.value_call_fallbacks,
        ),
    ]
}

/// Each form of the static containers occurs in at least 10% of 256
/// programs, and a form takes a fallback in at most 20% of its positions.
#[test]
fn programs_cover_static_containers() {
    const TAPES: usize = 256;
    let mut with = BTreeMap::<&str, usize>::new();
    let mut pairs = BTreeMap::<&str, (u32, u32)>::new();
    for tape in tapes(TAPES) {
        let mut b = Builder::new(tape);
        let p = b.program();
        assert!(p.is_ok(), "a program faults: {p:?}");
        let Ok(p) = p else { continue };
        for (form, seen) in static_forms(&b.stats) {
            *with.entry(form).or_default() += usize::from(seen);
        }
        for (form, total, fallbacks) in fallback_pairs(&b.stats) {
            let entry = pairs.entry(form).or_default();
            entry.0 += total;
            entry.1 += fallbacks;
        }
        let probed = p.probe().1.starts_with("(array") || p.probe().1.starts_with("(tuple");
        let statics = stmts_of(&p.items)
            .into_iter()
            .filter_map(|s| match s {
                Stmt::StaticLet(_, t, _) => Some(t),
                _ => None,
            })
            .chain(p.items.iter().filter_map(|i| match i {
                Item::Const { ty, .. } => Some(ty),
                _ => None,
            }));
        let nested = statics.map(levels).max().unwrap_or(0) >= 2;
        *with.entry("nested or probed").or_default() += usize::from(probed || nested);
    }
    assert_eq!(with.len(), 33, "{with:?}");
    for (form, n) in &with {
        assert!(
            n * 10 >= TAPES,
            "{form} occurs in {n} of {TAPES} programs: {with:?}"
        );
    }
    for (form, (total, fallbacks)) in &pairs {
        assert!(
            fallbacks * 5 <= *total,
            "{form}: {fallbacks} fallbacks of {total} positions"
        );
    }
}

/// The names of the effectful functions of `p` (a `diagnostic` in the body)
/// and of the consts that hold one.
fn effectful(p: &Program) -> BTreeSet<String> {
    let mut names: BTreeSet<String> = p
        .items
        .iter()
        .filter_map(|i| match i {
            Item::MutFn(f) if f.diag.is_some() => Some(f.name.clone()),
            _ => None,
        })
        .collect();
    for i in &p.items {
        if let Item::Const {
            name,
            value: SExpr::Name(target),
            ..
        } = i
            && names.contains(target)
        {
            names.insert(name.clone());
        }
    }
    names
}

/// No effectful function reaches a width, a `const`, a struct argument, a
/// parameter type, or a hardware arm (spec 9.4). Its name occurs only in
/// its declaration, in the `const` that holds it, and as the callee of a
/// call statement `let sN: Int = f(...)` or `let sN: Int = root.f(...)`.
/// Those statements are not in a helper body, which holds hardware
/// statements only.
#[test]
fn no_effectful_function_reaches_a_structural_position() {
    let mut effectful_programs = 0;
    for tape in tapes(256) {
        let Ok(p) = build(tape) else {
            panic!("a program faults");
        };
        let names = effectful(&p);
        effectful_programs += usize::from(!names.is_empty());
        for item in &p.items {
            if let Item::Helper { body, .. } = item {
                assert!(
                    stmts_of_body(body)
                        .iter()
                        .all(|s| !matches!(s, Stmt::MutCall { .. } | Stmt::Diagnostic(..))),
                    "a helper holds a static call or a diagnostic:\n{}",
                    p.text()
                );
            }
        }
        for line in p.text().lines() {
            let tokens: Vec<&str> = line
                .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .collect();
            let uses = tokens.iter().filter(|t| names.contains(**t)).count();
            if uses == 0 {
                continue;
            }
            let t = line.trim_start();
            let declaration = t.starts_with("comptime fn ") && uses == 1;
            let held = t.starts_with("const F") && t.ends_with(';') && uses <= 2;
            let call = t.starts_with("let s") && t.contains(": Int = ") && uses == 1;
            assert!(
                declaration || held || call,
                "an effectful function in a structural position: {line}\n{}",
                p.text()
            );
        }
    }
    assert!(effectful_programs >= 25, "{effectful_programs} of 256");
}

/// The depth of the instance tree below module `m`.
fn depth(m: &str, modules: &BTreeMap<&str, &[Stmt]>) -> usize {
    stmts_of_body(modules.get(m).copied().unwrap_or_default())
        .into_iter()
        .filter_map(|s| match s {
            Stmt::Instance(_, child, _) => Some(1 + depth(child, modules)),
            _ => None,
        })
        .max()
        .unwrap_or(0)
}

/// Counts of the program shapes that the oracles of `diff-si` need.
#[derive(Debug, Default)]
struct Shape {
    /// Top outputs, and those whose `:=` reads a hardware name.
    outputs: usize,
    reading: usize,
    /// Programs with two or more modules, an instance tree of depth two or
    /// more, a helper call, and a module in two contexts.
    modules: usize,
    deep: usize,
    calls: usize,
    contexts: usize,
}

impl Shape {
    fn add(&mut self, p: &Program, contexts: usize) {
        let modules: BTreeMap<&str, &[Stmt]> = p
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Module { name, body, .. } => Some((name.as_str(), body.as_slice())),
                _ => None,
            })
            .collect();
        if let Some(top) = modules.get("M0") {
            for s in *top {
                if let Stmt::Connect(Place::Name(n), e) = s
                    && n.starts_with('o')
                {
                    self.outputs += 1;
                    self.reading += usize::from(hw::reads_name(e));
                }
            }
        }
        self.modules += usize::from(modules.len() >= 2);
        self.deep += usize::from(depth("M0", &modules) >= 2);
        self.contexts += usize::from(contexts >= 2);
        let mut hexprs = Vec::new();
        for s in stmts_of(&p.items) {
            hexprs_of(s, &mut hexprs);
        }
        self.calls += usize::from(hexprs.iter().any(|e| matches!(e, HExpr::Call(..))));
    }
}

#[test]
fn lines_put_the_reset_first() {
    let ports = Ports {
        clocked: true,
        inputs: vec![
            ("a".to_owned(), Scalar::Bool),
            ("b".to_owned(), Scalar::SInt(4)),
        ],
        outputs: vec![],
    };
    let mut runner = TestRunner::deterministic();
    for _ in 0..16 {
        let Ok(tree) = lines(&ports, 8).new_tree(&mut runner) else {
            panic!("no lines");
        };
        let lines = tree.current();
        assert_eq!(lines.len(), 8);
        for line in lines {
            let inner = line
                .strip_prefix("in=(")
                .and_then(|l| l.strip_suffix(')'))
                .unwrap_or_default();
            let words: Vec<&str> = inner.split(' ').collect();
            let [reset, rst, a_name, a_val, b_name, b_val] = words.as_slice() else {
                panic!("bad line {line}");
            };
            assert_eq!(
                (*reset, *a_name, *b_name),
                ("clock$0rst", "a", "b"),
                "{line}"
            );
            assert!(["true", "false"].contains(rst) && ["true", "false"].contains(a_val));
            let b_val: i64 = b_val.parse().unwrap_or(99);
            assert!((-8..=7).contains(&b_val), "{line}");
        }
    }
    let empty = Ports {
        clocked: false,
        inputs: vec![],
        outputs: vec![("o0".to_owned(), Scalar::Bool)],
    };
    let Ok(tree) = lines(&empty, 8).new_tree(&mut runner) else {
        panic!("no lines");
    };
    assert_eq!(tree.current(), vec!["in=()".to_owned(); 8]);
}

#[test]
fn top_ports_are_evaluated_and_sorted() {
    let width = SExpr::Binary(
        SBin::Add,
        Box::new(SExpr::Name("P0".to_owned())),
        Box::new(SExpr::Int(BigInt::from(1), Radix::Dec)),
    );
    let items = vec![Item::Module {
        name: "M0".to_owned(),
        params: vec![("P0".to_owned(), STy::Nat)],
        clocked: false,
        body: vec![
            Stmt::Input("i1".to_owned(), Ty::UInt(width)),
            Stmt::Input("i0".to_owned(), Ty::Bool),
        ],
    }];
    let p = ports(&items, "M0", &[Value::Int(BigInt::from(5))]);
    let Ok(p) = p else {
        panic!("the ports fault: {p:?}");
    };
    assert_eq!(
        p.inputs,
        vec![
            ("i0".to_owned(), Scalar::Bool),
            ("i1".to_owned(), Scalar::UInt(6))
        ]
    );
}

/// A type `SInt[(s0[0] + s1)]` printed after `s0.pop()` would mean another
/// width, so the name loses the expression (seed 416 of the typed mode).
#[test]
fn a_write_to_a_root_drops_the_types_that_read_it() {
    let width = |root: &str| {
        Ty::SInt(SExpr::Binary(
            SBin::Add,
            Box::new(SExpr::Index(
                Box::new(SExpr::Name(root.to_owned())),
                Box::new(SExpr::Int(BigInt::from(0), Radix::Dec)),
            )),
            Box::new(SExpr::Name("s1".to_owned())),
        ))
    };
    let hw = |name: &str, ty: Ty| Hw {
        expr: HExpr::Name(name.to_owned()),
        ty: Some(ty),
        types: vec![Scalar::SInt(3)],
        mutable: false,
    };
    let mut ctx = Ctx {
        hw: vec![
            hw("l0", width("s0")),
            hw("l1", width("s00")),
            hw("l2", Ty::Bool),
        ],
        ..Ctx::default()
    };
    ctx.forget("s0");
    let kept: Vec<bool> = ctx.hw.iter().map(|h| h.ty.is_some()).collect();
    assert_eq!(kept, [false, true, true]);
}
