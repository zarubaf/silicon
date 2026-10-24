// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::eval::concrete;
use crate::program::{PTy, Place, Ports, Radix, SBin, render_items};
use num_bigint::BigInt;
use proptest::strategy::ValueTree;
use proptest::test_runner::TestRunner;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn tapes(count: usize) -> Vec<Vec<u32>> {
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
pub(super) fn stmts_of_body(body: &[Stmt]) -> Vec<&Stmt> {
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

/// The mean program stays small: at most 4950 bytes over these 256 tapes.
#[test]
fn the_mean_program_stays_small() {
    const TAPES: usize = 256;
    let total: usize = tapes(TAPES)
        .into_iter()
        .filter_map(|tape| build(tape).ok())
        .map(|p| p.text().len())
        .sum();
    assert!(total / TAPES <= 4950, "the mean is {} bytes", total / TAPES);
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
        ("pop", s.pops + s.pop_fallbacks, s.pop_fallbacks),
        (
            "mut call",
            s.mut_calls + s.mut_call_fallbacks,
            s.mut_call_fallbacks,
        ),
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

/// The nesting depth of a value of type `t` (spec 5.5): 1 for a part that
/// is no container, else 1 plus the largest depth of an element, a field,
/// or an element type.
fn value_depth(t: &STy) -> u32 {
    match t {
        STy::Tuple(ts) => 1 + ts.iter().map(value_depth).max().unwrap_or(0),
        STy::Array(t, _) | STy::List(t) => 1 + value_depth(t),
        STy::Record(r) => {
            1 + r
                .fields
                .iter()
                .map(|(_, t)| value_depth(t))
                .max()
                .unwrap_or(0)
        }
        _ => 1,
    }
}

/// The depth draw of the budget mode is `1..=8`. At least half of 256
/// programs hold a container with a depth of at least 2, so the draw
/// reaches the depth of a value (spec 5.5).
#[test]
fn programs_hold_containers_for_the_depth_draw() {
    const TAPES: usize = 256;
    let mut deep = 0;
    let mut deepest = 0;
    for tape in tapes(TAPES) {
        let p = build(tape);
        assert!(p.is_ok(), "a program faults: {p:?}");
        let Ok(p) = p else { continue };
        let lets = stmts_of(&p.items).into_iter().filter_map(|s| match s {
            Stmt::StaticLet(_, t, _) | Stmt::MutLet(_, t, _) => Some(t),
            _ => None,
        });
        let consts = p.items.iter().filter_map(|i| match i {
            Item::Const { ty, .. } => Some(ty),
            _ => None,
        });
        let depth = lets.chain(consts).map(value_depth).max().unwrap_or(1);
        deep += usize::from(depth >= 2);
        deepest = deepest.max(depth);
    }
    assert!(deep * 2 >= TAPES, "{deep} of {TAPES} programs");
    assert!(deepest >= 4, "the deepest value has the depth {deepest}");
}

/// The names of the effectful functions of `p` (a `diagnostic` in the body,
/// or a call of an effectful function) and of the consts that hold one.
fn effectful(p: &Program) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    loop {
        let before = names.len();
        for i in &p.items {
            match i {
                Item::MutFn(f) => {
                    let calls = f
                        .pre
                        .iter()
                        .any(|s| matches!(s, Stmt::MutCall { f, .. } if names.contains(f)));
                    if f.diag.is_some() || calls {
                        names.insert(f.name.clone());
                    }
                }
                Item::Const {
                    name,
                    value: SExpr::Name(target),
                    ..
                } if names.contains(target) => {
                    names.insert(name.clone());
                }
                _ => {}
            }
        }
        if names.len() == before {
            return names;
        }
    }
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
            // The call of a module body, or the call of a nested function.
            let call = (t.starts_with("let s") || t.starts_with("let r0"))
                && t.contains(": Int = ")
                && uses == 1;
            // A function value is no call; `diagnostic` may show it.
            let shown = t.starts_with("diagnostic(") && uses == 1;
            assert!(
                declaration || held || call || shown,
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

/// A register declared with `SInt[(s0[0] + s1)]` and driven after `s0.pop()`
/// must not print that width in the resize of its driver.
#[test]
fn a_write_to_a_root_drops_the_type_of_a_register_driver() {
    let width = Ty::SInt(SExpr::Binary(
        SBin::Add,
        Box::new(SExpr::Index(
            Box::new(SExpr::Name("s0".to_owned())),
            Box::new(SExpr::Int(BigInt::from(0), Radix::Dec)),
        )),
        Box::new(SExpr::Name("s1".to_owned())),
    ));
    let hw = |name: &str, ty: Ty, scalar: Scalar| Hw {
        expr: HExpr::Name(name.to_owned()),
        ty: Some(ty),
        types: vec![scalar],
        mutable: false,
    };
    let mut ctx = Ctx {
        envs: vec![Env::default()],
        hw: vec![
            hw(
                "i0",
                super::hw::literal_ty(Scalar::SInt(5)),
                Scalar::SInt(5),
            ),
            hw("r0", width, Scalar::SInt(3)),
        ],
        ..Ctx::default()
    };
    ctx.forget("s0");
    let mut b = Builder::new(vec![]);
    let mut out = Vec::new();
    assert!(b.close_regs(&ctx, vec!["r0".to_owned()], &mut out).is_ok());
    let items = vec![Item::Module {
        name: "M0".to_owned(),
        params: vec![],
        clocked: true,
        body: out,
    }];
    let text = render_items(&items);
    assert!(text.contains("resize"), "{text}");
    assert!(!text.contains("s0"), "{text}");
}

/// The record lines cover each field that the oracle compares: a frame, a
/// digest name, a readable name with arguments, a record in a loop, and a
/// parent record after the record of a child.
#[test]
fn the_records_cover_frames_names_and_order() {
    const TAPES: usize = 256;
    let (mut frames, mut digests, mut args, mut resumed) = (0, 0, 0, 0);
    for tape in tapes(TAPES) {
        let Ok(p) = build(tape) else { continue };
        let names: Vec<&str> = p
            .records()
            .iter()
            .filter_map(|r| r.split(' ').nth(3))
            .collect();
        let back = |i: usize| names[..i].contains(&names[i]) && names[i - 1] != names[i];
        frames += usize::from(p.records().iter().any(|r| r.contains("((call ")));
        digests += usize::from(names.iter().any(|n| n.contains("$0h")));
        args += usize::from(names.iter().any(|n| n.contains('$') && !n.contains("$0h")));
        resumed += usize::from((1..names.len()).any(back));
    }
    let want = TAPES / 32;
    assert!(
        frames >= want && digests >= want && args >= want && resumed >= want,
        "frames {frames}, digests {digests}, arguments {args}, resumed {resumed}"
    );
}

/// A module parameter of a finite type takes its argument as a plain
/// integer and as a conversion, and one identity occurs under both
/// spellings (spec 7.1, #188).
#[test]
fn the_arguments_cover_converted_identities() {
    const TAPES: usize = 256;
    let (mut params, mut converted, mut aliased) = (0, 0, 0);
    for tape in tapes(TAPES) {
        let mut b = Builder::new(tape);
        let Ok(p) = b.program() else { continue };
        let finite = p.items.iter().any(|i| {
            matches!(i, Item::Module { params, .. }
                if params.iter().any(|(_, t)| matches!(t, STy::UInt(_) | STy::SInt(_))))
        });
        params += usize::from(finite);
        converted += usize::from(b.stats.converted_args > 0);
        aliased += usize::from(b.stats.aliased_args > 0);
    }
    let want = TAPES / 32;
    assert!(
        params >= want && converted >= want && aliased >= want,
        "parameters {params}, conversions {converted}, aliases {aliased}"
    );
}

/// The value of a record line, after its message `(string "dK")`.
fn record_value(line: &str) -> Option<&str> {
    let (_, tail) = line.split_once("(string \"d")?;
    let (_, value) = tail.split_once("\") ")?;
    value.strip_suffix(')')
}

/// The records show each kind of static value that a `diagnostic` takes:
/// a string, a tuple, an array, a record, a list, a function, and a finite
/// integer (spec 7.1, 8.2). Each kind occurs in 1 program in 32.
#[test]
fn the_records_cover_the_kinds_of_values() {
    const TAPES: usize = 256;
    const KINDS: [&str; 10] = [
        "(int ",
        "(bool ",
        "(string ",
        "(tuple ",
        "(array ",
        "(record ",
        "(list ",
        "(function ",
        "(uint ",
        "(sint ",
    ];
    let mut with = BTreeMap::<&str, usize>::new();
    for tape in tapes(TAPES) {
        let Ok(p) = build(tape) else { continue };
        let values: Vec<&str> = p.records().iter().filter_map(|r| record_value(r)).collect();
        for kind in KINDS {
            let seen = values.iter().any(|v| v.starts_with(kind));
            *with.entry(kind).or_default() += usize::from(seen);
        }
    }
    for (kind, n) in &with {
        assert!(n * 32 >= TAPES, "{kind} occurs in {n} of {TAPES}: {with:?}");
    }
}

/// The positions `(call <name> <line> <col>)` of the frames of a record line.
fn frame_positions(record: &str) -> Vec<(usize, usize)> {
    let frames = record.split_once(" (").map_or("", |(_, t)| t);
    frames
        .split("(call ")
        .skip(1)
        .filter_map(|f| {
            let mut parts = f.split(' ').skip(1);
            let line = parts.next()?.parse().ok()?;
            let col = parts.next()?.trim_end_matches(')').parse().ok()?;
            Some((line, col))
        })
        .collect()
}

/// The records show nested call frames: a record with two or more frames,
/// whose inner call is by name, as a receiver, or through a function value
/// (spec 8.2). The test reads the executed frames of the records and the
/// text at the position of each inner call. Each shape occurs in 1 program
/// in 32.
#[test]
fn the_records_cover_nested_frames() {
    const TAPES: usize = 256;
    let (mut nested, mut named, mut receivers, mut values) = (0, 0, 0, 0);
    for tape in tapes(TAPES) {
        let Ok(p) = build(tape) else { continue };
        let text = p.text();
        let lines: Vec<&str> = text.lines().collect();
        let (mut has, mut by_name, mut by_receiver, mut by_value) = (false, false, false, false);
        for record in p.records() {
            let frames = frame_positions(record);
            has |= frames.len() >= 2;
            for (line, col) in frames.into_iter().skip(1) {
                let at = lines
                    .get(line - 1)
                    .and_then(|l| l.get(col - 1..))
                    .unwrap_or_default();
                let word: String = at.chars().take_while(char::is_ascii_alphanumeric).collect();
                let rest = &at[word.len()..];
                if rest.starts_with('.') {
                    by_receiver = true;
                } else if word.starts_with('F') {
                    by_value = true;
                } else {
                    by_name = true;
                }
            }
        }
        nested += usize::from(has);
        named += usize::from(by_name);
        receivers += usize::from(by_receiver);
        values += usize::from(by_value);
    }
    let want = TAPES / 32;
    assert!(
        [nested, named, receivers, values]
            .iter()
            .all(|n| *n >= want),
        "nested {nested}, by name {named}, receivers {receivers}, values {values}"
    );
}

/// The forms of enums and `match` that a program holds, by name.
fn enum_forms(p: &Program, s: &Stats) -> [(&'static str, bool); 24] {
    let port = |ports: &[(String, Scalar)]| ports.iter().any(|(n, _)| n.contains(".tag"));
    let ports = p.ports();
    [
        (
            "enum item",
            p.text().starts_with("enum ") || p.text().contains("\nenum "),
        ),
        ("static constructor", s.enum_ctors > 0),
        ("enum zero", s.enum_zeros > 0),
        ("static reinterpret", s.enum_unpacks > 0),
        ("enum const", s.enum_consts > 0),
        ("enum static let", s.enum_lets > 0),
        ("enum diagnostic", s.enum_diagnostics > 0),
        ("enum port", port(&ports.inputs) || port(&ports.outputs)),
        ("enum register", s.hw_regs > 0),
        ("enum wire", s.hw_wires > 0),
        ("hardware constructor", s.hw_ctors > 0),
        ("hardware reinterpret of bits", s.hw_unpacks > 0),
        ("hardware enum let", s.hw_lets > 0),
        ("bits of an enum name", s.hw_bits > 0),
        ("enum probe", s.enum_probes > 0),
        ("reinterpret of an enum value", s.enum_bits > 0),
        ("static match on an enum", s.static_enum_matches > 0),
        ("hardware match on an enum", s.hw_enum_matches > 0),
        ("static match", s.static_matches > 0),
        ("static binder", s.static_binders > 0),
        ("hardware match", s.hw_matches > 0),
        ("hardware binder", s.hw_binders > 0),
        ("nested match", s.nested_matches > 0),
        (
            "complete match without _",
            s.complete_matches > 0 || s.hw_complete_matches > 0,
        ),
    ]
}

/// Each form of enums and `match` occurs in at least 10% of 256 programs.
#[test]
fn programs_cover_enums_and_match() {
    const TAPES: usize = 256;
    let mut with = BTreeMap::<&str, usize>::new();
    for tape in tapes(TAPES) {
        let mut b = Builder::new(tape);
        let p = b.program();
        assert!(p.is_ok(), "a program faults: {p:?}");
        let Ok(p) = p else { continue };
        for (form, seen) in enum_forms(&p, &b.stats) {
            *with.entry(form).or_default() += usize::from(seen);
        }
        *with.entry("finite match").or_default() += usize::from(b.stats.finite_matches > 0);
        *with.entry("hardware match on an expression").or_default() +=
            usize::from(b.stats.hw_expr_scrutinees > 0);
    }
    assert_eq!(with.len(), 26, "{with:?}");
    for (form, n) in &with {
        assert!(
            n * 10 >= TAPES,
            "{form} occurs in {n} of {TAPES} programs: {with:?}"
        );
    }
}

/// The work of the generator is bounded: the largest text, the most arms
/// of a match, and the most open matches stay under fixed caps over 256
/// tapes. The elaborator budget of a `match` is the subject of the
/// budget mode of `diff-si`.
#[test]
fn matches_stay_within_the_work_caps() {
    const TAPES: usize = 256;
    const TEXT: usize = 16 * 1024;
    const ARMS: usize = 5;
    let (mut text, mut arms, mut levels) = (0, 0, 0);
    for tape in tapes(TAPES) {
        let mut b = Builder::new(tape);
        let Ok(p) = b.program() else { continue };
        text = text.max(p.text().len());
        arms = arms.max(b.stats.max_arms);
        assert_eq!(b.match_level, 0);
        levels = levels.max(b.stats.max_level);
    }
    assert!(text <= TEXT, "the largest text has {text} bytes");
    assert!(arms <= ARMS, "the largest match has {arms} arms");
    assert!(arms >= 3, "the tapes make no wide match: {arms}");
    assert!(levels <= NESTING, "matches open {levels} levels");
    assert!(levels >= 2, "no match nests: {levels}");
}

/// The tags of an enum are distinct, and an enum with every tag of its
/// tag type has exactly `2^W` variants.
#[test]
fn enums_have_distinct_tags() {
    for tape in tapes(256) {
        let mut b = Builder::new(tape);
        let Ok(p) = b.program() else { continue };
        for item in &p.items {
            let Item::Enum(def) = item else { continue };
            let tags: BTreeSet<_> = def.variants.iter().map(|v| v.tag.clone()).collect();
            assert_eq!(tags.len(), def.variants.len(), "{def:?}");
            assert!(def.variants.len() <= 1 << def.tag_width, "{def:?}");
            assert!(def.payload_bits() <= 2 * 257, "{def:?}");
        }
    }
}

/// The forms of ports that a program holds, by name. A form counts at an
/// executed declaration or call of a reached frame.
fn port_forms(p: &Program, s: &Stats) -> [(&'static str, bool); 21] {
    let ports = p.ports();
    // Two keys of one family whose order as numbers differs from their order
    // as text, in the vectors of the top: `2` and `10`.
    let mut keys: BTreeMap<String, Vec<u32>> = BTreeMap::new();
    for (name, _) in ports.inputs.iter().chain(&ports.outputs) {
        let Some((base, rest)) = name.split_once('[') else {
            continue;
        };
        let key: Option<u32> = rest.split(']').next().and_then(|k| k.parse().ok());
        keys.entry(base.to_owned()).or_default().extend(key);
    }
    let sort_pair = keys.values().any(|ks| {
        ks.iter()
            .any(|a| ks.iter().any(|b| a < b && a.to_string() > b.to_string()))
    });
    let as_keys = s.as_strings + s.as_computed + s.as_portkeys + s.as_joins;
    [
        ("family in a loop", s.fam_loops > 0),
        ("family in an arm", s.fam_arms > 0),
        ("family at the top", s.fam_tops > 0),
        ("own input entry selected", s.own_selects > 0),
        ("own output entry bound", s.own_targets > 0),
        ("second loop reads the keys", s.second_loops > 0),
        ("child input entry bound", s.child_binds > 0),
        ("child output entry read", s.child_reads > 0),
        ("as String key", s.as_strings > 0),
        ("as computed key", s.as_computed > 0),
        ("as scalar PortKey", s.as_portkeys > 0),
        ("as PortKey joins a family", s.as_joins > 0),
        ("as core keyword", s.as_core > 0),
        ("helper with a name", s.helper_names > 0),
        ("helper with a family", s.helper_families > 0),
        ("helper entry selected by another call", s.helper_chains > 0),
        ("empty entry", s.empty_entries > 0),
        ("key sort pair in the top", sort_pair),
        ("family entry", s.fam_loops + s.fam_arms + s.fam_tops > 0),
        ("as key", as_keys > 0),
        ("family in an arm that does not run", s.skipped_families > 0),
    ]
}

/// Each form of ports occurs in at least 10% of 256 programs, a family entry
/// in at least 40%, and an `as` key in at least 30%. The forms of the
/// arm that does not run have their own test of mutants (`ScalarFamily`
/// finds a family with no executed entry).
#[test]
fn programs_cover_families() {
    const TAPES: usize = 256;
    let mut with = BTreeMap::<&str, usize>::new();
    for tape in tapes(TAPES) {
        let mut b = Builder::new(tape);
        let p = b.program();
        assert!(p.is_ok(), "a program faults: {p:?}");
        let Ok(p) = p else { continue };
        for (form, seen) in port_forms(&p, &b.stats) {
            *with.entry(form).or_default() += usize::from(seen);
        }
        assert_eq!(b.stats.port_lost, 0, "a name of the pool reaches no output");
    }
    assert_eq!(with.len(), 21, "{with:?}");
    for (form, n) in &with {
        let least = match *form {
            "family entry" => 40,
            "as key" => 30,
            "family in an arm that does not run" => 5,
            _ => 10,
        };
        assert!(
            n * 100 >= TAPES * least,
            "{form} occurs in {n} of {TAPES} programs: {with:?}"
        );
    }
}

/// The port forms draw from their own tape: a program with handle forms
/// has port forms at about the rate of all programs.
#[test]
fn port_forms_do_not_follow_the_handle_forms() {
    const TAPES: usize = 256;
    let (mut ports, mut hands, mut both) = (0, 0, 0);
    for tape in tapes(TAPES) {
        let mut b = Builder::new(tape);
        let Ok(p) = b.program() else { continue };
        let s = &b.stats;
        let port = port_forms(&p, s).iter().any(|(_, seen)| *seen);
        let hand = s.bind_wire_calls
            + s.bind_reg_calls
            + s.bind_input_calls
            + s.bind_mem_calls
            + s.direct_mems
            + s.declare_calls
            + s.list_groups
            > 0;
        ports += usize::from(port);
        hands += usize::from(hand);
        both += usize::from(port && hand);
    }
    // Compare `both / hands` with `ports / TAPES`, within a factor of 1.3.
    assert!(hands >= 32 && ports >= 32, "{ports} {hands}");
    assert!(
        both * TAPES * 10 >= ports * hands * 7,
        "ports {ports}, hands {hands}, both {both}"
    );
    assert!(
        both * TAPES * 7 <= ports * hands * 10,
        "ports {ports}, hands {hands}, both {both}"
    );
}

/// The caps of the port forms hold for the plans of 256 programs: at most
/// 3 families and 6 entries of a family, at most 4 keyed ports, and at most
/// 4 calls of helpers that declare a port in a module (each call counts), at
/// most 24 ports in a program, and each key below 32.
#[test]
fn port_forms_stay_in_caps() {
    use ports::Form;
    let mut most = (0, 0, 0, 0, 0);
    for tape in tapes(256) {
        let mut b = Builder::new(tape);
        let Ok(_) = b.program() else { continue };
        let mut all = 0;
        for sig in &b.sigs {
            let declared = sig.plan.declared(&b.port_helpers);
            all += declared.len();
            let mut entries = BTreeMap::<&str, usize>::new();
            for d in &declared {
                if let Some(k) = d.public.key {
                    assert!(k < 32, "{:?}", d.public);
                    *entries.entry(d.public.base.as_str()).or_default() += 1;
                }
            }
            let keyed: usize = sig
                .plan
                .forms
                .iter()
                .map(|f| match f {
                    Form::Keyed { .. } => 1,
                    Form::KeyedLoop { count, .. } => *count as usize,
                    _ => 0,
                })
                .sum();
            let calls: usize = sig
                .plan
                .forms
                .iter()
                .map(|f| match f {
                    Form::Call { calls, .. } => *calls as usize,
                    _ => 0,
                })
                .sum();
            let families = sig
                .plan
                .forms
                .iter()
                .filter(|f| matches!(f, Form::Family { .. }))
                .count();
            assert!(entries.values().all(|&n| n <= 6), "{entries:?}");
            assert!(families <= 3 && keyed <= 4 && calls <= 4, "{:?}", sig.plan);
            most = (
                most.0.max(families),
                most.1.max(entries.values().copied().max().unwrap_or(0)),
                most.2.max(keyed),
                most.3.max(calls),
                most.4.max(all),
            );
        }
        assert!(all <= 24, "{all} ports");
    }
    // The caps are in reach.
    assert!(
        most.0 >= 2 && most.1 >= 3 && most.2 >= 2 && most.3 >= 4,
        "{most:?}"
    );
}

/// The ports of the top follow the plan of its signature: each entry and
/// keyed port of the plan with a type is a port with that type, and the
/// walk of the twin finds no other port than these and the plain ports of
/// the signature.
#[test]
fn the_plan_gives_the_ports_of_the_top() {
    // The owner of a leaf name: `a0[3].tag` belongs to `a0[3]`.
    let owners = |side: &[(String, Scalar)]| -> BTreeSet<String> {
        side.iter()
            .map(|(n, _)| n.split('.').next().unwrap_or(n).to_owned())
            .collect()
    };
    let mut checked = 0;
    for tape in tapes(256) {
        let mut b = Builder::new(tape);
        let Ok(p) = b.program() else { continue };
        let Some(sig) = b.sigs.first() else { continue };
        let env = Env::of(&sig.params, &p.args);
        let ports = p.ports();
        let mut inputs: BTreeSet<String> = sig
            .inputs
            .iter()
            .map(|(n, _)| n.clone())
            .chain(sig.enum_inputs.iter().map(|(n, _)| n.clone()))
            .collect();
        let mut outputs: BTreeSet<String> = sig
            .outputs
            .iter()
            .map(|(n, _)| n.clone())
            .chain(sig.enum_outputs.iter().map(|(n, _)| n.clone()))
            .collect();
        for d in sig.plan.declared(&b.port_helpers) {
            let PTy::Data(t) = &d.ty else { continue };
            let want = (d.public.to_string(), concrete(t, &env, &b.scope).unwrap());
            let (side, names) = match d.dir {
                ports::Dir::In => (&ports.inputs, &mut inputs),
                ports::Dir::Out => (&ports.outputs, &mut outputs),
            };
            assert!(side.contains(&want), "{want:?} missing in {side:?}");
            names.insert(want.0);
            checked += 1;
        }
        assert_eq!(owners(&ports.inputs), inputs, "{:?}", sig.plan);
        assert_eq!(owners(&ports.outputs), outputs, "{:?}", sig.plan);
    }
    assert!(checked > 100, "{checked}");
}

/// A port draw comes from the port tape only, also while the hand tape or
/// the side tape is swapped in (tape isolation): the other tapes keep all
/// of their numbers.
#[test]
fn port_draws_stay_on_the_port_tape() {
    let left = |b: &Builder| {
        (
            b.tape.numbers.len(),
            b.side.numbers.len(),
            b.hand.numbers.len(),
            b.port.numbers.len(),
        )
    };
    for outer in [Some(Lane::Hand), Some(Lane::Side), None] {
        let mut b = Builder::new(vec![7; 16]);
        let before = left(&b);
        let draw = |b: &mut Builder| {
            b.on_port(|b| {
                b.tape.below(9);
            });
        };
        match outer {
            Some(Lane::Hand) => b.on_hand(draw),
            Some(_) => b.on_side(draw),
            None => draw(&mut b),
        }
        let after = left(&b);
        // Only the port tape (the fourth count) loses a number.
        assert_eq!(
            (after.0, after.1, after.2, after.3 + 1),
            before,
            "{before:?} {after:?}"
        );
    }
}
