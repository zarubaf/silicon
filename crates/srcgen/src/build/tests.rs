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

/// The mean program stays small: at most 5600 bytes over these 256 tapes.
#[test]
fn the_mean_program_stays_small() {
    const TAPES: usize = 256;
    let total: usize = tapes(TAPES)
        .into_iter()
        .filter_map(|tape| build(tape).ok())
        .map(|p| p.text().len())
        .sum();
    assert!(total / TAPES <= 5600, "the mean is {} bytes", total / TAPES);
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
fn port_forms(p: &Program, s: &Stats) -> [(&'static str, bool); 32] {
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
        ("child read through a temporary", s.temp_reads > 0),
        ("temporary tuple", s.temp_tuples > 0),
        ("temporary array", s.temp_arrays > 0),
        ("temporary struct literal", s.temp_records > 0),
        ("temporary helper result", s.temp_helpers > 0),
        ("child write through a local", s.temp_writes > 0),
        ("local tuple of instances", s.write_tuples > 0),
        ("local array of instances", s.write_arrays > 0),
        ("local struct of instances", s.write_records > 0),
        ("container with another instance", s.mixed_slots > 0),
        (
            "two reads through containers of one child",
            s.temp_pairs > 0,
        ),
    ]
}

/// Each form of ports occurs in at least 10% of 256 programs, a family entry
/// in at least 40%, and an `as` key in at least 30%. The forms of the
/// arm that does not run have their own test of mutants (`ScalarFamily`
/// finds a family with no executed entry). A read of a child through a
/// temporary container (#368) occurs in at least 10% of the programs, and
/// so does each container: a tuple, an array, a struct literal, and a
/// helper result.
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
    assert_eq!(with.len(), 32, "{with:?}");
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

/// FNV-1a of a text: a stable fingerprint without a dependency.
fn fingerprint(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// The fingerprints of the texts of the programs of `tapes(256)`, from the
/// builder before the `@field` forms.
const PINNED: [u64; 256] = [
    0xc0ed_37dd_2468_ec4b,
    0xa8eb_0b1b_8313_04c7,
    0x9941_f5d3_568f_720a,
    0x14c0_82d8_2aaa_fa96,
    0xb03d_cc8c_a91f_19dd,
    0x6b93_5460_81da_9911,
    0x141f_abb8_1ae4_a6b7,
    0x47f0_3e19_aa53_2a84,
    0x74fc_6885_5406_2160,
    0xf617_cc45_0662_098f,
    0xe07f_3ad8_cff1_a81d,
    0x12bd_d504_0260_7768,
    0x4177_b275_da71_ba9a,
    0x195e_fdcb_8bf7_0503,
    0x50ae_76d4_3d06_d063,
    0x1d55_b9a6_5841_dbd5,
    0x9e2b_2089_c4f3_7927,
    0xfd24_b3b3_7307_d9cf,
    0x9f4f_666c_18c1_368c,
    0xbd4e_a01b_c662_2561,
    0x58ce_cb1e_be5c_e693,
    0xc5bd_59c1_00fe_f9e4,
    0x4968_c750_d957_f53c,
    0xe592_c313_2014_95e4,
    0x8011_50a8_437b_44ea,
    0x8d6b_8e0c_7504_b7e6,
    0x87c5_1d91_3f23_2d89,
    0xe2d4_86f8_54b0_421d,
    0xca30_9318_fcc0_528d,
    0x7dab_b8ab_6a5e_cdb5,
    0xa260_1212_327c_ddea,
    0xc277_ed0f_bb05_204f,
    0x2d4a_4865_7dc4_dd69,
    0xc53b_4aec_6890_0b41,
    0x171c_ecb6_ea5c_9e87,
    0xa7e7_c280_e038_6a04,
    0x2d15_a7ef_38c0_f2fa,
    0x12fd_5949_8910_f5fc,
    0x5637_910e_2c58_720d,
    0x23fa_44e0_7e87_47d0,
    0xc857_dff3_1190_83ce,
    0x86e4_bc88_8325_78f7,
    0x5d61_d7ea_305f_2881,
    0x5b9c_8786_841b_0ab0,
    0x3b98_c1d4_4805_0199,
    0xf6b2_2ab3_01b1_8da4,
    0x27fe_a920_b37a_5f92,
    0x08ed_2987_3432_c60e,
    0xbd85_47e4_f961_bd35,
    0x8554_ccc8_3d73_2d01,
    0x41b4_565c_c9b5_28f4,
    0x04f4_40e5_f2a5_44f7,
    0xde8e_5a0b_239b_927c,
    0x94da_02cf_5984_01e7,
    0x647e_3194_9334_6be6,
    0xa9af_c4c3_cd9d_c760,
    0x1d64_ed82_448a_889d,
    0xbe6c_7b8b_b0ab_b2e3,
    0xcc97_f79c_9923_3d11,
    0x0e05_b549_82fc_c8ab,
    0x0db7_79f4_a5f6_af9e,
    0x2df3_02d4_57a6_fc78,
    0x3ef6_d4b6_aad4_c9b3,
    0x33e0_df56_25d8_d451,
    0x246e_ef2e_7741_96a6,
    0x53a1_3ecb_f5e5_ee5f,
    0x8fd1_a68a_1955_1925,
    0x20c3_99fc_0363_9c54,
    0x9752_ac15_1005_519a,
    0x2df0_0bb4_6c21_7b2c,
    0x21ac_e5b5_9be1_72d9,
    0x0234_eda4_3b03_c0e9,
    0x432b_832c_c474_053f,
    0x76e7_8716_711b_e828,
    0xff37_e3de_b8da_f3f9,
    0x418c_2baf_f107_7e6c,
    0x4269_3de6_f353_b24f,
    0xcac7_1f0d_da88_f3f4,
    0xb12b_2fc9_d290_b955,
    0xbf9b_7c8a_53fc_8522,
    0x71a9_c6f4_1bed_ed76,
    0xfef2_9d66_085e_c0d0,
    0x3023_f351_78ae_249c,
    0x1740_f030_f9a4_4dca,
    0x03b5_fc93_076c_768f,
    0x9e32_3e5c_4a3e_c260,
    0x0925_9e5d_8230_0487,
    0xfb86_d55a_4816_62f6,
    0x77d7_b293_7c60_5a5e,
    0x953c_8e75_1827_5f6a,
    0xd1a8_1281_fddd_f7c9,
    0x7922_28ed_1bd5_5a11,
    0xfae4_4a82_5799_8874,
    0xbcd8_6b59_bf9c_2727,
    0x8e74_3b60_2ea3_3622,
    0x4845_33ac_1251_4e9d,
    0x9919_3424_022f_d355,
    0x0d75_fd2b_d221_6a5a,
    0x14b9_2228_e744_46bb,
    0x592a_01c4_a8c0_476b,
    0xaa14_6f49_7123_b6f9,
    0xf711_9871_70d3_b97d,
    0xfca4_cf2d_ed9a_f959,
    0xb8e4_59f3_929b_ca79,
    0x8f12_aa3b_7c03_667d,
    0xab15_598a_0ce7_181f,
    0x85fb_9b58_5b59_f75b,
    0x41df_6f8b_0e84_ec68,
    0x969b_54c1_30c4_748d,
    0x5157_0306_301c_31b2,
    0x36b6_23a9_799f_0dfc,
    0x2841_1a3b_93bb_d03c,
    0xfb96_0763_3bee_4fa8,
    0x165d_fdd8_6e92_723a,
    0x989c_94ab_ff0e_39e2,
    0x8191_40a9_8947_7123,
    0x7d3a_c693_b278_7460,
    0xce76_d8aa_e3a3_2c1f,
    0x3e33_8033_1aa6_9d22,
    0xe095_777d_b7b6_8c6b,
    0xf8e9_5057_ad72_9f6b,
    0x01ad_ae1d_43a4_9f1a,
    0x552e_09f3_2770_5ec5,
    0x71c0_7899_7466_ca6d,
    0xf84d_38fb_ecd2_8de1,
    0x2531_b5c0_1fbe_c035,
    0x80ab_88b5_bd51_3f80,
    0x4baa_2456_7f64_cbd2,
    0x1c1c_512c_dfa0_8517,
    0xfb34_42f6_84ab_9e5b,
    0xee40_1071_37a6_54d8,
    0x59e1_7edf_33e4_7c7a,
    0xf544_bbf6_f0bc_2569,
    0x759f_98ab_4497_0155,
    0xe911_40d0_987c_fa0b,
    0x7a2d_d3dc_2d67_1da5,
    0x8acb_21a4_9823_37d5,
    0x6f61_1ae8_5ba9_1ae5,
    0x8a04_56f8_2515_7b66,
    0x63af_60b5_989f_4bf6,
    0x0cca_b04a_504f_4ebb,
    0xfead_eed0_d1a1_be7c,
    0xc216_4ea1_7eee_56ee,
    0x2fee_779f_c70d_ffa8,
    0xc274_7067_6952_c7a1,
    0x2c33_48ca_1315_2e84,
    0xb850_3519_c594_915a,
    0x28b0_3a07_d31c_46cc,
    0x6891_8abc_c5dd_be05,
    0x3c44_86b5_e000_4315,
    0xd815_8ba6_8712_1898,
    0xc688_b957_c2a6_ee47,
    0xbe79_72ab_be7a_bcf9,
    0x0e32_3065_eba5_0055,
    0xaa18_0e9c_39cb_d5b5,
    0x6df3_5b9c_e79e_eb31,
    0xa7d9_95c2_ede6_9ab8,
    0xe9e1_3c1e_8f44_02cf,
    0x3bc0_7159_bc00_20eb,
    0x5268_214e_0f81_2df9,
    0xda9c_c83b_2d19_0a83,
    0x826c_dbb8_dd02_25ae,
    0x1bc9_42d5_c91e_8364,
    0x305b_7a3e_49f1_7d83,
    0xdff0_2d89_d575_138a,
    0xc5d9_c07e_9113_53e1,
    0x367f_0540_fcc9_0925,
    0x1af3_4560_7dbd_410a,
    0x69a7_93fa_93a5_23a0,
    0xfe9e_f4ac_bbee_1e35,
    0x6ac6_8e2a_9214_d845,
    0x140c_5a28_e593_ab26,
    0x12c5_6017_96e4_772f,
    0xc81a_b7de_30c7_4fe8,
    0xeae3_fa0a_22ed_8450,
    0x22a7_43e6_ea97_b1d1,
    0xa9ad_14c7_11c9_7009,
    0xfc58_dda1_d825_c49c,
    0x17e4_844f_f9c3_de96,
    0x9bcb_cc77_565a_b758,
    0xc382_2105_f4a0_d8ac,
    0x26de_c33a_61fc_2cd9,
    0x2574_d25a_ac2a_2305,
    0x9c85_d8c7_8011_9375,
    0xbd6b_86c8_b30a_e20e,
    0xa615_7a2c_1211_2fab,
    0xfb9c_9376_a916_1bb7,
    0x34a1_3a34_de99_a149,
    0x3496_4fa3_9e27_e797,
    0x53d0_6c1f_7ff6_15cb,
    0xefca_2e3b_795e_5236,
    0x4526_1355_a928_2161,
    0xbc49_b49f_3019_d14e,
    0x084c_ee35_4327_4ea9,
    0x6a17_3a67_a6cc_aa5f,
    0xddec_8def_78b7_f118,
    0xad34_61ed_6ace_2db1,
    0xa6dc_c757_98e0_0d1c,
    0x5c3c_39dd_a805_98cd,
    0x403b_f33b_9c75_d62f,
    0xe7a6_3a14_7999_3e01,
    0x673d_617b_b858_cb77,
    0xee8e_2f97_e93b_9b47,
    0x988b_11e8_f417_fe87,
    0xe9dd_8ed2_a08c_6ece,
    0x5d3d_04fb_f551_1da1,
    0xa8cd_430f_e20e_03f1,
    0x806f_72a6_9444_b1af,
    0x1d3f_7ca1_4134_2f81,
    0xf144_71fb_72b6_a980,
    0xdf0d_8bdb_6669_1c57,
    0x7cc2_e66d_f9d0_8c86,
    0xe284_a946_0808_49db,
    0x60ef_b906_4587_936b,
    0xe144_b544_841a_c3b2,
    0x8b9b_feb3_751f_e4d2,
    0x31b4_2890_97ce_469e,
    0x2c67_92fe_17ca_2199,
    0x43e5_7f3a_262e_3b52,
    0x39d8_e50d_d3d7_d14d,
    0xfd4b_583a_5725_5ee9,
    0xf31a_a816_87d9_10e3,
    0x229b_e798_f1a3_2fa3,
    0x4bd5_648d_7f83_c2ee,
    0x5082_4fc9_52ca_db7b,
    0xe3b0_ea54_b46d_44c9,
    0x11ba_d086_0f89_d42c,
    0x0bf7_3520_e5de_9555,
    0xbf15_c462_1494_a342,
    0xb983_d964_c28e_a343,
    0xf9e2_9d45_b8ae_f34a,
    0x5878_5112_10b5_4011,
    0x3a27_8abe_c8db_d79b,
    0xfc76_25a8_0b45_e67a,
    0x5f44_11b5_de97_24af,
    0x9faf_d38d_e27f_2a8a,
    0x7dac_17f4_e3bc_2d95,
    0xe196_b57f_b158_491b,
    0x4bfa_4300_c911_2cc6,
    0xe669_e59c_df47_3fba,
    0xc8a1_ca76_bc77_f3ad,
    0x85fe_bbbb_0c54_48a8,
    0x857f_a58f_14c6_e03a,
    0xc6cc_910b_f97d_2023,
    0x731a_4563_500c_4266,
    0x4090_c7ae_311f_aa7c,
    0x99d4_2930_8b4b_0101,
    0x25ff_ca53_519b_43b6,
    0x9790_ea5a_2790_827f,
    0xb86d_3568_bfb1_4a43,
    0xdbde_c625_c326_1eda,
    0xcb10_6f02_7b0b_94d8,
    0xee93_00ad_f5d7_4740,
    0x922b_1b3a_743f_1bb3,
    0x077b_55f2_c5ea_ca9c,
    0x1479_b723_234d_9f97,
];

/// A program with no `@field` is the program of the same tape before the
/// form existed: a form draws only from its own tape and adds only text that
/// holds `@field`. At least 40% of the tapes hold no `@field`.
#[test]
fn a_program_without_field_forms_keeps_its_text() {
    let mut kept = 0;
    for (tape, pinned) in tapes(256).into_iter().zip(PINNED) {
        let text = build(tape).map_or_else(|e| e.to_string(), |p| p.text());
        if !text.contains("@field") {
            assert_eq!(fingerprint(&text), pinned, "{text}");
            kept += 1;
        }
    }
    assert!(kept >= 256 / 10, "{kept}");
}
