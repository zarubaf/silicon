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
