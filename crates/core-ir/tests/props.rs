// SPDX-License-Identifier: Apache-2.0
//! Property tests over the random designs of `gen`.

use std::collections::{BTreeMap, BTreeSet};

use core_ir::ast::{Design, Dir, Expr, Item, Module, Stmt, Ty};
use core_ir::check::check;
use core_ir::r#gen;
use core_ir::interp::Sim;
use core_ir::text::{canonicalize, parse, print};
use core_ir::typed;
use core_ir::vectors::{parse_input, print_output};
use proptest::collection::vec;
use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::TestRunner;

fn checked(d: &Design) -> typed::Design {
    match check(d) {
        Ok(typed) => typed,
        Err(e) => panic!("{e}\n{}", print(d)),
    }
}

/// A design with a few input lines for its top module.
fn design_and_lines() -> impl Strategy<Value = (Design, Vec<String>)> {
    r#gen::design().prop_flat_map(|d| {
        let typed = checked(&d);
        let top = typed.modules()[typed.top().index()].clone();
        (Just(d), vec(r#gen::inputs(&top), 1..=4))
    })
}

/// `d` with its items, statements, and connections in reverse order.
fn reversed(d: &Design) -> Design {
    let mut out = d.clone();
    out.items.reverse();
    for item in &mut out.items {
        if let Item::Module(m) = item {
            m.stmts.reverse();
            for stmt in &mut m.stmts {
                if let Stmt::Inst { conns, .. } = stmt {
                    conns.reverse();
                }
            }
        }
    }
    out
}

/// The modules of `d` by name.
fn modules(d: &Design) -> BTreeMap<&str, &Module> {
    d.items
        .iter()
        .filter_map(|item| match item {
            Item::Module(m) => Some((m.name.text.as_str(), m)),
            Item::Extern(_) => None,
        })
        .collect()
}

/// The names of the modules that module `m` instantiates.
fn children(m: &Module) -> impl Iterator<Item = &str> {
    m.stmts.iter().filter_map(|s| match s {
        Stmt::Inst { module, .. } => Some(module.text.as_str()),
        _ => None,
    })
}

/// The levels of instances below module `name`.
fn levels(modules: &BTreeMap<&str, &Module>, name: &str) -> u32 {
    modules.get(name).map_or(0, |m| {
        children(m)
            .map(|c| levels(modules, c) + 1)
            .max()
            .unwrap_or(0)
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        failure_persistence: None,
        ..ProptestConfig::default()
    })]

    #[test]
    fn generated_designs_check(d in r#gen::design()) {
        prop_assert!(check(&d).is_ok(), "{:?}\n{}", check(&d).err(), print(&d));
    }

    #[test]
    fn print_parse_round_trip(d in r#gen::design()) {
        let text = print(&d);
        match parse(&text) {
            Ok(parsed) => prop_assert_eq!(parsed.without_spans(), d.without_spans()),
            Err(e) => prop_assert!(false, "{e}\n{text}"),
        }
    }

    #[test]
    fn canonicalize_is_idempotent(d in r#gen::design()) {
        let once = canonicalize(&d);
        prop_assert_eq!(canonicalize(&once), once);
    }

    #[test]
    fn the_canonical_print_ignores_statement_order(d in r#gen::design()) {
        let text = print(&canonicalize(&d));
        prop_assert_eq!(print(&canonicalize(&reversed(&d))), text.clone());
        match parse(&text) {
            Ok(parsed) => prop_assert_eq!(print(&canonicalize(&parsed)), text),
            Err(e) => prop_assert!(false, "{e}\n{text}"),
        }
    }

    #[test]
    fn parser_never_panics(bytes in vec(any::<u8>(), 0..512)) {
        let _ = parse(&String::from_utf8_lossy(&bytes));
    }

    #[test]
    fn checker_never_panics_on_damaged_designs(
        d in r#gen::design(),
        cut in any::<prop::sample::Index>(),
        byte in any::<u8>(),
    ) {
        let mut text = print(&d).into_bytes();
        let at = cut.index(text.len());
        text[at] = byte;
        if let Ok(parsed) = parse(&String::from_utf8_lossy(&text)) {
            let _ = check(&parsed);
        }
    }

    #[test]
    fn the_top_reaches_every_module(d in r#gen::design()) {
        let modules = modules(&d);
        let mut reached = BTreeSet::from([d.top.text.as_str()]);
        let mut work = vec![d.top.text.as_str()];
        while let Some(name) = work.pop() {
            for child in modules.get(name).into_iter().flat_map(|m| children(m)) {
                if reached.insert(child) {
                    work.push(child);
                }
            }
        }
        prop_assert_eq!(reached.len(), modules.len(), "{}", print(&d));
    }

    #[test]
    fn interpreter_never_panics((d, lines) in design_and_lines()) {
        let typed = checked(&d);
        let top = &typed.modules()[typed.top().index()];
        let Ok(mut sim) = Sim::new(&typed) else {
            return Err(TestCaseError::fail("a generated design has no extern"));
        };
        for line in &lines {
            match parse_input(line, top) {
                Ok(inputs) => {
                    let out = print_output(top, &sim.step(&inputs));
                    let pairs = out.trim_end().trim_start_matches("out=(").trim_end_matches(')');
                    let tokens = pairs.split(' ').filter(|t| !t.is_empty()).count();
                    prop_assert_eq!(tokens, 2 * top.outputs().len(), "{}", out);
                }
                Err(e) => prop_assert!(false, "{line}: {e}"),
            }
        }
    }
}

/// What a sample of designs uses: the operations, the reset kinds, the
/// memory depths and write ports, the widths, the instance levels below the
/// top, and the shapes of the instance connections.
#[derive(Default)]
struct Coverage {
    forms: BTreeSet<String>,
    depths: BTreeSet<u32>,
    widths: BTreeSet<u32>,
    levels: u32,
}

impl Coverage {
    fn note(&mut self, form: &str) {
        self.forms.insert(form.to_owned());
    }

    fn expr(&mut self, e: &Expr) {
        let form = match e {
            Expr::Ref(_) => "ref".to_owned(),
            Expr::InstOut { .. } => "inst-out".to_owned(),
            Expr::Const { .. } => "const".to_owned(),
            Expr::Unary { op, arg, .. } => {
                self.expr(arg);
                format!("{op:?}")
            }
            Expr::Binary { op, lhs, rhs, .. } => {
                self.expr(lhs);
                self.expr(rhs);
                format!("{op:?}")
            }
            Expr::Icmp { pred, lhs, rhs, .. } => {
                self.expr(lhs);
                self.expr(rhs);
                format!("{pred:?}")
            }
            Expr::Mux {
                cond, then, els, ..
            } => {
                self.expr(cond);
                self.expr(then);
                self.expr(els);
                "mux".to_owned()
            }
            Expr::Extract { arg, .. } => {
                self.expr(arg);
                "extract".to_owned()
            }
            Expr::Replicate { arg, .. } => {
                self.expr(arg);
                "replicate".to_owned()
            }
            Expr::Read { addr, .. } => {
                self.expr(addr);
                "read".to_owned()
            }
        };
        self.forms.insert(form);
    }

    fn design(&mut self, d: &Design) {
        let modules = modules(d);
        self.levels = self.levels.max(levels(&modules, &d.top.text));
        let instantiated: BTreeSet<&str> = modules.values().flat_map(|m| children(m)).collect();
        for m in modules.values() {
            for s in &m.stmts {
                self.stmt(s);
            }
            self.insts(&modules, m);
            let reads = m.stmts.iter().any(|s| match s {
                Stmt::Assign { expr, .. } => has_read(expr),
                _ => false,
            });
            if reads && instantiated.contains(m.name.text.as_str()) {
                self.note("read-in-child");
            }
        }
        self.paths(&checked(d));
    }

    /// Notes connections out of port order and two siblings that read the
    /// outputs of each other.
    fn insts(&mut self, modules: &BTreeMap<&str, &Module>, m: &Module) {
        let mut reads: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for s in &m.stmts {
            if let Stmt::Inst {
                name,
                module,
                conns,
                ..
            } = s
            {
                let mut insts = BTreeSet::new();
                for c in conns {
                    inst_reads(&c.expr, &mut insts);
                }
                if conns
                    .iter()
                    .any(|c| c.port.text == r#gen::RESET && is_rst(&c.expr))
                {
                    self.note("rst-conn");
                }
                reads.insert(&name.text, insts);
                let child = modules
                    .get(module.text.as_str())
                    .map_or(&[][..], |c| &c.ports);
                let positions: Vec<Option<usize>> = conns
                    .iter()
                    .map(|c| child.iter().position(|p| p.name == c.port))
                    .collect();
                if !positions.is_sorted() {
                    self.note("shuffled-conns");
                }
            }
        }
        for (a, others) in &reads {
            if others
                .iter()
                .any(|b| b != a && reads.get(b).is_some_and(|r| r.contains(a)))
            {
                self.note("handshake");
            }
        }
    }

    /// Notes an output that reads an instance output that reads an input of
    /// the parent combinationally.
    fn paths(&mut self, d: &typed::Design) {
        for m in d.modules() {
            let nexts = m.regs().iter().map(|r| &r.next);
            if m.assigns().iter().chain(nexts).any(reads_output) {
                self.note("output-read");
            }
            for assign in m.assigns() {
                let through = inst_outs(assign).into_iter().any(|(u, o)| {
                    let inst = &m.insts()[u.index()];
                    let typed::Callee::Module(child) = inst.callee else {
                        return false;
                    };
                    d.modules()[child.index()].deps()[o.index()]
                        .iter()
                        .any(|i| reads_input(&inst.inputs[i.index()]))
                });
                if through {
                    self.note("path-through-child");
                }
            }
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { width, expr, .. } => {
                self.widths.insert(width.value);
                self.expr(expr);
            }
            Stmt::Reg { width, reset, .. } => {
                self.widths.insert(width.value);
                match reset {
                    Some(r) => {
                        self.note("reset");
                        self.expr(&r.signal);
                        self.expr(&r.value);
                    }
                    None => self.note("no-reset"),
                }
            }
            Stmt::Mem { depth, .. } => {
                self.depths.insert(depth.value);
            }
            Stmt::Next { expr, .. } | Stmt::Assign { expr, .. } => self.expr(expr),
            Stmt::Write {
                port,
                addr,
                data,
                en,
                ..
            } => {
                if *port == 1 {
                    self.note("second-write-port");
                }
                self.expr(addr);
                self.expr(data);
                self.expr(en);
            }
            Stmt::Inst { conns, .. } => conns.iter().for_each(|c| self.expr(&c.expr)),
        }
    }
}

fn has_read(e: &Expr) -> bool {
    match e {
        Expr::Read { .. } => true,
        Expr::Ref(_) | Expr::InstOut { .. } | Expr::Const { .. } => false,
        Expr::Unary { arg, .. } | Expr::Extract { arg, .. } | Expr::Replicate { arg, .. } => {
            has_read(arg)
        }
        Expr::Binary { lhs, rhs, .. } | Expr::Icmp { lhs, rhs, .. } => {
            has_read(lhs) || has_read(rhs)
        }
        Expr::Mux {
            cond, then, els, ..
        } => has_read(cond) || has_read(then) || has_read(els),
    }
}

/// The instances whose outputs `e` reads.
fn inst_reads<'a>(e: &'a Expr, out: &mut BTreeSet<&'a str>) {
    match e {
        Expr::InstOut { inst, .. } => {
            out.insert(&inst.text);
        }
        Expr::Ref(_) | Expr::Const { .. } => {}
        Expr::Unary { arg, .. } | Expr::Extract { arg, .. } | Expr::Replicate { arg, .. } => {
            inst_reads(arg, out);
        }
        Expr::Read { addr, .. } => inst_reads(addr, out),
        Expr::Binary { lhs, rhs, .. } | Expr::Icmp { lhs, rhs, .. } => {
            inst_reads(lhs, out);
            inst_reads(rhs, out);
        }
        Expr::Mux {
            cond, then, els, ..
        } => {
            inst_reads(cond, out);
            inst_reads(then, out);
            inst_reads(els, out);
        }
    }
}

/// Whether a typed expression reads an input directly, through slices and
/// operations but not through `let` bindings.
fn reads_input(e: &typed::Expr) -> bool {
    match e {
        typed::Expr::Input(_) => true,
        typed::Expr::InstOut(..)
        | typed::Expr::Let(_)
        | typed::Expr::Output(_)
        | typed::Expr::Reg(_)
        | typed::Expr::Const(_) => false,
        typed::Expr::Un(_, a)
        | typed::Expr::Extract(a, ..)
        | typed::Expr::Replicate(a, _)
        | typed::Expr::Read(_, a) => reads_input(a),
        typed::Expr::Bin(_, a, b) | typed::Expr::Icmp(_, a, b) => reads_input(a) || reads_input(b),
        typed::Expr::Mux(c, t, e) => reads_input(c) || reads_input(t) || reads_input(e),
    }
}

/// Whether a typed expression reads an output of its own module.
fn reads_output(e: &typed::Expr) -> bool {
    match e {
        typed::Expr::Output(_) => true,
        typed::Expr::Input(_)
        | typed::Expr::InstOut(..)
        | typed::Expr::Let(_)
        | typed::Expr::Reg(_)
        | typed::Expr::Const(_) => false,
        typed::Expr::Un(_, a)
        | typed::Expr::Extract(a, ..)
        | typed::Expr::Replicate(a, _)
        | typed::Expr::Read(_, a) => reads_output(a),
        typed::Expr::Bin(_, a, b) | typed::Expr::Icmp(_, a, b) => {
            reads_output(a) || reads_output(b)
        }
        typed::Expr::Mux(c, t, e) => reads_output(c) || reads_output(t) || reads_output(e),
    }
}

/// The instance outputs that a typed expression reads directly, through
/// slices and operations but not through `let` bindings.
fn inst_outs(e: &typed::Expr) -> Vec<(typed::InstIdx, typed::OutputIdx)> {
    match e {
        typed::Expr::InstOut(u, o) => vec![(*u, *o)],
        typed::Expr::Input(_)
        | typed::Expr::Let(_)
        | typed::Expr::Output(_)
        | typed::Expr::Reg(_)
        | typed::Expr::Const(_) => vec![],
        typed::Expr::Un(_, a)
        | typed::Expr::Extract(a, ..)
        | typed::Expr::Replicate(a, _)
        | typed::Expr::Read(_, a) => inst_outs(a),
        typed::Expr::Bin(_, a, b) | typed::Expr::Icmp(_, a, b) => {
            let mut out = inst_outs(a);
            out.extend(inst_outs(b));
            out
        }
        typed::Expr::Mux(c, t, e) => {
            let mut out = inst_outs(c);
            out.extend(inst_outs(t));
            out.extend(inst_outs(e));
            out
        }
    }
}

/// The forms that the generator makes with every configuration.
const FORMS: &[&str] = &[
    "ref",
    "inst-out",
    "const",
    "Not",
    "Add",
    "Sub",
    "Mul",
    "And",
    "Or",
    "Xor",
    "Shl",
    "Shru",
    "Shrs",
    "Concat",
    "Eq",
    "Ne",
    "Ult",
    "Ule",
    "Ugt",
    "Uge",
    "Slt",
    "Sle",
    "Sgt",
    "Sge",
    "mux",
    "extract",
    "replicate",
    "reset",
    "path-through-child",
    "handshake",
    "shuffled-conns",
    "output-read",
];

/// The designs of 400 samples of `strategy`.
fn sample(strategy: impl Strategy<Value = Design>) -> Coverage {
    let mut runner = TestRunner::deterministic();
    let mut seen = Coverage::default();
    for _ in 0..400 {
        let Ok(tree) = strategy.new_tree(&mut runner) else {
            panic!("the generator never rejects");
        };
        seen.design(&tree.current());
    }
    seen
}

fn assert_covers(seen: &Coverage, forms: &[&str]) {
    let missing: Vec<_> = forms.iter().filter(|f| !seen.forms.contains(**f)).collect();
    assert!(missing.is_empty(), "never generated: {missing:?}");
}

#[test]
fn the_generator_covers_the_core_ir() {
    let seen = sample(r#gen::design());
    assert_covers(
        &seen,
        &["read", "no-reset", "second-write-port", "read-in-child"],
    );
    assert_covers(&seen, FORMS);
    assert!(seen.depths.contains(&1) && seen.depths.contains(&20));
    assert!(seen.depths.iter().all(|d| (1..=20).contains(d)));
    assert!(seen.depths.iter().any(|d| !d.is_power_of_two()));
    assert!(seen.widths.iter().any(|w| *w > 64));
    assert!(seen.widths.iter().all(|w| (1..=300).contains(w)));
    assert_eq!(seen.levels, 3, "the top never has 3 levels below it");
}

fn source() -> impl Strategy<Value = Design> {
    r#gen::design_with(r#gen::Config::source())
}

#[test]
fn the_source_generator_covers_the_lift_forms() {
    let seen = sample(source());
    assert_covers(&seen, FORMS);
    assert_covers(&seen, &["rst-conn"]);
    assert!(!seen.forms.contains("read"));
    assert!(!seen.forms.contains("no-reset"));
}

/// The statements of `m` that read a memory, write one, or declare one.
fn has_mem_form(m: &Module) -> bool {
    m.stmts.iter().any(|s| match s {
        Stmt::Mem { .. } | Stmt::Write { .. } => true,
        Stmt::Let { expr, .. } | Stmt::Next { expr, .. } | Stmt::Assign { expr, .. } => {
            has_read(expr)
        }
        Stmt::Reg { reset, .. } => reset
            .as_ref()
            .is_some_and(|r| has_read(&r.signal) || has_read(&r.value)),
        Stmt::Inst { conns, .. } => conns.iter().any(|c| has_read(&c.expr)),
    })
}

/// Whether `m` has the 1-bit input `rst`.
fn has_reset_input(m: &Module) -> bool {
    m.ports.iter().any(|p| {
        p.dir == Dir::Input
            && p.name.text == r#gen::RESET
            && matches!(&p.ty, Ty::Bits(w) if w.value == 1)
    })
}

fn is_rst(e: &Expr) -> bool {
    matches!(e, Expr::Ref(n) if n.text == r#gen::RESET)
}

fn source_forms(d: &Design) -> Result<(), String> {
    if print(d).contains('$') {
        return Err("a name has a $ field".to_owned());
    }
    let modules = modules(d);
    for item in &d.items {
        let Item::Module(m) = item else {
            return Err("an extern".to_owned());
        };
        if has_mem_form(m) {
            return Err(format!("{} has a memory form", m.name.text));
        }
        let clocked = m.ports.iter().any(|p| p.ty == Ty::Clock);
        if clocked != has_reset_input(m) {
            return Err(format!("{}: rst and clock differ", m.name.text));
        }
        for s in &m.stmts {
            match s {
                Stmt::Reg { reset, .. } => match reset {
                    Some(r) if is_rst(&r.signal) && matches!(r.value, Expr::Const { .. }) => {}
                    _ => return Err("a register has no module reset to a constant".to_owned()),
                },
                Stmt::Inst { module, conns, .. } => {
                    let child = modules.get(module.text.as_str());
                    let clocked = child.is_some_and(|c| c.ports.iter().any(|p| p.ty == Ty::Clock));
                    let wired = conns
                        .iter()
                        .any(|c| c.port.text == r#gen::RESET && is_rst(&c.expr));
                    if clocked != wired {
                        return Err("an instance misses its rst connection".to_owned());
                    }
                }
                _ => {}
            }
        }
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig {
        failure_persistence: None,
        ..ProptestConfig::default()
    })]

    #[test]
    fn source_designs_check(d in source()) {
        prop_assert!(check(&d).is_ok(), "{:?}\n{}", check(&d).err(), print(&d));
    }

    #[test]
    fn source_designs_have_only_source_forms(d in source()) {
        prop_assert_eq!(source_forms(&d), Ok(()), "{}", print(&d));
    }
}

/// Draws one value of `strategy` from `runner`.
fn draw<S: Strategy>(strategy: &S, runner: &mut TestRunner) -> S::Value {
    match strategy.new_tree(runner) {
        Ok(tree) => tree.current(),
        Err(e) => panic!("the strategy never rejects: {e}"),
    }
}

#[test]
fn resets_favor_the_first_line() {
    let mut runner = TestRunner::deterministic();
    let strategy = r#gen::resets(8);
    let draws: Vec<Vec<bool>> = (0..2000).map(|_| draw(&strategy, &mut runner)).collect();
    assert!(draws.iter().all(|d| d.len() == 8));
    let first = draws.iter().filter(|d| d[0]).count();
    assert!((1350..=1650).contains(&first), "line 0: {first} of 2000");
    let later = draws.iter().flat_map(|d| &d[1..]).filter(|&&b| b).count();
    // 9 % to 16 % of 2000 * 7 entries.
    assert!(
        (1260..=2240).contains(&later),
        "later lines: {later} of 14000"
    );
    assert!(draw(&r#gen::resets(0), &mut runner).is_empty());
}

#[test]
fn source_lines_take_the_reset_pattern() {
    let mut runner = TestRunner::deterministic();
    let (mut seen, mut first, mut later) = (0, 0, 0);
    while seen < 50 {
        let design = draw(&source(), &mut runner);
        let typed = checked(&design);
        let top = typed.modules()[typed.top().index()].clone();
        if !top.inputs().iter().any(|p| p.name == r#gen::RESET) {
            continue;
        }
        let lines = draw(&r#gen::lines(&top, 8), &mut runner);
        assert_eq!(lines.len(), 8);
        for line in &lines {
            assert!(parse_input(line, &top).is_ok(), "{line}");
        }
        first += usize::from(reset_of(&lines[0]));
        later += lines[1..].iter().filter(|line| reset_of(line)).count();
        seen += 1;
    }
    assert!(first * 2 > seen, "line 0 resets in {first} of {seen}");
    assert!(
        later * 4 < seen * 7,
        "later lines reset {later} of {}",
        seen * 7
    );
}

/// Whether the `in=` line `line` sets the input `rst` to 1.
fn reset_of(line: &str) -> bool {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    tokens
        .iter()
        .position(|t| t.trim_start_matches("in=(") == r#gen::RESET)
        .and_then(|k| tokens.get(k + 1))
        .is_some_and(|t| t.trim_end_matches(')') == "1")
}

#[test]
fn generator_designs_are_pinned() {
    let mut runner = TestRunner::deterministic();
    let mut texts = Vec::new();
    for _ in 0..3 {
        let Ok(tree) = r#gen::design().new_tree(&mut runner) else {
            panic!("the generator never rejects");
        };
        texts.push(print(&tree.current()));
    }
    insta::assert_snapshot!(texts.join("\n"));
}
