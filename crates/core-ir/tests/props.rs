//! Property tests over the random designs of `gen`.

use std::collections::{BTreeMap, BTreeSet};

use core_ir::ast::{Design, Expr, Item, Stmt};
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
        let top = typed.modules[typed.top.index()].clone();
        (Just(d), vec(r#gen::inputs(&top), 1..=4))
    })
}

/// `d` with its items and statements in reverse order.
fn reversed(d: &Design) -> Design {
    let mut out = d.clone();
    out.items.reverse();
    for item in &mut out.items {
        if let Item::Module(m) = item {
            m.stmts.reverse();
        }
    }
    out
}

proptest! {
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
    fn interpreter_never_panics((d, lines) in design_and_lines()) {
        let typed = checked(&d);
        let top = &typed.modules[typed.top.index()];
        let Ok(mut sim) = Sim::new(&typed) else {
            return Err(TestCaseError::fail("a generated design has no extern"));
        };
        for line in &lines {
            match parse_input(line, top) {
                Ok(inputs) => {
                    let out = print_output(top, &sim.step(&inputs));
                    prop_assert!(out.starts_with("out=("));
                }
                Err(e) => prop_assert!(false, "{line}: {e}"),
            }
        }
    }
}

/// What a sample of designs uses: the operations, the reset kinds, the
/// memory depths, the widths, and the instance levels.
#[derive(Default)]
struct Coverage {
    forms: BTreeSet<String>,
    depths: BTreeSet<u32>,
    widths: BTreeSet<u32>,
    levels: u32,
}

impl Coverage {
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
        let mut levels: BTreeMap<&str, u32> = BTreeMap::new();
        let mut modules: Vec<_> = d
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Module(m) => Some(m),
                Item::Extern(_) => None,
            })
            .collect();
        // A child has a lower number than its parents.
        modules.sort_by_key(|m| m.name.text[1..].parse::<u32>().unwrap_or(0));
        for m in modules {
            let mut level = 0;
            for s in &m.stmts {
                self.stmt(s);
                if let Stmt::Inst { module, .. } = s {
                    level = level.max(levels.get(module.text.as_str()).map_or(0, |l| l + 1));
                }
            }
            levels.insert(&m.name.text, level);
            self.levels = self.levels.max(level);
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
                        self.forms.insert("reset".into());
                        self.expr(&r.signal);
                        self.expr(&r.value);
                    }
                    None => {
                        self.forms.insert("no-reset".into());
                    }
                }
            }
            Stmt::Mem { depth, .. } => {
                self.depths.insert(depth.value);
            }
            Stmt::Next { expr, .. } | Stmt::Assign { expr, .. } => self.expr(expr),
            Stmt::Write { addr, data, en, .. } => {
                self.expr(addr);
                self.expr(data);
                self.expr(en);
            }
            Stmt::Inst { conns, .. } => conns.iter().for_each(|c| self.expr(&c.expr)),
        }
    }
}

#[test]
fn the_generator_covers_the_core_ir() {
    let mut runner = TestRunner::deterministic();
    let mut seen = Coverage::default();
    for _ in 0..200 {
        let Ok(tree) = r#gen::design().new_tree(&mut runner) else {
            panic!("the generator never rejects");
        };
        seen.design(&tree.current());
    }
    let forms = [
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
        "read",
        "reset",
        "no-reset",
    ];
    let missing: Vec<_> = forms.iter().filter(|f| !seen.forms.contains(**f)).collect();
    assert!(missing.is_empty(), "never generated: {missing:?}");
    assert!(seen.depths.contains(&1) && seen.depths.contains(&20));
    assert!(seen.depths.iter().all(|d| (1..=20).contains(d)));
    assert!(seen.depths.iter().any(|d| !d.is_power_of_two()));
    assert!(seen.widths.iter().any(|w| *w > 64));
    assert!(seen.widths.iter().all(|w| (1..=300).contains(w)));
    assert_eq!(seen.levels, 3);
}
