// SPDX-License-Identifier: Apache-2.0
//! The cases of the typed use and the bindings of a hardware aggregate in
//! `Silicon.Source.Test.Eval` and `Test.Elab` in Lean (design sections 5.4 and 7.3): a typed use
//! that never expands a reference, the parts that check in walk order before the charge, the
//! copy of a register read, the leaf `let` statements of a binding, the rebind of a place update
//! with its exact charge, the arguments, the results, and the write-backs. The tests count the
//! work of each walk and not the time.

use super::{Elab, Evaluator, Slot, Stop};
use crate::agg::{Agg, Base};
use crate::counters;
use crate::hw::{Handle, Kind, Op, Val};
use crate::names::{self, Field, PathId, Role, Step};
use crate::ops::Fuel;
use crate::scan;
use crate::tests_elab::{load, names as core_names};
use crate::types::{Ty, TyId};
use crate::value::Value;
use crate::{Budget, int::Int};
use parse::ast::{Item, Pos};

const AT: Pos = Pos { line: 1, col: 1 };

/// The core name of `p` as text.
pub(super) fn name_of(ev: &Evaluator<'_>, p: PathId) -> String {
    names::encode(&ev.paths.name(p, &ev.syms.texts))
}

fn base_text(ev: &Evaluator<'_>, b: &Base) -> String {
    match b {
        Base::Name(p) => name_of(ev, *p),
        Base::Out(i, q) => format!("{}.{}", name_of(ev, *i), name_of(ev, *q)),
        Base::Word(m, off) => format!("{}+{off}", name_of(ev, *m)),
    }
}

/// A hardware leaf: its core name, or `hardware T` for an operation.
fn hw_text(ev: &Evaluator<'_>, h: crate::hw::HwId) -> String {
    match ev.graph.node(h) {
        Some(n) => match &n.op {
            Op::Ref(p) => name_of(ev, *p),
            Op::Lit(v) => v.serialize(&ev.tys),
            _ => format!("hardware {}", ev.tys.text_of(&n.ty)),
        },
        None => String::new(),
    }
}

/// An aggregate: a part of a node prints in brackets, and a reference as `ref` and its base.
fn agg_text(ev: &Evaluator<'_>, a: &Agg) -> String {
    match a {
        Agg::Static(v) => v.serialize(&ev.tys),
        Agg::Hw(h) => hw_text(ev, *h),
        Agg::Ref(b, _) => format!("ref {}", base_text(ev, b)),
        Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p) => {
            let parts: Vec<String> = p.0.iter().map(|x| agg_text(ev, x)).collect();
            format!("[{}]", parts.join(", "))
        }
    }
}

fn val_text(ev: &Evaluator<'_>, v: &Val) -> String {
    match v {
        Val::Agg(a) => agg_text(ev, a),
        Val::Hw(h) => hw_text(ev, *h),
        Val::Static(v) => v.serialize(&ev.tys),
        v => ev.text(v.seen()),
    }
}

fn error_text<T>(r: Result<T, Stop>) -> Result<T, String> {
    match r {
        Ok(v) => Ok(v),
        Err(Stop::Error(e)) => Err(format!("{} {}:{}", e.code, e.pos.line, e.pos.col)),
        Err(Stop::Stack(_)) => Err("stack".to_owned()),
    }
}

/// An evaluator over `src` with the run number `run`, which keys its counters.
fn evaluator(file: &resolve::Resolved, run: u64) -> Evaluator<'_> {
    Evaluator::new(
        file,
        None,
        Budget {
            fuel: run,
            depth: 1000,
        },
        scan::of(file, None),
        Elab::new(names::sha16),
    )
}

/// A hardware leaf of the type `ty` with the core name `name`.
fn leaf(ev: &mut Evaluator<'_>, name: &str, ty: Ty) -> Agg {
    ev.syms.texts.push(name.to_owned());
    let sym = ev.syms.texts.len() - 1;
    let p = ev.paths.child(None, sym);
    Agg::Hw(ev.graph.mk(AT, ty, Op::Ref(p), Vec::new()))
}

fn tuple_of(ev: &mut Evaluator<'_>, parts: Vec<Ty>) -> TyId {
    let parts = parts.into_iter().map(|t| ev.tys.mk(t)).collect();
    ev.tys.tuple(parts)
}

pub(super) fn node(ev: &Evaluator<'_>, ty: TyId, parts: Vec<Agg>) -> Val {
    match Agg::node(&ev.graph, &ev.tys, ty, parts) {
        Some(a) => a.into_val(),
        None => Val::Static(Value::Unit),
    }
}

/// A reference to the core name `name` of the type `t`.
fn reference(ev: &mut Evaluator<'_>, name: &str, t: TyId) -> Agg {
    ev.syms.texts.push(name.to_owned());
    let sym = ev.syms.texts.len() - 1;
    Agg::Ref(Base::Name(ev.paths.child(None, sym)), t)
}

const TUPLES: &str = "type A = (Bool, UInt[4]);\ntype B = (Bool, Nat);\ntype C = (UInt[1], Nat);\n\
    type D = (Nat, UInt[1]);\ntype E = (Bool, UInt[8]);\n\
    type F = (Bool, [UInt[8]; 4], UInt[4]);\nstruct Q { a: Bool }\nstruct R { a: Bool }\n";

/// The typed use of the value that `make` builds at the type expression `ty` after the items
/// of `src`. The result shows the value and the units of the typed use alone, with the fuel
/// `fuel` for it. `run` keys the counters.
fn typed_use(
    src: &str,
    ty: &str,
    run: u64,
    fuel: u64,
    make: impl FnOnce(&mut Evaluator<'_>, TyId) -> Val,
) -> String {
    let file = load(src).unwrap();
    let e = parse::parse_expr(ty, parse::DEFAULT_SYNTAX_DEPTH)
        .unwrap()
        .unwrap();
    let top = resolve::resolve_expr(&file, e).unwrap().unwrap();
    let mut ev = Evaluator::new(
        &file,
        Some(&top),
        Budget {
            fuel: run,
            depth: 1000,
        },
        scan::of(&file, Some(&top)),
        Elab::new(names::sha16),
    );
    let t = match ev.eval(top.expr()) {
        Ok(Some(out)) => match ev.store.value(&out) {
            Value::Type(t) => *t,
            _ => return "no type".to_owned(),
        },
        _ => return "no type".to_owned(),
    };
    let v = make(&mut ev, t);
    ev.fuel = Fuel::new(fuel);
    match error_text(ev.copy_use(AT, t, false, super::Out::Made(v))) {
        Ok(x) => format!("{} {}", val_text(&ev, &x), fuel - ev.fuel.left()),
        Err(e) => e,
    }
}

fn pair(ev: &mut Evaluator<'_>, second: Ty, x: Value) -> Val {
    let t = tuple_of(ev, vec![Ty::Bool, second]);
    let b = leaf(ev, "b", Ty::Bool);
    node(ev, t, vec![b, Agg::Static(x)])
}

pub(super) fn int(n: i64) -> Value {
    Value::Int(Int::from_decimal(&n.to_string()).unwrap_or_else(Int::zero))
}

/// A reference checks by its type in one step and never expands. Thus a typed use of a
/// reference to a huge array at its own type takes no unit and walks nothing, and another type
/// is `S010` before any charge.
#[test]
fn a_typed_use_of_a_reference_at_its_type_takes_one_step() {
    let run = 700_000_200;
    let huge = typed_use("", "[UInt[8]; 1099511627776]", run, 0, |ev, t| {
        reference(ev, "r", t).into_val()
    });
    assert_eq!(huge, "ref r 0");
    let c = counters::of(run);
    assert_eq!((c.typed, c.nodes, c.bound, c.expanded), (0, 0, 0, 0));
    let other = typed_use("", "[UInt[4]; 4]", run + 1, 0, |ev, _| {
        let t = ev.tys.mk(Ty::UInt(8));
        let t = ev.tys.array(t, Int::from_u64(4));
        reference(ev, "r", t).into_val()
    });
    assert_eq!(other, "S010 1:1");
}

/// Another aggregate checks each part first: a hardware leaf needs the type of its position
/// (`S010`), and a static leaf its sign (`S012`). The first failing part in walk order reports,
/// before the charge. Then the conversion charges the size of the value plus the size of the
/// result, here 3 + 3. Then a static leaf converts and checks its fit (`S012`), after the
/// charge. A reference part keeps its form and counts its zero size, here 5, in both sizes.
#[test]
fn the_parts_check_in_walk_order_before_the_charge() {
    let plenty = 1000;
    let typed = |src: &str, ty: &str, run: u64, fuel: u64, second: Ty, x: Value| {
        typed_use(src, ty, run, fuel, move |ev, _| pair(ev, second, x))
    };
    assert_eq!(
        typed(TUPLES, "A", 700_000_210, plenty, Ty::Int, int(3)),
        "[b, (uint 4 3)] 6"
    );
    assert_eq!(
        typed(TUPLES, "B", 700_000_211, 0, Ty::Int, int(-1)),
        "S012 1:1"
    );
    assert_eq!(
        typed(TUPLES, "C", 700_000_212, 0, Ty::Int, int(-1)),
        "S010 1:1"
    );
    let d = typed_use(TUPLES, "D", 700_000_213, 0, |ev, _| {
        let t = tuple_of(ev, vec![Ty::Int, Ty::Bool]);
        let b = leaf(ev, "b", Ty::Bool);
        node(ev, t, vec![Agg::Static(int(-1)), b])
    });
    assert_eq!(d, "S012 1:1");
    assert_eq!(
        typed(TUPLES, "E", 700_000_214, plenty, Ty::Int, int(300)),
        "S012 1:1"
    );
    assert_eq!(
        typed(TUPLES, "E", 700_000_215, 5, Ty::Int, int(300)),
        "S015 1:1"
    );
    let big = typed_use(TUPLES, "F", 700_000_216, plenty, |ev, _| {
        let arr = ev.tys.mk(Ty::UInt(8));
        let arr = ev.tys.array(arr, Int::from_u64(4));
        let t = {
            let (b, i) = (ev.tys.mk(Ty::Bool), ev.tys.mk(Ty::Int));
            ev.tys.tuple(vec![b, arr, i])
        };
        let b = leaf(ev, "b", Ty::Bool);
        let r = reference(ev, "r", arr);
        node(ev, t, vec![b, r, Agg::Static(int(3))])
    });
    assert_eq!(big, "[b, ref r, (uint 4 3)] 16");
}

/// A record needs its own struct type, and it converts nothing.
#[test]
fn a_record_needs_its_own_struct_type() {
    let own = typed_use(TUPLES, "Q", 700_000_220, 0, |ev, t| {
        let b = leaf(ev, "b", Ty::Bool);
        node(ev, t, vec![b])
    });
    assert_eq!(own, "[b] 0");
    let other = typed_use(TUPLES, "Q", 700_000_221, 0, |ev, _| {
        let Ok(r) = ev.spec(AT, 7, &[]) else {
            return Val::Static(Value::Unit);
        };
        let b = leaf(ev, "b", Ty::Bool);
        node(ev, r, vec![b])
    });
    assert_eq!(other, "S010 1:1");
}

/// A register of the type `t` as the handle that a use reads.
fn register(ev: &mut Evaluator<'_>, t: TyId) -> Val {
    ev.syms.texts.push("r".to_owned());
    let path = ev.paths.child(None, ev.syms.texts.len() - 1);
    Val::Handle(Handle::Res {
        kind: Kind::Reg,
        id: 0,
        ty: ev.tys.get(t).clone(),
        path,
    })
}

/// The copy of a register charges 1 for the handle. A read of an aggregate register is a
/// reference, so its copy also charges the zero size of its type. A huge one thus fails before
/// any leaf exists. A scalar read charges only the handle, as in slice 1. A read without a
/// hardware leaf makes a new static value with the charge of its zero size.
#[test]
fn the_copy_of_an_aggregate_register_read_charges_its_zero_size() {
    let copy = |run: u64, ty: Ty, len: Option<u64>, fuel: u64| {
        let file = load("").unwrap();
        let mut ev = evaluator(&file, run);
        let t = ev.tys.mk(ty);
        let t = match len {
            Some(n) => ev.tys.array(t, Int::from_u64(n)),
            None => t,
        };
        let r = register(&mut ev, t);
        ev.fuel = Fuel::new(fuel);
        match error_text(ev.copy_use(AT, t, true, super::Out::Named(r))) {
            Ok(v) => format!("{} {}", val_text(&ev, &v), fuel - ev.fuel.left()),
            Err(e) => e,
        }
    };
    assert_eq!(copy(700_000_230, Ty::UInt(8), Some(4), 100), "ref r 6");
    assert_eq!(
        copy(700_000_231, Ty::UInt(8), Some(1 << 40), 100),
        "S015 1:1"
    );
    assert_eq!(copy(700_000_232, Ty::UInt(256), None, 100), "r 1");
    let empty = copy(700_000_233, Ty::Unit, Some(3), 100);
    assert!(empty.ends_with(" 5"), "{empty}");
}

/// The text of a hardware value in a core `let`.
pub(super) type Shown = fn(&Evaluator<'_>, crate::hw::HwId) -> String;

/// The text of the core `let` statements: each core name with its value.
fn lets_text(ev: &Evaluator<'_>, shown: Shown) -> String {
    let parts: Vec<String> = ev
        .naming
        .lets
        .iter()
        .map(|l| format!("{}={}", name_of(ev, l.path), shown(ev, l.value)))
        .collect();
    parts.join(" ")
}

/// The body of the function `f` of `src`. Its first parameter `x` is a mutable local with the
/// value that `base` makes at the name path of `x`, and it took its first core name, as a
/// copy-in does. The result shows the core `let` statements, the final value of `x`, and the
/// units of the body alone, with the fuel `fuel` for it. `run` keys the counters.
pub(super) fn run_f(
    src: &str,
    run: u64,
    fuel: u64,
    base: impl FnOnce(&mut Evaluator<'_>, PathId, TyId) -> Val + Send,
) -> String {
    run_shown(src, run, fuel, base, hw_text)
}

/// `run_f` with the text `shown` of the hardware value of each core `let`.
pub(super) fn run_shown(
    src: &str,
    run: u64,
    fuel: u64,
    base: impl FnOnce(&mut Evaluator<'_>, PathId, TyId) -> Val + Send,
    shown: Shown,
) -> String {
    parse::on_stack(1024, move || run_shown_here(src, run, fuel, base, shown))
        .unwrap_or_else(|_| "stack".to_owned())
}

/// `run_shown` on the thread that calls it.
fn run_shown_here(
    src: &str,
    run: u64,
    fuel: u64,
    base: impl FnOnce(&mut Evaluator<'_>, PathId, TyId) -> Val,
    shown: Shown,
) -> String {
    let file = load(src).unwrap();
    let mut ev = evaluator(&file, run);
    let drive = |ev: &mut Evaluator<'_>| -> Result<String, Stop> {
        let Some(item) = file
            .ast()
            .iter()
            .position(|it| matches!(it, Item::Fn { name, .. } if name.name == "f"))
        else {
            return Ok("no function f".to_owned());
        };
        let Some(Item::Fn { params, body, .. }) = file.ast().get(item) else {
            return Ok("no function f".to_owned());
        };
        let Some(param) = params.first() else {
            return Ok("no parameter".to_owned());
        };
        ev.item = item;
        ev.ret = Some(ev.tys.mk(Ty::Bool));
        let ty = ev.type_expr(&param.ty)?;
        let id = ev.decl(&param.name)?;
        let sym = ev.sym(id);
        let path = ev.paths.child(None, sym);
        let value = base(ev, path, ty);
        ev.bind(
            id,
            Slot {
                ty: Some(ty),
                mutable: true,
                value,
            },
        );
        ev.fresh(id);
        ev.fuel = Fuel::new(fuel);
        for stmt in body {
            if ev.stmt(stmt, false)?.is_some() {
                break;
            }
        }
        let last = ev
            .store
            .frame()
            .and_then(|f| f.get(&id))
            .map(|s| val_text(ev, &s.value));
        Ok(format!(
            "{} | {} | {}",
            lets_text(ev, shown),
            last.unwrap_or_else(|| "-".to_owned()),
            fuel - ev.fuel.left()
        ))
    };
    match error_text(drive(&mut ev)) {
        Ok(s) | Err(s) => s,
    }
}

/// A reference to the name of `x` at the type of its parameter.
pub(super) fn ref_x(ev: &mut Evaluator<'_>, p: PathId, t: TyId) -> Val {
    let _ = ev;
    Agg::Ref(Base::Name(p), t).into_val()
}

/// The hardware leaf of the element `k` of `x`, of the type `UInt[8]`.
pub(super) fn leaf_x(ev: &mut Evaluator<'_>, p: PathId, k: u64) -> Agg {
    let q = ev.paths.push(p, Step::Elem(k));
    let ty = Ty::UInt(8);
    Agg::Hw(ev.graph.mk(AT, ty, Op::Ref(q), Vec::new()))
}

pub(super) fn assign_in(t: &str, s: &str) -> String {
    format!("fn f(mut x: {t}) -> Bool {{\n  {s}\n  return true;\n}}\n")
}

/// A place update can give a new root with a hardware leaf. It then binds each hardware leaf of
/// the root again, at the next version of the root (section 7.3). The static leaf `7` gets no
/// core name. The assignment charges 1, its step 1, the index 2, the value 2, and its
/// conversion 2. The rebind charges 5: the old size 5, minus the part 1, plus the new part 1.
/// `return true;` charges 4.
#[test]
fn a_place_update_rebinds_each_hardware_leaf_with_its_exact_charge() {
    let src = assign_in("[UInt[8]; 4]", "x[1] = 7;");
    assert_eq!(
        run_f(&src, 700_000_240, 1000, ref_x),
        "x$1v$0e=x$0e x$1v$2e=x$2e x$1v$3e=x$3e | [x$1v$0e, (uint 8 7), x$1v$2e, x$1v$3e] | 17"
    );
    assert_eq!(run_f(&src, 700_000_241, 12, ref_x), "S015 2:3");
    assert_eq!(run_f(&src, 700_000_242, 13, ref_x), "S015 3:3");
}

/// The rebind charges from the stored sizes before the path copies and before the reference
/// root expands. Thus a huge root fails at the assignment before any work on its elements.
#[test]
fn a_huge_reference_root_fails_at_the_rebind_before_it_expands() {
    let run = 700_000_250;
    let src = assign_in("[UInt[8]; 1 << 40]", "x[5] = 7;");
    assert_eq!(run_f(&src, run, 1_000_000, ref_x), "S015 2:3");
    let c = counters::of(run);
    assert_eq!((c.expanded, c.nodes, c.bound, c.typed), (0, 0, 0, 0));
}

/// Only the references on the path expand, one level for each step. The part `x[0]` stays a
/// reference, and its binding refers to its new name.
#[test]
fn only_the_references_on_the_path_expand() {
    let run = 700_000_251;
    let src = assign_in("[[UInt[8]; 2]; 2]", "x[1][0] = x[0][1];");
    assert_eq!(
        run_f(&src, run, 1_000_000, ref_x),
        "x$1v$0e$0e=x$0e$0e x$1v$0e$1e=x$0e$1e x$1v$1e$0e=x$0e$1e x$1v$1e$1e=x$1e$1e | \
         [ref x$1v$0e, [x$1v$1e$0e, x$1v$1e$1e]] | 26"
    );
    assert_eq!(counters::of(run).expanded, 4);
}

/// A new root without a hardware leaf is a static value with no rebind charge. A static part of
/// an aggregate root takes a static value and keeps the other leaves. A static part that takes a
/// hardware value opens one level, and the root binds again.
#[test]
fn a_static_part_of_a_root_takes_a_static_value_or_opens_for_a_hardware_one() {
    let src = assign_in("(UInt[8], Int)", "x.0 = 5;");
    let mixed = |ev: &mut Evaluator<'_>, p: PathId, t: TyId| {
        let a = leaf_x(ev, p, 0);
        node(ev, t, vec![a, Agg::Static(int(3))])
    };
    assert_eq!(
        run_f(&src, 700_000_252, 1000, mixed),
        " | (tuple ((uint 8 5) (int 3))) | 10"
    );
    let with_array = |ev: &mut Evaluator<'_>, p: PathId, t: TyId| {
        let a = leaf_x(ev, p, 0);
        let e = ev.tys.mk(Ty::UInt(8));
        let xs = vec![byte(1), byte(2)];
        node(ev, t, vec![a, Agg::Static(Value::Array(e, xs))])
    };
    let src = assign_in("(UInt[8], [UInt[8]; 2])", "x.1[0] = 9;");
    let out = run_f(&src, 700_000_253, 1000, with_array);
    assert_eq!(
        out,
        "x$1v$0e=x$0e | [x$1v$0e, (array (uint 8) ((uint 8 9) (uint 8 2)))] | 18"
    );
    let src = assign_in("(UInt[8], [UInt[8]; 2])", "x.1[0] = x.0;");
    assert_eq!(
        run_f(&src, 700_000_254, 1000, with_array),
        "x$1v$0e=x$0e x$1v$1e$0e=x$0e | [x$1v$0e, [x$1v$1e$0e, (uint 8 2)]] | 17"
    );
}

/// The value `n` of the type `UInt[8]`.
fn byte(n: u64) -> Value {
    Value::UInt(crate::int::finite(8, n).unwrap_or_else(|| panic!("a byte")))
}

/// A binding takes one version, and each hardware leaf gets one core `let`. A typed binding and
/// an assignment without a step read a reference by its leaves.
#[test]
fn a_binding_takes_one_version_and_a_let_for_each_leaf() {
    let src = assign_in("[UInt[8]; 2]", "let y: [UInt[8]; 2] = x;\n  x = y;");
    assert_eq!(
        run_f(&src, 700_000_260, 1000, ref_x),
        "y$0e=x$0e y$1e=x$1e x$1v$0e=y$0e x$1v$1e=y$1e | ref x$1v | 30"
    );
}

const AGG_CALLS: &str = "struct S { a: UInt[8], b: Bool }\nfn g(a: S) -> S {\n  return a;\n}\n\
    fn f(mut x: S) -> Bool {\n  let y = g(x);\n  comptime for i in 0..2 {\n\
    \x20   let z = g(y);\n  }\n  return true;\n}\n";

/// An argument, a call result, and a `mut` write-back bind by leaf (section 7.3). The result
/// puts its role `0ret` in the place of a name, with no version, and the leaves follow it. A
/// loop adds its frame, so no two names are equal.
#[test]
fn an_argument_and_a_result_bind_by_leaf_and_the_result_takes_no_version() {
    let out = run_f(AGG_CALLS, 700_000_270, 1_000_000, ref_x);
    assert_eq!(
        out,
        "g$0c$a$a=x$a g$0c$a$b=x$b g$0c$0ret$a=g$0c$a$a g$0c$0ret$b=g$0c$a$b y$a=g$0c$0ret$a \
         y$b=g$0c$0ret$b i$0$g$1c$a$a=y$a i$0$g$1c$a$b=y$b i$0$g$1c$0ret$a=i$0$g$1c$a$a \
         i$0$g$1c$0ret$b=i$0$g$1c$a$b i$0$z$a=i$0$g$1c$0ret$a i$0$z$b=i$0$g$1c$0ret$b \
         i$1$g$1c$a$a=y$a i$1$g$1c$a$b=y$b i$1$g$1c$0ret$a=i$1$g$1c$a$a \
         i$1$g$1c$0ret$b=i$1$g$1c$a$b i$1$z$a=i$1$g$1c$0ret$a i$1$z$b=i$1$g$1c$0ret$b \
         | ref x | 60"
    );
    let called: Vec<names::Name> = out
        .split(" | ")
        .next()
        .unwrap_or_default()
        .split(' ')
        .filter_map(|w| names::decode(w.split('=').next().unwrap_or_default()))
        .collect();
    let ret = Field::Role(Role::Ret);
    let leaves: Vec<&names::Name> = called.iter().filter(|p| p.rest.contains(&ret)).collect();
    assert_eq!(leaves.len(), 6);
    assert!(
        leaves
            .iter()
            .all(|p| !p.rest.iter().any(|f| matches!(f, Field::Version(_))))
    );
    assert!(
        leaves
            .iter()
            .all(|p| { p.rest.iter().skip_while(|f| **f != ret).count() == 2 })
    );
    let mut all: Vec<String> = called.iter().map(names::encode).collect();
    let n = all.len();
    all.sort();
    all.dedup();
    assert_eq!(all.len(), n);
}

/// A call result never gets a version (section 7.3), for a scalar result as for an aggregate.
/// A loop and a recursion add frames. Each result name thus ends with `0ret`, and no two names
/// are equal.
#[test]
fn a_scalar_call_result_takes_no_version() {
    let src = "fn g(comptime n: Nat, a: UInt[8]) -> UInt[8] {\n\
        \x20 comptime if (n == 0) {\n    return a +% 1;\n  }\n\
        \x20 let b = g(n - 1, a);\n  return b +% 1;\n}\n\
        module M() {\n  input x: UInt[8];\n  output y: UInt[8];\n\
        \x20 let mut s = g(0, x);\n  comptime for i in 0..2 {\n    s = g(2, s);\n  }\n  y := s;\n}\n";
    let all = core_names(src, "M", "M");
    let ret = Field::Role(Role::Ret);
    let rets: Vec<names::Name> = all
        .iter()
        .filter_map(|n| names::decode(n))
        .filter(|p| p.rest.contains(&ret))
        .collect();
    assert_eq!(rets.len(), 7);
    assert!(rets.iter().all(|p| p.rest.last() == Some(&ret)));
    assert!(
        rets.iter()
            .all(|p| !p.rest.iter().any(|f| matches!(f, Field::Version(_))))
    );
    let mut sorted = all.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), all.len());
    assert!(all.iter().any(|n| n == "i$1$g$1c$g$0c$g$0c$0ret"));
}

/// A `mut` write-back binds the final value of the formal to the next version of the caller
/// root. The update of the formal rebinds it in the frame of the call first.
#[test]
fn a_write_back_binds_the_final_value_at_the_next_version_of_the_root() {
    let src = "fn g(mut a: [UInt[8]; 2]) -> Bool {\n  a[0] = 1;\n  return true;\n}\n\
        fn f(mut x: [UInt[8]; 2]) -> Bool {\n  let b = g(x);\n  return b;\n}\n";
    assert_eq!(
        run_f(src, 700_000_280, 1_000_000, ref_x),
        "g$0c$a$0e=x$0e g$0c$a$1e=x$1e g$0c$a$1v$1e=g$0c$a$1e x$1v$1e=g$0c$a$1v$1e | \
         [(uint 8 1), x$1v$1e] | 45"
    );
}

/// A list holds no value with a hardware leaf: `push` of an aggregate is `S011` at the element.
#[test]
fn push_of_an_aggregate_is_s011_at_the_element() {
    let src = assign_in(
        "[UInt[8]; 2]",
        "let mut l = list([UInt[8]; 2]);\n  l.push(x);",
    );
    assert_eq!(run_f(&src, 700_000_290, 1_000_000, ref_x), "S011 3:10");
}

/// A rebind that leaves no hardware leaf charges the zero size of each empty part that a
/// reference on its path makes, from the metadata, before the static value exists (Lean
/// `Agg.emptySize`). On `(UInt[8], [(); 3])`, `x.0 = 5;` charges 10, and 4 of it is the zero
/// size of `[(); 3]`. `return true;` charges 4.
#[test]
fn a_rebind_without_a_hardware_leaf_charges_the_empty_parts_it_makes() {
    let run = 700_000_300;
    let src = assign_in("(UInt[8], ())", "x.0 = 5;");
    assert_eq!(
        run_f(&src, run, 1000, ref_x),
        " | (tuple ((uint 8 5) (unit))) | 11"
    );
    let src = assign_in("(UInt[8], [(); 3])", "x.0 = 5;");
    assert_eq!(
        run_f(&src, run + 1, 1000, ref_x),
        " | (tuple ((uint 8 5) (array unit ((unit) (unit) (unit))))) | 14"
    );
    assert_eq!(run_f(&src, run + 2, 9, ref_x), "S015 2:3");
    assert_eq!(run_f(&src, run + 3, 10, ref_x), "S015 3:3");
    let src = assign_in("((UInt[8], [(); 3]), [(); 2])", "x.0.0 = 5;");
    assert_eq!(
        run_f(&src, run + 4, 1000, ref_x),
        " | (tuple ((tuple ((uint 8 5) (array unit ((unit) (unit) (unit))))) (array unit ((unit) (unit))))) | 18"
    );
}

/// A huge empty part fails at the charge, before any work on its elements.
#[test]
fn a_huge_empty_part_fails_at_the_charge_before_it_expands() {
    let run = 700_000_310;
    let src = assign_in("(UInt[8], [(); 1 << 40])", "x.0 = 5;");
    assert_eq!(run_f(&src, run, 1000, ref_x), "S015 2:3");
    assert_eq!(counters::of(run).expanded, 0);
}
