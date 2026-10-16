// SPDX-License-Identifier: Apache-2.0
//! The cases of the aggregate form in `Silicon.Source.Test.Eval` and `Test.Elab` in Lean (design
//! section 5.1): the size of a name, the stored numbers of a node, the static form of a
//! container without a hardware leaf, and `normalize`. The walks over a deep aggregate keep
//! their own stack. The selection cases of `Test.Eval` follow: an implicit read of a register,
//! the steps on a reference, the work of a huge array type, and the node of an aggregate.

use super::{Code, Evaluator, Out, Res, Stop};
use crate::agg::{Agg, Base, Node, Parts};
use crate::counters;
use crate::hw::{Handle, Kind, Op, Seen, Val};
use crate::int::Int;
use crate::names::Step;
use crate::tests_elab::load;
use crate::types::{Ty, TyId};
use crate::value::Value;
use crate::{Budget, scan};
use parse::ast::Pos;
use parse::ast::UnOp;

const AT: Pos = Pos { line: 1, col: 1 };

/// An evaluator over an empty file with the fuel `fuel`, for the function `act`.
fn with<T>(fuel: u64, act: impl FnOnce(&mut Evaluator<'_>) -> T) -> T {
    let file = load("").unwrap();
    let scan = scan::of(&file, None);
    let mut ev = Evaluator::new(
        &file,
        None,
        Budget { fuel, depth: 1000 },
        scan,
        super::Elab::new(crate::names::sha16),
    );
    act(&mut ev)
}

/// A core name for the references of the cases.
fn base(ev: &mut Evaluator<'_>) -> Base {
    let root = ev.paths.child(None, 1);
    Base::Name(ev.paths.push(root, Step::Int(Int::from_u64(0))))
}

fn array(ev: &mut Evaluator<'_>, elem: Ty, len: u64) -> TyId {
    let elem = ev.tys.mk(elem);
    ev.tys.array(elem, Int::from_u64(len))
}

fn tuple(ev: &mut Evaluator<'_>, parts: Vec<Ty>) -> TyId {
    let parts = parts.into_iter().map(|t| ev.tys.mk(t)).collect();
    ev.tys.tuple(parts)
}

/// The result of `normalize` as text: the static value, or the hardware size, or the
/// aggregate size, with the used fuel; or the code and the position of the error.
fn normal(fuel: u64, make: impl FnOnce(&mut Evaluator<'_>) -> Agg) -> String {
    with(fuel, |ev| {
        let a = make(ev);
        let r: Res<Val> = ev.normalize(AT, a);
        let used = fuel - ev.fuel.left();
        match r {
            Ok(Val::Static(v)) => format!("{} {used}", v.serialize(&ev.tys)),
            Ok(Val::Hw(h)) => format!("hardware {} {used}", ev.graph.size(h)),
            Ok(Val::Agg(a)) => format!("agg {} {used}", a.size(&ev.graph, &ev.tys)),
            Ok(_) => "other".to_owned(),
            Err(Stop::Error(e)) => format!("{} {}:{}", e.code, e.pos.line, e.pos.col),
            Err(Stop::Stack(_)) => "stack".to_owned(),
        }
    })
}

#[test]
fn a_name_and_a_child_output_have_the_size_of_their_type() {
    with(100, |ev| {
        let p = base(ev).op();
        let wide = ev.graph.mk(AT, Ty::UInt(256), p, Vec::new());
        assert_eq!(ev.graph.size(wide), 4);
        let out = Op::Out(ev.paths.child(None, 2), ev.paths.child(None, 3));
        let flag = ev.graph.mk(AT, Ty::Bool, out, Vec::new());
        assert_eq!(ev.graph.size(flag), 1);
        let inv = ev
            .graph
            .mk(AT, Ty::UInt(256), Op::Un(UnOp::Not), vec![wide]);
        assert_eq!(ev.graph.size(inv), 5);
    });
}

#[test]
fn a_reference_has_the_zero_size_and_depth_of_its_type() {
    with(100, |ev| {
        let t = array(ev, Ty::UInt(8), 4);
        let r = Agg::Ref(base(ev), t);
        assert_eq!((r.size(&ev.graph, &ev.tys), r.depth(&ev.tys)), (5, 2));
        assert_eq!(r.leaves(&ev.tys), 4);
    });
}

#[test]
fn a_node_stores_its_type_size_depth_and_leaves() {
    with(100, |ev| {
        let flag = Ty::Bool;
        let op = base(ev).op();
        let h = ev.graph.mk(AT, flag, op, Vec::new());
        let arr = array(ev, Ty::UInt(8), 4);
        let t = tuple(ev, vec![Ty::Bool, Ty::Int, Ty::Unit]);
        let parts = vec![
            Agg::Hw(h),
            Agg::Static(Value::Int(Int::from_u64(3))),
            Agg::Static(Value::Unit),
        ];
        let Some(Agg::Tuple(n, _)) = Agg::node(&ev.graph, &ev.tys, t, parts) else {
            panic!("a tuple node")
        };
        assert_eq!((n.size, n.depth, n.leaves), (4, 2, 1));
        let xs = vec![Agg::Ref(base(ev), ev.tys.mk(Ty::UInt(8))); 4];
        let Some(Agg::Array(n, _)) = Agg::node(&ev.graph, &ev.tys, arr, xs) else {
            panic!("an array node")
        };
        assert_eq!((n.size, n.depth, n.leaves), (5, 2, 4));
    });
}

#[test]
fn a_container_without_a_hardware_leaf_is_a_static_value() {
    with(100, |ev| {
        let t = array(ev, Ty::Int, 2);
        let xs = vec![
            Agg::Static(Value::Int(Int::from_u64(1))),
            Agg::Static(Value::Int(Int::from_u64(2))),
        ];
        let Some(Agg::Static(v)) = Agg::node(&ev.graph, &ev.tys, t, xs) else {
            panic!("a static value")
        };
        assert_eq!(v.serialize(&ev.tys), "(array int ((int 1) (int 2)))");
    });
}

#[test]
fn a_node_needs_a_container_type_of_its_length() {
    with(100, |ev| {
        let t = array(ev, Ty::Int, 3);
        let xs = vec![Agg::Static(Value::Unit)];
        assert!(Agg::node(&ev.graph, &ev.tys, t, xs).is_none());
        let scalar = ev.tys.mk(Ty::Bool);
        assert!(Agg::node(&ev.graph, &ev.tys, scalar, Vec::new()).is_none());
    });
}

#[test]
fn normalize_charges_an_empty_reference_before_its_zero_exists() {
    let unit3 = |ev: &mut Evaluator<'_>| {
        let t = array(ev, Ty::Unit, 3);
        Agg::Ref(base(ev), t)
    };
    assert_eq!(normal(100, unit3), "(array unit ((unit) (unit) (unit))) 4");
    assert_eq!(normal(3, unit3), "S015 1:1");
    let huge = |ev: &mut Evaluator<'_>| {
        let t = array(ev, Ty::Unit, 1 << 40);
        Agg::Ref(base(ev), t)
    };
    assert_eq!(normal(100, huge), "S015 1:1");
    let mixed = |ev: &mut Evaluator<'_>| {
        let e = array(ev, Ty::Bool, 0);
        let unit = ev.tys.mk(Ty::Unit);
        let t = ev.tys.tuple(vec![unit, e]);
        Agg::Ref(base(ev), t)
    };
    assert_eq!(normal(100, mixed), "(tuple ((unit) (array bool ()))) 3");
}

#[test]
fn normalize_makes_a_scalar_reference_hardware_and_keeps_another_lazy() {
    let wide = |ev: &mut Evaluator<'_>| {
        let t = ev.tys.mk(Ty::UInt(256));
        Agg::Ref(base(ev), t)
    };
    assert_eq!(normal(100, wide), "hardware 4 0");
    let bytes = |ev: &mut Evaluator<'_>| {
        let t = array(ev, Ty::UInt(8), 4);
        Agg::Ref(base(ev), t)
    };
    assert_eq!(normal(100, bytes), "agg 5 0");
    let huge = |ev: &mut Evaluator<'_>| {
        let t = array(ev, Ty::UInt(8), 1 << 40);
        Agg::Ref(base(ev), t)
    };
    assert_eq!(normal(0, huge), "agg 1099511627777 0");
}

/// A tower of `n` array nodes around one hardware leaf.
fn tower(ev: &mut Evaluator<'_>, n: u64) -> Agg {
    let leaf = ev.tys.mk(Ty::Bool);
    let mut ty = leaf;
    let mut a = Agg::Ref(base(ev), leaf);
    for k in 0..n {
        ty = ev.tys.array(ty, Int::from_u64(1));
        a = Agg::Array(
            Node {
                ty,
                size: k + 2,
                depth: k + 2,
                leaves: 1,
                heavy: 0,
            },
            Parts(vec![a]),
        );
    }
    a
}

#[test]
fn the_clone_and_the_drop_of_a_deep_aggregate_keep_their_own_stack() {
    let fuel = 700_000_001;
    with(fuel, |ev| {
        let a = tower(ev, 200_000);
        assert_eq!(a.depth(&ev.tys), 200_001);
        counters::start(fuel);
        let b = a.clone();
        assert_eq!(counters::of(fuel).nodes, 200_001);
        drop(a);
        assert_eq!(b.leaves(&ev.tys), 1);
    });
}

#[test]
fn a_build_visits_each_part_once() {
    let fuel = 700_000_002;
    with(fuel, |ev| {
        counters::start(fuel);
        let t = array(ev, Ty::UInt(8), 5);
        let e = ev.tys.mk(Ty::UInt(8));
        let xs: Vec<Agg> = (0..5).map(|_| Agg::Ref(base(ev), e)).collect();
        assert!(Agg::node(&ev.graph, &ev.tys, t, xs).is_some());
        assert_eq!(counters::of(fuel).nodes, 5);
    });
}

#[test]
fn an_error_of_normalize_is_s010_for_a_type_without_a_zero() {
    let none = |ev: &mut Evaluator<'_>| {
        let t = ev.tys.mk(Ty::Int);
        Agg::Ref(base(ev), t)
    };
    assert_eq!(normal(100, none), format!("{} 1:1", Code::S010));
}

/// The items of the selection cases: two constants that the cases replace, and two structs.
const SHAPES: &str = "const X: Int = 0;\nconst Y: Int = 0;\n\
    struct P { a: UInt[8], z: [Unit; 1099511627776], t: (Bool, [UInt[4]; 3]), e: [Unit; 3] }\n\
    struct Q { a: UInt[8], b: Int }\n";

/// The text of the base of a reference.
fn base_text(ev: &Evaluator<'_>, b: &Base) -> String {
    let name = |p| crate::names::encode(&ev.paths.name(p, &ev.syms.texts));
    match b {
        Base::Name(p) => name(*p),
        Base::Out(i, q) => format!("{}.{}", name(*i), name(*q)),
        Base::Word(m, off) => format!("{}+{off}", name(*m)),
    }
}

/// The part that a selection gave: a static value, a hardware value with its type, name, and
/// size, or a reference with its type, base, and size.
fn describe(ev: &Evaluator<'_>, out: &Out) -> String {
    match ev.store.seen(out) {
        Seen::Static(v) => v.serialize(&ev.tys),
        Seen::Hw(h) => {
            let name = match ev.graph.node(h).map(|n| &n.op) {
                Some(Op::Ref(p)) => base_text(ev, &Base::Name(*p)),
                Some(Op::Out(i, q)) => base_text(ev, &Base::Out(*i, *q)),
                Some(Op::Word(m, off)) => base_text(ev, &Base::Word(*m, *off)),
                _ => String::new(),
            };
            let t = ev.graph.ty(h);
            format!("hw {} {name} {}", ev.tys.text_of(&t), ev.graph.size(h))
        }
        Seen::Agg(a @ Agg::Ref(b, t)) => format!(
            "ref {} {} {}",
            ev.tys.text(*t),
            base_text(ev, b),
            a.size(&ev.graph, &ev.tys)
        ),
        s => ev.text(s),
    }
}

/// A register `r` of the type `t`, as the handle that a use reads.
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

/// The struct type `P` or `Q`: the item 2 or 3.
fn record(ev: &mut Evaluator<'_>, item: usize) -> TyId {
    ev.spec(AT, item, &[])
        .unwrap_or_else(|_| panic!("a struct"))
}

/// The result of the expression `expr` over the constants `X` and `Y`, which `make` sets. The
/// result shows the part, whether it refers, and the used fuel: or the code and the position.
fn sel(expr: &str, fuel: u64, make: impl FnOnce(&mut Evaluator<'_>) -> Vec<Val>) -> String {
    sel_counted(expr, fuel, make).0
}

fn sel_counted(
    expr: &str,
    fuel: u64,
    make: impl FnOnce(&mut Evaluator<'_>) -> Vec<Val>,
) -> (String, u64) {
    let depth = parse::DEFAULT_SYNTAX_DEPTH;
    let file = load(SHAPES).unwrap();
    let e = parse::parse_expr(expr, depth).unwrap().unwrap();
    let top = resolve::resolve_expr(&file, e).unwrap().unwrap();
    let scan = scan::of(&file, Some(&top));
    let mut ev = Evaluator::new(
        &file,
        Some(&top),
        Budget { fuel, depth: 1000 },
        scan,
        super::Elab::new(crate::names::sha16),
    );
    let unit = ev.tys.mk(Ty::Unit);
    for (i, v) in make(&mut ev).into_iter().enumerate() {
        ev.store.finish_const(i, v, unit);
    }
    let before = ev.fuel.left();
    let r = ev.eval(top.expr()).and_then(|o| super::need(top.expr(), o));
    let used = before - ev.fuel.left();
    let text = match r {
        Ok(out) => format!("{} {} {used}", describe(&ev, &out), out.is_ref()),
        Err(Stop::Error(e)) => {
            eprintln!("{}", e.message);
            format!("{} {}:{}", e.code, e.pos.line, e.pos.col)
        }
        Err(Stop::Stack(_)) => "stack".to_owned(),
    };
    (text, counters::of(fuel).selected)
}

/// A register of the type `t` made by `ty`.
fn reg(ty: impl FnOnce(&mut Evaluator<'_>) -> TyId) -> impl FnOnce(&mut Evaluator<'_>) -> Vec<Val> {
    move |ev| {
        let t = ty(ev);
        vec![register(ev, t)]
    }
}

fn p_type(ev: &mut Evaluator<'_>) -> TyId {
    record(ev, 2)
}

#[test]
fn an_implicit_read_of_an_aggregate_register_is_a_reference_and_each_step_adds_a_leaf_field() {
    let f = 700_000_100;
    assert_eq!(sel("X.a", f, reg(p_type)), "hw UInt[8] r$a 1 true 2");
    assert_eq!(
        sel("X.t", f, reg(p_type)),
        "ref (Bool, [UInt[4]; 3]) r$t 6 true 2"
    );
    assert_eq!(
        sel("X.t.1[2]", f, reg(p_type)),
        "hw UInt[4] r$t$1e$2e 1 true 6"
    );
    assert_eq!(sel("X.t[0]", f, reg(p_type)), "hw Bool r$t$0e 1 true 5");
    assert_eq!(
        sel("X", f, reg(|ev| ev.tys.mk(Ty::UInt(8)))),
        "a register true 1"
    );
    assert_eq!(sel("X[0]", f, reg(|ev| ev.tys.mk(Ty::UInt(8)))), "S010 1:1");
}

fn bytes(ev: &mut Evaluator<'_>, len: u64) -> TyId {
    array(ev, Ty::UInt(8), len)
}

#[test]
fn an_index_of_a_reference_takes_the_units_of_a_small_array_and_expands_nothing() {
    let f = 700_000_101;
    let huge = |ev: &mut Evaluator<'_>| bytes(ev, 1 << 40);
    let small = |ev: &mut Evaluator<'_>| bytes(ev, 4);
    assert_eq!(
        sel("X[1099511627775]", f, reg(huge)),
        "hw UInt[8] r$1099511627775e 1 true 4"
    );
    assert_eq!(sel("X[3]", f, reg(small)), "hw UInt[8] r$3e 1 true 4");
    let nested = |ev: &mut Evaluator<'_>| {
        let inner = bytes(ev, 1 << 40);
        ev.tys.array(inner, Int::from_u64(1 << 40))
    };
    assert_eq!(
        sel("X[7][9]", f, reg(nested)),
        "hw UInt[8] r$7e$9e 1 true 7"
    );
    assert_eq!(sel("X[1099511627776]", f, reg(huge)), "S013 1:3");
    let t2 = |ev: &mut Evaluator<'_>| tuple(ev, vec![Ty::Bool, Ty::UInt(8)]);
    assert_eq!(sel("X.2", f, reg(t2)), "S013 1:3");
    assert_eq!(sel("X[1]", f, reg(t2)), "hw UInt[8] r$1e 1 true 4");
}

#[test]
fn a_step_on_a_huge_reference_counts_one_part_and_walks_no_node() {
    let huge = |ev: &mut Evaluator<'_>| bytes(ev, 1 << 40);
    let nested = |ev: &mut Evaluator<'_>| {
        let inner = bytes(ev, 1 << 40);
        ev.tys.array(inner, Int::from_u64(1 << 40))
    };
    let (_, parts) = sel_counted("X[5]", 700_000_102, reg(huge));
    assert_eq!(parts, 1);
    assert_eq!(counters::of(700_000_102).nodes, 0);
    let (_, parts) = sel_counted("X[5][6]", 700_000_103, reg(nested));
    assert_eq!(parts, 2);
    let c = counters::of(700_000_103);
    assert_eq!((c.nodes, c.walked), (0, 0));
}

#[test]
fn a_hardware_index_is_s011_before_the_container_check_and_a_wrong_step_is_s010() {
    let f = 700_000_104;
    let with_index = |ty: fn(&mut Evaluator<'_>) -> TyId| {
        move |ev: &mut Evaluator<'_>| {
            let t = ty(ev);
            let r = register(ev, t);
            let op = Op::Ref(ev.paths.child(None, 0));
            let h = ev.graph.mk(AT, Ty::UInt(2), op, Vec::new());
            vec![r, Val::Hw(h)]
        }
    };
    assert_eq!(sel("X[Y]", f, with_index(|ev| bytes(ev, 4))), "S011 1:3");
    assert_eq!(
        sel("X[Y]", f, with_index(|ev| ev.tys.mk(Ty::UInt(8)))),
        "S011 1:3"
    );
    assert_eq!(sel("X.0", f, reg(|ev| bytes(ev, 4))), "S010 1:1");
    assert_eq!(sel("X.a", f, reg(|ev| bytes(ev, 4))), "S010 1:1");
    assert_eq!(sel("X.y", f, reg(p_type)), "S010 1:1");
}

#[test]
fn a_part_without_a_hardware_leaf_charges_its_zero_size_first_and_does_not_refer() {
    let f = 700_000_105;
    assert_eq!(
        sel("X.e", f, reg(p_type)),
        "(array unit ((unit) (unit) (unit))) false 6"
    );
    assert_eq!(sel("X.z", f, reg(p_type)), "S015 1:1");
    let e = |ev: &mut Evaluator<'_>| {
        let pair = array(ev, Ty::Unit, 2);
        let unit = ev.tys.mk(Ty::Bool);
        let part = ev.tys.tuple(vec![pair, unit]);
        ev.tys.array(part, Int::from_u64(1 << 40))
    };
    assert_eq!(
        sel("X[5].0", f, reg(e)),
        "(array unit ((unit) (unit))) false 8"
    );
    let empty = |ev: &mut Evaluator<'_>| {
        let inner = array(ev, Ty::Unit, 2);
        ev.tys.array(inner, Int::from_u64(1 << 40))
    };
    assert_eq!(sel("X[5]", f, reg(empty)), "S015 1:1");
}

/// A hardware leaf of a node.
fn leaf(ev: &mut Evaluator<'_>, ty: Ty) -> Agg {
    Agg::Hw(
        ev.graph
            .mk(AT, ty, Op::Ref(ev.paths.child(None, 0)), Vec::new()),
    )
}

#[test]
fn a_container_node_gives_its_part_in_its_normal_form() {
    let f = 700_000_106;
    let record_node = |ev: &mut Evaluator<'_>| {
        let t = record(ev, 3);
        let a = leaf(ev, Ty::UInt(8));
        let parts = vec![a, Agg::Static(Value::Int(Int::from_u64(3)))];
        let node = Agg::node(&ev.graph, &ev.tys, t, parts);
        vec![Val::Agg(Box::new(node.unwrap_or(Agg::Static(Value::Unit))))]
    };
    assert_eq!(sel("X.a", f, record_node), "hw UInt[8] X 1 true 2");
    assert_eq!(sel("X.b", f, record_node), "(int 3) true 2");
    assert_eq!(sel("X.c", f, record_node), "S010 1:1");
    let tuple_node = |ev: &mut Evaluator<'_>| {
        let arr = array(ev, Ty::UInt(8), 4);
        let t = tuple(ev, vec![Ty::Bool, Ty::Int, Ty::UInt(8)]);
        let a = leaf(ev, Ty::Bool);
        let parts = vec![
            a,
            Agg::Static(Value::Int(Int::from_u64(3))),
            Agg::Ref(base(ev), ev.tys.mk(Ty::UInt(8))),
        ];
        let _ = arr;
        let node = Agg::node(&ev.graph, &ev.tys, t, parts);
        vec![Val::Agg(Box::new(node.unwrap_or(Agg::Static(Value::Unit))))]
    };
    assert_eq!(sel("X.1", f, tuple_node), "(int 3) true 2");
    assert_eq!(sel("X[2]", f, tuple_node), "hw UInt[8] Y$0 1 true 4");
    assert_eq!(sel("X.3", f, tuple_node), "S013 1:3");
    assert_eq!(sel("X[3]", f, tuple_node), "S013 1:3");
}

#[test]
fn the_leaf_fields_of_a_child_output_append_to_its_port_name() {
    with(100, |ev| {
        let inst = ev.paths.child(None, 5);
        ev.syms.texts.resize(8, String::new());
        ev.syms.texts[6] = "q".to_owned();
        let port = ev.paths.child(None, 6);
        let out = Base::Out(inst, port);
        let field = ev.syms.texts.len();
        ev.syms.texts.push("t".to_owned());
        let out = out.sub(&mut ev.paths, Step::User(field), 0);
        let out = out.sub(&mut ev.paths, Step::Elem(1), 0);
        let out = out.sub(&mut ev.paths, Step::Elem(2), 0);
        assert_eq!(base_text(ev, &out), ".q$t$1e$2e");
        let leaf = ev.tys.mk(Ty::UInt(4));
        let Ok(Val::Hw(h)) = ev.normalize(AT, Agg::Ref(out, leaf)) else {
            panic!("a hardware leaf")
        };
        assert!(matches!(ev.graph.node(h).map(|n| &n.op), Some(Op::Out(..))));
    });
}

/// The leaf of `u.q[1].a[0]` has the core name `u.q$1e$a$0e`, as in Lean.
#[test]
fn the_leaf_of_a_child_output_puts_its_fields_in_order() {
    with(100, |ev| {
        ev.syms.texts.resize(8, String::new());
        ev.syms.texts[5] = "u".to_owned();
        ev.syms.texts[6] = "q".to_owned();
        ev.syms.texts[7] = "a".to_owned();
        let inst = ev.paths.child(None, 5);
        let port = ev.paths.child(None, 6);
        let out = Base::Out(inst, port);
        let out = out.sub(&mut ev.paths, Step::Elem(1), 0);
        let out = out.sub(&mut ev.paths, Step::User(7), 0);
        let out = out.sub(&mut ev.paths, Step::Elem(0), 0);
        assert_eq!(base_text(ev, &out), "u.q$1e$a$0e");
    });
}

#[test]
fn len_of_a_reference_reads_its_type() {
    let f = 700_000_107;
    let len = |ev: &mut Evaluator<'_>, v: Val| match ev.len(AT, vec![Out::Made(v)]) {
        Ok(Some(o)) => ev.store.value(&o).serialize(&ev.tys),
        Ok(None) => "none".to_owned(),
        Err(Stop::Error(e)) => format!("{} {}:{}", e.code, e.pos.line, e.pos.col),
        Err(Stop::Stack(_)) => "stack".to_owned(),
    };
    with(f, |ev| {
        let t = bytes(ev, 1 << 40);
        let r = register(ev, t);
        assert_eq!(len(ev, r), "(int 1099511627776)");
        assert_eq!(f - ev.fuel.left(), 0);
        let flags = tuple(ev, vec![Ty::Bool, Ty::Bool]);
        let r = register(ev, flags);
        assert_eq!(len(ev, r), format!("{} 1:1", Code::S010));
        let flags = array(ev, Ty::Bool, 2);
        let parts = vec![leaf(ev, Ty::Bool), Agg::Static(Value::Bool(true))];
        let node = Agg::node(&ev.graph, &ev.tys, flags, parts);
        let v = Val::Agg(Box::new(node.unwrap_or(Agg::Static(Value::Unit))));
        assert_eq!(len(ev, v), "(int 2)");
        assert_eq!(f - ev.fuel.left(), 0);
    });
}

/// `struct R { a: Bool, b: UInt[8], c: SInt[3] }` as a specialization of the table.
fn three_fields(ev: &mut Evaluator<'_>) -> TyId {
    let s = ev.tys.begin_spec("R", 0, Vec::new(), false);
    let fields = vec![
        ev.tys.mk(Ty::Bool),
        ev.tys.mk(Ty::UInt(8)),
        ev.tys.mk(Ty::SInt(3)),
    ];
    let (meta, depth) = ev.tys.struct_meta(s, &fields);
    ev.tys.finish_spec(s, fields, meta, depth)
}

#[test]
fn the_table_stores_the_offset_of_each_part_of_a_word() {
    with(100, |ev| {
        let arr = array(ev, Ty::UInt(8), 4);
        let tup = tuple(
            ev,
            vec![Ty::Bool, Ty::UInt(8), Ty::SInt(3), Ty::Unit, Ty::Bool],
        );
        let rec = three_fields(ev);
        let offsets = |ev: &Evaluator<'_>, t: TyId, n: u64| -> Vec<u64> {
            (0..n).map(|k| ev.tys.offset(t, k)).collect()
        };
        assert_eq!(offsets(ev, arr, 4), [0, 8, 16, 24]);
        assert_eq!(offsets(ev, tup, 5), [0, 1, 9, 12, 12]);
        assert_eq!(offsets(ev, rec, 3), [0, 1, 9]);
        let nested = tuple(ev, vec![Ty::Bool]);
        let both = ev.tys.tuple(vec![rec, arr, nested]);
        assert_eq!(offsets(ev, both, 3), [0, 12, 44]);
        let scalar = ev.tys.mk(Ty::UInt(8));
        assert_eq!(ev.tys.offset(scalar, 0), 0);
    });
}

#[test]
fn a_step_on_a_word_adds_the_offset_and_makes_no_path_node() {
    let fuel = 700_000_120;
    with(fuel, |ev| {
        let m = ev.paths.child(None, 1);
        let before = counters::of(fuel).paths;
        let tup = tuple(ev, vec![Ty::Bool, Ty::UInt(8), Ty::SInt(3)]);
        let word = Base::Word(m, 5);
        let part = word.sub(&mut ev.paths, Step::Elem(2), ev.tys.offset(tup, 2));
        assert_eq!(part, Base::Word(m, 14));
        let again = part.sub(&mut ev.paths, Step::Elem(0), 0);
        assert_eq!(again, Base::Word(m, 14));
        assert_eq!(counters::of(fuel).paths, before);
        // A name ignores the offset and adds its field.
        let name = Base::Name(m).sub(&mut ev.paths, Step::Elem(2), 9);
        assert_ne!(name, Base::Name(m));
        assert_eq!(counters::of(fuel).paths, before + 1);
    });
}

#[test]
fn a_word_leaf_has_the_size_of_a_name_of_its_type() {
    with(100, |ev| {
        let m = ev.paths.child(None, 1);
        let op = Base::Word(m, 12).op();
        assert!(matches!(op, Op::Word(p, 12) if p == m));
        let wide = ev.graph.mk(AT, Ty::UInt(256), op, Vec::new());
        assert_eq!(ev.graph.size(wide), 4);
        let flag = ev.graph.mk(AT, Ty::Bool, Op::Word(m, 0), Vec::new());
        assert_eq!(ev.graph.size(flag), 1);
    });
}

#[test]
fn a_selection_on_a_word_reference_adds_the_offset_of_the_part() {
    let word = |ev: &mut Evaluator<'_>| {
        ev.syms.texts.push("w".to_owned());
        let m = ev.paths.child(None, ev.syms.texts.len() - 1);
        let t = record(ev, 2);
        vec![Agg::Ref(Base::Word(m, 5), t).into_val()]
    };
    // The record `P` has the parts `a: UInt[8]`, `z` and `e` without bits, and
    // `t: (Bool, [UInt[4]; 3])`. A step reads the stored offset: 8 for `t`, 1 for its second
    // part, and 4 for the element 1. The text ends with the used fuel, which these cases do
    // not compare.
    let part = |expr: &str, fuel: u64| {
        let text = sel(expr, fuel, word);
        text.rsplit_once(' ')
            .map_or(text.clone(), |(head, _)| head.to_owned())
    };
    assert_eq!(part("X.a", 700_000_121), "hw UInt[8] w+5 1 true");
    assert_eq!(part("X.t.0", 700_000_122), "hw Bool w+13 1 true");
    assert_eq!(part("X.t.1[0]", 700_000_123), "hw UInt[4] w+14 1 true");
    assert_eq!(part("X.t.1[2]", 700_000_124), "hw UInt[4] w+22 1 true");
}
