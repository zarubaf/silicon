// SPDX-License-Identifier: Apache-2.0
//! The cases of the aggregate form in `Silicon.Source.Test.Eval` and `Test.Elab` in Lean (design
//! section 5.1): the size of a name, the stored numbers of a node, the static form of a
//! container without a hardware leaf, and `normalize`. The walks over a deep aggregate keep
//! their own stack.

use super::{Code, Evaluator, Res, Stop};
use crate::agg::{Agg, Base, Node, Parts};
use crate::counters;
use crate::hw::{Op, Val};
use crate::int::Int;
use crate::names::{Name, Step};
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
        let out = Op::Out(
            ev.paths.child(None, 2),
            Name {
                head: "q".to_owned(),
                rest: Vec::new(),
            },
        );
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
