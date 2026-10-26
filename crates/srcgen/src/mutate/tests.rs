// SPDX-License-Identifier: Apache-2.0
//! Tests of the mutation kinds and their predictions.

use super::super::build::typed;
use super::super::eval::Value;
use super::super::program::tests::{TEXT, program};
use super::super::program::{
    EnumDef, FTy, FieldTy, HBin, HExpr, Item, Match, Pattern, Place, Ports, Program, Radix, SBin,
    SExpr, STy, Scalar, Stmt, Ty, Un, Variant,
};
use super::*;
use num_bigint::{BigInt, BigUint};
use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::TestRunner;

fn dec(n: i64) -> SExpr {
    SExpr::Int(BigInt::from(n), Radix::Dec)
}

fn u8() -> Ty {
    Ty::UInt(dec(8))
}

fn name(n: &str) -> HExpr {
    HExpr::Name(n.to_owned())
}

fn connect(n: &str, v: HExpr) -> Stmt {
    Stmt::Connect(Place::Name(n.to_owned()), v)
}

fn module(n: &str, body: Vec<Stmt>) -> Item {
    Item::Module {
        name: n.to_owned(),
        params: vec![],
        clocked: false,
        body,
    }
}

/// A program of `items` with the top `M0()`. Only the items matter
/// to a mutation.
fn of(items: Vec<Item>) -> Program {
    Program {
        items,
        top: "M0".to_owned(),
        args: vec![],
        ports: Ports {
            clocked: false,
            inputs: vec![],
            outputs: vec![],
        },
        probe: (dec(0), Value::Int(BigInt::from(0))),
        records: Vec::new(),
    }
}

/// `module M0() domains() { output o0: Bool; o0 := false; }`.
fn smallest() -> Program {
    of(vec![module(
        "M0",
        vec![
            Stmt::Output("o0".to_owned(), Ty::Bool),
            connect("o0", HExpr::Static(SExpr::Bool(false))),
        ],
    )])
}

/// `input i0: UInt[8]; output o0: UInt[8];`, then `rest`.
fn ports_then(rest: Vec<Stmt>) -> Vec<Stmt> {
    let mut body = vec![
        Stmt::Input("i0".to_owned(), u8()),
        Stmt::Output("o0".to_owned(), u8()),
    ];
    body.extend(rest);
    body
}

fn all(p: &Program, kind: Kind) -> Vec<Mutant> {
    let k = index(kind);
    (0..sites(kind, &p.items, &p.top))
        .map(|s| mutate(p, k, u32::try_from(s).unwrap()))
        .collect()
}

/// A draw that picks `kind`: the kinds of ports come from the draws that
/// leave the remainder `PORT_ODDS - 1`, the kinds of `@field` from the
/// others with the remainder `FIELD_ODDS - 1` of the quotient, the kinds
/// of queries from the digit above those of `EarlyStep`, and the other
/// kinds from the rest.
fn index(kind: Kind) -> u32 {
    let at = KINDS.iter().position(|&k| k == kind).unwrap();
    let queries = KINDS.len() - QUERY_KINDS;
    let gaps = OLD_KINDS + PORT_KINDS + FIELD_KINDS;
    let draw = if (gaps..queries).contains(&at) {
        // The digit above those of the queries picks the kind of the gaps.
        (at - gaps) * GAP_SPLIT * GAP_ODDS + (GAP_ODDS - 1) * GAP_SPLIT
    } else if at >= queries {
        // The digit above those of `EarlyStep` picks the kind of queries.
        (at - queries) * QUERY_SPLIT * QUERY_ODDS + (QUERY_ODDS - 1) * QUERY_SPLIT
    } else if at >= OLD_KINDS + PORT_KINDS {
        let nth = at - OLD_KINDS - PORT_KINDS;
        (nth * FIELD_ODDS + FIELD_ODDS - 1) * PORT_ODDS
    } else if at >= OLD_KINDS {
        (at - OLD_KINDS) * PORT_ODDS + PORT_ODDS - 1
    } else {
        (0..PORT_ODDS * FIELD_ODDS)
            .map(|t| at + OLD_KINDS * t)
            .find(|d| {
                d % PORT_ODDS != PORT_ODDS - 1 && (d / PORT_ODDS) % FIELD_ODDS != FIELD_ODDS - 1
            })
            .unwrap()
    };
    u32::try_from(draw).unwrap()
}

fn programs() -> Vec<Program> {
    let mut runner = TestRunner::deterministic();
    (0..400)
        .map(|_| typed().new_tree(&mut runner).unwrap().current().unwrap())
        .collect()
}

#[test]
fn delete_predicts_s018_in_the_top_frame() {
    let p = of(vec![module(
        "M0",
        ports_then(vec![
            Stmt::Let {
                name: "l0".to_owned(),
                mutable: false,
                ty: None,
                value: name("i0"),
            },
            connect("o0", name("l0")),
        ]),
    )]);
    let k = index(Kind::Delete);
    assert_eq!(sites(Kind::Delete, &p.items, &p.top), 4);
    let m = mutate(&p, k, 3);
    assert_eq!(m.text, p.text().replace("    o0 := l0;\n", ""));
    assert_eq!(m.expect, Some("S018"));
    let m = mutate(&p, k, 2);
    assert_eq!(m.text, p.text().replace("    let l0 = i0;\n", ""));
    assert_eq!(m.expect, Some("S003"));
    assert_eq!(m.what, "delete statement 3 of M0");
}

#[test]
fn delete_in_a_loop_predicts_nothing() {
    let body = vec![Stmt::Wire("w0".to_owned(), u8()), connect("w0", name("i0"))];
    let p = of(vec![module(
        "M0",
        ports_then(vec![
            Stmt::Let {
                name: "v0".to_owned(),
                mutable: true,
                ty: Some(u8()),
                value: name("i0"),
            },
            Stmt::For("j0".to_owned(), dec(0), dec(2), body),
            Stmt::Assign("v0".to_owned(), name("i0")),
            connect("o0", name("v0")),
        ]),
    )]);
    let deleted = |line: &str| {
        all(&p, Kind::Delete)
            .into_iter()
            .find(|m| m.text == p.text().replacen(line, "", 1))
            .unwrap()
    };
    assert_eq!(deleted("        w0 := i0;\n").expect, None);
    assert_eq!(deleted("    v0 = i0;\n").expect, None);
    assert_eq!(deleted("    o0 := v0;\n").expect, Some("S018"));
}

#[test]
fn delete_of_a_used_item_predicts_s003() {
    let helper = Item::Helper {
        mut_first: false,
        name: "h0".to_owned(),
        params: vec![("x0".to_owned(), u8().into())],
        ret: u8().into(),
        body: vec![],
        result: name("x0"),
    };
    let c0 = Item::Const {
        name: "C0".to_owned(),
        ty: STy::Nat,
        value: dec(8),
    };
    let m0 = module(
        "M0",
        vec![
            Stmt::Input("i0".to_owned(), Ty::UInt(SExpr::Name("C0".to_owned()))),
            Stmt::Output("o0".to_owned(), Ty::Bool),
            connect("o0", HExpr::Static(SExpr::Bool(false))),
        ],
    );
    let p = of(vec![c0, helper, m0]);
    assert_eq!(sites(Kind::Delete, &p.items, &p.top), 5);
    let k = index(Kind::Delete);
    let m = mutate(&p, k, 0);
    assert!(!m.text.contains("const C0"));
    assert_eq!(
        (m.what.as_str(), m.expect),
        ("delete item C0", Some("S003"))
    );
    let m = mutate(&p, k, 1);
    assert!(!m.text.contains("fn h0"));
    assert_eq!(m.expect, None);
    assert!(
        all(&p, Kind::Delete)
            .iter()
            .all(|m| m.text.contains("module M0"))
    );
}

#[test]
fn duplicate_predicts_s002() {
    let p = of(vec![module(
        "M0",
        ports_then(vec![
            Stmt::Wire("w0".to_owned(), u8()),
            connect("w0", name("i0")),
            connect("o0", name("w0")),
        ]),
    )]);
    let m = all(&p, Kind::Duplicate)
        .into_iter()
        .find(|m| {
            m.text
                .contains("    wire w0: UInt[8];\n    wire w0: UInt[8];\n")
        })
        .unwrap();
    assert_eq!(m.expect, Some("S002"));
    assert_eq!(m.text.matches("wire w0").count(), 2);
}

#[test]
fn rename_writes_q0() {
    let p = program();
    assert_eq!(p.text(), TEXT);
    // C0 0; f0 5 (f0, x0, x1, C0, x1); h0 2 (x0, l0); M0 22 (f0, P0;
    // P0; M1; w0, i0, i0, u0; u0, h0, i0; w0; P0, v0, v0, j0; s0; r0,
    // r0; o0, i0; o1); M1 2 (o0, i0).
    assert_eq!(sites(Kind::Rename, &p.items, &p.top), 31);
    for m in all(&p, Kind::Rename) {
        assert_eq!(m.text.matches("q0").count(), 1, "{}", m.what);
        assert_eq!(m.expect, Some("S003"));
    }
    let m = mutate(&p, index(Kind::Rename), 30);
    assert_eq!(m.what, "rename i0 to q0 in M1");
}

#[test]
fn arity_mutations_predict_s007() {
    let p = program();
    let find = |kind: Kind, text: &str| {
        all(&p, kind)
            .into_iter()
            .find(|m| m.text.contains(text))
            .unwrap()
    };
    let m = find(Kind::DropArg, "instance u0 = M1();");
    assert_eq!(m.expect, Some("S007"));
    assert_eq!(m.what, "drop argument 1 of M1 in M0");
    let m = find(Kind::AddArg, "instance u0 = M1(0b10, 0);");
    assert_eq!(m.expect, Some("S007"));
    let m = find(Kind::DropArg, "let s0: Int = f0(P0);");
    assert_eq!(m.expect, Some("S007"));
    assert_eq!(m.what, "drop argument 2 of f0 in M0");
}

#[test]
fn an_arity_change_of_a_call_through_a_value_predicts_where_the_site_always_runs() {
    use super::super::program::{ComptimeFn, FnTy};
    let f0 = Item::ComptimeFn(ComptimeFn {
        name: "f0".to_owned(),
        params: vec![("x0".to_owned(), STy::Nat), ("x1".to_owned(), STy::Int)],
        ret: STy::Int,
        base: SExpr::Name("x1".to_owned()),
        step: SExpr::Name("x1".to_owned()),
    });
    let value = Item::Const {
        name: "F0".to_owned(),
        ty: STy::Fn(Box::new(FnTy {
            params: vec![(false, STy::Nat), (false, STy::Int)],
            ret: STy::Int,
        })),
        value: SExpr::Name("f0".to_owned()),
    };
    let call = |f: &str| SExpr::Call(f.to_owned(), vec![dec(1), dec(2)]);
    let m0 = module(
        "M0",
        vec![
            Stmt::Output("o0".to_owned(), Ty::Bool),
            Stmt::StaticLet("s0".to_owned(), STy::Int, call("f0")),
            Stmt::StaticLet("s1".to_owned(), STy::Int, call("F0")),
            connect("o0", HExpr::Static(SExpr::Bool(false))),
        ],
    );
    let p = of(vec![f0, value, m0]);
    let by_name = |kind: Kind, text: &str| {
        all(&p, kind)
            .into_iter()
            .find(|m| m.text.contains(text))
            .unwrap()
    };
    // A named call has its arity checked in pass 4, on dead code too.
    let m = by_name(Kind::DropArg, "let s0: Int = f0(1);");
    assert_eq!(m.expect, Some("S007"));
    let m = by_name(Kind::AddArg, "let s0: Int = f0(1, 2, 0);");
    assert_eq!(m.expect, Some("S007"));
    // A call through a value is checked when it runs, in pass 5; the
    // top frame of a module always runs.
    let m = by_name(Kind::DropArg, "let s1: Int = F0(1);");
    assert_eq!(m.expect, Some("S007"));
    let m = by_name(Kind::AddArg, "let s1: Int = F0(1, 2, 0);");
    assert_eq!(m.expect, Some("S007"));
    // A name that no declaration holds is still unresolved in pass 3.
    let m = by_name(Kind::Rename, "let s1: Int = q0(1, 2);");
    assert_eq!(m.expect, Some("S003"));
}

#[test]
fn an_arity_change_of_a_call_through_a_value_predicts_nothing_where_the_site_may_not_run() {
    use super::super::program::{ComptimeFn, FnTy};
    let f0 = Item::ComptimeFn(ComptimeFn {
        name: "f0".to_owned(),
        params: vec![("x0".to_owned(), STy::Nat), ("x1".to_owned(), STy::Int)],
        ret: STy::Int,
        base: SExpr::Name("x1".to_owned()),
        step: SExpr::Name("x1".to_owned()),
    });
    let value = Item::Const {
        name: "F0".to_owned(),
        ty: STy::Fn(Box::new(FnTy {
            params: vec![(false, STy::Nat), (false, STy::Int)],
            ret: STy::Int,
        })),
        value: SExpr::Name("f0".to_owned()),
    };
    let call = SExpr::Call("F0".to_owned(), vec![dec(1), dec(2)]);
    let hcall = HExpr::Static(call.clone());
    let boolean = |b| Box::new(SExpr::Bool(b));
    let unused = Item::Const {
        name: "K0".to_owned(),
        ty: STy::Int,
        value: call.clone(),
    };
    let m0 = module(
        "M0",
        vec![
            Stmt::Output("o0".to_owned(), Ty::Bool),
            Stmt::StaticLet(
                "s0".to_owned(),
                STy::Int,
                SExpr::If(boolean(false), Box::new(call.clone()), Box::new(dec(0))),
            ),
            Stmt::StaticLet(
                "s1".to_owned(),
                STy::Bool,
                SExpr::Binary(SBin::Land, boolean(false), Box::new(call.clone())),
            ),
            Stmt::StaticLet(
                "s2".to_owned(),
                STy::Bool,
                SExpr::Binary(SBin::Lor, boolean(true), Box::new(call.clone())),
            ),
            Stmt::Let {
                name: "h0".to_owned(),
                mutable: false,
                ty: None,
                value: HExpr::Binary(
                    HBin::Lor,
                    Box::new(HExpr::Static(SExpr::Bool(true))),
                    Box::new(hcall.clone()),
                ),
            },
            Stmt::Let {
                name: "h1".to_owned(),
                mutable: false,
                ty: None,
                value: HExpr::If(
                    Box::new(HExpr::Static(SExpr::Bool(false))),
                    Box::new(hcall),
                    Box::new(HExpr::Static(dec(0))),
                ),
            },
            Stmt::If(
                SExpr::Bool(false),
                vec![Stmt::StaticLet("s3".to_owned(), STy::Int, call.clone())],
                None,
            ),
            Stmt::For(
                "j0".to_owned(),
                dec(0),
                dec(0),
                vec![Stmt::StaticLet("s4".to_owned(), STy::Int, call)],
            ),
            connect("o0", HExpr::Static(SExpr::Bool(false))),
        ],
    );
    let p = of(vec![f0, value, unused, m0]);
    for kind in [Kind::DropArg, Kind::AddArg] {
        let ms = all(&p, kind);
        assert_eq!(ms.len(), 8, "{kind:?}");
        assert!(ms.iter().all(|m| m.expect.is_none()), "{ms:?}");
    }
}

#[test]
fn width_mutations() {
    let p = of(vec![module(
        "M0",
        vec![
            Stmt::Input("i0".to_owned(), u8()),
            Stmt::Output("o0".to_owned(), Ty::Bool),
            connect("o0", HExpr::Static(SExpr::Bool(false))),
        ],
    )]);
    let m = mutate(&p, index(Kind::Widen), 0);
    assert_eq!(m.text, p.text().replace("UInt[8]", "UInt[(8 + 1)]"));
    assert_eq!(m.expect, None);
    let m = mutate(&p, index(Kind::ZeroWidth), 0);
    assert_eq!(m.text, p.text().replace("UInt[8]", "UInt[0]"));
    assert_eq!(m.expect, None);
}

#[test]
fn fault_writes_a_division_by_zero() {
    let p = program();
    let before = p.text().matches("(1 / 0)").count();
    let ms = all(&p, Kind::Fault);
    assert!(ms.len() > 20);
    for m in ms {
        assert_eq!(m.text.matches("(1 / 0)").count(), before + 1, "{}", m.what);
        assert_eq!(m.expect, None);
    }
}

#[test]
fn kinds_fall_back_in_order() {
    let p = smallest();
    let m = mutate(&p, index(Kind::AddArg), 0);
    assert_eq!(
        m.text,
        "module M0() domains() {\n    output o0: Bool;\n    o0 := (1 / 0);\n}\n"
    );
    assert_eq!(mutate(&p, 8, 5), mutate(&p, 0, 5));
}

#[test]
fn each_kind_changes_the_text() {
    for p in programs() {
        let text = p.text();
        for kind in 0..8 {
            for site in [0, 7919] {
                let m = mutate(&p, kind, site);
                assert_ne!(m.text, text, "{}", m.what);
                let lexed = syntax::lex(&m.text, 4096);
                assert!(lexed.errors.is_empty(), "{}: {:?}", m.what, lexed.errors);
            }
        }
    }
}

#[test]
fn predictions_are_frequent() {
    let mut applied = [0; 8];
    let mut predicted = 0;
    let mut codes = std::collections::BTreeSet::new();
    let ps = programs();
    for (n, p) in ps.iter().enumerate() {
        let kind = index(KINDS[n % 8]);
        if sites(KINDS[n % 8], &p.items, &p.top) > 0 {
            applied[n % 8] += 1;
        }
        let m = mutate(p, kind, u32::try_from(n).unwrap().wrapping_mul(7919));
        if let Some(c) = m.expect {
            predicted += 1;
            codes.insert(c);
        }
    }
    assert!(applied.iter().all(|&a| a >= 20), "{applied:?}");
    assert!(
        predicted * 10 >= ps.len() * 4,
        "{predicted} of {}",
        ps.len()
    );
    for code in ["S002", "S003", "S007", "S018"] {
        assert!(codes.contains(code), "{code} missing from {codes:?}");
    }
}

/// `struct S0(comptime W0: Nat) { m0: UInt[W0], m1: Int }` and
/// `comptime fn k0(mut a0: List[Int], x1: Int) -> Int` with the const
/// `F0` that holds it.
fn slice_two_items() -> Vec<Item> {
    use super::super::program::{FnTy, MutFn, StructDef};
    let s0 = Item::Struct(StructDef {
        name: "S0".to_owned(),
        params: vec!["W0".to_owned()],
        fields: vec![
            ("m0".to_owned(), FieldTy::UInt(SExpr::Name("W0".to_owned()))),
            ("m1".to_owned(), FieldTy::Static(STy::Int)),
        ],
    });
    let list = STy::List(Box::new(STy::Int));
    let k0 = Item::MutFn(MutFn {
        name: "k0".to_owned(),
        root: list.clone(),
        pre: Vec::new(),
        update: SExpr::Name("x1".to_owned()),
        ret: SExpr::Len(Box::new(SExpr::Name("a0".to_owned()))),
        diag: None,
    });
    let f0 = Item::Const {
        name: "F0".to_owned(),
        ty: STy::Fn(Box::new(FnTy {
            params: vec![(true, list), (false, STy::Int)],
            ret: STy::Int,
        })),
        value: SExpr::Name("k0".to_owned()),
    };
    vec![s0, k0, f0]
}

/// A module that builds a list, calls `k0` on it by name, as a receiver
/// and through `F0`, and ends with the top outputs.
fn mut_call_module() -> Item {
    let call = |n: &str, f: &str, receiver| Stmt::MutCall {
        name: n.to_owned(),
        root: "s0".to_owned(),
        f: f.to_owned(),
        args: vec![dec(1)],
        receiver,
    };
    module(
        "M0",
        vec![
            Stmt::Output("o0".to_owned(), Ty::Bool),
            Stmt::MutLet(
                "s0".to_owned(),
                STy::List(Box::new(STy::Int)),
                SExpr::NewList(STy::Int),
            ),
            call("s1", "k0", false),
            call("s2", "k0", true),
            call("s3", "F0", false),
            Stmt::Push("s0".to_owned(), dec(2)),
            Stmt::Diagnostic("d0".to_owned(), SExpr::Name("s1".to_owned())),
            connect("o0", HExpr::Static(SExpr::Bool(false))),
        ],
    )
}

fn slice_two() -> Program {
    let mut items = slice_two_items();
    items.push(mut_call_module());
    of(items)
}

fn find(p: &Program, kind: Kind, text: &str) -> Mutant {
    all(p, kind)
        .into_iter()
        .find(|m| m.text.contains(text))
        .unwrap_or_else(|| panic!("no {kind:?} mutant with `{text}`"))
}

#[test]
fn delete_of_a_mut_root_predicts_s003() {
    let p = slice_two();
    let root = "    let mut s0: List[Int] = list(Int);\n";
    let m = all(&p, Kind::Delete)
        .into_iter()
        .find(|m| m.text == p.text().replacen(root, "", 1))
        .unwrap();
    assert_eq!(m.expect, Some("S003"));
    // The call result `s1` is read by the `diagnostic`; `s2` is not.
    let result = "    let s1: Int = k0(s0, 1);\n";
    let m = all(&p, Kind::Delete)
        .into_iter()
        .find(|m| m.text == p.text().replacen(result, "", 1))
        .unwrap();
    assert_eq!(m.expect, Some("S003"));
    let unread = "    let s2: Int = s0.k0(1);\n";
    let m = all(&p, Kind::Delete)
        .into_iter()
        .find(|m| m.text == p.text().replacen(unread, "", 1))
        .unwrap();
    assert_eq!(m.expect, None);
    // A statement that declares nothing predicts nothing, in the top
    // frame too.
    for line in ["    s0.push(2);\n", "    diagnostic(\"d0\", s1);\n"] {
        let m = all(&p, Kind::Delete)
            .into_iter()
            .find(|m| m.text == p.text().replacen(line, "", 1))
            .unwrap();
        assert_eq!(m.expect, None, "{line}");
    }
}

#[test]
fn delete_of_a_struct_item_predicts_s003_only_where_it_is_used() {
    let mut p = slice_two();
    let delete = |p: &Program| {
        all(p, Kind::Delete)
            .into_iter()
            .find(|m| !m.text.contains("struct S0"))
            .unwrap()
    };
    // No statement or item names the struct: no prediction.
    assert_eq!(delete(&p).expect, None);
    // A constructor names it.
    if let Some(Item::Module { body, .. }) = p.items.last_mut() {
        let record = SExpr::Record("S0".to_owned(), vec![dec(3)], vec![dec(1), dec(2)]);
        body.insert(1, Stmt::StaticLet("s9".to_owned(), STy::Int, record));
    }
    assert_eq!(delete(&p).expect, Some("S003"));
}

#[test]
fn drop_and_add_arg_of_a_receiver_call_predict_s007() {
    let p = slice_two();
    let m = find(&p, Kind::DropArg, "let s2: Int = s0.k0();");
    assert_eq!(m.expect, Some("S007"));
    assert_eq!(m.what, "drop argument 1 of k0 in M0");
    let m = find(&p, Kind::DropArg, "let s1: Int = k0(s0);");
    assert_eq!(m.expect, Some("S007"));
    let m = find(&p, Kind::AddArg, "let s2: Int = s0.k0(1, 0);");
    assert_eq!(m.expect, Some("S007"));
    // A call through the value `F0` checks its arguments when it runs,
    // and this call is in the top frame.
    let m = find(&p, Kind::DropArg, "let s3: Int = F0(s0);");
    assert_eq!(m.expect, Some("S007"));
    let m = find(&p, Kind::AddArg, "let s3: Int = F0(s0, 1, 0);");
    assert_eq!(m.expect, Some("S007"));
}

#[test]
fn widths_of_a_struct_field_are_width_sites() {
    let p = slice_two();
    let m = find(&p, Kind::Widen, "m0: UInt[(W0 + 1)],");
    assert_eq!(m.expect, None);
    assert_eq!(m.what, "change width W0 to (W0 + 1) in S0");
    let m = find(&p, Kind::ZeroWidth, "m0: UInt[0],");
    assert_eq!(m.expect, None);
    assert_eq!(m.text, p.text().replace("m0: UInt[W0]", "m0: UInt[0]"));
}

#[test]
fn duplicate_of_a_slice_two_item_or_declaration_predicts_s002() {
    let p = slice_two();
    let doubled = |m: &Mutant, text: &str| m.text.matches(text).count() == 2;
    let item = all(&p, Kind::Duplicate)
        .into_iter()
        .find(|m| doubled(m, "struct S0(comptime W0: Nat) {"))
        .unwrap();
    assert_eq!(item.expect, Some("S002"));
    for text in [
        "const F0: fn (mut List[Int], Int) -> Int = k0;",
        "let mut s0: List[Int] = list(Int);",
        "let s1: Int = k0(s0, 1);",
    ] {
        let m = all(&p, Kind::Duplicate)
            .into_iter()
            .find(|m| doubled(m, text))
            .unwrap_or_else(|| panic!("no duplicate of `{text}`"));
        assert_eq!(m.expect, Some("S002"), "{text}");
    }
    // A `push` and a `diagnostic` declare nothing, so a duplicate of the
    // module is the only copy that holds them twice.
    for text in [
        "    s0.push(2);\n    s0.push(2);\n",
        "    diagnostic(\"d0\", s1);\n    diagnostic(\"d0\", s1);\n",
    ] {
        assert!(
            all(&p, Kind::Duplicate)
                .iter()
                .all(|m| !m.text.contains(text))
        );
    }
}

#[test]
fn rename_of_a_slice_two_name_predicts_s003() {
    let p = slice_two();
    let renamed = all(&p, Kind::Rename);
    for text in [
        "let mut s0: List[Int] = list(Int);\n    let s1: Int = q0(s0, 1);",
        "let s2: Int = q0.k0(1);",
        "let s2: Int = s0.q0(1);",
        "let s3: Int = q0(s0, 1);",
        "s0.push(2);\n    diagnostic(\"d0\", q0);",
        "q0.push(2);",
    ] {
        assert!(renamed.iter().any(|m| m.text.contains(text)), "{text}");
    }
    assert!(renamed.iter().all(|m| m.expect == Some("S003")));
}

#[test]
fn fault_in_a_diagnostic_value_predicts_nothing() {
    let p = slice_two();
    let m = find(&p, Kind::Fault, "diagnostic(\"d0\", (1 / 0));");
    assert_eq!(m.expect, None);
}

fn list_ty() -> STy {
    STy::List(Box::new(STy::Int))
}

fn mut_let(n: &str) -> Stmt {
    Stmt::MutLet(n.to_owned(), list_ty(), SExpr::NewList(STy::Int))
}

fn mut_call(n: &str, root: &str, f: &str, receiver: bool) -> Stmt {
    Stmt::MutCall {
        name: n.to_owned(),
        root: root.to_owned(),
        f: f.to_owned(),
        args: vec![dec(1)],
        receiver,
    }
}

/// `slice_two` with the body of `M0` replaced by `body`, after the output.
fn slice_two_with(body: Vec<Stmt>) -> Program {
    let mut items = slice_two_items();
    let mut stmts = vec![Stmt::Output("o0".to_owned(), Ty::Bool)];
    stmts.extend(body);
    stmts.push(connect("o0", HExpr::Static(SExpr::Bool(false))));
    items.push(module("M0", stmts));
    of(items)
}

#[test]
fn immutable_predicts_s008_where_a_named_mut_actual_uses_the_root() {
    let p = slice_two();
    let m = find(&p, Kind::Immutable, "let s0: List[Int] = list(Int);");
    assert_eq!(m.expect, Some("S008"));
    assert_eq!(m.what, "make s0 immutable in M0");
    assert_eq!(m.text, p.text().replace("let mut s0", "let s0"));
    // A `push` is a named `mut` actual too.
    let p = slice_two_with(vec![mut_let("s0"), Stmt::Push("s0".to_owned(), dec(2))]);
    assert_eq!(all(&p, Kind::Immutable)[0].expect, Some("S008"));
    // A `pop` and a receiver call are.
    let p = slice_two_with(vec![
        mut_let("s0"),
        Stmt::PopLet("s1".to_owned(), "s0".to_owned()),
    ]);
    assert_eq!(all(&p, Kind::Immutable)[0].expect, Some("S008"));
    let p = slice_two_with(vec![mut_let("s0"), mut_call("s1", "s0", "k0", true)]);
    assert_eq!(all(&p, Kind::Immutable)[0].expect, Some("S008"));
}

#[test]
fn immutable_predicts_nothing_where_pass_four_cannot_see_the_mutation() {
    // No mutation: the mutant is accepted.
    let p = slice_two_with(vec![mut_let("s0")]);
    assert_eq!(all(&p, Kind::Immutable)[0].expect, None);
    // The only mutation is a call through a function value.
    let p = slice_two_with(vec![mut_let("s0"), mut_call("s1", "s0", "F0", false)]);
    assert_eq!(all(&p, Kind::Immutable)[0].expect, None);
    // Each root has its own mutations.
    let p = slice_two_with(vec![
        mut_let("s0"),
        mut_call("s1", "s0", "F0", false),
        mut_let("s2"),
        mut_call("s3", "s2", "k0", false),
    ]);
    let m = all(&p, Kind::Immutable);
    assert_eq!(
        m.iter().map(|m| m.expect).collect::<Vec<_>>(),
        [None, Some("S008")]
    );
}

/// `fn g0(mut a0: UInt[8], x1: UInt[8]) -> UInt[8] { a0 = x1; a0 }` and a
/// module that declares `let mut v0` and then `body`.
fn hardware_root(body: Vec<Stmt>) -> Program {
    let helper = Item::Helper {
        name: "g0".to_owned(),
        params: vec![
            ("a0".to_owned(), u8().into()),
            ("x1".to_owned(), u8().into()),
        ],
        mut_first: true,
        ret: u8().into(),
        body: vec![Stmt::Assign("a0".to_owned(), name("x1"))],
        result: name("a0"),
    };
    let mut stmts = ports_then(vec![Stmt::Let {
        name: "v0".to_owned(),
        mutable: true,
        ty: Some(u8()),
        value: name("i0"),
    }]);
    stmts.extend(body);
    stmts.push(connect("o0", name("v0")));
    of(vec![helper, module("M0", stmts)])
}

fn let_of(n: &str, value: HExpr) -> Stmt {
    Stmt::Let {
        name: n.to_owned(),
        mutable: false,
        ty: None,
        value,
    }
}

#[test]
fn immutable_of_a_hardware_root_follows_its_mutations() {
    let call = HExpr::Call("g0".to_owned(), vec![name("v0"), name("i0")]);
    let p = hardware_root(vec![let_of("l0", call)]);
    let m = find(&p, Kind::Immutable, "let v0: UInt[8] = i0;");
    assert_eq!(m.expect, Some("S008"));
    let recv = HExpr::Receiver(Box::new(name("v0")), "g0".to_owned(), vec![name("i0")]);
    let p = hardware_root(vec![let_of("l0", recv)]);
    assert_eq!(
        find(&p, Kind::Immutable, "let v0: UInt[8] = i0;").expect,
        Some("S008")
    );
    // An assignment to an immutable root has another code.
    let assign = Stmt::Assign("v0".to_owned(), name("i0"));
    let call = HExpr::Call("g0".to_owned(), vec![name("v0"), name("i0")]);
    let p = hardware_root(vec![assign, let_of("l0", call)]);
    assert_eq!(
        find(&p, Kind::Immutable, "let v0: UInt[8] = i0;").expect,
        None
    );
    // A read of the root is no mutation.
    let p = hardware_root(vec![let_of("l0", name("v0"))]);
    assert_eq!(
        find(&p, Kind::Immutable, "let v0: UInt[8] = i0;").expect,
        None
    );
    // The helper takes the root as its second formal: a read.
    let read = HExpr::Call("g0".to_owned(), vec![name("i0"), name("v0")]);
    let p = hardware_root(vec![let_of("l0", read)]);
    assert_eq!(
        find(&p, Kind::Immutable, "let v0: UInt[8] = i0;").expect,
        None
    );
}

#[test]
fn window_predicts_s008_for_a_pop_of_the_receiver() {
    let p = slice_two();
    assert_eq!(sites(Kind::Window, &p.items, &p.top), 1);
    let m = find(&p, Kind::Window, "s0.k0(s0.pop())");
    assert_eq!(m.expect, Some("S008"));
    assert_eq!(m.what, "pop s0 in argument 1 of k0 in M0");
    assert_eq!(m.text, p.text().replace("s0.k0(1)", "s0.k0(s0.pop())"));
    // Pass 4 reports it in dead code too.
    let call = mut_call("s1", "s0", "k0", true);
    let p = slice_two_with(vec![
        mut_let("s0"),
        Stmt::If(SExpr::Bool(false), vec![call], None),
    ]);
    assert_eq!(all(&p, Kind::Window)[0].expect, Some("S008"));
}

#[test]
fn window_has_no_site_on_an_integer_root_or_a_plain_call() {
    let int_root = Stmt::MutLet("s0".to_owned(), STy::Int, dec(0));
    let p = slice_two_with(vec![int_root, mut_call("s1", "s0", "k1", true)]);
    assert_eq!(sites(Kind::Window, &p.items, &p.top), 0);
    let p = slice_two_with(vec![mut_let("s0"), mut_call("s1", "s0", "k0", false)]);
    assert_eq!(sites(Kind::Window, &p.items, &p.top), 0);
    // The root of a `let` is not in scope before its declaration.
    let p = slice_two_with(vec![mut_call("s1", "s0", "k0", true), mut_let("s0")]);
    assert_eq!(sites(Kind::Window, &p.items, &p.top), 0);
}

#[test]
fn value_window_predicts_s008_where_the_call_always_runs() {
    let p = slice_two();
    assert_eq!(sites(Kind::ValueWindow, &p.items, &p.top), 1);
    let m = find(&p, Kind::ValueWindow, "F0(s0, s0.pop())");
    assert_eq!(m.expect, Some("S008"));
    assert_eq!(m.what, "pop s0 in argument 1 of F0 in M0");
    // Where the call may not run, pass 5 may never see the window.
    let call = || mut_call("s1", "s0", "F0", false);
    for inner in [
        Stmt::If(SExpr::Bool(false), vec![call()], None),
        Stmt::For("j0".to_owned(), dec(0), dec(0), vec![call()]),
        Stmt::Block(vec![call()]),
    ] {
        let p = slice_two_with(vec![mut_let("s0"), inner]);
        let m = &all(&p, Kind::ValueWindow)[0];
        assert!(m.text.contains("F0(s0, s0.pop())"));
        assert_eq!(m.expect, None);
    }
}

#[test]
fn value_window_has_no_site_on_a_named_call() {
    let p = slice_two_with(vec![mut_let("s0"), mut_call("s1", "s0", "k0", false)]);
    assert_eq!(sites(Kind::ValueWindow, &p.items, &p.top), 0);
}

fn bool_name_if(arm_then: HExpr, arm_else: HExpr) -> HExpr {
    HExpr::If(Box::new(name("c0")), Box::new(arm_then), Box::new(arm_else))
}

fn make(n: i64) -> HExpr {
    HExpr::Make(u8(), dec(n))
}

/// A module with the port `c0: Bool`, the register `r0` and the output
/// `o0: UInt[8]`, then `body`, then `o0 := value`.
fn arm_module(body: Vec<Stmt>, value: HExpr) -> Program {
    let mut stmts = vec![
        Stmt::Input("c0".to_owned(), Ty::Bool),
        Stmt::Reg("r0".to_owned(), Ty::Bool, SExpr::Bool(false)),
        Stmt::Output("o0".to_owned(), u8()),
    ];
    stmts.extend(body);
    stmts.push(connect("o0", value));
    of(vec![module("M0", stmts)])
}

const EFFECT: &str =
    "comptime fn e0(x: Int) -> Int {\n    diagnostic(\"e0\", x);\n    return x;\n}\n";
const KEEP: &str = "comptime fn p0(mut n: Int, x: Int) -> Int {\n    return x;\n}\n";

#[test]
fn arm_effect_predicts_s016_in_the_arm_of_a_port_condition() {
    let p = arm_module(vec![], bool_name_if(make(1), make(2)));
    assert_eq!(sites(Kind::ArmEffect, &p.items, &p.top), 2);
    let ms = all(&p, Kind::ArmEffect);
    assert_eq!(
        ms[0].text,
        format!(
            "{}{EFFECT}",
            p.text().replace("UInt[8](1)", "UInt[8](e0(1))")
        )
    );
    assert_eq!(ms[0].what, "call e0 on 1 in an arm of M0");
    assert_eq!(
        ms[1].text,
        format!(
            "{}{EFFECT}",
            p.text().replace("UInt[8](2)", "UInt[8](e0(2))")
        )
    );
    assert!(ms.iter().all(|m| m.expect == Some("S016")));
    // A register, and the negation of a port or a register.
    let not = |n: &str| HExpr::Unary(Un::Not, Box::new(name(n)));
    for cond in [name("r0"), not("c0"), not("r0")] {
        let e = HExpr::If(Box::new(cond), Box::new(make(1)), Box::new(make(2)));
        let p = arm_module(vec![], e);
        assert!(
            all(&p, Kind::ArmEffect)
                .iter()
                .all(|m| m.expect == Some("S016"))
        );
    }
    // A static `Int` operand without a type around it is a site too, and a
    // `Bool` operand or a name is not.
    let sum = SExpr::Binary(SBin::Add, Box::new(dec(1)), Box::new(dec(2)));
    let p = arm_module(
        vec![],
        bool_name_if(HExpr::Static(sum), HExpr::Static(SExpr::Bool(true))),
    );
    let ms = all(&p, Kind::ArmEffect);
    assert_eq!(ms.len(), 1);
    assert!(ms[0].text.contains("e0((1 + 2))"));
    assert_eq!(ms[0].expect, Some("S016"));
}

#[test]
fn arm_effect_predicts_nothing_where_the_if_may_take_one_arm() {
    let has_site = |p: &Program, expect| {
        let ms = all(p, Kind::ArmEffect);
        assert!(!ms.is_empty());
        assert!(ms.iter().all(|m| m.expect == expect), "{ms:?}");
    };
    // A static condition takes one arm.
    let p = arm_module(
        vec![],
        HExpr::If(
            Box::new(HExpr::Static(SExpr::Bool(true))),
            Box::new(make(1)),
            Box::new(make(2)),
        ),
    );
    has_site(&p, None);
    // Any other condition may fold: a comparison, a call, or a name that is
    // no port or register.
    let cmp = HExpr::Binary(HBin::Eq, Box::new(name("c0")), Box::new(name("c0")));
    let p = arm_module(
        vec![],
        HExpr::If(Box::new(cmp), Box::new(make(1)), Box::new(make(2))),
    );
    has_site(&p, None);
    let p = arm_module(
        vec![let_of("l0", name("c0"))],
        HExpr::If(Box::new(name("l0")), Box::new(make(1)), Box::new(make(2))),
    );
    has_site(&p, None);
    // An arm in the arm of a static `if`, or in a lazy operand.
    let inner = bool_name_if(make(1), make(2));
    let outer = HExpr::If(
        Box::new(HExpr::Static(SExpr::Bool(true))),
        Box::new(inner),
        Box::new(make(3)),
    );
    let sites: Vec<_> = all(&arm_module(vec![], outer), Kind::ArmEffect)
        .iter()
        .map(|m| m.expect)
        .collect();
    assert_eq!(sites, [None, None, None]);
    let lazy = HExpr::Binary(
        HBin::Land,
        Box::new(name("c0")),
        Box::new(bool_name_if(name("c0"), name("c0"))),
    );
    let p = arm_module(vec![let_of("l0", lazy)], make(1));
    assert_eq!(sites_of(&p, Kind::ArmEffect), 0);
    // A hardware `if` in the arm of a hardware `if` runs.
    let nested = bool_name_if(bool_name_if(make(1), make(2)), make(3));
    let ms = all(&arm_module(vec![], nested), Kind::ArmEffect);
    assert_eq!(ms.len(), 3);
    assert!(ms.iter().all(|m| m.expect == Some("S016")));
    // The top frame only: a loop, a branch, and a helper body.
    for inner in [
        Stmt::For(
            "j0".to_owned(),
            dec(0),
            dec(0),
            vec![let_of("l0", bool_name_if(make(1), make(2)))],
        ),
        Stmt::If(
            SExpr::Bool(true),
            vec![let_of("l0", bool_name_if(make(1), make(2)))],
            None,
        ),
        Stmt::Block(vec![let_of("l0", bool_name_if(make(1), make(2)))]),
    ] {
        has_site(&arm_module(vec![inner], make(0)), None);
    }
    let helper = Item::Helper {
        name: "h0".to_owned(),
        params: vec![("c0".to_owned(), Ty::Bool.into())],
        mut_first: false,
        ret: u8().into(),
        body: vec![],
        result: bool_name_if(make(1), make(2)),
    };
    has_site(&of(vec![helper]), None);
}

fn sites_of(p: &Program, kind: Kind) -> usize {
    sites(kind, &p.items, &p.top)
}

#[test]
fn type_effect_predicts_s016_in_a_width_of_the_top_frame() {
    let p = arm_module(vec![], make(1));
    let ms = all(&p, Kind::TypeEffect);
    // The widths of `o0: UInt[8]` and of `UInt[8](1)`.
    assert_eq!(ms.len(), 2);
    assert_eq!(
        ms[0].text,
        format!(
            "{}{EFFECT}",
            p.text()
                .replace("output o0: UInt[8]", "output o0: UInt[e0(8)]")
        )
    );
    assert_eq!(ms[0].what, "call e0 in the width 8 in M0");
    assert!(ms.iter().all(|m| m.expect == Some("S016")));
    // A width in the value of a statement in an arm.
    let l = Stmt::Let {
        name: "l0".to_owned(),
        mutable: false,
        ty: Some(u8()),
        value: name("c0"),
    };
    let ms = all(&arm_module(vec![l], make(1)), Kind::TypeEffect);
    assert!(ms.iter().all(|m| m.expect == Some("S016")));
}

#[test]
fn type_effect_predicts_nothing_off_the_top_frame() {
    let l = || let_of("l0", HExpr::Resize(u8(), Box::new(name("c0"))));
    for inner in [
        Stmt::For("j0".to_owned(), dec(0), dec(0), vec![l()]),
        Stmt::If(SExpr::Bool(true), vec![l()], None),
    ] {
        let p = arm_module(vec![inner], make(0));
        let ms = all(&p, Kind::TypeEffect);
        let nested = ms
            .iter()
            .filter(|m| m.text.contains("resize(UInt[e0(8)]"))
            .collect::<Vec<_>>();
        assert_eq!(nested.len(), 1);
        assert_eq!(nested[0].expect, None);
    }
    // A lazy operand of `&&`.
    let lazy = HExpr::Binary(
        HBin::Land,
        Box::new(name("c0")),
        Box::new(HExpr::Resize(u8(), Box::new(name("c0")))),
    );
    let ms = all(
        &arm_module(vec![let_of("l0", lazy)], make(0)),
        Kind::TypeEffect,
    );
    let m = ms
        .iter()
        .find(|m| m.text.contains("resize(UInt[e0(8)]"))
        .unwrap();
    assert_eq!(m.expect, None);
    // A struct field and a helper signature.
    let p = slice_two();
    let m = find(&p, Kind::TypeEffect, "m0: UInt[e0(W0)],");
    assert_eq!(m.expect, None);
    let helper = Item::Helper {
        name: "h0".to_owned(),
        params: vec![("x0".to_owned(), u8().into())],
        mut_first: false,
        ret: u8().into(),
        body: vec![],
        result: name("x0"),
    };
    assert!(
        all(&of(vec![helper]), Kind::TypeEffect)
            .iter()
            .all(|m| m.expect.is_none())
    );
}

fn counter_let() -> Stmt {
    Stmt::MutLet("s0".to_owned(), STy::Int, dec(0))
}

#[test]
fn mutation_kinds_of_a_context_use_the_newest_int_root() {
    // A root from before the arm: the write-back is `S016`.
    let p = arm_module(vec![counter_let()], bool_name_if(make(1), make(2)));
    let ms = all(&p, Kind::ArmMutation);
    assert_eq!(ms.len(), 2);
    assert_eq!(
        ms[0].text,
        format!(
            "{}{KEEP}",
            p.text().replace("UInt[8](1)", "UInt[8](p0(s0, 1))")
        )
    );
    assert_eq!(ms[0].what, "call p0 on s0 and 1 in an arm of M0");
    assert!(ms.iter().all(|m| m.expect == Some("S016")));
    let ms = all(&p, Kind::TypeMutation);
    assert_eq!(ms[0].what, "call p0 on s0 in the width 8 in M0");
    assert!(ms.iter().all(|m| m.expect == Some("S016")));
    // A list root is no `Int` root, and a root after the site is no root
    // from before it.
    let p = arm_module(vec![mut_let("s0")], bool_name_if(make(1), make(2)));
    assert_eq!(sites_of(&p, Kind::ArmMutation), 0);
    assert_eq!(sites_of(&p, Kind::TypeMutation), 0);
    // The ports come before the root: only the width after it is a site.
    let p = arm_module(vec![counter_let()], make(0));
    let ms = all(&p, Kind::TypeMutation);
    assert_eq!(ms.len(), 1);
    assert!(ms[0].text.contains("o0 := UInt[p0(s0, 8)](0);"));
}

#[test]
fn mutation_kinds_need_a_root_in_scope() {
    // No root: no site.
    let p = arm_module(vec![], bool_name_if(make(1), make(2)));
    assert_eq!(sites_of(&p, Kind::ArmMutation), 0);
    // The root of a block body is out of scope after the block.
    let body = vec![counter_let()];
    let p = arm_module(vec![Stmt::Block(body)], bool_name_if(make(1), make(2)));
    assert_eq!(sites_of(&p, Kind::ArmMutation), 0);
    // The `Int` root of the enclosing frame is in scope in a loop, and the
    // site predicts nothing there.
    let inner = let_of("l0", bool_name_if(make(1), make(2)));
    let p = arm_module(
        vec![
            counter_let(),
            Stmt::For("j0".to_owned(), dec(0), dec(1), vec![inner]),
        ],
        make(0),
    );
    let ms = all(&p, Kind::ArmMutation);
    assert_eq!(ms.len(), 2);
    assert!(ms.iter().all(|m| m.expect.is_none()));
    // A static operand in the arm of a static `if` predicts nothing.
    let e = HExpr::If(
        Box::new(HExpr::Static(SExpr::Bool(true))),
        Box::new(make(1)),
        Box::new(make(2)),
    );
    let p = arm_module(vec![counter_let()], e);
    assert!(
        all(&p, Kind::ArmMutation)
            .iter()
            .all(|m| m.expect.is_none())
    );
}

#[test]
fn the_fixed_set_of_mutants_reaches_s008_and_s016() {
    let mut runner = TestRunner::deterministic();
    let mut counts = std::collections::BTreeMap::<&str, usize>::new();
    let mut by_kind = std::collections::BTreeMap::<usize, usize>::new();
    for tape in 0..256u32 {
        let p = typed().new_tree(&mut runner).unwrap().current().unwrap();
        for (k, kind) in KINDS.iter().enumerate().skip(8).take(7) {
            let count = sites(*kind, &p.items, &p.top);
            if count == 0 {
                continue;
            }
            let m = mutate(&p, index(*kind), tape.wrapping_mul(7919));
            if let Some(code) = m.expect {
                *counts.entry(code).or_default() += 1;
                *by_kind.entry(k).or_default() += 1;
            }
        }
    }
    assert!(counts.get("S008").copied().unwrap_or(0) >= 5, "{counts:?}");
    assert!(counts.get("S016").copied().unwrap_or(0) >= 5, "{counts:?}");
    assert_eq!(by_kind.len(), 7, "{by_kind:?}");
}

#[test]
fn mutation_is_deterministic() {
    let p = program();
    for kind in 0..15 {
        assert_eq!(mutate(&p, kind, 11), mutate(&p, kind, 11));
    }
}

/// `match (scrutinee) { patterns => values }` of static `Int`s.
fn matching(scrutinee: SExpr, arms: &[(Pattern, i64)]) -> SExpr {
    SExpr::Match(Match {
        scrutinee: Box::new(scrutinee),
        arms: arms.iter().map(|(p, v)| (p.clone(), dec(*v))).collect(),
    })
}

fn literal(n: i64) -> Pattern {
    Pattern::Int(BigInt::from(n), Radix::Dec)
}

/// `module M0() domains() { <body> }` where a static `let` holds `e`.
fn with_static(e: SExpr, nested: bool) -> Program {
    let held = Stmt::StaticLet("s0".to_owned(), STy::Int, e);
    let body = if nested {
        vec![Stmt::If(SExpr::Bool(true), vec![held], None)]
    } else {
        vec![held]
    };
    of(vec![module("M0", body)])
}

fn expects(p: &Program, kind: Kind) -> Vec<Option<&'static str>> {
    all(p, kind).into_iter().map(|m| m.expect).collect()
}

#[test]
fn the_arm_kinds_follow_the_coverage_rules() {
    let arms = [(literal(1), 10), (literal(2), 20), (Pattern::Wild, 30)];
    let p = with_static(matching(dec(3), &arms), false);
    // Only the arm `_` and a match without `_` lose their coverage.
    assert_eq!(expects(&p, Kind::DeleteArm), [None, None, Some("S021")]);
    assert_eq!(expects(&p, Kind::DuplicateArm), [Some("S021"); 3]);
    assert_eq!(expects(&p, Kind::WildFirst), [Some("S021")]);
    assert!(expects(&p, Kind::DeadWild).is_empty());
    let both = [(Pattern::Bool(true), 1), (Pattern::Bool(false), 2)];
    let p = with_static(matching(SExpr::Bool(true), &both), false);
    assert_eq!(expects(&p, Kind::DeleteArm), [Some("S021"); 2]);
    assert_eq!(expects(&p, Kind::DeadWild), [Some("S021")]);
    assert!(expects(&p, Kind::WildFirst).is_empty());
    // A match in a branch may not run.
    let p = with_static(matching(SExpr::Bool(true), &both), true);
    assert_eq!(expects(&p, Kind::DeleteArm), [None; 2]);
    assert_eq!(expects(&p, Kind::DuplicateArm), [None; 2]);
    assert_eq!(expects(&p, Kind::DeadWild), [None]);
}

/// A mutant of a variant pattern: the binders and the tags.
#[test]
fn the_pattern_kinds_follow_the_pass_order() {
    let enum_def = e0();
    let variant = |v: &str, binders: &[Option<&str>]| {
        Pattern::Variant(
            "E0".to_owned(),
            v.to_owned(),
            binders.iter().map(|b| b.map(str::to_owned)).collect(),
        )
    };
    let scrutinee = SExpr::Ctor("E0".to_owned(), "V1".to_owned(), vec![]);
    let m = SExpr::Match(Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            (variant("V0", &[Some("B0"), Some("B1")]), dec(1)),
            (variant("V1", &[]), dec(2)),
            (Pattern::Wild, dec(3)),
        ],
    });
    let top = module("M0", vec![Stmt::StaticLet("s0".to_owned(), STy::Int, m)]);
    let p = of(vec![Item::Enum(enum_def), top]);
    // The arm `V0` binds `B0` and `B1`, and no arm reads them.
    assert_eq!(expects(&p, Kind::DupBinder), [Some("S002")]);
    assert!(
        expects(&p, Kind::DropArg)
            .iter()
            .all(|c| *c == Some("S007"))
    );
    assert!(expects(&p, Kind::AddArg).iter().all(|c| *c == Some("S007")));
    // The enum is used in the top frame by the constructor.
    assert_eq!(expects(&p, Kind::SameTag), [Some("S021")]);
    assert_eq!(expects(&p, Kind::TagFit), [Some("S012"); 2]);
    assert_eq!(expects(&p, Kind::PayloadOverflow), [Some("S012")]);
    // A pattern of another kind is `S010` in an arm that reads no binder.
    assert_eq!(expects(&p, Kind::PatternSwap), [Some("S010"); 2]);
}

/// A fixed set of 256 programs gives at least 5 predictions of `S021`, and
/// the kinds of the match reach each new code. Each mutant lexes.
#[test]
fn the_fixed_set_of_mutants_reaches_s021_and_the_match_codes() {
    let mut runner = TestRunner::deterministic();
    let mut counts = std::collections::BTreeMap::<&str, usize>::new();
    let mut by_kind = std::collections::BTreeMap::<usize, usize>::new();
    for tape in 0..256u32 {
        let p = typed().new_tree(&mut runner).unwrap().current().unwrap();
        for (k, kind) in KINDS.iter().enumerate().skip(15) {
            if sites(*kind, &p.items, &p.top) == 0 {
                continue;
            }
            let m = mutate(&p, index(*kind), tape.wrapping_mul(7919));
            let lexed = syntax::lex(&m.text, usize::MAX);
            assert!(lexed.errors.is_empty(), "{:?} in\n{}", lexed.errors, m.text);
            if let Some(code) = m.expect {
                *counts.entry(code).or_default() += 1;
                *by_kind.entry(k).or_default() += 1;
            }
        }
    }
    assert!(counts.get("S021").copied().unwrap_or(0) >= 5, "{counts:?}");
    for code in ["S002", "S010", "S011", "S012"] {
        assert!(
            counts.get(code).copied().unwrap_or(0) >= 1,
            "{code}: {counts:?}"
        );
    }
    // The four kinds that change an alias of `@Struct` predict nothing.
    assert_eq!(by_kind.len(), KINDS.len() - 15 - 4, "{by_kind:?}");
}

/// `enum E0: UInt[2] { V0(UInt[4], Bool) = 1, V1 = 2 }`.
fn e0() -> EnumDef {
    EnumDef {
        name: "E0".to_owned(),
        tag_width: 2,
        variants: vec![
            Variant {
                name: "V0".to_owned(),
                tag: BigUint::from(1u8),
                payload: vec![Scalar::UInt(4), Scalar::Bool],
            },
            Variant {
                name: "V1".to_owned(),
                tag: BigUint::from(2u8),
                payload: vec![],
            },
        ],
    }
}

/// `E0::V0(1, true)`, static.
fn static_v0() -> SExpr {
    SExpr::Ctor(
        "E0".to_owned(),
        "V0".to_owned(),
        vec![dec(1), SExpr::Bool(true)],
    )
}

/// A constructor with arguments, static and hardware, and a pattern with
/// binders, pin the exact `S007` of each site.
#[test]
fn the_argument_kinds_of_constructors_and_patterns_are_s007() {
    let pattern = Pattern::Variant(
        "E0".to_owned(),
        "V0".to_owned(),
        vec![Some("B0".to_owned()), Some("B1".to_owned())],
    );
    let scrutinee = SExpr::Ctor("E0".to_owned(), "V1".to_owned(), vec![]);
    let m = SExpr::Match(Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            (pattern, dec(1)),
            (
                Pattern::Variant("E0".to_owned(), "V1".to_owned(), vec![]),
                dec(2),
            ),
            (Pattern::Wild, dec(3)),
        ],
    });
    let hardware = HExpr::Ctor(
        "E0".to_owned(),
        "V0".to_owned(),
        vec![HExpr::Static(dec(1)), HExpr::Static(SExpr::Bool(true))],
    );
    let top = module(
        "M0",
        vec![
            Stmt::Output("eo".to_owned(), Ty::Enum("E0".to_owned())),
            Stmt::StaticLet("s0".to_owned(), STy::Int, m),
            Stmt::Diagnostic("d0".to_owned(), static_v0()),
            connect("eo", hardware),
        ],
    );
    let p = of(vec![Item::Enum(e0()), top]);
    // The binder `B1` of the first pattern, the static constructor, and
    // the hardware constructor.
    assert_eq!(expects(&p, Kind::DropArg), [Some("S007"); 3]);
    // The two patterns, the constructor of the scrutinee without arguments,
    // and the two constructors with arguments.
    assert_eq!(expects(&p, Kind::AddArg), [Some("S007"); 5]);
}

/// An effect in an arm of a hardware `match` over a port is `S016`. One
/// over a folding scrutinee, such as `false && i0`, predicts nothing.
#[test]
fn the_arms_of_a_hardware_match_follow_the_scrutinee() {
    let arms = |scrutinee: HExpr, pattern: Pattern| {
        HExpr::Match(Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                (
                    pattern,
                    HExpr::Binary(
                        HBin::Addw,
                        Box::new(name("i0")),
                        Box::new(HExpr::Static(dec(1))),
                    ),
                ),
                (Pattern::Wild, name("i0")),
            ],
        })
    };
    let body = |e: HExpr| of(vec![module("M0", ports_then(vec![connect("o0", e)]))]);
    let port = body(arms(name("i0"), literal(0)));
    assert_eq!(expects(&port, Kind::ArmEffect), [Some("S016")]);
    // `false && i0` is a static `Bool`, so it selects one arm.
    let folded = HExpr::Binary(
        HBin::Land,
        Box::new(HExpr::Static(SExpr::Bool(false))),
        Box::new(HExpr::Binary(
            HBin::Ne,
            Box::new(name("i0")),
            Box::new(HExpr::Static(dec(0))),
        )),
    );
    let p = body(arms(folded, Pattern::Bool(true)));
    assert!(expects(&p, Kind::ArmEffect).iter().all(Option::is_none));
    // The scrutinee of a static match is no hardware either.
    let p = body(arms(HExpr::Static(dec(2)), literal(0)));
    assert!(expects(&p, Kind::ArmEffect).iter().all(Option::is_none));
}

/// A register that a branch declares is out of scope after the branch, so
/// `ArmStage` cannot name it.
#[test]
fn a_name_of_a_nested_frame_leaves_scope() {
    let branch = Stmt::If(
        SExpr::Bool(true),
        vec![Stmt::Reg("r0".to_owned(), u8(), dec(0))],
        None,
    );
    let sum = HExpr::Binary(
        HBin::Addw,
        Box::new(HExpr::Make(u8(), dec(3))),
        Box::new(HExpr::Static(dec(1))),
    );
    let p = of(vec![module(
        "M0",
        vec![
            branch,
            Stmt::Output("o0".to_owned(), u8()),
            connect("o0", sum),
        ],
    )]);
    assert_eq!(sites(Kind::ArmStage, &p.items, &p.top), 0);
}

/// A kind without a site falls back to the earlier kinds, not to the next
/// kind of the list.
#[test]
fn a_kind_without_a_site_falls_back_to_the_earlier_kinds() {
    let sum = HExpr::Binary(
        HBin::Addw,
        Box::new(name("i0")),
        Box::new(HExpr::Static(dec(1))),
    );
    let p = of(vec![module("M0", ports_then(vec![connect("o0", sum)]))]);
    let staged = |k: u32| mutate(&p, k, 0).what.starts_with("stage the operand");
    // The draws of the kinds of `match` that have no site here.
    for k in 15..23 {
        assert!(!staged(k), "kind {k}");
    }
    // The draw of the kind `ArmStage` has a site.
    assert!(staged(index(Kind::ArmStage)));
}

/// `fn H0(a0: Reg[UInt[8]], x1: UInt[8]) -> ()` binds `a0`, and `H1()`
/// declares and binds a register of its own.
fn handle_items() -> Vec<Item> {
    let binder = Item::Helper {
        name: "H0".to_owned(),
        params: vec![
            ("a0".to_owned(), FTy::Reg(u8())),
            ("x1".to_owned(), u8().into()),
        ],
        mut_first: false,
        ret: FTy::Unit,
        body: vec![connect("a0", name("x1"))],
        result: HExpr::Unit,
    };
    let declarer = Item::Helper {
        name: "H1".to_owned(),
        params: vec![("x0".to_owned(), u8().into())],
        mut_first: false,
        ret: FTy::Unit,
        body: vec![
            Stmt::Reg("r0".to_owned(), u8(), dec(0)),
            connect("r0", name("x0")),
        ],
        result: HExpr::Unit,
    };
    vec![binder, declarer]
}

fn call(f: &str, args: &[&str]) -> Stmt {
    Stmt::Call(f.to_owned(), args.iter().map(|a| name(a)).collect())
}

/// A clocked module that declares `r0`, calls `H0` on it, and calls `H1`.
fn handle_program(top: Vec<Stmt>) -> Program {
    let mut body = ports_then(vec![Stmt::Reg("r0".to_owned(), u8(), dec(0))]);
    body.extend(top);
    body.push(connect("o0", name("r0")));
    let mut items = handle_items();
    items.push(Item::Module {
        name: "M0".to_owned(),
        params: vec![],
        clocked: true,
        body,
    });
    of(items)
}

/// A deleted call of a helper with a handle formal in the top frame leaves
/// the register unbound. A deleted call of a helper that declares binds
/// nothing from outside, so the program stays valid.
#[test]
fn delete_of_a_binding_call_predicts_s018_in_the_top_frame() {
    let p = handle_program(vec![call("H0", &["r0", "i0"]), call("H1", &["i0"])]);
    let deleted = |line: &str| {
        all(&p, Kind::Delete)
            .into_iter()
            .find(|m| m.text == p.text().replacen(line, "", 1))
            .unwrap()
    };
    assert_eq!(deleted("    H0(r0, i0);\n").expect, Some("S018"));
    assert_eq!(deleted("    H1(i0);\n").expect, None);
    // The `:=` in the body of a helper is no top frame.
    assert_eq!(deleted("    a0 := x1;\n").expect, None);
}

#[test]
fn delete_of_a_binding_call_in_a_loop_predicts_nothing() {
    let looped = Stmt::For(
        "j0".to_owned(),
        dec(0),
        dec(2),
        vec![
            Stmt::Reg("r1".to_owned(), u8(), dec(0)),
            call("H0", &["r1", "i0"]),
        ],
    );
    let p = handle_program(vec![looped]);
    let m = all(&p, Kind::Delete)
        .into_iter()
        .find(|m| m.text == p.text().replacen("        H0(r1, i0);\n", "", 1))
        .unwrap();
    assert_eq!(m.expect, None);
}

/// `DuplicateBind` copies a `:=`, a `write_port`, or a call of a helper
/// with a handle formal in the top frame, and it predicts `S018`. It has no
/// site on the call of a helper that only declares, in a loop, or in a
/// helper.
#[test]
fn duplicate_bind_predicts_s018_at_a_binding_of_the_top_frame() {
    let looped = Stmt::For(
        "j0".to_owned(),
        dec(0),
        dec(2),
        vec![Stmt::Wire("w0".to_owned(), u8()), connect("w0", name("i0"))],
    );
    let write = Stmt::WritePort {
        mem: "n0".to_owned(),
        addr: Box::new(name("i0")),
        data: Box::new(name("i0")),
        en: Box::new(HExpr::Static(SExpr::Bool(true))),
        receiver: false,
    };
    let top = vec![
        call("H0", &["r0", "i0"]),
        call("H1", &["i0"]),
        Stmt::Mem("n0".to_owned(), u8(), dec(2)),
        write,
        looped,
    ];
    let p = handle_program(top);
    let copies = all(&p, Kind::DuplicateBind);
    // The call of `H0`, the write, and the `:=` of the output.
    assert_eq!(
        copies.len(),
        3,
        "{:?}",
        copies.iter().map(|m| &m.what).collect::<Vec<_>>()
    );
    assert!(copies.iter().all(|m| m.expect == Some("S018")));
    let texts: Vec<&str> = [
        "    H0(r0, i0);\n",
        "    write_port(n0, i0, i0, true);\n",
        "    o0 := r0;\n",
    ]
    .to_vec();
    for (m, line) in copies.iter().zip(texts) {
        assert_eq!(m.text, p.text().replacen(line, &format!("{line}{line}"), 1));
    }
}

/// The line that the mutant `m` of the program text `text` removed.
fn removed(text: &str, m: &Mutant) -> Option<String> {
    let kept: Vec<&str> = m.text.lines().collect();
    let mut lines = text.lines();
    let mut at = 0;
    for line in lines.by_ref() {
        if kept.get(at) == Some(&line) {
            at += 1;
        } else {
            return Some(line.to_owned());
        }
    }
    None
}

/// Across 120 typed programs, the mutants that delete a call of a helper
/// with a handle formal, and the mutants that copy a binding, predict
/// `S018`. The kinds that the programs of slice 3 add keep `S018` rare
/// otherwise, so a count shows that the handle forms reach it.
#[test]
fn the_fixed_set_of_mutants_reaches_s018_of_handles() {
    let (mut deleted, mut copied) = (0, 0);
    for p in programs().into_iter().take(120) {
        let text = p.text();
        for m in all(&p, Kind::Delete) {
            let call = removed(&text, &m).is_some_and(|l| l.starts_with("    H"));
            deleted += usize::from(call && m.expect == Some("S018"));
        }
        for m in all(&p, Kind::DuplicateBind) {
            assert_eq!(m.expect, Some("S018"), "{}", m.what);
            copied += 1;
        }
    }
    assert!(deleted >= 5, "{deleted} deleted binding calls");
    assert!(copied >= 5, "{copied} copied bindings");
}

/// The lines of a program text that declare the name `n` (`reg n`, `wire n`,
/// `mem n`, `instance n`) in the helper that the line `at` belongs to.
fn declared_in_helper(text: &str, at: usize, n: &str) -> bool {
    let lines: Vec<&str> = text.lines().collect();
    let start = lines[..at]
        .iter()
        .rposition(|l| l.starts_with("fn H"))
        .unwrap_or(0);
    lines[start..at].iter().any(|l| {
        let t = l.trim_start();
        ["reg ", "wire ", "mem ", "instance "].iter().any(|k| {
            t.strip_prefix(k).is_some_and(|r| {
                r.starts_with(&format!("{n}:"))
                    || r.starts_with(&format!("{n} ="))
                    || r.starts_with(&format!("{n};"))
            })
        })
    })
}

/// The name that the binding line `l` binds: the target of a `:=` (before a
/// port), the memory of a `write_port`, or the first actual of a call.
fn bound_name(l: &str) -> Option<String> {
    let t = l.trim();
    let name = |s: &str| {
        let end = s.find(|c: char| !c.is_ascii_alphanumeric() && c != '_')?;
        Some(s[..end].to_owned())
    };
    if t.contains(" := ") {
        return name(t);
    }
    let args = t.strip_prefix("write_port(").or_else(|| {
        t.strip_prefix('H')
            .and_then(|r| r.split_once('('))
            .map(|(_, r)| r)
    })?;
    name(args)
}

/// The cases of the seeds 1 to 100 of `diff-si --mode mutation`: a program,
/// and the draws of the kind and the site.
fn mutation_cases() -> Vec<(Program, u32, u32)> {
    use proptest::prelude::any;
    use proptest::strategy::Just;
    use proptest::test_runner::{Config, RngAlgorithm, RngSeed, TestRng};
    (1u64..=100)
        .map(|seed| {
            let mut bytes = [0; 32];
            bytes[..8].copy_from_slice(&seed.to_le_bytes());
            let config = Config {
                rng_algorithm: RngAlgorithm::ChaCha,
                rng_seed: RngSeed::Fixed(seed),
                ..Config::default()
            };
            let mut runner =
                TestRunner::new_with_rng(config, TestRng::from_seed(RngAlgorithm::ChaCha, &bytes));
            let strategy = typed().prop_flat_map(|p| (Just(p), any::<u32>(), any::<u32>()));
            let (p, kind, site) = strategy.new_tree(&mut runner).unwrap().current();
            (p.unwrap(), kind, site)
        })
        .collect()
}

/// A deleted binding of a resource that its own helper declares leaves the
/// resource unbound at the declaration, where a front end can report it at
/// the wrong place. The 100 programs of the CI seeds hold sites of them in
/// reach: the test counts each site of `Delete`, not the one draw of the
/// seed.
#[test]
fn the_ci_seeds_delete_bindings_of_helper_declared_resources() {
    let mut found = 0;
    for (p, _, _) in mutation_cases() {
        let text = p.text();
        let mut seen = std::collections::BTreeSet::new();
        for m in all(&p, Kind::Delete) {
            if !m.what.starts_with("delete statement")
                || !m.what.contains(" of H")
                || !seen.insert(m.what.clone())
            {
                continue;
            }
            let Some(line) = removed(&text, &m) else {
                continue;
            };
            let at = text.lines().position(|l| l == line).unwrap_or(0);
            if bound_name(&line).is_some_and(|n| declared_in_helper(&text, at, &n)) {
                found += 1;
            }
        }
    }
    assert!(
        found >= 60,
        "{found} deleted bindings of declared resources"
    );
}

fn port(output: bool, n: &str, key: Option<SExpr>, public: Option<SExpr>) -> Stmt {
    Stmt::Port(super::super::program::Port {
        output,
        name: n.to_owned(),
        key,
        public,
        ty: super::super::program::PTy::Data(u8()),
    })
}

fn string(s: &str) -> SExpr {
    SExpr::Str(s.to_owned())
}

fn entry(fam: &str, k: SExpr) -> HExpr {
    HExpr::Entry(fam.to_owned(), k)
}

/// A module with an entry at the top, a family in a loop, a keyed port, and
/// a scalar `PortKey`; the output reads the entry and the keyed port.
fn with_ports() -> Program {
    let body = vec![
        Stmt::Input("i0".to_owned(), u8()),
        Stmt::Output("o0".to_owned(), u8()),
        port(false, "A0", Some(dec(1)), None),
        Stmt::For(
            "j0".to_owned(),
            dec(0),
            dec(2),
            vec![port(
                false,
                "A0",
                Some(SExpr::Binary(
                    SBin::Add,
                    Box::new(SExpr::Name("j0".to_owned())),
                    Box::new(dec(5)),
                )),
                None,
            )],
        ),
        port(false, "Y0", None, Some(string("c0"))),
        port(
            false,
            "Y1",
            None,
            Some(SExpr::PortKey(
                Box::new(string("c1")),
                false,
                Box::new(dec(0)),
            )),
        ),
        connect(
            "o0",
            HExpr::Binary(
                HBin::Xor,
                Box::new(entry("A0", dec(1))),
                Box::new(HExpr::Binary(
                    HBin::Xor,
                    Box::new(name("Y0")),
                    Box::new(name("Y1")),
                )),
            ),
        ),
    ];
    of(vec![module("M0", body)])
}

fn texts(ms: &[Mutant]) -> Vec<(&str, Option<&'static str>)> {
    ms.iter().map(|m| (m.what.as_str(), m.expect)).collect()
}

/// An entry that always runs is `S019` at its copy. One in a loop predicts
/// nothing, and a keyed port is a second binder (`S002`).
#[test]
fn a_copy_of_an_indexed_declaration_is_s019_where_it_runs() {
    let p = with_ports();
    let copies = all(&p, Kind::Duplicate);
    let codes: Vec<Option<&str>> = copies
        .iter()
        .filter(|m| m.what.starts_with("duplicate statement"))
        .map(|m| m.expect)
        .collect();
    // i0, o0, A0[1], the loop body (A0[j0 + 5]), Y0, Y1.
    assert_eq!(
        codes,
        [
            Some("S002"),
            Some("S002"),
            Some("S019"),
            None,
            Some("S002"),
            Some("S002")
        ]
    );
    let twice = copies.iter().find(|m| m.expect == Some("S019")).unwrap();
    assert!(
        twice
            .text
            .contains("input A0[1]: UInt[8];\n    input A0[1]: UInt[8];")
    );
}

/// A deleted entry keeps the family while another indexed declaration of the
/// name remains, so only the last one is `S003`, if the item mentions it.
#[test]
fn a_deleted_indexed_declaration_keeps_the_family_while_another_remains() {
    let p = with_ports();
    let deleted = all(&p, Kind::Delete);
    let top = deleted
        .iter()
        .find(|m| m.text.contains("input A0[(j0 + 5)]") && !m.text.contains("input A0[1]"))
        .unwrap();
    assert_eq!(top.expect, None);
    let looped = deleted
        .iter()
        .find(|m| m.text.contains("input A0[1]") && !m.text.contains("input A0[(j0 + 5)]"))
        .unwrap();
    assert_eq!(looped.expect, None);
    // The only declaration of `A0`, which `o0` reads.
    let body = vec![
        Stmt::Output("o0".to_owned(), u8()),
        port(false, "A0", Some(dec(1)), None),
        connect("o0", entry("A0", dec(1))),
    ];
    let p = of(vec![module("M0", body)]);
    let m = all(&p, Kind::Delete)
        .into_iter()
        .find(|m| !m.text.contains("input A0"))
        .unwrap();
    assert_eq!(m.expect, Some("S003"));
    // A family that nothing reads leaves nothing to report.
    let body = vec![
        Stmt::Output("o0".to_owned(), u8()),
        port(false, "A0", Some(dec(1)), None),
        connect("o0", HExpr::Static(dec(0))),
    ];
    let p = of(vec![module("M0", body)]);
    let m = all(&p, Kind::Delete)
        .into_iter()
        .find(|m| !m.text.contains("input A0"))
        .unwrap();
    assert_eq!(m.expect, None);
}

#[test]
fn the_keys_of_entries_predict_where_they_always_run() {
    let p = with_ports();
    let range = all(&p, Kind::KeyRange);
    // The declaration at the top, the declaration in the loop, and the read.
    assert_eq!(range.len(), 3);
    assert_eq!(
        texts(&range).iter().map(|(_, c)| *c).collect::<Vec<_>>(),
        [Some("S012"), None, Some("S012")]
    );
    assert!(range[0].text.contains("input A0[4294967296]: UInt[8];"));
    assert!(range[2].text.contains("A0[4294967296]"));
    let typed = all(&p, Kind::KeyType);
    let by: Vec<(bool, Option<&str>)> = typed
        .iter()
        .map(|m| (m.what.contains("`as` key"), m.expect))
        .collect();
    // The two keys, the two `as` keys, and the read.
    assert_eq!(
        by,
        [
            (false, Some("S010")),
            (false, None),
            (true, Some("S010")),
            (true, Some("S010")),
            (false, Some("S010")),
        ]
    );
    assert!(typed[2].text.contains("input Y0: UInt[8] as 3;"));
}

#[test]
fn a_scalar_port_takes_the_key_of_a_family_of_its_module() {
    let p = with_ports();
    let m = all(&p, Kind::ScalarFamily);
    // i0, o0, Y0, and Y1 are the scalar ports of the top frame.
    assert_eq!(m.len(), 4);
    assert!(m.iter().all(|m| m.expect == Some("S019")));
    assert!(m[0].text.contains("input i0: UInt[8] as \"A0\";"));
    assert!(m[2].text.contains("input Y0: UInt[8] as \"A0\";"));
    // A module without a family offers no site.
    assert!(all(&smallest(), Kind::ScalarFamily).is_empty());
}

/// A family that only an arm that does not run declares is offered too:
/// the table of public names holds it from the start.
#[test]
fn a_scalar_port_takes_a_family_of_an_untaken_arm() {
    let body = vec![
        Stmt::Input("i0".to_owned(), u8()),
        Stmt::Output("o0".to_owned(), u8()),
        Stmt::If(
            SExpr::Bool(true),
            vec![port(false, "A0", Some(dec(1)), None)],
            Some(vec![port(false, "B0", Some(dec(2)), None)]),
        ),
        connect("o0", name("i0")),
    ];
    let p = of(vec![module("M0", body)]);
    let m = all(&p, Kind::ScalarFamily);
    assert_eq!(m.len(), 2);
    assert!(m.iter().all(|m| m.expect == Some("S019")));
    assert!(m[0].text.contains("input i0: UInt[8] as \"A0\";"));
    assert!(m[1].text.contains("output o0: UInt[8] as \"B0\";"));
    assert!(!no_entry_runs(&p, &m[0]));
    assert!(no_entry_runs(&p, &m[1]));
}

#[test]
fn a_bad_name_or_index_is_s022() {
    let p = with_ports();
    let m = all(&p, Kind::BadName);
    assert_eq!(m.len(), 2);
    assert!(m.iter().all(|m| m.expect == Some("S022")));
    assert!(m[1].text.contains("PortKey(\"c1\", false, 1)"));
    let bad = ["\"1c\"", "\"\"", "\"reg\""];
    assert!(
        bad.iter().any(|b| m[0].text.contains(&format!("as {b};"))),
        "{}",
        m[0].text
    );
}

/// Whether a statement of `body` that runs declares an entry of `family`: a
/// `comptime if` runs one arm.
fn declares_running(body: &[Stmt], family: &str) -> bool {
    body.iter().any(|s| match s {
        Stmt::Port(p) => p.key.is_some() && p.name == family,
        Stmt::If(SExpr::Bool(c), then, els) => declares_running(
            if *c {
                then
            } else {
                els.as_deref().unwrap_or_default()
            },
            family,
        ),
        Stmt::For(_, _, _, inner) | Stmt::Block(inner) => declares_running(inner, family),
        _ => false,
    })
}

/// Whether the family of a `ScalarFamily` mutant has no declaration that
/// runs in its module: only an arm that does not run declares it.
fn no_entry_runs(p: &Program, m: &Mutant) -> bool {
    let Some((head, item)) = m.what.rsplit_once(" in ") else {
        return false;
    };
    let Some(family) = head.rsplit(" the key of the family ").next() else {
        return false;
    };
    p.items.iter().any(|i| {
        matches!(i, Item::Module { name, body, .. }
            if name == item && !declares_running(body, family))
    })
}

/// What the mutants of the ports predict, by the text of the mutation.
fn kind_of_prediction(m: &Mutant) -> Option<&'static str> {
    m.expect?;
    let w = m.what.as_str();
    Some(
        if w.starts_with("duplicate statement") && m.expect == Some("S019") {
            "indexed Duplicate"
        } else if w.starts_with("make a family key 2^32") {
            "KeyRange"
        } else if w.starts_with("make a family key a value") {
            "KeyType key"
        } else if w.starts_with("make an `as` key an integer") {
            "KeyType as"
        } else if w.starts_with("give the scalar port") {
            "ScalarFamily"
        } else if w.starts_with("break the name rule") || w.starts_with("give a scalar PortKey") {
            "BadName"
        } else {
            return None;
        },
    )
}

/// A fixed set of 256 programs has at least 5 predictions of each kind of
/// ports, and at least 5 `ScalarFamily` predictions whose family has no
/// declaration that runs: the table holds the family from the start.
#[test]
fn the_fixed_set_of_mutants_reaches_the_codes_of_ports() {
    let mut runner = TestRunner::deterministic();
    let mut counts = std::collections::BTreeMap::<&str, usize>::new();
    let mut codes = std::collections::BTreeMap::<&str, usize>::new();
    let mut untaken = 0;
    for _ in 0..256 {
        let p = typed().new_tree(&mut runner).unwrap().current().unwrap();
        for kind in [
            Kind::Duplicate,
            Kind::KeyRange,
            Kind::KeyType,
            Kind::ScalarFamily,
            Kind::BadName,
        ] {
            for m in all(&p, kind) {
                let lexed = syntax::lex(&m.text, usize::MAX);
                assert!(lexed.errors.is_empty(), "{:?} in\n{}", lexed.errors, m.text);
                let Some(what) = kind_of_prediction(&m) else {
                    continue;
                };
                *counts.entry(what).or_default() += 1;
                *codes.entry(m.expect.unwrap_or_default()).or_default() += 1;
                if what == "ScalarFamily" && no_entry_runs(&p, &m) {
                    untaken += 1;
                }
            }
        }
    }
    for what in [
        "indexed Duplicate",
        "KeyRange",
        "KeyType key",
        "KeyType as",
        "ScalarFamily",
        "BadName",
    ] {
        assert!(
            counts.get(what).copied().unwrap_or(0) >= 5,
            "{what}: {counts:?}"
        );
    }
    for code in ["S010", "S012", "S019", "S022"] {
        assert!(
            codes.get(code).copied().unwrap_or(0) >= 5,
            "{code}: {codes:?}"
        );
    }
    assert!(
        untaken >= 5,
        "{untaken} families with no declaration that runs: {counts:?}"
    );
}

/// The kinds of `@field`, with the code that their mutants predict.
const FIELD_CODES: [(Kind, &[&str]); 11] = [
    (Kind::FieldKeyType, &["S010"]),
    (Kind::NoField, &["S010"]),
    (Kind::FieldRange, &["S012", "S013"]),
    (Kind::FieldBase, &["S010"]),
    (Kind::EnumField, &["S010"]),
    (Kind::KeyNotStatic, &["S005"]),
    (Kind::ReadInput, &["S017"]),
    (Kind::FamilyValue, &["S010"]),
    (Kind::ScalarKeyIndex, &["S022"]),
    (Kind::TargetKey, &["S016"]),
    (Kind::EarlyStep, &["S013"]),
];

/// Each kind of `@field` gets at least 5 predictions over the fixed
/// programs, and each prediction is one of its codes.
#[test]
fn the_kinds_of_field_get_predictions() {
    let ps = programs();
    for (kind, codes) in FIELD_CODES {
        let mut predicted = 0;
        for p in &ps {
            for site in 0..sites(kind, &p.items, &p.top).min(4) {
                let m = mutate(p, index(kind), u32::try_from(site).unwrap());
                if let Some(code) = m.expect {
                    assert!(codes.contains(&code), "{kind:?} predicted {code}");
                    predicted += 1;
                }
            }
        }
        assert!(predicted >= 5, "{kind:?} predicted {predicted} mutants");
    }
}

/// The mutants of `EarlyStep` are at least 5% of the mutants of the fixed
/// programs, though its site is rare, and none predicts another code than
/// `S013`.
#[test]
fn early_step_gets_a_share_of_the_draws() {
    let ps = programs();
    let early = ps
        .iter()
        .enumerate()
        .filter(|(n, p)| {
            let draw = u32::try_from(*n).unwrap().wrapping_mul(0x9e37_79b1);
            let m = mutate(p, draw, draw.rotate_left(7));
            let hit = m
                .what
                .contains("give the step before a key with a diagnostic");
            assert!(
                !hit || m.expect.is_none_or(|c| c == "S013"),
                "{:?}",
                m.expect
            );
            hit
        })
        .count();
    assert!(early * 20 >= ps.len(), "{early} of {}", ps.len());
}

/// A key of more than 64 characters occurs in a mutant of `NoField`, which
/// both front ends cut in their messages (section 5.5, #386).
#[test]
fn a_missing_key_is_sometimes_longer_than_64_characters() {
    let long = "a".repeat(70);
    let found = programs().iter().any(|p| {
        (0..sites(Kind::NoField, &p.items, &p.top)).any(|s| {
            mutate(p, index(Kind::NoField), u32::try_from(s).unwrap())
                .text
                .contains(&long)
        })
    });
    assert!(found);
}

/// The kinds of queries, with the codes that their mutants predict. A kind
/// of an alias of `@Struct` predicts nothing: the type is elaborated at its
/// first use.
const QUERY_CODES: [(Kind, &[&str]); 19] = [
    (Kind::BuiltinName, &["S001"]),
    (Kind::BuiltinArity, &["S001"]),
    (Kind::QueryOperand, &["S001"]),
    (Kind::IndexBuiltinType, &["S007"]),
    (Kind::NoType, &["S010"]),
    (Kind::StringIndex, &["S010"]),
    (Kind::QueryHardware, &["S011"]),
    (Kind::KeyHardware, &["S005"]),
    (Kind::TypeInfoValue, &["S010"]),
    (Kind::PortsValue, &["S010"]),
    (Kind::BuiltinType, &["S010"]),
    (Kind::ConstructorArity, &["S007"]),
    (Kind::KeyEffect, &["S016"]),
    (Kind::KeyMutation, &["S016"]),
    (Kind::StructArg, &[]),
    (Kind::FieldName, &[]),
    (Kind::UserFieldInfo, &[]),
    (Kind::SelfStruct, &[]),
    (Kind::ZeroNonData, &["S010"]),
];

/// Each kind of queries gets at least 5 mutants over the fixed programs, a
/// kind that predicts gets 5 predictions, and each prediction is one of its
/// codes.
#[test]
fn the_kinds_of_queries_get_predictions() {
    let ps = programs();
    for (kind, codes) in QUERY_CODES {
        let (mut mutants, mut predicted) = (0, 0);
        for p in &ps {
            let count = sites(kind, &p.items, &p.top);
            for site in 0..count.min(4) {
                let m = mutate(p, index(kind), u32::try_from(site).unwrap());
                // A kind that falls back to another kind does not count: the
                // mutant says what its own kind does at the site.
                let own = apply(kind, &mut p.items.clone(), &p.top, site).map(|(what, _)| what);
                if own.as_deref() != Some(m.what.as_str()) {
                    continue;
                }
                mutants += 1;
                if let Some(code) = m.expect {
                    assert!(codes.contains(&code), "{kind:?} predicted {code}");
                    predicted += 1;
                }
            }
        }
        assert!(mutants >= 5, "{kind:?} has {mutants} mutants");
        assert!(
            codes.is_empty() || predicted >= 5,
            "{kind:?} predicted {predicted} mutants"
        );
    }
}

/// The kinds of the gaps of `@field`, with the code that their mutants
/// predict.
const GAP_CODES: [(Kind, &[&str]); 5] = [
    (Kind::KeyValue, &["S011"]),
    (Kind::TargetMutation, &["S016"]),
    (Kind::TargetBase, &["S017"]),
    (Kind::PortPlace, &["S010"]),
    (Kind::InstanceData, &["S010"]),
];

/// Each kind of the gaps gets at least 5 mutants and 5 predictions over the
/// fixed programs, and each prediction is one of its codes.
#[test]
fn the_kinds_of_the_gaps_get_predictions() {
    let ps = programs();
    for (kind, codes) in GAP_CODES {
        let (mut mutants, mut predicted) = (0, 0);
        for p in &ps {
            for site in 0..sites(kind, &p.items, &p.top).min(4) {
                let m = mutate(p, index(kind), u32::try_from(site).unwrap());
                let own = apply(kind, &mut p.items.clone(), &p.top, site).map(|(what, _)| what);
                assert_eq!(own.as_deref(), Some(m.what.as_str()), "{kind:?}");
                mutants += 1;
                if let Some(code) = m.expect {
                    assert!(codes.contains(&code), "{kind:?} predicted {code}");
                    predicted += 1;
                }
            }
        }
        assert!(mutants >= 5, "{kind:?} has {mutants} mutants");
        assert!(predicted >= 5, "{kind:?} predicted {predicted} mutants");
    }
}
