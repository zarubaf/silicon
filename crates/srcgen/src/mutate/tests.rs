// SPDX-License-Identifier: Apache-2.0
//! Tests of the mutation kinds and their predictions.

use super::super::build::typed;
use super::super::eval::Value;
use super::super::program::tests::{TEXT, program};
use super::super::program::{
    FieldTy, HBin, HExpr, Item, Place, Ports, Program, Radix, SBin, SExpr, STy, Stmt, Ty,
};
use super::*;
use num_bigint::BigInt;
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

fn index(kind: Kind) -> u32 {
    u32::try_from(KINDS.iter().position(|&k| k == kind).unwrap()).unwrap()
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
        params: vec![("x0".to_owned(), u8())],
        ret: u8(),
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
        let kind = u32::try_from(n % 8).unwrap();
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
    assert_eq!(
        codes.into_iter().collect::<Vec<_>>(),
        ["S002", "S003", "S007", "S018"]
    );
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
        params: vec![("a0".to_owned(), u8()), ("x1".to_owned(), u8())],
        mut_first: true,
        ret: u8(),
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

#[test]
fn mutation_is_deterministic() {
    let p = program();
    for kind in 0..11 {
        assert_eq!(mutate(&p, kind, 11), mutate(&p, kind, 11));
    }
}
