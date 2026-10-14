// SPDX-License-Identifier: Apache-2.0
//! The function cases of `Silicon.Source.Test.Value`, `Test.Eval`, and `Test.Elab` in Lean:
//! the function types and function values of the value model, the function type as a type
//! expression, the function name as a value, `==`, the join, and the hardware `if`. The calls
//! through function values are in `tests_fn_call`. The tests of the work count the steps of the
//! walks and not the time.

use crate::counters::of;
use crate::eval::COPIES;
use crate::int::Int;
use crate::tests::{cost, exact, out, serialized_len, type_work};
use crate::tests_elab::{cost as elab_cost, order};
use crate::types::{Ty, TyId, TyParam, Types};
use crate::value::{InstantiationId, Value};

fn param(mutable: bool, ty: TyId) -> TyParam {
    TyParam { mutable, ty }
}

/// `fn (mut UInt[8], Bool) -> Unit`, the form of section 7.1.
fn inc_ty(tys: &mut Types) -> TyId {
    let (byte, flag, unit) = (tys.mk(Ty::UInt(8)), tys.mk(Ty::Bool), tys.mk(Ty::Unit));
    tys.function(vec![param(true, byte), param(false, flag)], unit)
}

/// `fn () -> Bool`.
fn pred_ty(tys: &mut Types) -> TyId {
    let flag = tys.mk(Ty::Bool);
    tys.function(Vec::new(), flag)
}

/// A function type is a node with each parameter type and the result type. Each `mut` mark is
/// one more node. The depth is 1 more than the deepest part, and a mark adds none.
#[test]
fn the_form_size_depth_and_text_of_a_function_type() {
    let mut tys = Types::default();
    let (inc, pred) = (inc_ty(&mut tys), pred_ty(&mut tys));
    let byte = tys.mk(Ty::UInt(8));
    let array = tys.array(byte, Int::from_u64(4));
    let higher = tys.function(vec![param(false, pred)], array);
    assert_eq!(
        Value::Type(inc).serialize(&tys),
        "(type (fn ((mut (uint 8)) bool) unit))"
    );
    assert_eq!(tys.serialize(pred), "(fn () bool)");
    assert_eq!(
        tys.serialize(higher),
        "(fn ((fn () bool)) (array (uint 8) 4))"
    );
    assert_eq!(tys.text(inc), "fn (mut UInt[8], Bool) -> Unit");
    assert_eq!(tys.text(pred), "fn () -> Bool");
    assert_eq!(tys.text(higher), "fn (fn () -> Bool) -> [UInt[8]; 4]");
    let list = tys.list(pred);
    assert_eq!(tys.text(list), "List[fn () -> Bool]");
    assert_eq!((inc.size(), pred.size(), higher.size()), (6, 2, 7));
    assert_eq!((inc.depth(), pred.depth(), higher.depth()), (2, 2, 3));
    let (flag, unit) = (tys.mk(Ty::Bool), tys.mk(Ty::Unit));
    let marked = tys.function(vec![param(true, flag)], unit);
    let plain = tys.function(vec![param(false, flag)], unit);
    assert_eq!(marked.size(), plain.size() + 1);
    assert_eq!(marked.depth(), plain.depth());
    assert_ne!(marked, plain);
    assert_eq!(Value::Type(higher).depth(), 3);
}

/// A function type is not hardware data: its three numbers are 0. The function flag holds at
/// any depth of a type, and a struct takes it from its field types and not its arguments.
#[test]
fn the_function_flag_of_the_metadata() {
    let mut tys = Types::default();
    let (inc, pred) = (inc_ty(&mut tys), pred_ty(&mut tys));
    let meta = tys.meta(inc);
    assert_eq!(
        (
            meta.width.clone(),
            meta.leaves.clone(),
            meta.zero_size.clone()
        ),
        (Int::zero(), Int::zero(), Int::zero())
    );
    assert!(!meta.data);
    assert!(inc.holds_fn() && pred.holds_fn());
    let (flag, int) = (tys.mk(Ty::Bool), tys.mk(Ty::Int));
    let (zero_array, list) = (tys.array(pred, Int::zero()), tys.list(pred));
    assert!(zero_array.holds_fn() && list.holds_fn());
    let tuple = tys.tuple(vec![flag, pred]);
    let nested = tys.tuple(vec![flag, list]);
    let deep = tys.array(nested, Int::from_u64(2));
    assert!(tuple.holds_fn() && deep.holds_fn());
    let plain = tys.tuple(vec![flag, int]);
    let strings = tys.mk(Ty::String);
    let plain_list = tys.list(strings);
    let plain_array = tys.array(plain_list, Int::from_u64(2));
    assert!(!plain.holds_fn() && !plain_array.holds_fn() && !flag.holds_fn());
    let spec = tys.begin_spec("Holder", 0, Vec::new(), false);
    let (meta, depth) = tys.struct_meta(spec, &[pred]);
    let holder = tys.finish_spec(spec, vec![pred], meta, depth);
    assert!(holder.holds_fn() && tys.list(holder).holds_fn());
    let spec = tys.begin_spec("Tag", 1, vec![Value::Type(pred)], false);
    let (meta, depth) = tys.struct_meta(spec, &[]);
    let tag = tys.finish_spec(spec, Vec::new(), meta, depth);
    assert!(!tag.holds_fn());
}

/// A function value is its item and its signature. It serializes its package and its name,
/// has the size 1 and the depth 1, and its type is its signature.
#[test]
fn the_function_value() {
    let mut tys = Types::default();
    let (inc_sig, pred) = (inc_ty(&mut tys), pred_ty(&mut tys));
    tys.name_fn(0, "inc");
    tys.name_fn(1, "yes");
    let inc = Value::Function(0, inc_sig);
    assert_eq!(inc.serialize(&tys), "(function root inc)");
    assert_eq!((inc.size(), inc.depth(), inc.measure_charge()), (1, 1, 0));
    assert_eq!(inc.ty(&mut tys), inc_sig);
    assert_eq!(inc.text(&tys), "fn (mut UInt[8], Bool) -> Unit");
    assert_eq!(inc, Value::Function(0, inc_sig));
    assert_ne!(inc, Value::Function(1, inc_sig));
    assert_ne!(inc, Value::Function(0, pred));
    let tuple = Value::tuple(vec![inc.clone()]);
    assert_eq!(tuple.serialize(&tys), "(tuple ((function root inc)))");
    assert_eq!((tuple.size(), tuple.depth()), (2, 2));
    let one = tys.tuple(vec![inc_sig]);
    assert_eq!(tuple.ty(&mut tys), one);
    let list = Value::List(pred, vec![Value::Function(1, pred)]);
    assert_eq!(
        list.serialize(&tys),
        "(list (fn () bool) ((function root yes)))"
    );
    assert_eq!(Value::List(pred, Vec::new()).depth(), 3);
    let id = InstantiationId {
        module: "Map".to_owned(),
        args: vec![inc.clone()],
    };
    assert_eq!(
        id.serialize(&tys),
        "(instantiation root Map ((function root inc)))"
    );
    assert_eq!(inc.serialized_len(&tys), 19);
    assert!(inc.holds_fn() && tuple.holds_fn() && list.holds_fn());
    assert!(!Value::tuple(vec![Value::Bool(true)]).holds_fn());
}

fn o(src: &str, expr: &str) -> String {
    out(src, expr, 100_000_000, 1000)
}

fn with(src: &str, expr: &str, fuel: u64) -> String {
    out(src, expr, fuel, 1000)
}

fn depth(src: &str, expr: &str, depth: u64) -> String {
    out(src, expr, 100_000_000, depth)
}

/// A function type is a type. Its parameter types evaluate, then its result type. It charges
/// its node, its parts, and its size, and a `mut` mark is one more node of the size.
#[test]
fn the_function_type_and_its_charges() {
    assert_eq!(o("", "fn () -> Bool"), "(type (fn () bool))");
    assert_eq!(
        o("", "fn (Bool, mut UInt[8]) -> (Bool, Nat)"),
        "(type (fn (bool (mut (uint 8))) (tuple (bool nat))))"
    );
    assert_eq!(
        o("const C: Type = fn (mut [Bool; 2]) -> Bool;", "C"),
        "(type (fn ((mut (array bool 2))) bool))"
    );
    assert_eq!(
        o("fn f(T: Type) -> Type { return fn (T) -> T; }", "f(Bool)"),
        "(type (fn (bool) bool))"
    );
    exact("", "fn () -> Bool", 4);
    exact("", "fn (Bool) -> Bool", 6);
    exact("", "fn (mut Bool) -> Bool", 7);
    exact("", "fn (fn () -> Bool) -> UInt[8]", 16);
    assert_eq!(depth("", "fn () -> Bool", 2), "(type (fn () bool))");
    assert_eq!(depth("", "fn () -> Bool", 1), "S015 1:1");
    let body = |s: &str| format!("fn f() -> Bool {{ {s} }}");
    assert_eq!(
        cost(&body("type X = fn (mut Bool) -> Bool; return true;"), "f()"),
        cost(&body("type X = Bool; return true;"), "f()") + 6
    );
}

/// A typed use at a function type needs a function of that exact type, also in the `mut`
/// marks. It charges nothing. Another value is `S010` at the typed use.
#[test]
fn the_typed_use_of_a_function() {
    let body = |s: &str| format!("fn f() -> Bool {{ {s} }}");
    assert_eq!(
        o(&body("let x: fn () -> Bool = true; return x;"), "f()"),
        "S010 1:18"
    );
    let mut tys = Types::default();
    let (flag, unit) = (tys.mk(Ty::Bool), tys.mk(Ty::Unit));
    let nullary = tys.function(Vec::new(), flag);
    let marked = tys.function(vec![param(true, flag)], flag);
    let plain = tys.function(vec![param(false, flag)], flag);
    let mut fuel = crate::ops::Fuel::new(100);
    let g = Value::Function(0, nullary);
    assert!(matches!(
        crate::ops::convert(nullary, &g, &mut fuel, &tys),
        Ok(None)
    ));
    let k = Value::Function(1, marked);
    assert!(matches!(
        crate::ops::convert(marked, &k, &mut fuel, &tys),
        Ok(None)
    ));
    assert!(crate::ops::convert(plain, &k, &mut fuel, &tys).is_err());
    assert!(crate::ops::convert(nullary, &Value::Bool(true), &mut fuel, &tys).is_err());
    assert!(crate::ops::convert(flag, &g, &mut fuel, &tys).is_err());
    assert!(crate::ops::convert(unit, &g, &mut fuel, &tys).is_err());
    assert_eq!(fuel.left(), 100);
}

/// A unary operator on a function type is `S010` at the operator, before its charge. A
/// constructor of a function type is `S010` at the call, after its callee and before its
/// arguments, also with a wrong number of arguments.
#[test]
fn the_operator_and_the_constructor_of_a_function_type() {
    assert_eq!(with("", "-fn () -> Bool", 5), "S010 1:1");
    assert_eq!(with("", "-fn () -> Bool", 4), "S015 1:2");
    assert_eq!(o("", "(fn () -> Bool)()"), "S010 1:1");
    assert_eq!(o("", "(fn () -> Bool)(1)"), "S010 1:1");
    assert_eq!(with("", "(fn () -> Bool)(1, 2, 3)", 5), "S010 1:1");
    assert_eq!(with("", "(fn () -> Bool)(1, 2, 3)", 4), "S015 1:2");
}

/// `==` and `!=` are `S010` at the operator when the type of an operand holds a function
/// type. The check comes after both operands and before the join and the charge of the
/// operator. Two function types are types, so they compare and charge the sum of their sizes.
#[test]
fn equality_takes_no_function() {
    let eq = "list(fn () -> Bool) == list(fn () -> Bool)";
    assert_eq!(with("", eq, 19), "S010 1:1");
    assert_eq!(with("", eq, 18), "S015 1:24");
    assert_eq!(o("", "list(fn () -> Bool) != 1"), "S010 1:1");
    let body = |s: &str| format!("fn f() -> Bool {{ {s} }}");
    assert_eq!(
        o(
            &body("let a: [fn () -> Bool; 0] = []; return a == a;"),
            "f()"
        ),
        "S010 1:57"
    );
    assert_eq!(
        o(
            &body("let a: [fn () -> Bool; 0] = []; return (1, [a]) != (1, [a]);"),
            "f()"
        ),
        "S010 1:57"
    );
    assert_eq!(o("", "(fn () -> Bool) == (fn () -> Bool)"), "(bool true)");
    assert_eq!(
        o("", "(fn () -> Bool) == (fn (mut Bool) -> Bool)"),
        "(bool false)"
    );
    exact("", "(fn () -> Bool) == (fn () -> Bool)", 13);
}

/// A join of two function types charges as a type equality, the sum of the two sizes. The two
/// types are equal, also in their `mut` marks, else the join fails.
#[test]
fn the_join_of_function_types() {
    let lists = |t: &str, u: &str| format!("[list({t}), list({u})]");
    let same = lists("fn () -> Bool", "fn () -> Bool");
    assert_eq!(
        o("", &same),
        "(array (list (fn () bool)) ((list (fn () bool) ()) (list (fn () bool) ())))"
    );
    assert_eq!(
        cost("", &same),
        cost("", "(list(fn () -> Bool), list(fn () -> Bool))") + 5
    );
    assert_eq!(
        o("", &lists("fn () -> Bool", "fn (mut Bool) -> Bool")),
        "S010 1:1"
    );
    assert_eq!(
        o("", &lists("fn (Bool) -> Bool", "fn (mut Bool) -> Bool")),
        "S010 1:1"
    );
}

const FNS: &str = "fn g() -> Bool { return true; }\n\
fn g2() -> Bool { return false; }\n\
fn k(mut b: Bool) -> Bool { return b; }\n\
fn h(x: fn () -> Bool) -> Bool { return true; }\n\
comptime fn c() -> Bool { return true; }\n\
fn gen(comptime n: Nat) -> Bool { return true; }\n\
const N: Nat = 2;\n\
fn a(x: [Bool; N]) -> Bool { return true; }\n";

/// A function name that is not a callee gives a function value. The name charges its node, then
/// the signature evaluates as type expressions, then the function type checks its depth and
/// charges its size. Each use evaluates the signature again.
#[test]
fn a_function_name_is_a_value() {
    assert_eq!(o(FNS, "g"), "(function root g)");
    assert_eq!(o(FNS, "k"), "(function root k)");
    exact(FNS, "g", 4);
    exact(FNS, "k", 7);
    exact(FNS, "h", 10);
    exact(FNS, "(g, g)", 1 + 4 + 4 + 3);
    assert_eq!(cost(FNS, "(g, g)"), cost(FNS, "(true, true)") + 4);
    // The signature reads the items in its scope.
    assert_eq!(o(FNS, "a"), "(function root a)");
    assert_eq!(
        o(FNS, "[a]"),
        "(array (fn ((array bool 2)) bool) ((function root a)))"
    );
    // A `comptime fn` gives a function value of the same function type.
    assert_eq!(o(FNS, "c"), "(function root c)");
    assert_eq!(
        o(FNS, "[g, c]"),
        "(array (fn () bool) ((function root g) (function root c)))"
    );
}

/// A generic function and a builtin are `S010` at the name, after the charge of its node. The
/// signature does not evaluate.
#[test]
fn a_generic_function_and_a_builtin_are_no_value() {
    assert_eq!(with(FNS, "gen", 1), "S010 1:1");
    assert_eq!(with(FNS, "gen", 0), "S015 1:1");
    assert_eq!(with(FNS, "len", 1), "S010 1:1");
    assert_eq!(with(FNS, "len", 0), "S015 1:1");
    assert_eq!(with(FNS, "(1, push)", 100), "S010 1:5");
}

/// The function type checks its depth at the name, and each depth check of the signature
/// reports at the name. A constant in the signature nests, so its own depth reports at its
/// own node.
#[test]
fn the_depth_of_a_signature_reports_at_the_name() {
    assert_eq!(depth(FNS, "h", 3), "(function root h)");
    assert_eq!(depth(FNS, "h", 2), "S015 1:1");
    assert_eq!(depth(FNS, "(1, h)", 2), "S015 1:5");
    let deep = "fn p(x: fn () -> fn () -> Bool) -> Bool { return true; }\n\
fn r() -> fn () -> fn () -> Bool { return r; }\n\
const D: [[Bool; 1]; 1] = [[true]];\n\
fn q(x: [Bool; len(D)]) -> Bool { return true; }\n";
    assert_eq!(depth(deep, "p", 4), "(function root p)");
    assert_eq!(depth(deep, "p", 2), "S015 1:1");
    assert_eq!(depth(deep, "(1, r)", 2), "S015 1:5");
    assert_eq!(depth(deep, "q", 3), "(function root q)");
    assert_eq!(depth(deep, "q", 2), "S015 3:10");
}

/// A binding of a function name is no copy. A binding of a local that holds a function copies
/// its size 1. A typed use at the exact function type charges nothing more than its type.
#[test]
fn bindings_of_function_values() {
    let fl = |s: &str| format!("{FNS}fn f() -> Bool {{ {s} }}");
    assert_eq!(o(&fl("let x = g; return true;"), "f()"), "(bool true)");
    let base = cost(&fl("let x = g; return true;"), "f()");
    assert_eq!(cost(&fl("let x = true; return true;"), "f()") + 2, base);
    assert_eq!(
        cost(&fl("let x = g; let y = x; return true;"), "f()"),
        base + 3
    );
    assert_eq!(
        cost(&fl("let x: fn () -> Bool = g; return true;"), "f()"),
        base + 4
    );
    let base_k = cost(&fl("let x = k; return true;"), "f()");
    assert_eq!(
        cost(&fl("let x: fn (mut Bool) -> Bool = k; return true;"), "f()"),
        base_k + 7
    );
}

/// A typed use needs the exact function type, also in the `mut` marks, else `S010`: a `let`, an
/// assignment, an argument, and a return.
#[test]
fn the_typed_use_of_a_function_name() {
    let fl = |s: &str| format!("{FNS}fn f() -> Bool {{ {s} }}");
    let run = |s: &str| o(&fl(s), "f()");
    assert_eq!(
        run("let x: fn (Bool) -> Bool = k; return true;"),
        "S010 9:18"
    );
    assert_eq!(
        run("let x: fn (mut Bool) -> Bool = g; return true;"),
        "S010 9:18"
    );
    assert_eq!(run("let x: fn () -> Bool = c; return true;"), "(bool true)");
    assert_eq!(run("let x: Bool = g; return true;"), "S010 9:18");
    assert_eq!(run("let mut x = g; x = g2; return true;"), "(bool true)");
    assert_eq!(run("let mut x = g; x = k; return true;"), "S010 9:33");
    assert_eq!(o(FNS, "h(g)"), "(bool true)");
    assert_eq!(o(FNS, "h(c)"), "(bool true)");
    assert_eq!(o(FNS, "h(k)"), "S010 1:1");
    let ret = |s: &str| format!("{FNS}fn r() -> fn () -> Bool {{ {s} }}");
    assert_eq!(o(&ret("return g2;"), "r()"), "(function root g2)");
    assert_eq!(o(&ret("return k;"), "r()"), "S010 9:27");
    let pass = format!("{FNS}fn r(x: fn () -> Bool) -> fn () -> Bool {{ return x; }}");
    assert_eq!(o(&pass, "r(g)"), "(function root g)");
}

/// A function value is an element of an array, a tuple, and a list. The elements of an array
/// join their function types as a type equality.
#[test]
fn function_values_in_containers() {
    assert_eq!(
        o(FNS, "[g, g2]"),
        "(array (fn () bool) ((function root g) (function root g2)))"
    );
    assert_eq!(cost(FNS, "[g, g2]"), cost(FNS, "(g, g2)") + 4);
    assert_eq!(o(FNS, "[g, k]"), "S010 1:1");
    assert_eq!(
        o(FNS, "(g, k)"),
        "(tuple ((function root g) (function root k)))"
    );
    let fl = |s: &str| format!("{FNS}fn f() -> Bool {{ {s} }}");
    assert_eq!(
        o(
            &fl("let mut xs = list(fn () -> Bool); push(xs, g); push(xs, c); return true;"),
            "f()"
        ),
        "(bool true)"
    );
    let pop = format!(
        "{FNS}fn r() -> fn () -> Bool {{ let mut xs = list(fn () -> Bool); \
         xs.push(g2); return xs.pop(); }}"
    );
    assert_eq!(o(&pop, "r()"), "(function root g2)");
    assert_eq!(
        o(
            &fl("let mut xs = list(fn () -> Bool); push(xs, k); return true;"),
            "f()"
        ),
        "S010 9:52"
    );
}

/// `==` and `!=` are `S010` at the operator after both operands, before the charge: here the
/// operator charges 1 and each `g` charges 4.
#[test]
fn equality_of_function_values() {
    assert_eq!(with(FNS, "g == g", 9), "S010 1:1");
    assert_eq!(with(FNS, "g == g", 8), "S015 1:6");
    assert_eq!(o(FNS, "[g] != [g]"), "S010 1:1");
    assert_eq!(o(FNS, "(1, g) == (1, g)"), "S010 1:1");
    let fl = format!("{FNS}fn f() -> Bool {{ let x = g; return x(); }}");
    assert_eq!(o(&fl, "f()"), "(bool true)");
}

fn arms(body: &str) -> String {
    format!(
        "fn g() -> Bool {{ return true; }}\nfn g2() -> Bool {{ return false; }}\n\
         module T() {{\n  input c: Bool;\n  output o: Bool;\n{body}  o := c;\n}}\n"
    )
}

/// A hardware `if` with two function arms: one function item gives the static value, and two
/// different items are `S011` at the `if`. The pair charges as a static equality, 1 + 1. A
/// function and another value are `S010` at the `if`.
#[test]
fn a_hardware_if_with_function_arms() {
    let total = |body: &str| elab_cost(&arms(body), "T");
    assert!(total("  let f = if (c) { g } else { g };\n").starts_with("total"));
    let units = |body: &str| {
        let text = total(body);
        text.lines()
            .next()
            .and_then(|l| l.strip_prefix("total "))
            .and_then(|n| n.parse::<u64>().ok())
            .unwrap_or(0)
    };
    assert_eq!(
        units("  let f = if (c) { g } else { g };\n"),
        units("  let f = g;\n") + 8
    );
    assert_eq!(total("  let f = if (c) { g } else { g2 };\n"), "S011 6:11");
    assert_eq!(
        total("  let f = if (c) { g } else { true };\n"),
        "S010 6:11"
    );
    assert!(total("  let f: fn () -> Bool = if (c) { g } else { g };\n").starts_with("total"));
}

const ITEMS: &str = "fn inc(a: UInt[8]) -> UInt[8] { return a +% 1; }\n\
fn dec(a: UInt[8]) -> UInt[8] { return a -% 1; }\n\
fn bump(mut a: UInt[8]) -> UInt[8] { return a; }\n\
fn gen(comptime W: Nat, a: UInt[W]) -> UInt[W] { return a; }\n";
const FN_TY: &str = "fn (UInt[8]) -> UInt[8]";

fn argument(ty: &str, arg: &str) -> String {
    format!(
        "{ITEMS}module C(comptime f: {ty}) {{\n}}\nmodule M() {{\n  instance c = C({arg});\n}}\n"
    )
}

fn digest(arg: &str) -> String {
    format!(
        "C$0h{}",
        crate::names::sha16(&format!("(instantiation root C ({arg}))"))
    )
}

/// A function value is a module argument (section 7.1). It serializes as `(function root
/// inc)`, so it gives the digest form of the emitted name.
#[test]
fn a_function_is_a_module_argument() {
    let names = |src: &str| order(src, "M");
    assert_eq!(
        names(&argument(FN_TY, "inc")),
        [digest("(function root inc)"), "M".to_owned()]
    );
    assert_eq!(
        names(&argument(FN_TY, "dec")),
        [digest("(function root dec)"), "M".to_owned()]
    );
    assert_eq!(
        names(&argument("Type", "fn (mut UInt[8]) -> Bool")),
        [digest("(type (fn ((mut (uint 8))) bool))"), "M".to_owned()]
    );
    assert_eq!(
        names(&argument(&format!("[{FN_TY}; 1]"), "[inc]")),
        [
            digest("(array (fn ((uint 8)) (uint 8)) ((function root inc)))"),
            "M".to_owned()
        ]
    );
    assert_eq!(
        names(&argument(&format!("[{FN_TY}; 0]"), "[]")),
        [
            digest("(array (fn ((uint 8)) (uint 8)) ())"),
            "M".to_owned()
        ]
    );
    let shared = format!(
        "const F: {FN_TY} = inc;\n{ITEMS}module C(comptime f: {FN_TY}) {{\n}}\n\
         module M() {{\n  instance c = C(F);\n  instance d = C(inc);\n}}\n"
    );
    assert_eq!(
        names(&shared),
        [digest("(function root inc)"), "M".to_owned()]
    );
}

/// A typed use at a module parameter needs the exact function type: another `mut` mark,
/// another function type, and another value are `S010` at the statement. A generic function
/// and a builtin are `S010` at the name, before the statement. A top selection has only
/// literal arguments.
#[test]
fn a_module_parameter_takes_the_exact_function_type() {
    let cost = |ty: &str, arg: &str| elab_cost(&argument(ty, arg), "M");
    assert!(cost(FN_TY, "inc").starts_with("total"));
    assert_eq!(cost(FN_TY, "bump"), "S010 8:3");
    assert_eq!(cost("fn (UInt[8]) -> Bool", "inc"), "S010 8:3");
    assert_eq!(cost(FN_TY, "3"), "S010 8:3");
    assert_eq!(cost("UInt[8]", "inc"), "S010 8:3");
    assert_eq!(cost(FN_TY, "gen"), "S010 8:18");
    assert_eq!(cost(FN_TY, "len"), "S010 8:18");
    let top = format!("{ITEMS}module C(comptime f: {FN_TY}) {{\n}}\n");
    assert_eq!(elab_cost(&top, "C(inc)"), "usage");
    assert_eq!(elab_cost(&top, "C(3)"), "S010 1:1");
}

/// A function value is a struct argument and a field of a record. The struct type serializes
/// its arguments, so the key of the specialization and the `InstantiationId` hold the
/// function.
#[test]
fn a_function_is_a_struct_argument_and_a_field() {
    let program = |field: &str, arg: &str| {
        format!(
            "{ITEMS}struct S(comptime f: {FN_TY}) {{ a: UInt[8] }}\nstruct R {{ f: {FN_TY} }}\n\
             module C(comptime s: {field}) {{\n}}\nmodule M() {{\n  instance c = C({arg});\n}}\n"
        )
    };
    assert_eq!(
        order(&program("S[inc]", "S[inc](1)"), "M"),
        [
            digest("(record (struct root S ((function root inc))) ((uint 8 1)))"),
            "M".to_owned()
        ]
    );
    assert_eq!(
        order(&program("R", "R(inc)"), "M"),
        [
            digest("(record (struct root R ()) ((function root inc)))"),
            "M".to_owned()
        ]
    );
    assert_eq!(elab_cost(&program("S[inc]", "S[dec](1)"), "M"), "S010 10:3");
    assert_eq!(
        elab_cost(&program("S[inc]", "S[bump](1)"), "M"),
        "S010 10:18"
    );
    assert_eq!(elab_cost(&program("R", "R(bump)"), "M"), "S010 10:18");
}

/// A function type is not hardware data. A port, a register, and a wire of a function type,
/// also in an array, are `S010` at the statement. A function value at a hardware use is
/// `S010` at the statement.
#[test]
fn no_function_reaches_hardware() {
    let hw = |body: &str| {
        elab_cost(
            &format!("{ITEMS}module M() domains(clk) {{\n  input c: Bool;\n{body}}}\n"),
            "M",
        )
    };
    for ports in [
        format!("  input x: {FN_TY};\n"),
        format!("  output x: {FN_TY};\n"),
        format!("  wire x: {FN_TY};\n"),
        format!("  reg x: {FN_TY} = inc;\n"),
        format!("  input x: [{FN_TY}; 0];\n"),
        "  reg r: UInt[8] = inc;\n  r := r;\n".to_owned(),
    ] {
        assert_eq!(hw(&ports), "S010 7:3", "{ports}");
    }
    assert_eq!(hw("  output y: UInt[8];\n  y := inc;\n"), "S010 8:3");
    assert_eq!(
        hw("  output y: UInt[8];\n  y := if (c) { inc } else { inc };\n"),
        "S010 8:3"
    );
}

/// The work counters of the function types follow their parts. A chain of `n` function types
/// makes `n` types, with one lookup for each, and its text has a length in `n`. The charges
/// grow faster, because each level pays the size of its type, but no walk does.
#[test]
fn a_chain_of_function_types_costs_linear_work() {
    let chain = |n: usize| format!("{}Bool", "fn () -> ".repeat(n));
    let fuel_of = |n: usize| 100_000_000 + n as u64;
    let measure = |n: usize| {
        let fuel = fuel_of(n);
        let text = out("", &chain(n), fuel, 1000);
        assert!(text.starts_with("(type (fn () (fn () "), "{n}");
        let counts = of(fuel);
        (
            counts.params,
            serialized_len("", &chain(n)),
            type_work("", &chain(n)),
        )
    };
    let (a, b, c) = (measure(100), measure(200), measure(400));
    assert_eq!((a.0, b.0, c.0), (100, 200, 400));
    // The text has 8 bytes for each type and 11 for the rest.
    assert_eq!((a.1, b.1, c.1), (811, 1611, 3211));
    // The lookups of the table grow by a constant for each type.
    assert_eq!(c.2 - b.2, 2 * (b.2 - a.2));
}

/// Many uses of one function name make a signature each, with no copy of the name. The type
/// is found again in the table, so the work of the table grows by a constant for each use, and
/// the charge of each use is the same.
#[test]
fn many_uses_of_one_function_name_cost_linear_work() {
    let uses = |n: usize| format!("({})", vec!["g"; n].join(", "));
    let measure = |n: usize| {
        let fuel = 200_000_000 + n as u64;
        let text = out(FNS, &uses(n), fuel, 1000);
        assert!(text.starts_with("(tuple ((function root g)"), "{n}");
        let copies = COPIES
            .lock()
            .ok()
            .and_then(|c| c.get(&fuel).copied())
            .unwrap_or(u64::MAX);
        (
            of(fuel).params,
            copies,
            type_work(FNS, &uses(n)),
            cost(FNS, &uses(n)),
        )
    };
    let (a, b, c) = (measure(50), measure(100), measure(200));
    assert_eq!((a.0, b.0, c.0), (50, 100, 200));
    assert_eq!((a.1, b.1, c.1), (0, 0, 0));
    assert_eq!(c.2 - b.2, 2 * (b.2 - a.2));
    assert_eq!(c.3 - b.3, 2 * (b.3 - a.3));
}

/// The check of `==` reads the function flag of each operand in constant work: it does not
/// walk the tuples (section 5.1).
#[test]
fn the_function_flag_check_does_constant_work() {
    let tuple = |n: usize, last: &str| format!("({}, {last})", vec!["1"; n].join(", "));
    let measure = |n: usize| {
        let fuel = 300_000_000 + n as u64;
        let expr = format!("{0} == {0}", tuple(n, "2"));
        assert_eq!(out("", &expr, fuel, 1000), "(bool true)");
        of(fuel).flagged
    };
    assert_eq!((measure(10), measure(50), measure(100)), (2, 2, 2));
    // A function in the last element of a long tuple gives one read, which short-circuits.
    let fuel = 300_000_999;
    let expr = format!("{0} == {0}", tuple(100, "g"));
    let src = "fn g() -> Bool { return true; }";
    assert!(out(src, &expr, fuel, 1000).starts_with("S010"));
    assert_eq!(of(fuel).flagged, 1);
    // The type id of a list holds the flag.
    let fuel = 300_000_998;
    let expr = "(list(fn () -> Bool), 1) == (list(fn () -> Bool), 1)";
    assert!(out("", expr, fuel, 1000).starts_with("S010"));
    assert_eq!(of(fuel).flagged, 1);
}
