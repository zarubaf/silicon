// SPDX-License-Identifier: Apache-2.0
//! One mutation of a typed program (front-end spec 11.4, mode 3).
//!
//! The mutation edits a copy of the items and prints it with the one
//! printer, so each mutant parses. The original program elaborates, and
//! each pass of the front ends stops the run (spec 6.2). A mutation that
//! adds one error of an early pass therefore fixes the first code, and
//! `Mutant::expect` predicts it:
//!
//! - A copy of a declaration is `S002` (pass 2): all local kinds and the
//!   items share one namespace in a scope, and the copy is in that scope.
//! - A name reference `q0` is `S003` (pass 3): `q` is no prefix of the
//!   builder, and the resolver checks each name, also in dead code.
//! - A deleted declaration that its item still mentions (an item: that
//!   any item still mentions) is `S003`. Generated names are unique in an
//!   item, so no other declaration catches the use.
//! - One argument more or less is `S007` (pass 4), on all code.
//! - A deleted `:=` in the top frame of a module body is `S018` (pass 5):
//!   each module of a program has a context, so its top frame runs, and
//!   nothing else fails.
//!
//! Any other mutation can fail in pass 5 at a point that depends on the
//! values, or pass, so its prediction is `None`.

use super::program::sexpr as sexpr_text;
use super::program::{HExpr, Item, Place, Program, Radix, SBin, SExpr, Stmt, Ty, render_items};
use num_bigint::BigInt;
use std::mem;

/// A mutant: its source text, what the mutation did, and the first code
/// that both front ends must report, where the pass order makes it certain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mutant {
    pub text: String,
    pub what: String,
    pub expect: Option<&'static str>,
}

/// The kinds of mutation, in the cyclic order of the fallback.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// A statement of a module or helper body, or an item other than the
    /// top module, goes.
    Delete,
    /// A declaration statement or an item, copied right after itself.
    Duplicate,
    /// A name reference becomes `q0`.
    Rename,
    /// The last argument of an instance or a call goes.
    DropArg,
    /// An instance or a call gets the argument `0` at its end.
    AddArg,
    /// A width `w` becomes `(w + 1)`.
    Widen,
    /// A width becomes `0`.
    ZeroWidth,
    /// A static expression becomes `(1 / 0)`.
    Fault,
}

const KINDS: [Kind; 8] = [
    Kind::Delete,
    Kind::Duplicate,
    Kind::Rename,
    Kind::DropArg,
    Kind::AddArg,
    Kind::Widen,
    Kind::ZeroWidth,
    Kind::Fault,
];

/// The mutant of `program` for the kind `kind % 8`, or for the next kind
/// in cyclic order that has a site, at the site `site % count` in the
/// pre-order of the items.
#[must_use]
pub fn mutate(program: &Program, kind: u32, site: u32) -> Mutant {
    let first = kind as usize % KINDS.len();
    let mutant = KINDS
        .iter()
        .cycle()
        .skip(first)
        .take(KINDS.len())
        .find_map(|&kind| {
            let count = sites(kind, &program.items, &program.top);
            if count == 0 {
                return None;
            }
            let mut items = program.items.clone();
            let (what, expect) = apply(kind, &mut items, &program.top, site as usize % count)?;
            Some(Mutant {
                text: render_items(&items),
                what,
                expect,
            })
        });
    // A built program has the `:=` of a top output, a `Delete` site. The
    // equal text shows the bug to `diff-si`.
    mutant.unwrap_or_else(|| Mutant {
        text: program.text(),
        what: "no mutation site".to_owned(),
        expect: None,
    })
}

/// The number of sites of `kind` in `items`.
fn sites(kind: Kind, items: &[Item], top: &str) -> usize {
    let mut w = Walk::new(kind, top, None);
    w.items(&mut items.to_vec());
    w.seen
}

/// Applies `kind` at the site `site` and gives what it did and the
/// predicted code, or `None` if `site` is not below `sites`.
fn apply(
    kind: Kind,
    items: &mut Vec<Item>,
    top: &str,
    site: usize,
) -> Option<(String, Option<&'static str>)> {
    let mut w = Walk::new(kind, top, Some(site));
    w.items(items);
    let Hit { what, effect } = w.hit?;
    let expect = match effect {
        Effect::Code(c) => c,
        Effect::Gone(name, scope) => {
            let scope = match scope {
                Some(i) => items.get(i..=i).unwrap_or_default(),
                None => items.as_slice(),
            };
            mentions(&name, scope).then_some("S003")
        }
    };
    Some((what, expect))
}

/// Whether a name reference in `items` is `name`: a value, an assignment
/// target, the instance of a field, an instance module, or a callee. The
/// guard `x == 0` of a `comptime fn` is no walked expression, so neither
/// this check nor `Rename` sees it. That costs no prediction: the guard
/// names the first parameter, and no mutation deletes a parameter.
fn mentions(name: &str, items: &[Item]) -> bool {
    let mut w = Walk::new(Kind::Rename, "", None);
    w.items(&mut items.to_vec());
    w.names.iter().any(|n| n == name)
}

/// The effect of a mutation on the first error.
enum Effect {
    Code(Option<&'static str>),
    /// The declaration of a name went: `S003` if the item at the index
    /// (all items if `None`) still mentions it.
    Gone(String, Option<usize>),
}

struct Hit {
    what: String,
    effect: Effect,
}

/// A pre-order walk over the sites of one kind: items in order, then
/// statements in order, then expressions left to right. Without a target
/// it only counts the sites (and, for `Rename`, collects the names); with
/// one it mutates that site.
struct Walk<'a> {
    kind: Kind,
    top: &'a str,
    target: Option<usize>,
    seen: usize,
    hit: Option<Hit>,
    names: Vec<String>,
    /// The name and index of the current item, and the count of its
    /// statements so far.
    item: String,
    index: usize,
    stmt: usize,
}

impl<'a> Walk<'a> {
    fn new(kind: Kind, top: &'a str, target: Option<usize>) -> Walk<'a> {
        Walk {
            kind,
            top,
            target,
            seen: 0,
            hit: None,
            names: Vec::new(),
            item: String::new(),
            index: 0,
            stmt: 0,
        }
    }

    /// Counts a site of `kind`; true if it is the target.
    fn site(&mut self, kind: Kind) -> bool {
        if kind != self.kind || self.hit.is_some() {
            return false;
        }
        self.seen += 1;
        self.target == Some(self.seen - 1)
    }

    fn hit(&mut self, what: String, effect: Effect) {
        self.hit = Some(Hit { what, effect });
    }

    fn items(&mut self, items: &mut Vec<Item>) {
        let mut i = 0;
        while let Some(item) = items.get(i) {
            let name = item_name(item).to_owned();
            if name != self.top && self.site(Kind::Delete) {
                items.remove(i);
                self.hit(format!("delete item {name}"), Effect::Gone(name, None));
                return;
            }
            if self.site(Kind::Duplicate) {
                items.insert(i + 1, item.clone());
                self.hit(format!("duplicate item {name}"), Effect::Code(Some("S002")));
                return;
            }
            self.item = name;
            self.index = i;
            self.stmt = 0;
            if let Some(item) = items.get_mut(i) {
                self.item_body(item);
            }
            if self.hit.is_some() {
                return;
            }
            i += 1;
        }
    }

    fn item_body(&mut self, item: &mut Item) {
        match item {
            Item::Const { value, .. } => self.sexpr(value),
            Item::ComptimeFn(f) => {
                self.sexpr(&mut f.base);
                self.sexpr(&mut f.step);
            }
            Item::Helper {
                params,
                ret,
                body,
                result,
                ..
            } => {
                for (_, t) in params {
                    self.ty(t);
                }
                self.ty(ret);
                self.stmts(body, false);
                self.hexpr(result);
            }
            Item::Module { body, .. } => self.stmts(body, true),
        }
    }

    /// The statements of a body; `top` if it is the top frame of a module.
    fn stmts(&mut self, body: &mut Vec<Stmt>, top: bool) {
        let mut i = 0;
        while let Some(s) = body.get(i) {
            self.stmt += 1;
            let n = self.stmt;
            if self.site(Kind::Delete) {
                let effect = match (declared(s), s) {
                    (Some(name), _) => Effect::Gone(name.to_owned(), Some(self.index)),
                    (None, Stmt::Connect(..)) if top => Effect::Code(Some("S018")),
                    _ => Effect::Code(None),
                };
                body.remove(i);
                self.hit(format!("delete statement {n} of {}", self.item), effect);
                return;
            }
            if declared(s).is_some() && self.site(Kind::Duplicate) {
                body.insert(i + 1, s.clone());
                let what = format!("duplicate statement {n} of {}", self.item);
                self.hit(what, Effect::Code(Some("S002")));
                return;
            }
            if let Some(s) = body.get_mut(i) {
                self.stmt_parts(s);
            }
            if self.hit.is_some() {
                return;
            }
            i += 1;
        }
    }

    fn stmt_parts(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Input(_, t) | Stmt::Output(_, t) | Stmt::Wire(_, t) => self.ty(t),
            Stmt::Reg(_, t, reset) => {
                self.ty(t);
                self.sexpr(reset);
            }
            Stmt::Let { ty, value, .. } => {
                if let Some(t) = ty {
                    self.ty(t);
                }
                self.hexpr(value);
            }
            Stmt::StaticLet(_, _, v) | Stmt::Assert(v, _) => self.sexpr(v),
            Stmt::Assign(n, v) => {
                self.rename(n);
                self.hexpr(v);
            }
            Stmt::Connect(place, v) => {
                match place {
                    Place::Name(n) | Place::Field(n, _) => self.rename(n),
                }
                self.hexpr(v);
            }
            Stmt::Instance(_, m, args) => {
                self.rename(m);
                self.args(m, args, zero());
                for a in args {
                    self.sexpr(a);
                }
            }
            Stmt::If(c, then, els) => {
                self.sexpr(c);
                self.stmts(then, false);
                if let Some(els) = els {
                    self.stmts(els, false);
                }
            }
            Stmt::For(_, lo, hi, body) => {
                self.sexpr(lo);
                self.sexpr(hi);
                self.stmts(body, false);
            }
            Stmt::Error(_) => {}
            Stmt::Block(body) => self.stmts(body, false),
        }
    }

    fn rename(&mut self, name: &mut String) {
        if self.kind == Kind::Rename && self.target.is_none() {
            self.names.push(name.clone());
        }
        if self.site(Kind::Rename) {
            let old = mem::replace(name, "q0".to_owned());
            let what = format!("rename {old} to q0 in {}", self.item);
            self.hit(what, Effect::Code(Some("S003")));
        }
    }

    /// The arity sites of a call or an instance of `callee`.
    fn args<T>(&mut self, callee: &str, args: &mut Vec<T>, zero: T) {
        if !args.is_empty() && self.site(Kind::DropArg) {
            let what = format!("drop argument {} of {callee} in {}", args.len(), self.item);
            args.pop();
            self.hit(what, Effect::Code(Some("S007")));
        }
        if self.site(Kind::AddArg) {
            args.push(zero);
            let what = format!("add argument {} to {callee} in {}", args.len(), self.item);
            self.hit(what, Effect::Code(Some("S007")));
        }
    }

    fn ty(&mut self, t: &mut Ty) {
        let (Ty::UInt(w) | Ty::SInt(w)) = t else {
            return;
        };
        let new = if self.site(Kind::Widen) {
            let one = SExpr::Int(BigInt::from(1), Radix::Dec);
            SExpr::Binary(SBin::Add, Box::new(w.clone()), Box::new(one))
        } else if *w != zero() && self.site(Kind::ZeroWidth) {
            zero()
        } else {
            self.sexpr(w);
            return;
        };
        let what = format!(
            "change width {} to {} in {}",
            sexpr_text(w),
            sexpr_text(&new),
            self.item
        );
        *w = new;
        self.hit(what, Effect::Code(None));
    }

    fn sexpr(&mut self, e: &mut SExpr) {
        if *e != fault() && self.site(Kind::Fault) {
            let what = format!("change {} to (1 / 0) in {}", sexpr_text(e), self.item);
            *e = fault();
            self.hit(what, Effect::Code(None));
            return;
        }
        match e {
            SExpr::Int(..) | SExpr::Bool(_) => {}
            SExpr::Name(n) => self.rename(n),
            SExpr::Call(f, args) => {
                self.rename(f);
                self.args(f, args, zero());
                for a in args {
                    self.sexpr(a);
                }
            }
            SExpr::Unary(_, a) => self.sexpr(a),
            SExpr::Binary(_, a, b) => {
                self.sexpr(a);
                self.sexpr(b);
            }
            SExpr::If(c, t, f) => {
                self.sexpr(c);
                self.sexpr(t);
                self.sexpr(f);
            }
        }
    }

    fn hexpr(&mut self, e: &mut HExpr) {
        match e {
            HExpr::Name(n) | HExpr::Field(n, _) => self.rename(n),
            HExpr::Static(s) => self.sexpr(s),
            HExpr::Make(t, s) => {
                self.ty(t);
                self.sexpr(s);
            }
            HExpr::Unary(_, a) => self.hexpr(a),
            HExpr::Binary(_, a, b) => {
                self.hexpr(a);
                self.hexpr(b);
            }
            HExpr::If(c, t, f) => {
                self.hexpr(c);
                self.hexpr(t);
                self.hexpr(f);
            }
            HExpr::Resize(t, a) | HExpr::Reinterpret(t, a) => {
                self.ty(t);
                self.hexpr(a);
            }
            HExpr::Call(f, args) => {
                self.rename(f);
                self.args(f, args, HExpr::Static(zero()));
                for a in args {
                    self.hexpr(a);
                }
            }
        }
    }
}

fn item_name(item: &Item) -> &str {
    match item {
        Item::Const { name, .. } | Item::Helper { name, .. } | Item::Module { name, .. } => name,
        Item::ComptimeFn(f) => &f.name,
    }
}

/// The name that a declaration statement declares.
fn declared(s: &Stmt) -> Option<&str> {
    match s {
        Stmt::Input(n, _)
        | Stmt::Output(n, _)
        | Stmt::Reg(n, _, _)
        | Stmt::Wire(n, _)
        | Stmt::Let { name: n, .. }
        | Stmt::StaticLet(n, _, _)
        | Stmt::Instance(n, _, _) => Some(n),
        _ => None,
    }
}

fn zero() -> SExpr {
    SExpr::Int(BigInt::from(0), Radix::Dec)
}

/// `(1 / 0)`.
fn fault() -> SExpr {
    let one = SExpr::Int(BigInt::from(1), Radix::Dec);
    SExpr::Binary(SBin::Div, Box::new(one), Box::new(zero()))
}

#[cfg(test)]
mod tests {
    use super::super::build::typed;
    use super::super::eval::Value;
    use super::super::program::tests::{TEXT, program};
    use super::super::program::{
        HExpr, Item, Place, Ports, Program, Radix, SExpr, StaticTy, Stmt, Ty,
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
            name: "h0".to_owned(),
            params: vec![("x0".to_owned(), u8())],
            ret: u8(),
            body: vec![],
            result: name("x0"),
        };
        let c0 = Item::Const {
            name: "C0".to_owned(),
            ty: StaticTy::Nat,
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
                    let lexed = crate::lex(&m.text, 4096);
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

    #[test]
    fn mutation_is_deterministic() {
        let p = program();
        for kind in 0..8 {
            assert_eq!(mutate(&p, kind, 11), mutate(&p, kind, 11));
        }
    }
}
