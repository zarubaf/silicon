// SPDX-License-Identifier: Apache-2.0
//! The twin of a typed program (front-end spec 11.4): the same program with
//! each comptime construct written out. The oracle runs both programs on
//! the same source vectors and expects the same outputs.
//!
//! The twin walks from the top instantiation with the static env of each
//! frame. Its modules have no parameters and its expressions no static
//! names, so no static computation is left for a front end:
//!
//! - Each reached instantiation becomes a module without parameters, named
//!   after its module and the argument tokens of front-end design 7.1 with
//!   `_` for `$`. A generated name has no `_`, so no twin name collides.
//! - Each static expression folds to a decimal literal.
//! - A `comptime if` becomes a block of its selected branch, and a
//!   `comptime for` one block per iteration.
//! - A name that a loop body declares gets the suffix `_<binder>_<token>`
//!   per iteration, so the twin never depends on how elaboration treats a
//!   declaration that sibling blocks repeat in one frame (spec 7.3).
//! - `const`s, `comptime fn`s, static `let`s, and `static_assert`s go.
//!
//! A static fault is a builder bug. The twin then keeps the construct as it
//! is, with its static names (`build::STATIC_PREFIXES` and digits).
//! `Twin::static_names` finds them: the tests and `diff-si` check each twin
//! with it, so they show the bug.

use super::build::STATIC_PREFIXES;
use super::eval::{Env, Scope, Value, eval, exec_static, leaf_bits, loop_values};
use super::program::{
    EnumDef, HBin, HExpr, Item, Match, Pattern, Place, Program, Radix, SExpr, STy, Scalar, Stmt,
    Ty, render_items,
};
use num_bigint::{BigInt, BigUint, Sign};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// The source text of a twin and its top selection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Twin {
    pub text: String,
    pub top: String,
}

impl Twin {
    /// The static names left in the text: identifiers of a static prefix
    /// of the builder and digits (a parameter, const, `comptime fn`,
    /// static `let`, or loop binder). A static fault of the twin leaves
    /// them, so a twin of a built program has none. `x` is also a helper
    /// formal, so it is no static prefix.
    #[must_use]
    pub fn static_names(&self) -> Vec<String> {
        syntax::lex(&self.text, usize::MAX)
            .tokens
            .iter()
            .filter(|t| t.kind == syntax::SyntaxKind::Ident)
            .filter_map(|t| self.text.get(t.range.clone()))
            .filter(|n| {
                let mut cs = n.chars();
                cs.next().is_some_and(|c| STATIC_PREFIXES.contains(c))
                    && !cs.as_str().is_empty()
                    && cs.all(|c| c.is_ascii_digit())
            })
            .map(str::to_owned)
            .collect()
    }
}

/// The twin of `program`.
#[must_use]
pub fn twin(program: &Program) -> Twin {
    let mut w = Writer {
        items: &program.items,
        // A const that faults leaves an empty scope. Each fold that reads a
        // const or a `comptime fn` then fails, and its static name stays in
        // the twin, where the tests find it; `twin` returns no error.
        scope: Scope::new(&program.items).unwrap_or_default(),
        named: BTreeSet::new(),
        queue: VecDeque::new(),
        hw_values: program
            .items
            .iter()
            .filter_map(|item| match item {
                Item::HwFnValue { name, target, .. } => Some((name.clone(), target.clone())),
                _ => None,
            })
            .collect(),
        enums: program
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Enum(def) => Some((def.name.clone(), def.clone())),
                _ => None,
            })
            .collect(),
    };
    let Some(top) = w.specialize(&program.top, &program.args) else {
        // A container argument is a fault of the builder; the static names
        // of the program stay, where the tests find them.
        return Twin {
            text: program.text(),
            top: program.top(),
        };
    };
    let helpers: Vec<Item> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Helper {
                name,
                params,
                mut_first,
                ret,
                body,
                result,
            } => {
                let mut f = Frame::default();
                Some(Item::Helper {
                    name: name.clone(),
                    params: params
                        .iter()
                        .map(|(n, t)| (n.clone(), w.ty(t, &f)))
                        .collect(),
                    mut_first: *mut_first,
                    ret: w.ty(ret, &f),
                    body: w.stmts(body, &mut f),
                    result: w.hexpr(result, &f),
                })
            }
            _ => None,
        })
        .collect();
    let mut modules = Vec::new();
    while let Some((name, module, args)) = w.queue.pop_front() {
        modules.push(w.module(name, &module, &args));
    }
    let enums = program
        .items
        .iter()
        .filter(|item| matches!(item, Item::Enum(_)))
        .cloned();
    let items: Vec<Item> = enums.chain(helpers).chain(modules).collect();
    Twin {
        text: render_items(&items),
        top: format!("{top}()"),
    }
}

/// The suffix of a twin module name for a static argument: decimal, `5n` for
/// `-5`, `1b` or `0b`, and the item name of a function. It is the name of
/// the twin only; the emitted name of an instantiation is in `emitted.rs`.
/// A container argument has no suffix, and the builder never makes one.
fn token(v: &Value) -> Option<String> {
    match v {
        Value::Int(n) | Value::UInt(_, n) | Value::SInt(_, n) if n.sign() == Sign::Minus => {
            Some(format!("{}n", n.magnitude()))
        }
        Value::Int(n) | Value::UInt(_, n) | Value::SInt(_, n) => Some(n.to_string()),
        Value::Bool(true) => Some("1b".to_owned()),
        Value::Bool(false) => Some("0b".to_owned()),
        Value::Function(item, _) => Some(item.clone()),
        Value::Tuple(_)
        | Value::Array(_)
        | Value::Str(_)
        | Value::List(..)
        | Value::Record(..)
        | Value::Enum(..) => None,
    }
}

/// A static value as a literal, if it has one: a finite integer has none,
/// so a record of hardware data has none.
fn literal(v: Value) -> Option<SExpr> {
    let bits = v.bits();
    let all = |xs: Vec<Value>| xs.into_iter().map(literal).collect::<Option<Vec<_>>>();
    Some(match v {
        Value::Int(n) => SExpr::Int(n, Radix::Dec),
        Value::Bool(b) => SExpr::Bool(b),
        Value::Tuple(xs) => SExpr::Tuple(all(xs)?),
        Value::Array(xs) => SExpr::Array(all(xs)?),
        Value::UInt(..) | Value::SInt(..) | Value::List(..) => return None,
        Value::Str(s) => SExpr::Str(s),
        Value::Function(item, _) => SExpr::Name(item),
        Value::Record(rt, xs) => {
            let targs = all(rt.args.clone())?;
            SExpr::Record(rt.name.clone(), targs, all(xs)?)
        }
        Value::Enum(def, ..) => {
            let bits = SExpr::Int(BigInt::from(bits), Radix::Dec);
            let finite = SExpr::Convert(STy::UInt(def.data_bits()), Box::new(bits));
            SExpr::Unpack(def.name.clone(), Box::new(finite))
        }
    })
}

/// The scope of a frame: its static env, the twin name of each hardware
/// name that it declares, and the suffix of its declarations.
#[derive(Clone, Default)]
struct Frame {
    env: Env,
    names: BTreeMap<String, String>,
    suffix: String,
}

impl Frame {
    fn declare(&mut self, name: &str) -> String {
        let twin = format!("{name}{}", self.suffix);
        self.names.insert(name.to_owned(), twin.clone());
        twin
    }

    fn name(&self, name: &str) -> String {
        self.names
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    }
}

struct Writer<'a> {
    items: &'a [Item],
    scope: Scope,
    /// The specialized module names so far.
    named: BTreeSet<String>,
    /// The specializations to write: name, module, and arguments.
    queue: VecDeque<(String, String, Vec<Value>)>,
    /// The helper that each function value of a helper holds.
    hw_values: BTreeMap<String, String>,
    /// The enums of the program.
    enums: BTreeMap<String, EnumDef>,
}

impl Writer<'_> {
    /// The name of module `module` at `args`; a new one joins the queue.
    fn specialize(&mut self, module: &str, args: &[Value]) -> Option<String> {
        let tokens = args.iter().map(token).collect::<Option<Vec<_>>>()?;
        let name: String = std::iter::once(module.to_owned())
            .chain(tokens)
            .collect::<Vec<_>>()
            .join("_");
        if self.named.insert(name.clone()) {
            self.queue
                .push_back((name.clone(), module.to_owned(), args.to_vec()));
        }
        Some(name)
    }

    /// The specialized module `name`: module `module` at `args`.
    fn module(&mut self, name: String, module: &str, args: &[Value]) -> Item {
        let found = self.items.iter().find_map(|item| match item {
            Item::Module {
                name: n,
                params,
                clocked,
                body,
            } if n == module => Some((params, *clocked, body)),
            _ => None,
        });
        let Some((params, clocked, body)) = found else {
            return Item::Module {
                name,
                params: Vec::new(),
                clocked: false,
                body: vec![Stmt::Error(format!("no module {module}"))],
            };
        };
        let mut fr = Frame {
            env: Env::of(params, args),
            ..Frame::default()
        };
        Item::Module {
            name,
            params: Vec::new(),
            clocked,
            body: self.stmts(body, &mut fr),
        }
    }

    fn value(&self, e: &SExpr, fr: &Frame) -> Option<Value> {
        eval(e, &fr.env, &self.scope).ok()
    }

    fn fold(&self, e: &SExpr, fr: &Frame) -> SExpr {
        self.value(e, fr)
            .and_then(literal)
            .unwrap_or_else(|| e.clone())
    }

    fn ty(&self, t: &Ty, fr: &Frame) -> Ty {
        match t {
            Ty::Bool => Ty::Bool,
            Ty::UInt(w) => Ty::UInt(self.fold(w, fr)),
            Ty::SInt(w) => Ty::SInt(self.fold(w, fr)),
            Ty::Enum(name) => Ty::Enum(name.clone()),
        }
    }

    /// A hardware `match` as a chain of `if` expressions. The twin has no
    /// `match`, so the run oracle tests the lowering of `match` against
    /// the lowering of `if`, compares, `resize`, and shifts. An enum
    /// scrutinee compares `resize(UInt[W], reinterpret(UInt[D], s))` with
    /// the tag. A binder is the `resize` of the shifted bits, and a signed
    /// binder is the `reinterpret` of that `resize` (ADR 0025).
    fn chain(&self, m: &Match<HExpr, HExpr>, fr: &Frame) -> HExpr {
        let scrutinee = self.hexpr(&m.scrutinee, fr);
        let mut arms: Vec<(Option<HExpr>, HExpr)> = Vec::new();
        for (pattern, arm) in &m.arms {
            let arm = self.hexpr(arm, fr);
            arms.push(self.arm_test(pattern, &scrutinee, arm));
        }
        // The last arm needs no test: `_`, or the arm that completes the
        // match.
        let Some((_, last)) = arms.pop() else {
            panic!("a match of the builder has no arm");
        };
        arms.into_iter().rev().fold(last, |rest, (test, arm)| {
            let Some(test) = test else {
                panic!("a match of the builder has a `_` before its last arm");
            };
            HExpr::If(Box::new(test), Box::new(arm), Box::new(rest))
        })
    }

    /// `E::V(a, b)` as `reinterpret(E, bits)`: the tag, and each payload
    /// value shifted to its offset (ADR 0025). The twin thus packs the
    /// payload on its own, not through the constructor of the front end.
    fn constructor(&self, e: &str, v: &str, args: &[HExpr], fr: &Frame) -> HExpr {
        let Some(variant) = self.enums.get(e).and_then(|def| def.variant(v)) else {
            panic!("a constructor of the builder names no variant: {e}::{v}");
        };
        let def = &self.enums[e];
        let d = def.data_bits();
        let uint = |w: u32| Ty::UInt(SExpr::Int(BigInt::from(w), Radix::Dec));
        let constant = |n: BigUint| HExpr::Make(uint(d), SExpr::Int(BigInt::from(n), Radix::Dec));
        let mut fixed = variant.tag.clone();
        let mut parts = Vec::new();
        for (arg, (at, t)) in args.iter().zip(variant.leaves()) {
            let off = def.tag_width + at;
            if let HExpr::Static(s) = arg {
                let Some(value) = self.value(s, fr) else {
                    panic!("a static payload of the builder faults");
                };
                let Ok(bits) = leaf_bits(t, value) else {
                    panic!("a static payload of the builder does not fit");
                };
                fixed |= bits << off;
                continue;
            }
            let arg = self.hexpr(arg, fr);
            let shift = |x: HExpr| {
                let k = HExpr::Static(SExpr::Int(BigInt::from(off), Radix::Dec));
                HExpr::Binary(HBin::Shl, Box::new(x), Box::new(k))
            };
            parts.push(match t {
                Scalar::Bool => {
                    let (one, zero) = (constant(BigUint::from(1u8)), constant(BigUint::ZERO));
                    shift(HExpr::If(Box::new(arg), Box::new(one), Box::new(zero)))
                }
                Scalar::UInt(_) => shift(HExpr::Resize(uint(d), Box::new(arg))),
                Scalar::SInt(w) => {
                    let bits = HExpr::Reinterpret(uint(w), Box::new(arg));
                    shift(HExpr::Resize(uint(d), Box::new(bits)))
                }
            });
        }
        let bits = parts.into_iter().fold(constant(fixed), |acc, p| {
            HExpr::Binary(HBin::Or, Box::new(acc), Box::new(p))
        });
        HExpr::Reinterpret(Ty::Enum(e.to_owned()), Box::new(bits))
    }

    /// The test of an arm, and its value with the binders replaced.
    fn arm_test(&self, pattern: &Pattern, s: &HExpr, arm: HExpr) -> (Option<HExpr>, HExpr) {
        let eq =
            |a: HExpr, b: SExpr| HExpr::Binary(HBin::Eq, Box::new(a), Box::new(HExpr::Static(b)));
        match pattern {
            Pattern::Wild => (None, arm),
            Pattern::Bool(b) => (Some(eq(s.clone(), SExpr::Bool(*b))), arm),
            Pattern::Int(n, _) => (Some(eq(s.clone(), SExpr::Int(n.clone(), Radix::Dec))), arm),
            Pattern::Variant(e, v, binders) => {
                let Some(variant) = self.enums.get(e).and_then(|def| def.variant(v)) else {
                    panic!("a pattern of the builder names no variant: {e}::{v}");
                };
                let def = &self.enums[e];
                let uint = |w: u32| Ty::UInt(SExpr::Int(BigInt::from(w), Radix::Dec));
                let bits = HExpr::Reinterpret(uint(def.data_bits()), Box::new(s.clone()));
                let tag = HExpr::Resize(uint(def.tag_width), Box::new(bits.clone()));
                let test = eq(
                    tag,
                    SExpr::Int(BigInt::from(variant.tag.clone()), Radix::Dec),
                );
                let mut map = BTreeMap::new();
                for (b, (at, t)) in binders.iter().zip(variant.leaves()) {
                    if let Some(b) = b {
                        let off = def.tag_width + at;
                        map.insert(b.clone(), leaf(&bits, off, t));
                    }
                }
                (Some(test), subst(&arm, &map))
            }
        }
    }

    fn hexpr(&self, e: &HExpr, fr: &Frame) -> HExpr {
        let sub = |a: &HExpr| Box::new(self.hexpr(a, fr));
        match e {
            HExpr::Name(n) => HExpr::Name(fr.name(n)),
            HExpr::Field(u, q) => HExpr::Field(fr.name(u), q.clone()),
            HExpr::Static(s) => HExpr::Static(self.fold(s, fr)),
            HExpr::Make(t, s) => HExpr::Make(self.ty(t, fr), self.fold(s, fr)),
            HExpr::Unary(op, a) => HExpr::Unary(*op, sub(a)),
            HExpr::Binary(op, a, b) => HExpr::Binary(*op, sub(a), sub(b)),
            HExpr::If(c, a, b) => HExpr::If(sub(c), sub(a), sub(b)),
            HExpr::Resize(t, a) => HExpr::Resize(self.ty(t, fr), sub(a)),
            HExpr::Reinterpret(t, a) => HExpr::Reinterpret(self.ty(t, fr), sub(a)),
            HExpr::Call(g, args) => {
                // A call through a function value is a call of its helper.
                let g = self.hw_values.get(g).unwrap_or(g);
                HExpr::Call(g.clone(), args.iter().map(|a| self.hexpr(a, fr)).collect())
            }
            HExpr::Match(m) => self.chain(m, fr),
            HExpr::Ctor(e, v, args) => self.constructor(e, v, args, fr),
            HExpr::Receiver(recv, g, args) => HExpr::Receiver(
                sub(recv),
                g.clone(),
                args.iter().map(|a| self.hexpr(a, fr)).collect(),
            ),
        }
    }

    fn stmts(&mut self, body: &[Stmt], fr: &mut Frame) -> Vec<Stmt> {
        let mut out = Vec::new();
        for s in body {
            self.stmt(s, fr, &mut out);
        }
        out
    }

    /// The block of `body` in a nested frame of `fr` with `suffix`.
    fn block(&mut self, body: &[Stmt], fr: &Frame, env: Env, suffix: String) -> Stmt {
        let mut inner = Frame {
            env,
            names: fr.names.clone(),
            suffix,
        };
        Stmt::Block(self.stmts(body, &mut inner))
    }

    fn stmt(&mut self, s: &Stmt, fr: &mut Frame, out: &mut Vec<Stmt>) {
        match s {
            Stmt::Input(n, t) => out.push(Stmt::Input(n.clone(), self.ty(t, fr))),
            Stmt::Output(n, t) => out.push(Stmt::Output(n.clone(), self.ty(t, fr))),
            Stmt::Reg(n, t, reset) => {
                let (t, reset) = (self.ty(t, fr), self.fold(reset, fr));
                out.push(Stmt::Reg(fr.declare(n), t, reset));
            }
            Stmt::Wire(n, t) => {
                let t = self.ty(t, fr);
                out.push(Stmt::Wire(fr.declare(n), t));
            }
            Stmt::Let {
                name,
                mutable,
                ty,
                value,
            } => {
                let ty = ty.as_ref().map(|t| self.ty(t, fr));
                let value = self.hexpr(value, fr);
                out.push(Stmt::Let {
                    name: fr.declare(name),
                    mutable: *mutable,
                    ty,
                    value,
                });
            }
            Stmt::StaticLet(..)
            | Stmt::MutLet(..)
            | Stmt::Push(..)
            | Stmt::PopLet(..)
            | Stmt::MutCall { .. } => {
                if exec_static(s, &mut fr.env, &self.scope).is_err() {
                    out.push(s.clone());
                }
            }
            Stmt::Assign(n, v) => out.push(Stmt::Assign(fr.name(n), self.hexpr(v, fr))),
            Stmt::Connect(place, v) => {
                let place = match place {
                    Place::Name(n) => Place::Name(fr.name(n)),
                    Place::Field(u, p) => Place::Field(fr.name(u), p.clone()),
                };
                out.push(Stmt::Connect(place, self.hexpr(v, fr)));
            }
            Stmt::Instance(u, m, args) => {
                let Some(values) = args
                    .iter()
                    .map(|a| self.value(a, fr))
                    .collect::<Option<Vec<_>>>()
                else {
                    out.push(s.clone());
                    return;
                };
                let Some(child) = self.specialize(m, &values) else {
                    out.push(s.clone());
                    return;
                };
                out.push(Stmt::Instance(fr.declare(u), child, Vec::new()));
            }
            Stmt::If(c, then, els) => match self.value(c, fr) {
                Some(Value::Bool(true)) => {
                    out.push(self.block(then, fr, fr.env.clone(), fr.suffix.clone()));
                }
                Some(Value::Bool(false)) => {
                    if let Some(els) = els {
                        out.push(self.block(els, fr, fr.env.clone(), fr.suffix.clone()));
                    }
                }
                _ => out.push(s.clone()),
            },
            Stmt::For(binder, lo, hi, body) => {
                let (Some(Value::Int(lo)), Some(Value::Int(hi))) =
                    (self.value(lo, fr), self.value(hi, fr))
                else {
                    out.push(s.clone());
                    return;
                };
                for value in loop_values(&lo, &hi) {
                    let suffix = format!(
                        "_{binder}_{}{}",
                        token(&value).unwrap_or_default(),
                        fr.suffix
                    );
                    let mut env = fr.env.clone();
                    env.statics.insert(binder.clone(), value);
                    out.push(self.block(body, fr, env, suffix));
                }
            }
            Stmt::Assert(c, _) => {
                if self.value(c, fr) != Some(Value::Bool(true)) {
                    out.push(s.clone());
                }
            }
            Stmt::Error(_) => out.push(s.clone()),
            // The twin compares outputs only; a record is no output.
            Stmt::Diagnostic(..) => {}
            Stmt::Block(body) => out.push(self.block(body, fr, fr.env.clone(), fr.suffix.clone())),
        }
    }
}

/// The payload leaf of type `t` at the bit `off` of `bits`.
fn leaf(bits: &HExpr, off: u32, t: Scalar) -> HExpr {
    let uint = |w: u32| Ty::UInt(SExpr::Int(BigInt::from(w), Radix::Dec));
    let shifted = if off == 0 {
        bits.clone()
    } else {
        let k = HExpr::Static(SExpr::Int(BigInt::from(off), Radix::Dec));
        HExpr::Binary(HBin::Shr, Box::new(bits.clone()), Box::new(k))
    };
    match t {
        Scalar::Bool => {
            let low = HExpr::Resize(uint(1), Box::new(shifted));
            let zero = HExpr::Static(SExpr::Int(BigInt::ZERO, Radix::Dec));
            HExpr::Binary(HBin::Ne, Box::new(low), Box::new(zero))
        }
        Scalar::UInt(w) => HExpr::Resize(uint(w), Box::new(shifted)),
        Scalar::SInt(w) => {
            let low = HExpr::Resize(uint(w), Box::new(shifted));
            let signed = Ty::SInt(SExpr::Int(BigInt::from(w), Radix::Dec));
            HExpr::Reinterpret(signed, Box::new(low))
        }
    }
}

/// `e` with each name of `map` replaced by its expression.
fn subst(e: &HExpr, map: &BTreeMap<String, HExpr>) -> HExpr {
    let sub = |a: &HExpr| Box::new(subst(a, map));
    let all = |xs: &[HExpr]| xs.iter().map(|a| subst(a, map)).collect::<Vec<_>>();
    match e {
        HExpr::Name(n) => map.get(n).cloned().unwrap_or_else(|| e.clone()),
        HExpr::Field(..) | HExpr::Static(_) | HExpr::Make(..) => e.clone(),
        HExpr::Unary(op, a) => HExpr::Unary(*op, sub(a)),
        HExpr::Binary(op, a, b) => HExpr::Binary(*op, sub(a), sub(b)),
        HExpr::If(c, a, b) => HExpr::If(sub(c), sub(a), sub(b)),
        HExpr::Resize(t, a) => HExpr::Resize(t.clone(), sub(a)),
        HExpr::Reinterpret(t, a) => HExpr::Reinterpret(t.clone(), sub(a)),
        HExpr::Call(f, args) => HExpr::Call(f.clone(), all(args)),
        HExpr::Receiver(r, f, args) => HExpr::Receiver(sub(r), f.clone(), all(args)),
        HExpr::Ctor(en, v, args) => HExpr::Ctor(en.clone(), v.clone(), all(args)),
        HExpr::Match(m) => HExpr::Match(Match {
            scrutinee: sub(&m.scrutinee),
            arms: m
                .arms
                .iter()
                .map(|(p, a)| (p.clone(), subst(a, map)))
                .collect(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::super::build::typed;
    use super::super::eval::Value;
    use super::super::program::{
        ComptimeFn, HBin, HExpr, Item, Place, Ports, Radix, SBin, SExpr, STy, Stmt, Ty,
    };
    use super::*;
    use num_bigint::BigInt;
    use proptest::prelude::*;

    fn int(n: i64) -> SExpr {
        SExpr::Int(BigInt::from(n), Radix::Dec)
    }

    fn sname(n: &str) -> SExpr {
        SExpr::Name(n.to_owned())
    }

    fn hname(n: &str) -> HExpr {
        HExpr::Name(n.to_owned())
    }

    fn hbin(op: HBin, a: HExpr, b: HExpr) -> HExpr {
        HExpr::Binary(op, Box::new(a), Box::new(b))
    }

    fn sbin(op: SBin, a: SExpr, b: SExpr) -> SExpr {
        SExpr::Binary(op, Box::new(a), Box::new(b))
    }

    fn uint(w: i64) -> Ty {
        Ty::UInt(int(w))
    }

    fn connect(n: &str, v: HExpr) -> Stmt {
        Stmt::Connect(Place::Name(n.to_owned()), v)
    }

    fn mutable(n: &str, v: HExpr) -> Stmt {
        Stmt::Let {
            name: n.to_owned(),
            mutable: true,
            ty: None,
            value: v,
        }
    }

    fn module(name: &str, params: &[(&str, STy)], clocked: bool, body: Vec<Stmt>) -> Item {
        Item::Module {
            name: name.to_owned(),
            params: params
                .iter()
                .map(|(n, t)| ((*n).to_owned(), t.clone()))
                .collect(),
            clocked,
            body,
        }
    }

    /// A program of `items` with top `M0` at `args`; the twin reads
    /// neither the ports nor the probe.
    fn program(items: Vec<Item>, args: Vec<Value>) -> Program {
        Program {
            items,
            top: "M0".to_owned(),
            args,
            ports: Ports {
                clocked: false,
                inputs: Vec::new(),
                outputs: Vec::new(),
            },
            probe: (int(0), Value::Int(BigInt::ZERO)),
            records: Vec::new(),
        }
    }

    #[test]
    fn the_twin_unrolls_loops_and_selects_branches() {
        let body = vec![
            Stmt::Input("i0".to_owned(), uint(8)),
            Stmt::Output("o0".to_owned(), uint(8)),
            mutable("v0", hname("i0")),
            Stmt::For(
                "j0".to_owned(),
                int(0),
                sname("P0"),
                vec![Stmt::Assign(
                    "v0".to_owned(),
                    hbin(
                        HBin::Addw,
                        hname("v0"),
                        hbin(HBin::Shl, hname("i0"), HExpr::Static(sname("j0"))),
                    ),
                )],
            ),
            Stmt::If(
                sname("P1"),
                vec![Stmt::Assign(
                    "v0".to_owned(),
                    hbin(HBin::Addw, hname("v0"), HExpr::Static(int(1))),
                )],
                Some(vec![Stmt::Assign("v0".to_owned(), hname("v0"))]),
            ),
            connect("o0", hname("v0")),
        ];
        let m0 = module("M0", &[("P0", STy::Nat), ("P1", STy::Bool)], false, body);
        let p = program(
            vec![m0],
            vec![Value::Int(BigInt::from(2)), Value::Bool(true)],
        );
        let t = twin(&p);
        assert_eq!(t.top, "M0_2_1b()");
        assert_eq!(
            t.text,
            "module M0_2_1b() domains() {\n    input i0: UInt[8];\n    output o0: UInt[8];\n    let mut v0 = i0;\n    {\n        v0 = (v0 +% (i0 << 0));\n    }\n    {\n        v0 = (v0 +% (i0 << 1));\n    }\n    {\n        v0 = (v0 +% 1);\n    }\n    o0 := v0;\n}\n"
        );
    }

    /// `M1()`: a combinational child with a `UInt[4]` input and output.
    fn m1() -> Item {
        module(
            "M1",
            &[],
            false,
            vec![
                Stmt::Input("i0".to_owned(), uint(4)),
                Stmt::Output("o0".to_owned(), uint(4)),
                connect("o0", hname("i0")),
            ],
        )
    }

    #[test]
    fn the_twin_renames_what_a_loop_declares() {
        let field = HExpr::Field("u0".to_owned(), "o0".to_owned());
        let looped = vec![
            Stmt::Reg("r0".to_owned(), uint(4), int(0)),
            Stmt::Instance("u0".to_owned(), "M1".to_owned(), Vec::new()),
            Stmt::Connect(Place::Field("u0".to_owned(), "i0".to_owned()), hname("i0")),
            connect("r0", hbin(HBin::Addw, hname("r0"), field)),
            Stmt::Assign("v0".to_owned(), hbin(HBin::Xor, hname("v0"), hname("r0"))),
        ];
        let body = vec![
            Stmt::Input("i0".to_owned(), uint(4)),
            Stmt::Output("o0".to_owned(), uint(4)),
            mutable("v0", hname("i0")),
            Stmt::For("j0".to_owned(), int(-1), int(1), looped),
            connect("o0", hname("v0")),
        ];
        let p = program(vec![module("M0", &[], true, body), m1()], Vec::new());
        let t = twin(&p);
        assert_eq!(t.top, "M0()");
        let first = [
            "        reg r0_j0_1n: UInt[4] = 0;",
            "        instance u0_j0_1n = M1();",
            "        u0_j0_1n.i0 := i0;",
            "        r0_j0_1n := (r0_j0_1n +% u0_j0_1n.o0);",
            "        v0 = (v0 ^ r0_j0_1n);",
        ];
        let second = first.map(|l| l.replace("_j0_1n", "_j0_0"));
        let lines: Vec<&str> = t.text.lines().collect();
        let at = |l: &str| lines.iter().position(|x| *x == l);
        for (a, b) in first.iter().zip(&second) {
            assert!(at(a) < at(b) && at(a).is_some(), "{a} / {b} in\n{}", t.text);
        }
        assert!(t.text.contains("    let mut v0 = i0;\n"));
        assert!(t.text.contains("    o0 := v0;\n"));
        assert_eq!(t.text.matches("module M1() domains() {").count(), 1);
    }

    /// `f0` of the evaluator tests: `f0(x0, x1)` is `x1` at `x0 == 0`, else
    /// `f0(x0 - 1, x1 * 2) + 1`, so `f0(3, 1)` is 11.
    fn f0() -> Item {
        let step = sbin(
            SBin::Add,
            SExpr::Call(
                "f0".to_owned(),
                vec![
                    sbin(SBin::Sub, sname("x0"), int(1)),
                    sbin(SBin::Mul, sname("x1"), int(2)),
                ],
            ),
            int(1),
        );
        Item::ComptimeFn(ComptimeFn {
            name: "f0".to_owned(),
            params: vec![("x0".to_owned(), STy::Nat), ("x1".to_owned(), STy::Int)],
            ret: STy::Int,
            base: sname("x1"),
            step,
        })
    }

    #[test]
    fn the_twin_specializes_each_instantiation() {
        let m1 = module(
            "M1",
            &[("P0", STy::Nat)],
            false,
            vec![
                Stmt::Input("i0".to_owned(), Ty::UInt(sname("P0"))),
                Stmt::Output("o0".to_owned(), Ty::UInt(sname("P0"))),
                Stmt::Assert(sbin(SBin::Gt, sname("P0"), int(0)), "positive".to_owned()),
                connect("o0", hname("i0")),
            ],
        );
        let call = SExpr::Call("f0".to_owned(), vec![int(3), int(1)]);
        let instance =
            |u: &str, arg: SExpr| Stmt::Instance(u.to_owned(), "M1".to_owned(), vec![arg]);
        let m0 = module(
            "M0",
            &[],
            false,
            vec![
                Stmt::Output("o0".to_owned(), Ty::Bool),
                instance("u0", sbin(SBin::Sub, call, int(8))),
                instance("u1", int(4)),
                instance("u2", int(3)),
                connect("o0", HExpr::Static(SExpr::Bool(true))),
            ],
        );
        let consts = Item::Const {
            name: "C0".to_owned(),
            ty: STy::Nat,
            value: int(4),
        };
        let p = program(vec![consts, f0(), m0, m1], Vec::new());
        let t = twin(&p);
        assert_eq!(t.top, "M0()");
        assert_eq!(t.text.matches("module M1_3() domains() {").count(), 1);
        assert_eq!(t.text.matches("module M1_4() domains() {").count(), 1);
        let m1_3 = t.text.split("module M1_3()").nth(1).unwrap_or_default();
        let m1_3 = m1_3.split("\n}\n").next().unwrap_or_default();
        assert!(m1_3.contains("input i0: UInt[3];"), "{}", t.text);
        for l in [
            "instance u0 = M1_3();",
            "instance u1 = M1_4();",
            "instance u2 = M1_3();",
        ] {
            assert!(t.text.contains(l), "{l} in\n{}", t.text);
        }
        for word in ["comptime", "static_assert", "f0", "const"] {
            assert!(!t.text.contains(word), "{word} in\n{}", t.text);
        }
    }

    #[test]
    fn the_twin_calls_the_item_of_a_function_value() {
        use super::super::program::FnTy;
        let helper = Item::Helper {
            name: "h0".to_owned(),
            params: vec![("x0".to_owned(), uint(8))],
            mut_first: false,
            ret: uint(8),
            body: vec![],
            result: hname("x0"),
        };
        let value = Item::HwFnValue {
            name: "F0".to_owned(),
            target: "h0".to_owned(),
            params: vec![uint(8)],
            ret: uint(8),
        };
        // `module M1(comptime P0: fn (Nat) -> Nat)` reads the value `P0`.
        let fn_ty = STy::Fn(Box::new(FnTy {
            params: vec![(false, STy::Nat)],
            ret: STy::Nat,
        }));
        let f0 = Item::ComptimeFn(ComptimeFn {
            name: "f0".to_owned(),
            params: vec![("x0".to_owned(), STy::Nat)],
            ret: STy::Nat,
            base: int(2),
            step: sname("x0"),
        });
        let m1 = module(
            "M1",
            &[("P0", fn_ty)],
            false,
            vec![
                Stmt::Input(
                    "i0".to_owned(),
                    Ty::UInt(SExpr::Call("P0".to_owned(), vec![int(0)])),
                ),
                Stmt::Output("o0".to_owned(), uint(8)),
                connect("o0", HExpr::Call("F0".to_owned(), vec![hname("i0")])),
            ],
        );
        let m0 = module(
            "M0",
            &[],
            false,
            vec![
                Stmt::Output("o0".to_owned(), uint(8)),
                Stmt::Input("i0".to_owned(), uint(2)),
                Stmt::Instance("u0".to_owned(), "M1".to_owned(), vec![sname("f0")]),
                Stmt::Connect(Place::Field("u0".to_owned(), "i0".to_owned()), hname("i0")),
                connect("o0", HExpr::Field("u0".to_owned(), "o0".to_owned())),
            ],
        );
        let t = twin(&program(vec![f0, helper, value, m0, m1], Vec::new()));
        assert_eq!(
            t.text,
            "fn h0(x0: UInt[8]) -> UInt[8] {\n    return x0;\n}\nmodule M0() domains() {\n    output o0: UInt[8];\n    input i0: UInt[2];\n    instance u0 = M1_f0();\n    u0.i0 := i0;\n    o0 := u0.o0;\n}\nmodule M1_f0() domains() {\n    input i0: UInt[2];\n    output o0: UInt[8];\n    o0 := h0(i0);\n}\n"
        );
        assert!(t.static_names().is_empty(), "{:?}", t.static_names());
    }

    #[test]
    fn a_static_fault_leaves_a_static_name() {
        let fault = sbin(SBin::Div, int(1), int(0));
        let body = vec![
            Stmt::Output("o0".to_owned(), uint(4)),
            Stmt::StaticLet("s0".to_owned(), STy::Int, fault),
            connect("o0", HExpr::Static(sname("s0"))),
        ];
        let p = program(vec![module("M0", &[], false, body)], Vec::new());
        assert_eq!(twin(&p).static_names(), vec!["s0", "s0"]);
        let clean = program(vec![m1()], Vec::new());
        let clean = Program {
            top: "M1".to_owned(),
            ..clean
        };
        assert!(twin(&clean).static_names().is_empty());
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn twins_have_no_comptime_constructs(p in typed()) {
            let p = p.map_err(|e| TestCaseError::fail(e.to_string()))?;
            let t = twin(&p);
            for word in ["comptime", "const ", "static_assert", "error(", "match"] {
                prop_assert!(!t.text.contains(word), "{} in\n{}", word, t.text);
            }
            let lexed = syntax::lex(&t.text, 4096);
            prop_assert!(lexed.errors.is_empty(), "{:?}", lexed.errors);
            prop_assert!(t.top.ends_with("()"), "{}", t.top);
            let names = t.static_names();
            prop_assert!(names.is_empty(), "{:?} in\n{}", names, t.text);
        }
    }
}
