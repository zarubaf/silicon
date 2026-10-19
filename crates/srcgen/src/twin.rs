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
//! - A helper that takes or declares resources (its name starts with `H`)
//!   goes too. Each call of it becomes its body, with new names for its
//!   declarations, a typed `let` for each data actual, and the resource
//!   that a handle actual names in the place of the handle formal.
//!
//! A static fault is a builder bug. The twin then keeps the construct as it
//! is, with its static names (`build::STATIC_PREFIXES` and digits).
//! `Twin::static_names` finds them: the tests and `diff-si` check each twin
//! with it, so they show the bug.

use super::build::STATIC_PREFIXES;
use super::eval::{Env, Scope, Value, eval, exec_static, leaf_bits, loop_values};
use super::program::{
    EnumDef, FTy, HBin, HExpr, Item, Match, Pattern, Place, Program, Radix, SExpr, STy, Scalar,
    Stmt, Ty, helper_of, is_resource_helper, render_items,
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
    let (items, top) = twin_items(program);
    Twin {
        text: render_items(&items),
        top,
    }
}

/// The items of the twin of `program` and its top selection.
pub(crate) fn twin_items(program: &Program) -> (Vec<Item>, String) {
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
        calls: 0,
        lists: BTreeMap::new(),
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
        return (program.items.clone(), program.top());
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
            } if !is_resource_helper(name) => {
                let mut f = Frame::default();
                Some(Item::Helper {
                    name: name.clone(),
                    params: params
                        .iter()
                        .map(|(n, t)| (n.clone(), w.fty(t, &f)))
                        .collect(),
                    mut_first: *mut_first,
                    ret: w.fty(ret, &f),
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
    (items, format!("{top}()"))
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
    /// The resource that each handle formal of an inlined helper names.
    handles: BTreeMap<String, HVal>,
    suffix: String,
}

/// What a handle formal names in the twin: a resource, or the input of a
/// child.
#[derive(Clone)]
enum HVal {
    Res(String),
    /// The instance and the port.
    Port(String, String),
    /// The elements of a tuple, an array, or a list of handles.
    Seq(Vec<HVal>),
    /// A struct of handles: its fields by name.
    Rec(Vec<(String, HVal)>),
}

impl Frame {
    fn declare(&mut self, name: &str) -> String {
        let twin = format!("{name}{}", self.suffix);
        self.names.insert(name.to_owned(), twin.clone());
        twin
    }

    fn name(&self, name: &str) -> String {
        match self.handles.get(name) {
            Some(HVal::Res(twin)) => twin.clone(),
            _ => self
                .names
                .get(name)
                .cloned()
                .unwrap_or_else(|| name.to_owned()),
        }
    }

    /// The target of `name :=`.
    fn target(&self, name: &str) -> Place {
        match self.handles.get(name) {
            Some(HVal::Port(u, p)) => Place::Field(u.clone(), p.clone()),
            _ => Place::Name(self.name(name)),
        }
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
    /// The helper calls that the twin has inlined.
    calls: u32,
    /// The elements of each list of handles of the module, in push order.
    /// A push in a loop body must reach the list of the module, so the
    /// lists live here and not in a frame.
    lists: BTreeMap<String, Vec<HVal>>,
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
        self.lists.clear();
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

    /// The type of a formal or a result of a helper that stays in the twin:
    /// a data type, because the twin inlines each other helper.
    fn fty(&self, t: &FTy, fr: &Frame) -> FTy {
        match t {
            FTy::Data(t) => FTy::Data(self.ty(t, fr)),
            other => other.clone(),
        }
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
            HExpr::Field(u, q) if matches!(fr.handles.get(u), Some(HVal::Rec(_))) => {
                self.leaf(e, fr)
            }
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
            HExpr::Unit => HExpr::Unit,
            HExpr::ReadPort {
                mem,
                addr,
                en,
                receiver,
            } => HExpr::ReadPort {
                mem: fr.name(mem),
                addr: sub(addr),
                en: sub(en),
                receiver: *receiver,
            },
            HExpr::Index(..) | HExpr::Select(..) => self.leaf(e, fr),
            HExpr::Read(h) => HExpr::Read(sub(h)),
            HExpr::Tuple(_) | HExpr::Array(_) | HExpr::Record(..) => {
                panic!("a literal of handles reads as data: {e:?}")
            }
        }
    }

    /// The handle that the actual `e` of a handle formal names. A container
    /// selects its element here, so the twin has no container.
    fn handle(&self, e: &HExpr, fr: &Frame) -> HVal {
        let seq = |b: &HExpr| match self.handle(b, fr) {
            HVal::Seq(xs) => xs,
            _ => panic!("a selection of the builder is on no container: {e:?}"),
        };
        match e {
            HExpr::Name(n) => match (fr.handles.get(n), self.lists.get(n)) {
                (Some(h), _) => h.clone(),
                (None, Some(xs)) => HVal::Seq(xs.clone()),
                (None, None) => HVal::Res(fr.name(n)),
            },
            HExpr::Field(u, f) => match fr.handles.get(u) {
                Some(HVal::Rec(fields)) => fields.iter().find(|(n, _)| n == f).map_or_else(
                    || panic!("a field of the builder is missing: {e:?}"),
                    |(_, h)| h.clone(),
                ),
                _ => HVal::Port(fr.name(u), f.clone()),
            },
            HExpr::Select(b, k) => seq(b)
                .get(*k as usize)
                .cloned()
                .unwrap_or_else(|| panic!("a selection of the builder is out of range: {e:?}")),
            HExpr::Index(b, i) => match self.value(i, fr) {
                Some(Value::Int(i)) => usize::try_from(i)
                    .ok()
                    .and_then(|i| seq(b).get(i).cloned())
                    .unwrap_or_else(|| panic!("an index of the builder is out of range: {e:?}")),
                _ => panic!("an index of the builder is not static: {e:?}"),
            },
            HExpr::Tuple(xs) | HExpr::Array(xs) => {
                HVal::Seq(xs.iter().map(|x| self.handle(x, fr)).collect())
            }
            HExpr::Record(name, xs) => {
                let fields = self.items.iter().find_map(|item| match item {
                    Item::Struct(def) if def.name == *name => Some(&def.fields),
                    _ => None,
                });
                let Some(fields) = fields else {
                    panic!("a record of the builder names no struct: {name}");
                };
                HVal::Rec(
                    fields
                        .iter()
                        .zip(xs)
                        .map(|((f, _), x)| (f.clone(), self.handle(x, fr)))
                        .collect(),
                )
            }
            _ => panic!("a handle of the builder is no name or selection: {e:?}"),
        }
    }

    /// The name of the resource that the selection `e` of a container of
    /// handles names, read as data.
    fn leaf(&self, e: &HExpr, fr: &Frame) -> HExpr {
        match self.handle(e, fr) {
            HVal::Res(n) => HExpr::Name(n),
            _ => panic!("a read of the builder is on no register or wire: {e:?}"),
        }
    }

    /// The `:=` target for the handle `h`.
    fn place(h: HVal) -> Place {
        match h {
            HVal::Res(n) => Place::Name(n),
            HVal::Port(u, p) => Place::Field(u, p),
            HVal::Seq(_) | HVal::Rec(_) => panic!("a target of the builder is a container"),
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
            handles: fr.handles.clone(),
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
                if let HExpr::Call(f, args) = value
                    && is_resource_helper(f)
                {
                    self.inline_let(name, *mutable, (f, args), fr, out);
                    return;
                }
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
                    Place::Name(n) => fr.target(n),
                    Place::Field(u, p) => match fr.handles.get(u) {
                        Some(HVal::Rec(_)) => {
                            Writer::place(self.handle(&HExpr::Field(u.clone(), p.clone()), fr))
                        }
                        _ => Place::Field(fr.name(u), p.clone()),
                    },
                    Place::Path(e) => Writer::place(self.handle(e, fr)),
                };
                out.push(Stmt::Connect(place, self.hexpr(v, fr)));
            }
            Stmt::Instance(u, m, args) => self.instance(s, (u, m, args), fr, out),
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
            Stmt::For(binder, lo, hi, body) => self.unroll(s, (binder, lo, hi, body), fr, out),
            Stmt::Assert(c, _) => {
                if self.value(c, fr) != Some(Value::Bool(true)) {
                    out.push(s.clone());
                }
            }
            Stmt::Error(_) => out.push(s.clone()),
            // The twin compares outputs only; a record is no output.
            Stmt::Diagnostic(..) => {}
            Stmt::Block(body) => out.push(self.block(body, fr, fr.env.clone(), fr.suffix.clone())),
            Stmt::Call(f, args) => {
                self.inline(f, args, fr, out);
            }
            Stmt::Mem(..) | Stmt::WritePort { .. } => self.memory(s, fr, out),
            Stmt::HList(n, _) => {
                self.lists.insert(n.clone(), Vec::new());
            }
            Stmt::HPush(n, h) => {
                let h = self.handle(h, fr);
                self.lists.entry(n.clone()).or_default().push(h);
            }
        }
    }

    /// A `mem` statement, or a `write_port` call.
    fn memory(&mut self, s: &Stmt, fr: &mut Frame, out: &mut Vec<Stmt>) {
        match s {
            Stmt::Mem(n, t, depth) => {
                let (t, depth) = (self.ty(t, fr), self.fold(depth, fr));
                out.push(Stmt::Mem(fr.declare(n), t, depth));
            }
            Stmt::WritePort {
                mem,
                addr,
                data,
                en,
                receiver,
            } => {
                let [addr, data, en] = [addr, data, en].map(|e| Box::new(self.hexpr(e, fr)));
                let mem = fr.name(mem);
                let receiver = *receiver;
                out.push(Stmt::WritePort {
                    mem,
                    addr,
                    data,
                    en,
                    receiver,
                });
            }
            _ => out.push(s.clone()),
        }
    }

    /// `instance u = m(args);` as an instance of the specialized module.
    /// A fault of the builder keeps the statement `s`.
    fn instance(
        &mut self,
        s: &Stmt,
        (u, m, args): (&str, &str, &[SExpr]),
        fr: &mut Frame,
        out: &mut Vec<Stmt>,
    ) {
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

    /// The bound `hi` of a loop with `len(g)` of a list of handles replaced
    /// by the number of its elements: the evaluator knows no handle.
    fn length(&self, hi: &SExpr, fr: &Frame) -> SExpr {
        let SExpr::Len(inner) = hi else {
            return hi.clone();
        };
        let SExpr::Name(n) = &**inner else {
            return hi.clone();
        };
        let len = match (fr.handles.get(n), self.lists.get(n)) {
            (Some(HVal::Seq(xs)), _) | (None, Some(xs)) => xs.len(),
            _ => return hi.clone(),
        };
        SExpr::Int(BigInt::from(len), Radix::Dec)
    }

    /// One block for each iteration of a `comptime for`. A fault of the
    /// builder keeps the statement `s`.
    fn unroll(
        &mut self,
        s: &Stmt,
        (binder, lo, hi, body): (&str, &SExpr, &SExpr, &[Stmt]),
        fr: &Frame,
        out: &mut Vec<Stmt>,
    ) {
        let hi = self.length(hi, fr);
        let (Some(Value::Int(lo)), Some(Value::Int(hi))) =
            (self.value(lo, fr), self.value(&hi, fr))
        else {
            out.push(s.clone());
            return;
        };
        // A loop that pushes handles keeps its declarations in the scope of
        // the module, where the later calls bind them. Their names carry the
        // iteration, so no two iterations share a name.
        let flat = body.iter().any(|s| matches!(s, Stmt::HPush(..)));
        for value in loop_values(&lo, &hi) {
            let suffix = format!(
                "_{binder}_{}{}",
                token(&value).unwrap_or_default(),
                fr.suffix
            );
            let mut env = fr.env.clone();
            env.statics.insert(binder.to_owned(), value);
            match self.block(body, fr, env, suffix) {
                Stmt::Block(inner) if flat => out.extend(inner),
                block => out.push(block),
            }
        }
    }

    /// `let name = f(args);` of a helper that takes resources: the body, then
    /// a `let` of the result, which has the type of the result of `f`.
    fn inline_let(
        &mut self,
        name: &str,
        mutable: bool,
        call: (&str, &[HExpr]),
        fr: &mut Frame,
        out: &mut Vec<Stmt>,
    ) {
        let (callee, ret, result) = self.inline(call.0, call.1, fr, out);
        let FTy::Data(t) = &ret else {
            let h = self.handle(&result, &callee);
            fr.handles.insert(name.to_owned(), h);
            return;
        };
        let ty = Some(self.ty(t, &callee));
        let value = self.hexpr(&result, &callee);
        out.push(Stmt::Let {
            name: fr.declare(name),
            mutable,
            ty,
            value,
        });
    }

    /// The body of the helper `f` at a call with `args`, appended to `out`.
    /// A data formal becomes a typed `let` of its actual, so the actual
    /// converts as the formal does. A handle formal names the resource of
    /// its actual. Gives the frame of the call, the type of the result, and
    /// the result.
    fn inline(
        &mut self,
        f: &str,
        args: &[HExpr],
        fr: &Frame,
        out: &mut Vec<Stmt>,
    ) -> (Frame, FTy, HExpr) {
        let Some((params, ret, body, result)) = helper_of(self.items, f) else {
            panic!("a call of the builder names no helper: {f}");
        };
        self.calls += 1;
        let mut callee = Frame {
            suffix: format!("_c{}", self.calls),
            ..Frame::default()
        };
        for ((name, t), arg) in params.iter().zip(args) {
            if let FTy::Data(t) = t {
                let ty = self.ty(t, &callee);
                let value = self.hexpr(arg, fr);
                out.push(Stmt::Let {
                    name: callee.declare(name),
                    mutable: false,
                    ty: Some(ty),
                    value,
                });
            } else {
                callee.handles.insert(name.clone(), self.handle(arg, fr));
            }
        }
        let body = self.stmts(body, &mut callee);
        out.extend(body);
        (callee, ret.clone(), result.clone())
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
        HExpr::Field(..) | HExpr::Static(_) | HExpr::Make(..) | HExpr::Unit => e.clone(),
        HExpr::ReadPort {
            mem,
            addr,
            en,
            receiver,
        } => HExpr::ReadPort {
            mem: mem.clone(),
            addr: sub(addr),
            en: sub(en),
            receiver: *receiver,
        },
        HExpr::Tuple(xs) => HExpr::Tuple(all(xs)),
        HExpr::Array(xs) => HExpr::Array(all(xs)),
        HExpr::Record(s, xs) => HExpr::Record(s.clone(), all(xs)),
        HExpr::Index(b, i) => HExpr::Index(sub(b), i.clone()),
        HExpr::Select(b, k) => HExpr::Select(sub(b), *k),
        HExpr::Read(h) => HExpr::Read(sub(h)),
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
        ComptimeFn, FieldTy, HBin, HExpr, Item, Place, Ports, Radix, SBin, SExpr, STy, Stmt,
        StructDef, Ty,
    };
    use super::*;
    use num_bigint::BigInt;
    use proptest::prelude::*;
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;

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
            params: vec![("x0".to_owned(), uint(8).into())],
            mut_first: false,
            ret: uint(8).into(),
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

    /// A call of a helper that binds a register inlines the body: the
    /// data actual becomes a typed `let`, and the handle formal names the
    /// register. Two calls get two sets of names.
    #[test]
    fn the_twin_inlines_a_helper_that_binds_a_formal() {
        let helper = Item::Helper {
            name: "H0".to_owned(),
            params: vec![
                ("a0".to_owned(), FTy::Reg(uint(8))),
                ("x1".to_owned(), uint(8).into()),
            ],
            mut_first: false,
            ret: FTy::Unit,
            body: vec![
                Stmt::Let {
                    name: "l0".to_owned(),
                    mutable: false,
                    ty: None,
                    value: hbin(HBin::Addw, hname("a0"), hname("x1")),
                },
                connect("a0", hname("l0")),
            ],
            result: HExpr::Unit,
        };
        let call = |actual: HExpr| Stmt::Call("H0".to_owned(), vec![hname("r0"), actual]);
        let body = vec![
            Stmt::Input("i0".to_owned(), uint(8)),
            Stmt::Output("o0".to_owned(), uint(8)),
            Stmt::Reg("r0".to_owned(), uint(8), int(0)),
            call(hname("i0")),
            connect("o0", hname("r0")),
        ];
        let m0 = module("M0", &[], true, body);
        let t = twin(&program(vec![helper, m0], Vec::new()));
        assert_eq!(
            t.text,
            "module M0() {\n    input i0: UInt[8];\n    output o0: UInt[8];\n    reg r0: UInt[8] = 0;\n    let x1_c1: UInt[8] = i0;\n    let l0_c1 = (r0 +% x1_c1);\n    r0 := l0_c1;\n    o0 := r0;\n}\n"
        );
        assert!(t.static_names().is_empty(), "{:?}", t.static_names());
    }

    /// A helper with a `Mem` formal and a data result inlines at the root
    /// of a `let`: the `let` gets the type of the result. A helper with an
    /// `Input` formal binds the port of the child.
    #[test]
    fn the_twin_inlines_a_memory_helper_and_an_input_binder() {
        let word = uint(8);
        let mem_helper = Item::Helper {
            name: "H0".to_owned(),
            params: vec![
                (
                    "a0".to_owned(),
                    FTy::Mem(word.clone(), SExpr::Int(BigInt::from(4), Radix::Dec)),
                ),
                ("x1".to_owned(), uint(2).into()),
            ],
            mut_first: false,
            ret: word.clone().into(),
            body: vec![
                Stmt::WritePort {
                    mem: "a0".to_owned(),
                    addr: Box::new(hname("x1")),
                    data: Box::new(HExpr::Make(word.clone(), int(7))),
                    en: Box::new(HExpr::Static(SExpr::Bool(true))),
                    receiver: false,
                },
                Stmt::Let {
                    name: "l0".to_owned(),
                    mutable: false,
                    ty: None,
                    value: HExpr::ReadPort {
                        mem: "a0".to_owned(),
                        addr: Box::new(hname("x1")),
                        en: Box::new(HExpr::Static(SExpr::Bool(true))),
                        receiver: true,
                    },
                },
            ],
            result: HExpr::Field("l0".to_owned(), "data".to_owned()),
        };
        let input_helper = Item::Helper {
            name: "H1".to_owned(),
            params: vec![
                ("a0".to_owned(), FTy::Input(uint(4))),
                ("x1".to_owned(), uint(4).into()),
            ],
            mut_first: false,
            ret: FTy::Unit,
            body: vec![connect("a0", hname("x1"))],
            result: HExpr::Unit,
        };
        let body = vec![
            Stmt::Input("i0".to_owned(), uint(2)),
            Stmt::Output("o0".to_owned(), uint(8)),
            Stmt::Mem("n0".to_owned(), word.clone(), int(4)),
            Stmt::Let {
                name: "l0".to_owned(),
                mutable: false,
                ty: None,
                value: HExpr::Call("H0".to_owned(), vec![hname("n0"), hname("i0")]),
            },
            Stmt::Instance("u0".to_owned(), "M1".to_owned(), Vec::new()),
            Stmt::Call(
                "H1".to_owned(),
                vec![
                    HExpr::Field("u0".to_owned(), "i0".to_owned()),
                    HExpr::Make(uint(4), int(3)),
                ],
            ),
            connect("o0", hname("l0")),
        ];
        let m0 = module("M0", &[], true, body);
        let t = twin(&program(
            vec![mem_helper, input_helper, m0, m1()],
            Vec::new(),
        ));
        assert_eq!(
            t.text,
            "module M0() {\n    input i0: UInt[2];\n    output o0: UInt[8];\n    mem n0: [UInt[8]; 4];\n    let x1_c1: UInt[2] = i0;\n    write_port(n0, x1_c1, UInt[8](7), true);\n    let l0_c1 = n0.read_port(x1_c1, true);\n    let l0: UInt[8] = l0_c1.data;\n    instance u0 = M1();\n    let x1_c2: UInt[4] = UInt[4](3);\n    u0.i0 := x1_c2;\n    o0 := l0;\n}\nmodule M1() domains() {\n    input i0: UInt[4];\n    output o0: UInt[4];\n    o0 := i0;\n}\n"
        );
    }

    /// Helpers that return an array, a struct, and an instance of handles:
    /// the twin names the resource of each selection, so it has no
    /// container, and a `:=` through a selection binds the resource.
    #[test]
    fn the_twin_resolves_the_containers_of_a_declaring_helper() {
        let pair = Item::Struct(StructDef {
            name: "T0".to_owned(),
            params: Vec::new(),
            fields: vec![
                ("m0".to_owned(), FieldTy::Handle(FTy::Reg(uint(4)))),
                ("m1".to_owned(), FieldTy::Handle(FTy::Wire(uint(4)))),
            ],
        });
        let helper = |name: &str, ret: FTy, body: Vec<Stmt>, result: HExpr| Item::Helper {
            name: name.to_owned(),
            params: Vec::new(),
            mut_first: false,
            ret,
            body,
            result,
        };
        let reg = |n: &str| Stmt::Reg(n.to_owned(), uint(4), int(0));
        let array = helper(
            "H0",
            FTy::Array(Box::new(FTy::Reg(uint(4))), 2),
            vec![reg("r0"), reg("r1")],
            HExpr::Array(vec![hname("r0"), hname("r1")]),
        );
        let record = helper(
            "H1",
            FTy::Struct("T0".to_owned()),
            vec![reg("r2"), Stmt::Wire("w0".to_owned(), uint(4))],
            HExpr::Record("T0".to_owned(), vec![hname("r2"), hname("w0")]),
        );
        let instance = helper(
            "H2",
            FTy::Instance("M1".to_owned(), Vec::new()),
            vec![Stmt::Instance("u0".to_owned(), "M1".to_owned(), Vec::new())],
            hname("u0"),
        );
        let call = |name: &str, f: &str| Stmt::Let {
            name: name.to_owned(),
            mutable: false,
            ty: None,
            value: HExpr::Call(f.to_owned(), Vec::new()),
        };
        let element = HExpr::Index(Box::new(hname("a")), int(1));
        let body = vec![
            Stmt::Input("i0".to_owned(), uint(4)),
            Stmt::Output("o0".to_owned(), uint(4)),
            call("a", "H0"),
            call("b", "H1"),
            call("c", "H2"),
            Stmt::Connect(Place::Path(element.clone()), hname("i0")),
            Stmt::Connect(Place::Field("b".to_owned(), "m0".to_owned()), hname("i0")),
            Stmt::Connect(Place::Field("b".to_owned(), "m1".to_owned()), hname("i0")),
            Stmt::Connect(Place::Field("c".to_owned(), "i0".to_owned()), hname("i0")),
            connect(
                "o0",
                hbin(
                    HBin::Addw,
                    hbin(
                        HBin::Addw,
                        HExpr::Read(Box::new(element)),
                        HExpr::Field("b".to_owned(), "m0".to_owned()),
                    ),
                    HExpr::Field("c".to_owned(), "o0".to_owned()),
                ),
            ),
        ];
        let m0 = module("M0", &[], true, body);
        let items = vec![pair, array, record, instance, m0, m1()];
        let t = twin(&program(items, Vec::new()));
        assert_eq!(
            t.text,
            "module M0() {\n    input i0: UInt[4];\n    output o0: UInt[4];\n    reg r0_c1: UInt[4] = 0;\n    reg r1_c1: UInt[4] = 0;\n    reg r2_c2: UInt[4] = 0;\n    wire w0_c2: UInt[4];\n    instance u0_c3 = M1();\n    r1_c1 := i0;\n    r2_c2 := i0;\n    w0_c2 := i0;\n    u0_c3.i0 := i0;\n    o0 := ((read(r1_c1) +% r2_c2) +% u0_c3.o0);\n}\nmodule M1() domains() {\n    input i0: UInt[4];\n    output o0: UInt[4];\n    o0 := i0;\n}\n"
        );
        assert!(t.static_names().is_empty(), "{:?}", t.static_names());
    }

    /// A group: the loop that pushes declarations runs without blocks, so
    /// the call after it binds the resources of the iterations. The bound
    /// `len(a0)` of the helper is the number of pushes.
    #[test]
    fn the_twin_unrolls_a_list_of_handles_and_its_helper() {
        let helper = Item::Helper {
            name: "H0".to_owned(),
            params: vec![
                ("a0".to_owned(), FTy::List(Box::new(FTy::Reg(uint(4))))),
                ("x1".to_owned(), uint(4).into()),
            ],
            mut_first: false,
            ret: FTy::Unit,
            body: vec![Stmt::For(
                "j0".to_owned(),
                int(0),
                SExpr::Len(Box::new(sname("a0"))),
                vec![Stmt::Connect(
                    Place::Path(HExpr::Index(Box::new(hname("a0")), sname("j0"))),
                    hbin(HBin::Xor, hname("x1"), HExpr::Make(uint(4), sname("j0"))),
                )],
            )],
            result: HExpr::Unit,
        };
        let body = vec![
            Stmt::Input("i0".to_owned(), uint(4)),
            Stmt::Output("o0".to_owned(), uint(4)),
            Stmt::HList("G0".to_owned(), FTy::Reg(uint(4))),
            Stmt::For(
                "j1".to_owned(),
                int(0),
                int(2),
                vec![
                    Stmt::Reg("r0".to_owned(), uint(4), int(0)),
                    Stmt::HPush("G0".to_owned(), hname("r0")),
                ],
            ),
            Stmt::Call("H0".to_owned(), vec![hname("G0"), hname("i0")]),
            connect("o0", HExpr::Index(Box::new(hname("G0")), int(1))),
        ];
        let t = twin(&program(
            vec![helper, module("M0", &[], true, body)],
            Vec::new(),
        ));
        assert_eq!(
            t.text,
            "module M0() {\n    input i0: UInt[4];\n    output o0: UInt[4];\n    reg r0_j1_0: UInt[4] = 0;\n    reg r0_j1_1: UInt[4] = 0;\n    let x1_c1: UInt[4] = i0;\n    {\n        r0_j1_0 := (x1_c1 ^ UInt[4](0));\n    }\n    {\n        r0_j1_1 := (x1_c1 ^ UInt[4](1));\n    }\n    o0 := r0_j1_1;\n}\n"
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

    /// The bindings of one twin module.
    #[derive(Default)]
    struct Bindings {
        /// Registers, wires, and outputs by name, with whether a wire.
        targets: BTreeMap<String, bool>,
        assigned: BTreeMap<String, u32>,
        /// The instances, with their modules.
        children: BTreeMap<String, String>,
        ports: BTreeMap<(String, String), u32>,
        /// The memories, with their write and read ports.
        mems: BTreeMap<String, (u32, u32)>,
        declared: Vec<String>,
        /// The wires that read themselves.
        loops: Vec<String>,
    }

    fn read_names(e: &HExpr, out: &mut BTreeSet<String>) {
        match e {
            HExpr::Name(n) | HExpr::Field(n, _) => {
                out.insert(n.clone());
            }
            HExpr::Static(_) | HExpr::Make(..) | HExpr::Unit => {}
            HExpr::Unary(_, a)
            | HExpr::Resize(_, a)
            | HExpr::Reinterpret(_, a)
            | HExpr::Index(a, _)
            | HExpr::Select(a, _)
            | HExpr::Read(a) => read_names(a, out),
            HExpr::Binary(_, a, b) => {
                read_names(a, out);
                read_names(b, out);
            }
            HExpr::If(c, a, b) => {
                for x in [c, a, b] {
                    read_names(x, out);
                }
            }
            HExpr::Call(_, xs)
            | HExpr::Ctor(_, _, xs)
            | HExpr::Tuple(xs)
            | HExpr::Array(xs)
            | HExpr::Record(_, xs) => {
                for x in xs {
                    read_names(x, out);
                }
            }
            HExpr::Receiver(r, _, xs) => {
                read_names(r, out);
                for x in xs {
                    read_names(x, out);
                }
            }
            HExpr::Match(m) => {
                read_names(&m.scrutinee, out);
                for (_, a) in &m.arms {
                    read_names(a, out);
                }
            }
            HExpr::ReadPort { mem, addr, en, .. } => {
                out.insert(mem.clone());
                read_names(addr, out);
                read_names(en, out);
            }
        }
    }

    fn collect(body: &[Stmt], b: &mut Bindings) {
        for s in body {
            match s {
                Stmt::Output(n, _) | Stmt::Reg(n, ..) => {
                    b.targets.insert(n.clone(), false);
                    b.declared.push(n.clone());
                }
                Stmt::Wire(n, _) => {
                    b.targets.insert(n.clone(), true);
                    b.declared.push(n.clone());
                }
                Stmt::Instance(u, m, _) => {
                    b.children.insert(u.clone(), m.clone());
                    b.declared.push(u.clone());
                }
                Stmt::Mem(n, ..) => {
                    b.mems.insert(n.clone(), (0, 0));
                    b.declared.push(n.clone());
                }
                Stmt::WritePort { mem, .. } => {
                    b.mems.entry(mem.clone()).or_default().0 += 1;
                }
                Stmt::Let { name, value, .. } => {
                    b.declared.push(name.clone());
                    if let HExpr::ReadPort { mem, .. } = value {
                        b.mems.entry(mem.clone()).or_default().1 += 1;
                    }
                }
                Stmt::Connect(place, value) => match place {
                    Place::Name(n) => {
                        *b.assigned.entry(n.clone()).or_default() += 1;
                        let mut read = BTreeSet::new();
                        read_names(value, &mut read);
                        if b.targets.get(n) == Some(&true) && read.contains(n) {
                            b.loops.push(n.clone());
                        }
                    }
                    Place::Field(u, p) => {
                        *b.ports.entry((u.clone(), p.clone())).or_default() += 1;
                    }
                    Place::Path(_) => panic!("a twin has a container of handles"),
                },
                Stmt::Block(inner) => collect(inner, b),
                _ => {}
            }
        }
    }

    /// Each resource of a twin has one binding: a register, a wire, and an
    /// output one `:=`; a child input one `:=`; a memory one `write_port` and
    /// one `read_port`. No name has two declarations, and no wire reads
    /// itself. The twin has no list and no handle formal, so a count here
    /// tests the inlining of the helpers on its own.
    #[test]
    fn the_twin_binds_each_resource_once() {
        let mut runner = TestRunner::deterministic();
        let mut resources = 0;
        for _ in 0..256 {
            let p = typed().new_tree(&mut runner).unwrap().current().unwrap();
            let (items, _) = twin_items(&p);
            let inputs: BTreeMap<&str, Vec<&str>> = items
                .iter()
                .filter_map(|item| match item {
                    Item::Module { name, body, .. } => Some((
                        name.as_str(),
                        body.iter()
                            .filter_map(|s| match s {
                                Stmt::Input(n, _) => Some(n.as_str()),
                                _ => None,
                            })
                            .collect(),
                    )),
                    _ => None,
                })
                .collect();
            for item in &items {
                let Item::Module { name, body, .. } = item else {
                    continue;
                };
                let mut b = Bindings::default();
                collect(body, &mut b);
                let text = render_items(&items);
                let unique: BTreeSet<&String> = b.declared.iter().collect();
                assert_eq!(
                    unique.len(),
                    b.declared.len(),
                    "{name}: a name twice\n{text}"
                );
                for t in b.targets.keys() {
                    resources += 1;
                    assert_eq!(b.assigned.get(t), Some(&1), "{name}: {t}\n{text}");
                }
                for (u, m) in &b.children {
                    for port in inputs.get(m.as_str()).into_iter().flatten() {
                        resources += 1;
                        let key = (u.clone(), (*port).to_owned());
                        assert_eq!(b.ports.get(&key), Some(&1), "{name}: {u}.{port}\n{text}");
                    }
                }
                for (n, ports) in &b.mems {
                    resources += 1;
                    assert_eq!(*ports, (1, 1), "{name}: {n}\n{text}");
                }
                assert!(b.loops.is_empty(), "{name}: {:?}\n{text}", b.loops);
            }
        }
        assert!(resources > 1000, "{resources}");
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
