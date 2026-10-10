//! The static evaluator of slice 1 with the budgets and the cost model of section 5.4 of the
//! front-end spec. Lean `Source.Eval` is its normative definition: each charge here is a
//! charge there, in the same order and at the same node. It reads the checked AST. It
//! recurses over the AST and the calls, so it runs on the front-end thread.
//!
//! A result that refers to an existing value, such as a local or a constant, stays a
//! reference until a copy pays for it. Thus a read that the cost model does not charge does
//! no work in the size of the value.

use crate::int::Int;
use crate::ops::{self, Fault, Fuel, str_text};
use crate::value::{Ty, Value, int_size};
use crate::{Budget, Code, Error};
use parse::ast::{BinOp, Expr, Ident, Item, Param, Pos, Stmt, TypeExpr};
use parse::{NestedStack, StackError};
use resolve::{DeclId, Kind, Prelude, Resolved, ResolvedExpr, Target};
use std::collections::BTreeMap;

/// The state of a constant in the table of constants.
enum Entry {
    NotStarted,
    InProgress,
    Done(Value),
}

/// A local of the current frame. A string and a type have no `Ty`, so their `ty` is `None`.
struct Slot {
    ty: Option<Ty>,
    mutable: bool,
    value: Value,
}

/// The result of an expression. Only `Made` is a new value. The others are references, so a
/// binding of them is a copy.
enum Out {
    Made(Value),
    /// A new value that the cost model treats as a reference: a type name.
    Named(Value),
    /// A local of the frame at this index of the frame stack. A call evaluates its arguments
    /// in the caller frame and binds them in a new frame, so a reference names its frame.
    Local(usize, DeclId),
    Const(usize),
}

impl Out {
    fn is_ref(&self) -> bool {
        !matches!(self, Out::Made(_))
    }
}

/// The value that a reference finds when its target is absent. The evaluator binds a local
/// before a use reads it and sets a constant done before a use refers to it, so no reference
/// finds it.
static ABSENT: Value = Value::Bool(false);

type Frame = BTreeMap<DeclId, Slot>;

/// The values that a result can refer to: the table of constants by item index, and the
/// stack of frames. The last frame is the current frame. A frame holds only the bindings
/// that ran.
struct Store {
    consts: Vec<Entry>,
    frames: Vec<Frame>,
}

impl Store {
    fn frame(&self) -> Option<&Frame> {
        self.frames.last()
    }

    fn frame_mut(&mut self) -> Option<&mut Frame> {
        self.frames.last_mut()
    }

    fn view<'s>(&'s self, out: &'s Out) -> &'s Value {
        match out {
            Out::Made(v) | Out::Named(v) => v,
            Out::Local(k, id) => self
                .frames
                .get(*k)
                .and_then(|f| f.get(id))
                .map_or(&ABSENT, |s| &s.value),
            Out::Const(i) => match self.consts.get(*i) {
                Some(Entry::Done(v)) => v,
                _ => &ABSENT,
            },
        }
    }

    /// The value of a result as an owned value. A reference copies its value, so the caller
    /// paid for the copy before.
    fn take(&self, out: Out) -> Value {
        match out {
            Out::Made(v) | Out::Named(v) => v,
            other => self.view(&other).clone(),
        }
    }
}

/// Which map of targets the names read: the top expression has its own positions.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Names {
    Top,
    File,
}

struct Evaluator<'a> {
    file: &'a Resolved,
    top: &'a ResolvedExpr,
    names: Names,
    /// The index of each item by the declaration of its name.
    items: BTreeMap<DeclId, usize>,
    /// The value of each number literal that ran, by its map and its position. The decimal
    /// conversion runs once for each literal, as in the parse of Lean.
    numbers: BTreeMap<(bool, Pos), Int>,
    limit: u64,
    depth: u64,
    /// The stack of each thread of the evaluation.
    stack: NestedStack,
    ret: Option<Ty>,
    fuel: Fuel,
    store: Store,
}

/// Why an evaluation stops: its first error, or a deeper level for which the machine cannot
/// give the stack.
pub(crate) enum Stop {
    Error(Error),
    Stack(StackError),
}

type Res<T> = Result<T, Stop>;

fn fail<T>(code: Code, pos: Pos, message: String) -> Res<T> {
    Err(Stop::Error(Error { code, pos, message }))
}

fn at(pos: Pos) -> impl Fn(Fault) -> Stop {
    move |(code, message)| Stop::Error(Error { code, pos, message })
}

pub(crate) fn expr_pos(e: &Expr) -> Pos {
    match e {
        Expr::Num { pos, .. }
        | Expr::Bool { pos, .. }
        | Expr::Str { pos, .. }
        | Expr::Name { pos, .. }
        | Expr::Unary { pos, .. }
        | Expr::Binary { pos, .. }
        | Expr::Cond { pos, .. }
        | Expr::Call { pos, .. }
        | Expr::Index { pos, .. }
        | Expr::Field { pos, .. } => *pos,
    }
}

fn type_pos(t: &TypeExpr) -> Pos {
    match t {
        TypeExpr::Name { pos, .. } | TypeExpr::Index { pos, .. } => *pos,
    }
}

fn stmt_pos(s: &Stmt) -> Pos {
    match s {
        Stmt::Local { pos, .. }
        | Stmt::Assign { pos, .. }
        | Stmt::Connect { pos, .. }
        | Stmt::Reg { pos, .. }
        | Stmt::Wire { pos, .. }
        | Stmt::Input { pos, .. }
        | Stmt::Output { pos, .. }
        | Stmt::Inst { pos, .. }
        | Stmt::Ret { pos, .. }
        | Stmt::CtIf { pos, .. }
        | Stmt::CtFor { pos, .. }
        | Stmt::Block { pos, .. }
        | Stmt::Expr { pos, .. } => *pos,
    }
}

/// The value of `expr` in the file scope of `file`, and the used fuel.
pub(crate) fn run(
    file: &Resolved,
    top: &ResolvedExpr,
    budget: Budget,
    stack: NestedStack,
) -> Res<(Value, u64)> {
    let mut items = BTreeMap::new();
    let mut consts = Vec::new();
    for (i, item) in file.ast().iter().enumerate() {
        let (Item::Const { name, .. } | Item::Fn { name, .. } | Item::Module { name, .. }) = item;
        if let Some(Target::Decl(id)) = file.target(name.pos) {
            items.insert(id, i);
        }
        consts.push(Entry::NotStarted);
    }
    let mut ev = Evaluator {
        file,
        top,
        names: Names::Top,
        items,
        numbers: BTreeMap::new(),
        limit: budget.depth,
        depth: 0,
        stack,
        ret: None,
        fuel: Fuel::new(budget.fuel),
        store: Store {
            consts,
            frames: vec![Frame::new()],
        },
    };
    let e = top.expr();
    let out = ev.eval(e)?;
    let out = need(e, out)?;
    let value = ev.store.take(out);
    Ok((value, budget.fuel - ev.fuel.left()))
}

/// The value of `e`. Only `static_assert` and `error` give no value.
fn need(e: &Expr, out: Option<Out>) -> Res<Out> {
    match out {
        Some(out) => Ok(out),
        None => fail(
            Code::S010,
            expr_pos(e),
            "`static_assert` gives no value".to_owned(),
        ),
    }
}

/// A static condition.
fn test(pos: Pos, v: &Value) -> Res<bool> {
    match v {
        Value::Bool(b) => Ok(*b),
        v => fail(
            Code::S010,
            pos,
            format!("a condition is a Bool, not {}", v.text()),
        ),
    }
}

/// A scalar type of the prelude without its index.
fn prim(pos: Pos, name: &str, k: Prelude) -> Res<Ty> {
    match k {
        Prelude::Bool => Ok(Ty::Bool),
        Prelude::Nat => Ok(Ty::Nat),
        Prelude::Int => Ok(Ty::Int),
        _ => fail(
            Code::S007,
            pos,
            format!("`{name}` takes 1 argument(s), but it has 0"),
        ),
    }
}

/// A string and a type have no `Ty`, so an assignment keeps their form.
fn same_form(a: &Value, b: &Value) -> bool {
    matches!(
        (a, b),
        (Value::Str(_), Value::Str(_)) | (Value::Type(_), Value::Type(_))
    )
}

impl Evaluator<'_> {
    fn target(&self, pos: Pos) -> Option<Target> {
        match self.names {
            Names::Top => self.top.target(pos),
            Names::File => self.file.target(pos),
        }
    }

    /// The declaration of a binder. Each binder is in the body of an item of the file.
    fn decl(&self, name: &Ident) -> Res<DeclId> {
        match self.file.target(name.pos) {
            Some(Target::Decl(id)) => Ok(id),
            _ => fail(
                Code::S010,
                name.pos,
                format!("`{}` has no declaration", name.name),
            ),
        }
    }

    fn charge(&mut self, pos: Pos, units: u128) -> Res<()> {
        self.fuel.pay(units).map_err(at(pos))
    }

    fn size(&self, out: &Out) -> u128 {
        u128::from(self.store.view(out).size())
    }

    /// A binding copies a reference.
    fn copy(&mut self, pos: Pos, out: &Out) -> Res<()> {
        if out.is_ref() {
            self.charge(pos, self.size(out))?;
        }
        Ok(())
    }

    /// A typed use of a result at the type `t`.
    fn conform(&mut self, pos: Pos, t: Ty, out: Out) -> Res<Value> {
        let converted = ops::convert(t, self.store.view(&out), &mut self.fuel).map_err(at(pos))?;
        Ok(match converted {
            Some(v) => v,
            None => self.store.take(out),
        })
    }

    fn bind(&mut self, id: DeclId, slot: Slot) {
        if let Some(frame) = self.store.frame_mut() {
            frame.insert(id, slot);
        }
    }

    /// Runs `act` one level deeper, or gives `S015` at `pos` above the limit. A level that
    /// starts a new group of levels runs on a new thread with the stack of the group, so the
    /// stack of each thread stays small for any nesting depth.
    fn nested<T: Send>(
        &mut self,
        pos: Pos,
        act: impl FnOnce(&mut Self) -> Res<T> + Send,
    ) -> Res<T> {
        if self.limit <= self.depth {
            return fail(
                Code::S015,
                pos,
                format!("the nesting depth goes above {}", self.limit),
            );
        }
        self.depth += 1;
        let r = if self.stack.starts_thread(self.depth) {
            let stack = self.stack;
            stack
                .run(|| act(self))
                .unwrap_or_else(|e| Err(Stop::Stack(e)))
        } else {
            act(self)
        };
        self.depth -= 1;
        r
    }

    /// Runs `act` in the file scope with a new empty frame of locals and the return type
    /// `ret`. The frames below stay, so a reference into them still finds its value.
    fn in_frame<T>(&mut self, ret: Option<Ty>, act: impl FnOnce(&mut Self) -> Res<T>) -> Res<T> {
        self.store.frames.push(Frame::new());
        let saved_ret = std::mem::replace(&mut self.ret, ret);
        let names = std::mem::replace(&mut self.names, Names::File);
        let r = act(self);
        self.store.frames.pop();
        self.ret = saved_ret;
        self.names = names;
        r
    }

    /// The results of the arguments of a call, in order.
    fn args(&mut self, xs: &[Expr]) -> Res<Vec<Out>> {
        let mut outs = Vec::with_capacity(xs.len());
        for x in xs {
            let out = self.eval(x)?;
            outs.push(need(x, out)?);
        }
        Ok(outs)
    }

    fn number(&mut self, pos: Pos, digits: &str) -> Int {
        let key = (self.names == Names::Top, pos);
        if let Some(n) = self.numbers.get(&key) {
            return n.clone();
        }
        let n = Int::from_decimal(digits).unwrap_or_else(Int::zero);
        self.numbers.insert(key, n.clone());
        n
    }

    fn made(&mut self, pos: Pos, v: Value) -> Res<Option<Out>> {
        self.charge(pos, u128::from(v.size()))?;
        Ok(Some(Out::Made(v)))
    }

    fn eval(&mut self, e: &Expr) -> Res<Option<Out>> {
        self.charge(expr_pos(e), 1)?;
        match e {
            Expr::Num { pos, value } => {
                let n = self.number(*pos, value.as_str());
                self.made(*pos, Value::Int(n))
            }
            Expr::Bool { pos, value } => self.made(*pos, Value::Bool(*value)),
            Expr::Str { pos, value } => {
                // The size counts the characters, and the charge comes before the copy.
                let size = 1 + value.chars().count() as u128;
                self.charge(*pos, size)?;
                Ok(Some(Out::Made(Value::Str(value.clone()))))
            }
            Expr::Name { pos, name } => Ok(Some(self.name(*pos, name)?)),
            Expr::Unary { pos, op, arg } => {
                let a = self.eval(arg)?;
                let a = need(arg, a)?;
                let v = ops::unary(*op, self.store.view(&a), &mut self.fuel).map_err(at(*pos))?;
                Ok(Some(Out::Made(v)))
            }
            Expr::Binary {
                pos,
                op: op @ (BinOp::Land | BinOp::Lor),
                lhs,
                rhs,
            } => {
                let a = self.eval(lhs)?;
                let a = need(lhs, a)?;
                let a = test(*pos, self.store.view(&a))?;
                if a == (*op == BinOp::Lor) {
                    return Ok(Some(Out::Made(Value::Bool(a))));
                }
                let b = self.eval(rhs)?;
                let b = need(rhs, b)?;
                let b = test(*pos, self.store.view(&b))?;
                Ok(Some(Out::Made(Value::Bool(b))))
            }
            Expr::Binary { pos, op, lhs, rhs } => {
                let a = self.eval(lhs)?;
                let a = need(lhs, a)?;
                let b = self.eval(rhs)?;
                let b = need(rhs, b)?;
                Ok(Some(Out::Made(self.binary(*pos, *op, &a, &b)?)))
            }
            Expr::Cond { pos, cond, yes, no } => {
                let c = self.eval(cond)?;
                let c = need(cond, c)?;
                if test(*pos, self.store.view(&c))? {
                    self.eval(yes)
                } else {
                    self.eval(no)
                }
            }
            Expr::Call { pos, callee, args } => self.call(*pos, callee, args),
            Expr::Index { pos, base, args } => {
                if let Expr::Name { pos: bp, .. } = &**base
                    && let Some(Target::Prelude(k)) = self.target(*bp)
                    && k.is_type()
                {
                    self.charge(*bp, 1)?;
                    let t = self.index(*pos, k, args)?;
                    return Ok(Some(Out::Made(Value::Type(t))));
                }
                fail(
                    Code::S010,
                    *pos,
                    "slice 1 indexes only `UInt` and `SInt`".to_owned(),
                )
            }
            Expr::Field { pos, base, field } => {
                let b = self.eval(base)?;
                let b = need(base, b)?;
                fail(
                    Code::S010,
                    *pos,
                    format!(
                        "{} has no field `{}`",
                        self.store.view(&b).text(),
                        field.name
                    ),
                )
            }
        }
    }

    /// A binary operator with static operands. A static integer next to a finite operand
    /// takes the type of that operand first.
    fn binary(&mut self, pos: Pos, op: BinOp, a: &Out, b: &Out) -> Res<Value> {
        let (va, vb) = (self.store.view(a), self.store.view(b));
        let mut ca = None;
        let mut cb = None;
        if ops::unifies(op) {
            match (va, vb, va.finite_ty(), vb.finite_ty()) {
                (Value::Int(_), _, _, Some(t)) => {
                    ca = ops::convert(t, va, &mut self.fuel).map_err(at(pos))?;
                }
                (_, Value::Int(_), Some(t), _) => {
                    cb = ops::convert(t, vb, &mut self.fuel).map_err(at(pos))?;
                }
                _ => {}
            }
        }
        let va = ca.as_ref().unwrap_or(va);
        let vb = cb.as_ref().unwrap_or(vb);
        ops::binary(op, va, vb, &mut self.fuel).map_err(at(pos))
    }

    fn type_expr(&mut self, t: &TypeExpr) -> Res<Ty> {
        self.charge(type_pos(t), 1)?;
        match t {
            TypeExpr::Name { pos, name } => match self.target(*pos) {
                Some(Target::Prelude(k)) if k.is_type() => prim(*pos, name, k),
                _ => fail(Code::S010, *pos, format!("`{name}` is not a type")),
            },
            TypeExpr::Index { pos, base, args } => match &**base {
                TypeExpr::Name { pos: bp, name } => {
                    self.charge(*bp, 1)?;
                    match self.target(*bp) {
                        Some(Target::Prelude(k)) if k.is_type() => self.index(*pos, k, args),
                        _ => fail(Code::S010, *bp, format!("`{name}` is not a type")),
                    }
                }
                TypeExpr::Index { .. } => fail(
                    Code::S007,
                    *pos,
                    "a complete type takes no more index".to_owned(),
                ),
            },
        }
    }

    /// `UInt[e]` or `SInt[e]` in a type or an expression. The base charged its node.
    fn index(&mut self, pos: Pos, k: Prelude, xs: &[Expr]) -> Res<Ty> {
        let outs = self.args(xs)?;
        let views: Vec<&Value> = outs.iter().map(|o| self.store.view(o)).collect();
        let t = ops::family(k, &views).map_err(at(pos))?;
        self.charge(pos, u128::from(Value::Type(t).size()))?;
        Ok(t)
    }

    /// A name. A constant evaluates at its first use, in the table of constants.
    fn name(&mut self, pos: Pos, x: &str) -> Res<Out> {
        match self.target(pos) {
            Some(Target::Prelude(k)) if k.is_type() => {
                Ok(Out::Named(Value::Type(prim(pos, x, k)?)))
            }
            Some(Target::Decl(id)) => match self.file.decl(id).kind {
                Kind::Const => self.constant(pos, x, id),
                Kind::Fn | Kind::Module => fail(
                    Code::S010,
                    pos,
                    format!("`{x}` is a function; slice 1 has no function values"),
                ),
                _ => {
                    let k = self.store.frames.len().saturating_sub(1);
                    if self.store.frame().is_some_and(|f| f.contains_key(&id)) {
                        Ok(Out::Local(k, id))
                    } else {
                        fail(Code::S011, pos, format!("`{x}` is not a static value"))
                    }
                }
            },
            _ => fail(
                Code::S010,
                pos,
                format!("`{x}` is a function; slice 1 has no function values"),
            ),
        }
    }

    fn constant(&mut self, pos: Pos, x: &str, id: DeclId) -> Res<Out> {
        let file = self.file;
        let Some(&i) = self.items.get(&id) else {
            return fail(Code::S010, pos, format!("`{x}` is not an item"));
        };
        let Some(Item::Const {
            pos: cp, ty, value, ..
        }) = file.ast().get(i)
        else {
            return fail(Code::S010, pos, format!("`{x}` is not a constant"));
        };
        match self.store.consts.get(i) {
            Some(Entry::Done(_)) => return Ok(Out::Const(i)),
            Some(Entry::InProgress) => {
                return fail(
                    Code::S019,
                    pos,
                    format!("the constant `{x}` depends on itself"),
                );
            }
            _ => {}
        }
        self.nested(pos, |ev| {
            ev.store.consts[i] = Entry::InProgress;
            let c = ev.in_frame(None, |ev| {
                let t = ev.type_expr(ty)?;
                let o = ev.eval(value)?;
                let o = need(value, o)?;
                ev.copy(*cp, &o)?;
                ev.conform(*cp, t, o)
            })?;
            ev.store.consts[i] = Entry::Done(c);
            Ok(Out::Const(i))
        })
    }

    /// A call of a function item, a prelude function, or a type.
    fn call(&mut self, pos: Pos, f: &Expr, xs: &[Expr]) -> Res<Option<Out>> {
        if let Expr::Name { pos: fp, name: g } = f {
            match self.target(*fp) {
                Some(Target::Decl(id))
                    if matches!(
                        self.file.decl(id).kind,
                        Kind::Const | Kind::Fn | Kind::Module
                    ) =>
                {
                    return self.call_fn(pos, *fp, g, id, xs);
                }
                Some(Target::Prelude(h)) if !h.is_type() => {
                    return self.call_prelude(pos, *fp, g, h, xs);
                }
                _ => {}
            }
        }
        let t = self.eval(f)?;
        let t = need(f, t)?;
        match (self.store.view(&t), xs) {
            (Value::Type(t), [x]) => {
                let t = *t;
                let a = self.eval(x)?;
                let a = need(x, a)?;
                self.charge(pos, self.size(&a))?;
                Ok(Some(Out::Made(self.conform(pos, t, a)?)))
            }
            (Value::Type(_), _) => {
                fail(Code::S007, pos, "a constructor takes 1 argument".to_owned())
            }
            (v, _) => fail(Code::S010, pos, format!("{} is not a function", v.text())),
        }
    }

    fn call_fn(&mut self, pos: Pos, fp: Pos, g: &str, id: DeclId, xs: &[Expr]) -> Res<Option<Out>> {
        self.charge(fp, 1)?;
        let file = self.file;
        let item = self.items.get(&id).and_then(|&i| file.ast().get(i));
        let Some(Item::Fn {
            pos: ip,
            name: fname,
            params,
            ret,
            body,
            ..
        }) = item
        else {
            return fail(Code::S010, fp, format!("`{g}` is not a function"));
        };
        let vs = self.args(xs)?;
        if params.len() != vs.len() {
            return fail(
                Code::S007,
                pos,
                format!(
                    "`{g}` takes {} argument(s), but it has {}",
                    params.len(),
                    vs.len()
                ),
            );
        }
        self.nested(pos, |ev| {
            ev.in_frame(None, |ev| {
                for (q, v) in params.iter().zip(vs) {
                    ev.param(pos, q, v)?;
                }
                let rt = ev.type_expr(ret)?;
                ev.ret = Some(rt);
                match ev.block(*ip, body)? {
                    Some(v) => Ok(Some(Out::Made(v))),
                    None => fail(
                        Code::S010,
                        pos,
                        format!("`{}` ends without `return`", fname.name),
                    ),
                }
            })
        })
    }

    /// Binds a parameter of a call. Its type can use the parameters before it.
    fn param(&mut self, pos: Pos, q: &Param, v: Out) -> Res<()> {
        let t = self.type_expr(&q.ty)?;
        self.charge(pos, self.size(&v))?;
        // A static and a hardware parameter conform alike: a static evaluation has only
        // static values.
        let x = self.conform(pos, t, v)?;
        let id = self.decl(&q.name)?;
        self.bind(
            id,
            Slot {
                ty: Some(t),
                mutable: false,
                value: x,
            },
        );
        Ok(())
    }

    fn call_prelude(
        &mut self,
        pos: Pos,
        fp: Pos,
        g: &str,
        builtin: Prelude,
        xs: &[Expr],
    ) -> Res<Option<Out>> {
        self.charge(fp, 1)?;
        let vs = self.args(xs)?;
        let mut sizes = 0u128;
        for v in &vs {
            sizes += self.size(v);
        }
        self.charge(pos, sizes)?;
        let views: Vec<&Value> = vs.iter().map(|o| self.store.view(o)).collect();
        match (builtin, views.as_slice()) {
            (Prelude::Resize | Prelude::Reinterpret, [ty, v]) => {
                let Value::Type(ty) = ty else {
                    return fail(
                        Code::S010,
                        pos,
                        format!("`{g}` needs a type, not {}", ty.text()),
                    );
                };
                let made = if builtin == Prelude::Resize {
                    ops::resize(*ty, v, &mut self.fuel)
                } else {
                    ops::reinterpret(*ty, v, &mut self.fuel)
                };
                Ok(Some(Out::Made(made.map_err(at(pos))?)))
            }
            (Prelude::StaticAssert, [c, m]) => match (c, m) {
                (Value::Bool(true), Value::Str(_)) => Ok(None),
                (Value::Bool(false), Value::Str(m)) => fail(
                    Code::S014,
                    pos,
                    format!("static assertion failed: {}", str_text(m)),
                ),
                (c, m) => fail(
                    Code::S010,
                    pos,
                    format!("`{g}` does not accept [{}, {}]", c.text(), m.text()),
                ),
            },
            (Prelude::Error, [m]) => match m {
                Value::Str(m) => fail(Code::S014, pos, format!("error: {}", str_text(m))),
                m => fail(
                    Code::S010,
                    pos,
                    format!("`{g}` does not accept {}", m.text()),
                ),
            },
            (_, vs) => {
                let texts: Vec<String> = vs.iter().map(|v| v.text()).collect();
                fail(
                    Code::S010,
                    pos,
                    format!("`{g}` does not accept [{}]", texts.join(", ")),
                )
            }
        }
    }

    /// A block at `pos`. It charges as a statement.
    fn block(&mut self, pos: Pos, ss: &[Stmt]) -> Res<Option<Value>> {
        self.charge(pos, 1)?;
        self.stmts(ss)
    }

    fn stmts(&mut self, ss: &[Stmt]) -> Res<Option<Value>> {
        for s in ss {
            if let Some(r) = self.stmt(s)? {
                return Ok(Some(r));
            }
        }
        Ok(None)
    }

    /// A loop bound is a static `Int`.
    fn bound(&self, pos: Pos, out: &Out) -> Res<()> {
        match self.store.view(out) {
            Value::Int(_) => Ok(()),
            v => fail(
                Code::S010,
                pos,
                format!("a loop bound is a static Int, not {}", v.text()),
            ),
        }
    }

    fn local(
        &mut self,
        pos: Pos,
        mutable: bool,
        name: &Ident,
        ty: Option<&TypeExpr>,
        value: &Expr,
    ) -> Res<Option<Value>> {
        let t = match ty {
            Some(ty) => Some(self.type_expr(ty)?),
            None => None,
        };
        let o = self.eval(value)?;
        let o = need(value, o)?;
        self.copy(pos, &o)?;
        let x = match t {
            Some(t) => self.conform(pos, t, o)?,
            None => self.store.take(o),
        };
        let id = self.decl(name)?;
        let ty = t.or_else(|| x.ty());
        self.bind(
            id,
            Slot {
                ty,
                mutable,
                value: x,
            },
        );
        Ok(None)
    }

    /// An assignment to a `let mut` local. The target is a place, so it charges nothing.
    fn assign(&mut self, pos: Pos, target: &Expr, value: &Expr) -> Res<Option<Value>> {
        let place = match target {
            Expr::Name { pos: tp, .. } => match self.target(*tp) {
                Some(Target::Decl(id)) => self
                    .store
                    .frame()
                    .and_then(|f| f.get(&id))
                    .filter(|s| s.mutable)
                    .map(|s| (id, s.ty)),
                _ => None,
            },
            _ => None,
        };
        let Some((id, ty)) = place else {
            return fail(
                Code::S010,
                pos,
                "an assignment target is a `let mut` local".to_owned(),
            );
        };
        let o = self.eval(value)?;
        let o = need(value, o)?;
        self.copy(pos, &o)?;
        let y = if let Some(t) = ty {
            self.conform(pos, t, o)?
        } else {
            let old = self
                .store
                .frame()
                .and_then(|f| f.get(&id))
                .map_or(&ABSENT, |s| &s.value);
            let new = self.store.view(&o);
            if !same_form(old, new) {
                return fail(
                    Code::S010,
                    pos,
                    format!("expected {}, but the value is {}", old.text(), new.text()),
                );
            }
            self.store.take(o)
        };
        if let Some(slot) = self.store.frame_mut().and_then(|f| f.get_mut(&id)) {
            slot.value = y;
        }
        Ok(None)
    }

    /// A statement. The result is the value of a `return`.
    fn stmt(&mut self, s: &Stmt) -> Res<Option<Value>> {
        self.charge(stmt_pos(s), 1)?;
        match s {
            Stmt::Local {
                pos,
                mutable,
                name,
                ty,
                value,
            } => self.local(*pos, *mutable, name, ty.as_ref(), value),
            Stmt::Assign { pos, target, value } => self.assign(*pos, target, value),
            Stmt::Ret { pos, value } => {
                let Some(rt) = self.ret else {
                    return fail(Code::S006, *pos, "only a function has `return`".to_owned());
                };
                let Some(value) = value else {
                    return fail(
                        Code::S010,
                        *pos,
                        format!("`return` needs a value of {}", rt.text()),
                    );
                };
                let o = self.eval(value)?;
                let o = need(value, o)?;
                self.charge(*pos, self.size(&o))?;
                Ok(Some(self.conform(*pos, rt, o)?))
            }
            Stmt::CtIf { pos, cond, yes, no } => {
                let c = self.eval(cond)?;
                let c = need(cond, c)?;
                if test(*pos, self.store.view(&c))? {
                    self.block(*pos, yes)
                } else {
                    match no {
                        Some(no) => self.block(*pos, no),
                        None => Ok(None),
                    }
                }
            }
            Stmt::CtFor {
                pos,
                var,
                lo,
                hi,
                body,
            } => self.ct_for(*pos, var, lo, hi, body),
            Stmt::Block { body, .. } => self.stmts(body),
            Stmt::Expr { value, .. } => {
                self.eval(value)?;
                Ok(None)
            }
            Stmt::Connect { pos, .. }
            | Stmt::Reg { pos, .. }
            | Stmt::Wire { pos, .. }
            | Stmt::Input { pos, .. }
            | Stmt::Output { pos, .. }
            | Stmt::Inst { pos, .. } => fail(
                Code::S011,
                *pos,
                "a static evaluation makes no hardware".to_owned(),
            ),
        }
    }

    /// A `comptime for`. It charges the sizes of both bounds for the range, then each loop
    /// value before it binds it. The charge of the loop value `v` also pays the work of the
    /// next value `v + 1`.
    fn ct_for(
        &mut self,
        pos: Pos,
        var: &Ident,
        lo: &Expr,
        hi: &Expr,
        body: &[Stmt],
    ) -> Res<Option<Value>> {
        let a = self.eval(lo)?;
        let a = need(lo, a)?;
        self.bound(pos, &a)?;
        let z = self.eval(hi)?;
        let z = need(hi, z)?;
        self.bound(pos, &z)?;
        let sizes = self.size(&a) + self.size(&z);
        self.charge(pos, sizes)?;
        let (Value::Int(mut v), Value::Int(z)) = (self.store.take(a), self.store.take(z)) else {
            return Ok(None);
        };
        let id = self.decl(var)?;
        let one = Int::from_u64(1);
        while v < z {
            self.charge(pos, u128::from(int_size(&v)))?;
            self.bind(
                id,
                Slot {
                    ty: Some(Ty::Int),
                    mutable: false,
                    value: Value::Int(v.clone()),
                },
            );
            if let Some(r) = self.block(pos, body)? {
                return Ok(Some(r));
            }
            v = v.add(&one);
        }
        Ok(None)
    }
}
