// SPDX-License-Identifier: Apache-2.0
//! The static evaluator of the generator: static `Int` and `Bool` with the
//! semantics of v0.1 section 3. It is a third implementation of these
//! rules, next to the two front ends, so the `eval` probe compares it.

use super::program::{ComptimeFn, Item, SBin, SExpr, STy, Scalar, Ty, Un};
use num_bigint::{BigInt, BigUint, Sign};
use std::collections::BTreeMap;

/// A static value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Value {
    Int(BigInt),
    Bool(bool),
    Tuple(Vec<Value>),
    /// An array of at least one element, all of one type.
    Array(Vec<Value>),
}

impl Value {
    /// The serialization that `eval` prints (front-end spec 7.1). An array
    /// names its element type, which its first element gives.
    pub(crate) fn serialize(&self) -> String {
        match self {
            Value::Int(n) => format!("(int {n})"),
            Value::Bool(b) => format!("(bool {b})"),
            Value::Tuple(xs) => format!("(tuple ({}))", serialized(xs)),
            Value::Array(xs) => {
                let elem = xs.first().map_or_else(String::new, |x| x.ty().serialize());
                format!("(array {elem} ({}))", serialized(xs))
            }
        }
    }

    /// The spelling of the value as an argument of the top selection.
    pub(crate) fn spelling(&self) -> String {
        match self {
            Value::Int(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Tuple(xs) if xs.len() == 1 => format!("({},)", spelled(xs)),
            Value::Tuple(xs) => format!("({})", spelled(xs)),
            Value::Array(xs) => format!("[{}]", spelled(xs)),
        }
    }

    /// The type of the value. A `Nat` has the type `Int`, as in the
    /// front ends, so a value never has the type `Nat`.
    pub(crate) fn ty(&self) -> STy {
        match self {
            Value::Int(_) => STy::Int,
            Value::Bool(_) => STy::Bool,
            Value::Tuple(xs) => STy::Tuple(xs.iter().map(Value::ty).collect()),
            Value::Array(xs) => STy::Array(
                Box::new(xs.first().map_or(STy::Int, Value::ty)),
                u32::try_from(xs.len()).unwrap_or(u32::MAX),
            ),
        }
    }
}

fn serialized(xs: &[Value]) -> String {
    xs.iter()
        .map(Value::serialize)
        .collect::<Vec<_>>()
        .join(" ")
}

fn spelled(xs: &[Value]) -> String {
    xs.iter()
        .map(Value::spelling)
        .collect::<Vec<_>>()
        .join(", ")
}

impl STy {
    /// The serialization of the type (front-end spec 7.1).
    fn serialize(&self) -> String {
        match self {
            STy::Nat => "nat".to_owned(),
            STy::Int => "int".to_owned(),
            STy::Bool => "bool".to_owned(),
            STy::Tuple(ts) => format!(
                "(tuple ({}))",
                ts.iter().map(STy::serialize).collect::<Vec<_>>().join(" ")
            ),
            STy::Array(t, n) => format!("(array {} {n})", t.serialize()),
        }
    }
}

/// Why a static expression has no value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fault {
    /// `/` or `%` by zero (`S013`).
    Div,
    /// A negative shift count (`S013`).
    Shift,
    /// A negative `Nat` (`S012`).
    Nat,
    /// A value outside the bounds of the generator.
    Bound,
    /// An operand of the wrong type or an unknown name: a generator bug.
    Type,
}

/// The static bindings in scope: parameters, static `let`s, and loop binders.
#[derive(Clone, Debug, Default)]
pub(crate) struct Env {
    pub(crate) statics: BTreeMap<String, Value>,
}

impl Env {
    /// The env of a module context: each parameter bound to its argument.
    pub(crate) fn of(params: &[(String, STy)], args: &[Value]) -> Env {
        Env {
            statics: params
                .iter()
                .map(|(n, _)| n.clone())
                .zip(args.iter().cloned())
                .collect(),
        }
    }
}

/// The binder values of `comptime for` over the half-open `lo..hi`.
pub(crate) fn loop_values(lo: &BigInt, hi: &BigInt) -> impl Iterator<Item = Value> {
    let hi = hi.clone();
    std::iter::successors(Some(lo.clone()), |n| Some(n + 1))
        .take_while(move |n| *n < hi)
        .map(Value::Int)
}

/// The file scope: the `comptime fn`s and the values of the `const`s.
#[derive(Clone, Debug, Default)]
pub(crate) struct Scope {
    fns: BTreeMap<String, ComptimeFn>,
    consts: BTreeMap<String, Value>,
}

impl Scope {
    /// The scope of the items: all `comptime fn`s, then each `const` in item
    /// order. A `const` can read only earlier ones. Each `const` evaluates
    /// here, not at its first use, so a faulting `const` that nothing reads
    /// faults here but not in the language: stricter on purpose.
    pub(crate) fn new(items: &[Item]) -> Result<Scope, Fault> {
        let mut scope = Scope::default();
        for item in items {
            if let Item::ComptimeFn(f) = item {
                scope.fns.insert(f.name.clone(), f.clone());
            }
        }
        for item in items {
            if let Item::Const { name, ty, value } = item {
                let v = eval(value, &Env::default(), &scope)?;
                scope.consts.insert(name.clone(), typed(ty, v)?);
            }
        }
        Ok(scope)
    }
}

/// Every value that the generator makes stays within `-BOUND..=BOUND`.
pub(crate) const BOUND: u32 = 1 << 20;
/// The largest count of an `Int` left shift.
const MAX_SHIFT: u32 = 20;
/// The most active `comptime fn` calls; the native stack stays small.
const MAX_DEPTH: u32 = 64;
/// The most `comptime fn` calls of one evaluation.
const MAX_CALLS: u32 = 4096;
/// The widths of `UInt[w]` and `SInt[w]` (front-end `MAX_WIDTH`).
const MAX_WIDTH: u32 = 65536;

/// The value of a static expression, as both front ends compute it, or the
/// first fault in evaluation order.
pub(crate) fn eval(e: &SExpr, env: &Env, scope: &Scope) -> Result<Value, Fault> {
    Evaluator {
        scope,
        calls: 0,
        depth: 0,
    }
    .eval(e, env)
}

/// The type of `t` with its width evaluated.
pub(crate) fn concrete(t: &Ty, env: &Env, scope: &Scope) -> Result<Scalar, Fault> {
    let width = |w: &SExpr| -> Result<u32, Fault> {
        let w = int(eval(w, env, scope)?)?;
        u32::try_from(&w)
            .ok()
            .filter(|w| (1..=MAX_WIDTH).contains(w))
            .ok_or(Fault::Bound)
    };
    Ok(match t {
        Ty::Bool => Scalar::Bool,
        Ty::UInt(w) => Scalar::UInt(width(w)?),
        Ty::SInt(w) => Scalar::SInt(width(w)?),
    })
}

struct Evaluator<'a> {
    scope: &'a Scope,
    calls: u32,
    depth: u32,
}

impl Evaluator<'_> {
    fn eval(&mut self, e: &SExpr, env: &Env) -> Result<Value, Fault> {
        let v = match e {
            SExpr::Int(n, _) => Value::Int(n.clone()),
            SExpr::Bool(b) => Value::Bool(*b),
            SExpr::Name(n) => env
                .statics
                .get(n)
                .or_else(|| self.scope.consts.get(n))
                .cloned()
                .ok_or(Fault::Type)?,
            SExpr::Call(f, args) => self.call(f, args, env)?,
            SExpr::Tuple(xs) => Value::Tuple(self.all(xs, env)?),
            SExpr::Array(xs) if xs.is_empty() => return Err(Fault::Type),
            SExpr::Array(xs) => Value::Array(self.all(xs, env)?),
            SExpr::Index(base, index) => {
                let base = self.eval(base, env)?;
                let index = int(self.eval(index, env)?)?;
                match base {
                    Value::Array(xs) => usize::try_from(&index)
                        .ok()
                        .and_then(|i| xs.into_iter().nth(i))
                        .ok_or(Fault::Bound)?,
                    _ => return Err(Fault::Type),
                }
            }
            SExpr::Select(base, k, _) => match self.eval(base, env)? {
                Value::Tuple(xs) => xs.into_iter().nth(*k as usize).ok_or(Fault::Bound)?,
                _ => return Err(Fault::Type),
            },
            SExpr::Len(base) => match self.eval(base, env)? {
                Value::Array(xs) => Value::Int(BigInt::from(xs.len())),
                _ => return Err(Fault::Type),
            },
            SExpr::Unary(op, a) => match (op, self.eval(a, env)?) {
                (Un::Neg, Value::Int(n)) => Value::Int(-n),
                (Un::Inv, Value::Int(n)) => Value::Int(!n),
                (Un::Not, Value::Bool(b)) => Value::Bool(!b),
                _ => return Err(Fault::Type),
            },
            SExpr::Binary(SBin::Land, a, b) => {
                Value::Bool(boolean(&self.eval(a, env)?)? && boolean(&self.eval(b, env)?)?)
            }
            SExpr::Binary(SBin::Lor, a, b) => {
                Value::Bool(boolean(&self.eval(a, env)?)? || boolean(&self.eval(b, env)?)?)
            }
            SExpr::Binary(op, a, b) => {
                let a = self.eval(a, env)?;
                let b = self.eval(b, env)?;
                binary(*op, a, b)?
            }
            SExpr::If(c, t, e) => {
                if boolean(&self.eval(c, env)?)? {
                    self.eval(t, env)?
                } else {
                    self.eval(e, env)?
                }
            }
        };
        bounded(v)
    }

    /// The values of `xs`, left to right.
    fn all(&mut self, xs: &[SExpr], env: &Env) -> Result<Vec<Value>, Fault> {
        xs.iter().map(|x| self.eval(x, env)).collect()
    }

    /// The template of `ComptimeFn`: the base when the first formal is 0,
    /// else the step. Each formal and the result check their type.
    fn call(&mut self, f: &str, args: &[SExpr], env: &Env) -> Result<Value, Fault> {
        let scope = self.scope;
        let def = scope.fns.get(f).ok_or(Fault::Type)?;
        if args.len() != def.params.len() {
            return Err(Fault::Type);
        }
        let mut inner = Env::default();
        for (arg, (name, ty)) in args.iter().zip(&def.params) {
            let v = self.eval(arg, env)?;
            inner.statics.insert(name.clone(), typed(ty, v)?);
        }
        self.calls += 1;
        if self.calls > MAX_CALLS || self.depth >= MAX_DEPTH {
            return Err(Fault::Bound);
        }
        // The template compares the first formal with `0`; a `Bool` there is
        // `S010` in both front ends.
        let Some(Value::Int(first)) = def
            .params
            .first()
            .and_then(|(name, _)| inner.statics.get(name))
        else {
            return Err(Fault::Type);
        };
        let body = if *first == BigInt::ZERO {
            &def.base
        } else {
            &def.step
        };
        self.depth += 1;
        let v = self.eval(body, &inner);
        self.depth -= 1;
        typed(&def.ret, v?)
    }
}

/// An operator other than `&&` and `||`, after both operands.
fn binary(op: SBin, a: Value, b: Value) -> Result<Value, Fault> {
    let v = match (a, b) {
        (Value::Bool(x), Value::Bool(y)) => match op {
            SBin::Eq => x == y,
            SBin::Ne => x != y,
            _ => return Err(Fault::Type),
        },
        (Value::Int(x), Value::Int(y)) => match op {
            SBin::Eq => x == y,
            SBin::Ne => x != y,
            SBin::Lt => x < y,
            SBin::Le => x <= y,
            SBin::Gt => x > y,
            SBin::Ge => x >= y,
            _ => return arith(op, x, y).map(Value::Int),
        },
        _ => return Err(Fault::Type),
    };
    Ok(Value::Bool(v))
}

/// `num-bigint` has the rules of v0.1 section 3: `/` truncates toward zero,
/// `%` takes the sign of the dividend, `>>` rounds toward negative infinity,
/// and `!`, `&`, `|`, `^` work on infinite two's complement.
fn arith(op: SBin, x: BigInt, y: BigInt) -> Result<BigInt, Fault> {
    Ok(match op {
        SBin::Add => x + y,
        SBin::Sub => x - y,
        SBin::Mul => x * y,
        SBin::Div | SBin::Rem if y == BigInt::ZERO => return Err(Fault::Div),
        SBin::Div => x / y,
        SBin::Rem => x % y,
        SBin::And => x & y,
        SBin::Or => x | y,
        SBin::Xor => x ^ y,
        SBin::Shl => x << count(&y, MAX_SHIFT)?,
        SBin::Shr => x >> count(&y, BOUND)?,
        _ => return Err(Fault::Type),
    })
}

/// A shift count: negative is `Shift`, above `max` is `Bound`.
fn count(k: &BigInt, max: u32) -> Result<u32, Fault> {
    if k.sign() == Sign::Minus {
        return Err(Fault::Shift);
    }
    u32::try_from(k)
        .ok()
        .filter(|k| *k <= max)
        .ok_or(Fault::Bound)
}

fn bounded(v: Value) -> Result<Value, Fault> {
    match &v {
        Value::Int(n) if n.magnitude() > &BigUint::from(BOUND) => Err(Fault::Bound),
        _ => Ok(v),
    }
}

fn boolean(v: &Value) -> Result<bool, Fault> {
    match v {
        Value::Bool(b) => Ok(*b),
        _ => Err(Fault::Type),
    }
}

fn int(v: Value) -> Result<BigInt, Fault> {
    match v {
        Value::Int(n) => Ok(n),
        _ => Err(Fault::Type),
    }
}

/// A typed use of `v` at a static type: a `Nat` must not be negative, and
/// a container has the shape of its type.
fn typed(ty: &STy, v: Value) -> Result<Value, Fault> {
    match (ty, &v) {
        (STy::Nat, Value::Int(n)) if n.sign() == Sign::Minus => Err(Fault::Nat),
        (STy::Nat | STy::Int, Value::Int(_)) | (STy::Bool, Value::Bool(_)) => Ok(v),
        (STy::Tuple(ts), Value::Tuple(xs)) if ts.len() == xs.len() => {
            Ok(Value::Tuple(typed_all(ts.iter(), xs.iter().cloned())?))
        }
        (STy::Array(t, n), Value::Array(xs)) if *n as usize == xs.len() => Ok(Value::Array(
            typed_all(std::iter::repeat_n(&**t, xs.len()), xs.iter().cloned())?,
        )),
        _ => Err(Fault::Type),
    }
}

fn typed_all<'t>(
    tys: impl Iterator<Item = &'t STy>,
    vs: impl Iterator<Item = Value>,
) -> Result<Vec<Value>, Fault> {
    tys.zip(vs).map(|(t, v)| typed(t, v)).collect()
}

#[cfg(test)]
mod tests {
    use super::super::program::Radix;
    use super::*;

    fn int(n: i64) -> SExpr {
        SExpr::Int(BigInt::from(n), Radix::Dec)
    }

    fn bin(op: SBin, a: SExpr, b: SExpr) -> SExpr {
        SExpr::Binary(op, Box::new(a), Box::new(b))
    }

    fn un(op: Un, a: SExpr) -> SExpr {
        SExpr::Unary(op, Box::new(a))
    }

    fn name(n: &str) -> SExpr {
        SExpr::Name(n.to_owned())
    }

    fn run(e: &SExpr) -> Result<Value, Fault> {
        eval(e, &Env::default(), &Scope::default())
    }

    #[expect(clippy::unnecessary_wraps, reason = "it compares with results")]
    fn value(n: i64) -> Result<Value, Fault> {
        Ok(Value::Int(BigInt::from(n)))
    }

    #[test]
    fn int_ops_match_the_language() {
        assert_eq!(run(&bin(SBin::Div, int(-7), int(2))), value(-3));
        assert_eq!(run(&bin(SBin::Rem, int(-7), int(2))), value(-1));
        assert_eq!(run(&bin(SBin::Rem, int(7), int(-2))), value(1));
        assert_eq!(run(&bin(SBin::Shr, int(-3), int(1))), value(-2));
        assert_eq!(run(&bin(SBin::Shl, int(1), int(8))), value(256));
        assert_eq!(run(&un(Un::Inv, int(5))), value(-6));
        assert_eq!(run(&bin(SBin::And, int(-6), int(3))), value(2));
        assert_eq!(run(&bin(SBin::Or, int(-6), int(1))), value(-5));
        assert_eq!(run(&bin(SBin::Xor, int(-6), int(3))), value(-7));
        assert_eq!(run(&un(Un::Neg, int(4))), value(-4));
        assert_eq!(run(&bin(SBin::Sub, int(2), int(9))), value(-7));
        let fault = bin(SBin::Eq, bin(SBin::Div, int(1), int(0)), int(0));
        let short = bin(SBin::Land, SExpr::Bool(false), fault.clone());
        assert_eq!(run(&short), Ok(Value::Bool(false)));
        let short = bin(SBin::Lor, SExpr::Bool(true), fault);
        assert_eq!(run(&short), Ok(Value::Bool(true)));
        assert_eq!(run(&bin(SBin::Lt, int(-1), int(0))), Ok(Value::Bool(true)));
        assert_eq!(
            run(&bin(SBin::Ne, SExpr::Bool(true), SExpr::Bool(false))),
            Ok(Value::Bool(true))
        );
        let select = SExpr::If(
            Box::new(SExpr::Bool(false)),
            Box::new(bin(SBin::Div, int(1), int(0))),
            Box::new(int(3)),
        );
        assert_eq!(run(&select), value(3));
    }

    #[test]
    fn faults_and_bounds_are_errors() {
        assert_eq!(run(&bin(SBin::Div, int(1), int(0))), Err(Fault::Div));
        assert_eq!(run(&bin(SBin::Rem, int(1), int(0))), Err(Fault::Div));
        assert_eq!(run(&bin(SBin::Shl, int(1), int(-1))), Err(Fault::Shift));
        assert_eq!(run(&bin(SBin::Shr, int(1), int(-1))), Err(Fault::Shift));
        assert_eq!(run(&bin(SBin::Shl, int(1), int(21))), Err(Fault::Bound));
        assert_eq!(run(&bin(SBin::Shl, int(0), int(21))), Err(Fault::Bound));
        assert_eq!(run(&bin(SBin::Shl, int(1), int(20))), value(1 << 20));
        let big = bin(SBin::Mul, bin(SBin::Shl, int(1), int(20)), int(2));
        assert_eq!(run(&big), Err(Fault::Bound));
        assert_eq!(run(&int((1 << 20) + 1)), Err(Fault::Bound));
        assert_eq!(
            run(&bin(SBin::Add, int(1), SExpr::Bool(true))),
            Err(Fault::Type)
        );
        assert_eq!(run(&name("P0")), Err(Fault::Type));
    }

    fn twice() -> Vec<Item> {
        let step = bin(
            SBin::Add,
            SExpr::Call(
                "f".to_owned(),
                vec![
                    bin(SBin::Sub, name("x0"), int(1)),
                    bin(SBin::Mul, name("x1"), int(2)),
                ],
            ),
            int(1),
        );
        vec![
            Item::Const {
                name: "C0".to_owned(),
                ty: STy::Nat,
                value: SExpr::Call("f".to_owned(), vec![int(2), int(1)]),
            },
            Item::ComptimeFn(ComptimeFn {
                name: "f".to_owned(),
                params: vec![("x0".to_owned(), STy::Nat), ("x1".to_owned(), STy::Int)],
                ret: STy::Int,
                base: name("x1"),
                step,
            }),
        ]
    }

    #[test]
    fn calls_recurse_structurally() {
        let scope = Scope::new(&twice());
        let Ok(scope) = scope else {
            panic!("the scope faults: {scope:?}");
        };
        let call = |a: i64, b: i64| {
            eval(
                &SExpr::Call("f".to_owned(), vec![int(a), int(b)]),
                &Env::default(),
                &scope,
            )
        };
        assert_eq!(call(3, 1), value(11));
        assert_eq!(call(0, -4), value(-4));
        assert_eq!(call(-1, 0), Err(Fault::Nat));
        assert_eq!(call(70, 0), Err(Fault::Bound));
        assert_eq!(eval(&name("C0"), &Env::default(), &scope), value(6));
        let mut env = Env::default();
        env.statics
            .insert("x1".to_owned(), Value::Int(BigInt::from(5)));
        assert_eq!(eval(&name("x1"), &env, &scope), value(5));
    }

    #[test]
    fn a_bool_first_formal_is_a_type_fault() {
        let f2 = Item::ComptimeFn(ComptimeFn {
            name: "f2".to_owned(),
            params: vec![("x0".to_owned(), STy::Bool)],
            ret: STy::Int,
            base: int(1),
            step: int(2),
        });
        let Ok(scope) = Scope::new(&[f2]) else {
            panic!("the scope faults");
        };
        let call = SExpr::Call("f2".to_owned(), vec![SExpr::Bool(true)]);
        assert_eq!(eval(&call, &Env::default(), &scope), Err(Fault::Type));
    }

    #[test]
    fn nat_results_and_consts_are_checked() {
        let mut items = twice();
        if let Some(Item::ComptimeFn(f)) = items.get_mut(1) {
            f.ret = STy::Nat;
        }
        let Ok(scope) = Scope::new(&items) else {
            panic!("the scope faults");
        };
        let call = SExpr::Call("f".to_owned(), vec![int(1), int(-4)]);
        assert_eq!(eval(&call, &Env::default(), &scope), Err(Fault::Nat));
        let negative = Item::Const {
            name: "C1".to_owned(),
            ty: STy::Nat,
            value: int(-1),
        };
        assert_eq!(Scope::new(&[negative]).map(|_| ()), Err(Fault::Nat));
        let later = Item::Const {
            name: "C2".to_owned(),
            ty: STy::Int,
            value: name("C3"),
        };
        assert_eq!(Scope::new(&[later]).map(|_| ()), Err(Fault::Type));
    }

    #[test]
    fn widths_evaluate_to_concrete_types() {
        let mut env = Env::default();
        env.statics
            .insert("P0".to_owned(), Value::Int(BigInt::from(3)));
        let scope = Scope::default();
        let w = bin(SBin::Add, name("P0"), int(5));
        assert_eq!(
            concrete(&Ty::UInt(w.clone()), &env, &scope),
            Ok(Scalar::UInt(8))
        );
        assert_eq!(concrete(&Ty::SInt(w), &env, &scope), Ok(Scalar::SInt(8)));
        assert_eq!(concrete(&Ty::Bool, &env, &scope), Ok(Scalar::Bool));
        assert_eq!(concrete(&Ty::UInt(int(0)), &env, &scope), Err(Fault::Bound));
        assert_eq!(
            concrete(&Ty::UInt(int(65537)), &env, &scope),
            Err(Fault::Bound)
        );
        assert_eq!(
            concrete(&Ty::UInt(SExpr::Bool(true)), &env, &scope),
            Err(Fault::Type)
        );
    }

    fn array(xs: Vec<SExpr>) -> SExpr {
        SExpr::Array(xs)
    }

    fn tuple(xs: Vec<SExpr>) -> SExpr {
        SExpr::Tuple(xs)
    }

    fn index(base: SExpr, i: SExpr) -> SExpr {
        SExpr::Index(Box::new(base), Box::new(i))
    }

    fn select(base: SExpr, k: u32) -> SExpr {
        SExpr::Select(Box::new(base), k, Radix::Dec)
    }

    #[test]
    fn containers_index_select_and_measure() {
        let a = array(vec![int(10), int(20), int(30)]);
        assert_eq!(run(&index(a.clone(), int(1))), value(20));
        assert_eq!(run(&SExpr::Len(Box::new(a.clone()))), value(3));
        let t = tuple(vec![int(7), SExpr::Bool(true)]);
        assert_eq!(run(&select(t.clone(), 1)), Ok(Value::Bool(true)));
        assert_eq!(run(&index(a.clone(), int(3))), Err(Fault::Bound));
        assert_eq!(run(&index(a.clone(), int(-1))), Err(Fault::Bound));
        assert_eq!(run(&select(t.clone(), 2)), Err(Fault::Bound));
        assert_eq!(run(&index(t.clone(), int(0))), Err(Fault::Type));
        assert_eq!(run(&select(a.clone(), 0)), Err(Fault::Type));
        assert_eq!(run(&SExpr::Len(Box::new(t))), Err(Fault::Type));
        assert_eq!(run(&array(vec![])), Err(Fault::Type));
        let nested = array(vec![
            tuple(vec![int(1), int(2)]),
            tuple(vec![int(3), int(4)]),
        ]);
        assert_eq!(run(&select(index(nested, int(1)), 0)), value(3));
        // The base evaluates before the index.
        let late = index(a, bin(SBin::Div, int(1), int(0)));
        assert_eq!(run(&late), Err(Fault::Div));
    }

    #[test]
    fn containers_serialize_with_their_element_type() {
        let pair = tuple(vec![int(1), SExpr::Bool(true)]);
        assert_eq!(
            run(&pair).map(|v| v.serialize()),
            Ok("(tuple ((int 1) (bool true)))".to_owned())
        );
        assert_eq!(
            run(&tuple(vec![int(1)])).map(|v| v.serialize()),
            Ok("(tuple ((int 1)))".to_owned())
        );
        assert_eq!(
            run(&array(vec![pair])).map(|v| v.serialize()),
            Ok("(array (tuple (int bool)) ((tuple ((int 1) (bool true)))))".to_owned())
        );
        let rows = array(vec![array(vec![int(1)]), array(vec![int(-2)])]);
        assert_eq!(
            run(&rows).map(|v| v.serialize()),
            Ok("(array (array int 1) ((array int ((int 1))) (array int ((int -2)))))".to_owned())
        );
    }

    #[test]
    fn typed_containers_have_the_shape_of_their_type() {
        let ty = STy::Array(Box::new(STy::Tuple(vec![STy::Int, STy::Bool])), 1);
        let pair = Value::Tuple(vec![Value::Int(BigInt::from(1)), Value::Bool(true)]);
        let ok = Value::Array(vec![pair.clone()]);
        assert_eq!(typed(&ty, ok.clone()), Ok(ok));
        let two = Value::Array(vec![pair.clone(), pair]);
        assert_eq!(typed(&ty, two), Err(Fault::Type));
        let nat = STy::Array(Box::new(STy::Nat), 1);
        let negative = Value::Array(vec![Value::Int(BigInt::from(-1))]);
        assert_eq!(typed(&nat, negative), Err(Fault::Nat));
    }

    #[test]
    fn values_serialize_like_eval() {
        assert_eq!(Value::Int(BigInt::from(-5)).serialize(), "(int -5)");
        assert_eq!(Value::Bool(true).serialize(), "(bool true)");
        assert_eq!(Value::Bool(false).serialize(), "(bool false)");
    }
}
