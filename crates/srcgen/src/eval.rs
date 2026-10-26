// SPDX-License-Identifier: Apache-2.0
//! The static evaluator of the generator: static `Int` and `Bool` with the
//! semantics of v0.1 section 3. It is a third implementation of these
//! rules, next to the two front ends, so the `eval` probe compares it.

use super::program::{
    ComptimeFn, EnumDef, FieldTy, FnTy, Item, ListFn, Match, MutFn, Pattern, RecTy, SBin, SExpr,
    STy, Scalar, Stmt, StructDef, Ty, Un, string,
};
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
    /// A finite static integer; only the zero of a record makes one.
    UInt(u32, BigInt),
    SInt(u32, BigInt),
    /// A record: its type, and its field values in declaration order.
    Record(Box<RecTy>, Vec<Value>),
    Str(String),
    /// A list: its element type (`Int` or `Nat`), and its elements.
    List(STy, Vec<Value>),
    /// A function value: the item and its function type.
    Function(String, FnTy),
    /// An enum value: the enum, its tag, and its packed payload bits. The
    /// tag can be one that no variant declares.
    Enum(Box<EnumDef>, BigUint, BigUint),
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
            Value::Function(item, _) => format!("(function root {item})"),
            Value::Str(s) => format!("(string {})", string(s)),
            Value::List(t, xs) => format!("(list {} ({}))", t.serialize(), serialized(xs)),
            Value::UInt(w, n) => format!("(uint {w} {n})"),
            Value::SInt(w, n) => format!("(sint {w} {n})"),
            Value::Record(t, xs) => format!(
                "(record {} ({}))",
                STy::Record(t.clone()).serialize(),
                serialized(xs)
            ),
            Value::Enum(def, tag, payload) => {
                let ty = STy::Enum(def.clone()).serialize();
                match def.payload_bits() {
                    0 => format!("(enum {ty} {tag})"),
                    p => format!("(enum {ty} {tag} (uint {p} {payload}))"),
                }
            }
        }
    }

    /// The spelling of the value as an argument of the top selection.
    pub(crate) fn spelling(&self) -> String {
        match self {
            Value::Bool(b) => b.to_string(),
            Value::Tuple(xs) if xs.len() == 1 => format!("({},)", spelled(xs)),
            Value::Tuple(xs) => format!("({})", spelled(xs)),
            Value::Array(xs) => format!("[{}]", spelled(xs)),
            Value::Int(n) | Value::UInt(_, n) | Value::SInt(_, n) => n.to_string(),
            Value::Function(item, _) => item.clone(),
            Value::Str(s) => string(s),
            Value::List(t, _) => format!("list({})", t.text()),
            Value::Record(t, xs) => format!("{}({})", STy::Record(t.clone()).text(), spelled(xs)),
            Value::Enum(def, ..) => format!(
                "reinterpret({}, UInt[{}]({}))",
                def.name,
                def.data_bits(),
                self.bits()
            ),
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
            Value::Function(_, t) => STy::Fn(Box::new(t.clone())),
            Value::Str(_) => STy::Str,
            Value::List(t, _) => STy::List(Box::new(t.clone())),
            Value::UInt(w, _) => STy::UInt(*w),
            Value::SInt(w, _) => STy::SInt(*w),
            Value::Record(t, _) => STy::Record(t.clone()),
            Value::Enum(def, ..) => STy::Enum(def.clone()),
        }
    }

    /// The bits of an enum value: the tag in the low bits, then the
    /// payload. Another value has none.
    pub(crate) fn bits(&self) -> BigUint {
        match self {
            Value::Enum(def, tag, payload) => tag | (payload << def.tag_width),
            _ => BigUint::ZERO,
        }
    }
}

/// A step of a place: an evaluated key, a position, or a field name.
enum Step<'a> {
    Key(&'a SExpr),
    Pos(u32),
    Name(&'a String),
}

/// A resolved step of a place.
enum Sel {
    Pos(usize),
    Name(String),
}

/// The part of `v` that `sel` selects.
fn part<'v>(v: &'v Value, sel: &Sel) -> Result<&'v Value, Fault> {
    match (v, sel) {
        (Value::Tuple(xs) | Value::Array(xs) | Value::List(_, xs), Sel::Pos(k)) => {
            xs.get(*k).ok_or(Fault::Bound)
        }
        (Value::Record(ty, xs), Sel::Name(f)) => ty
            .fields
            .iter()
            .position(|(g, _)| g == f)
            .and_then(|k| xs.get(k))
            .ok_or(Fault::Type),
        _ => Err(Fault::Type),
    }
}

/// The part of `v` at the path `path`, to write.
fn part_mut<'v>(v: &'v mut Value, path: &[Sel]) -> Result<&'v mut Value, Fault> {
    let Some((sel, rest)) = path.split_first() else {
        return Ok(v);
    };
    let next = match (v, sel) {
        (Value::Tuple(xs) | Value::Array(xs) | Value::List(_, xs), Sel::Pos(k)) => {
            xs.get_mut(*k).ok_or(Fault::Bound)?
        }
        (Value::Record(ty, xs), Sel::Name(f)) => {
            let k = ty
                .fields
                .iter()
                .position(|(g, _)| g == f)
                .ok_or(Fault::Type)?;
            xs.get_mut(k).ok_or(Fault::Type)?
        }
        _ => return Err(Fault::Type),
    };
    part_mut(next, rest)
}

/// `@field(base, key)` after both operands have a value: a record takes the
/// `String` of one of its fields, and a tuple, an array, and a list take a
/// `Nat` below their length.
fn selected(base: Value, key: Value) -> Result<Value, Fault> {
    match (base, key) {
        (Value::Record(ty, xs), Value::Str(field)) => ty
            .fields
            .iter()
            .position(|(f, _)| *f == field)
            .and_then(|k| xs.into_iter().nth(k))
            .ok_or(Fault::Type),
        (Value::Tuple(xs) | Value::Array(xs) | Value::List(_, xs), Value::Int(n)) => {
            if n.sign() == Sign::Minus {
                return Err(Fault::Nat);
            }
            let at = usize::try_from(&n).map_err(|_| Fault::Bound)?;
            xs.into_iter().nth(at).ok_or(Fault::Bound)
        }
        _ => Err(Fault::Type),
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
            STy::UInt(w) => format!("(uint {w})"),
            STy::SInt(w) => format!("(sint {w})"),
            STy::Str => "string".to_owned(),
            STy::List(t) => format!("(list {})", t.serialize()),
            STy::Fn(f) => {
                let params: Vec<String> = f
                    .params
                    .iter()
                    .map(|(m, t)| {
                        if *m {
                            format!("(mut {})", t.serialize())
                        } else {
                            t.serialize()
                        }
                    })
                    .collect();
                format!("(fn ({}) {})", params.join(" "), f.ret.serialize())
            }
            STy::Record(r) => format!("(struct root {} ({}))", r.name, serialized(&r.args)),
            STy::Enum(d) => format!("(enum root {} ())", d.name),
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
    structs: BTreeMap<String, StructDef>,
    list_fns: BTreeMap<String, ListFn>,
    mut_fns: BTreeMap<String, MutFn>,
    enums: BTreeMap<String, EnumDef>,
    consts: BTreeMap<String, Value>,
}

impl Scope {
    /// The type of the function item `name`: the signature of the
    /// `comptime fn`, the list builder, or the function with a `mut` formal.
    pub(crate) fn fn_ty(&self, name: &str) -> Option<FnTy> {
        if let Some(f) = self.fns.get(name) {
            let params = f.params.iter().map(|(_, t)| (false, t.clone())).collect();
            return Some(FnTy {
                params,
                ret: f.ret.clone(),
            });
        }
        if let Some(f) = self.list_fns.get(name) {
            let params = f.params.iter().map(|(_, t)| (false, t.clone())).collect();
            return Some(FnTy {
                params,
                ret: STy::List(Box::new(f.elem.clone())),
            });
        }
        let f = self.mut_fns.get(name)?;
        Some(FnTy {
            params: vec![(true, f.root.clone()), (false, STy::Int)],
            ret: STy::Int,
        })
    }

    /// The scope of the items: all `comptime fn`s, then each `const` in item
    /// order. A `const` can read only earlier ones. Each `const` evaluates
    /// here, not at its first use, so a faulting `const` that nothing reads
    /// faults here but not in the language: stricter on purpose.
    pub(crate) fn new(items: &[Item]) -> Result<Scope, Fault> {
        let mut scope = Scope::default();
        for item in items {
            match item {
                Item::ComptimeFn(f) => {
                    scope.fns.insert(f.name.clone(), f.clone());
                }
                Item::ListFn(f) => {
                    scope.list_fns.insert(f.name.clone(), f.clone());
                }
                Item::MutFn(f) => {
                    scope.mut_fns.insert(f.name.clone(), f.clone());
                }
                Item::Struct(def) => {
                    scope.structs.insert(def.name.clone(), def.clone());
                }
                Item::Enum(def) => {
                    scope.enums.insert(def.name.clone(), def.clone());
                }
                _ => {}
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
/// The most scalars in a string, and elements in a list.
pub(crate) const MAX_STRING: usize = 16;
pub(crate) const MAX_LIST: usize = 8;
/// The most `comptime fn` calls of one evaluation.
const MAX_CALLS: u32 = 4096;
/// The widths of `UInt[w]` and `SInt[w]` (front-end `MAX_WIDTH`).
const MAX_WIDTH: u32 = 65536;

/// The item that a call of `name` runs: `name` itself, or the item that
/// the function value `name` holds (a `const` or a parameter). A value that
/// is no function is a fault.
fn callee<'s>(name: &'s str, env: &'s Env, scope: &'s Scope) -> Result<&'s str, Fault> {
    match env.statics.get(name).or_else(|| scope.consts.get(name)) {
        Some(Value::Function(item, _)) => Ok(item),
        Some(_) => Err(Fault::Type),
        None => Ok(name),
    }
}

/// One call frame of an observation record: the item that the call runs,
/// the function whose body holds the call (none: a module body), and the
/// name that the call binds, which keys the call in the printed text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Frame {
    /// Whether the call stands inside the expression of the statement that
    /// binds `result`, as a key, and not at its start.
    pub(crate) key: bool,
    pub(crate) callee: String,
    pub(crate) within: Option<String>,
    pub(crate) result: String,
}

/// The part of an observation record that the evaluator knows: the call
/// frames from the module body to the `diagnostic`, outermost first, the
/// message, and the value. A `diagnostic` of a module body has no frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Logged {
    pub(crate) frames: Vec<Frame>,
    pub(crate) message: String,
    value: String,
}

impl Logged {
    fn new(message: &str, value: &Value) -> Logged {
        Logged {
            frames: Vec::new(),
            message: message.to_owned(),
            value: value.serialize(),
        }
    }

    /// The tail of the record: the message and the value, as `observe`
    /// prints them after the frames (front-end spec 8.2).
    pub(crate) fn tail(&self) -> String {
        format!(
            "{} {}",
            Value::Str(self.message.clone()).serialize(),
            self.value
        )
    }
}

/// A call of a `comptime fn` with a `mut` formal: the final value of the
/// formal, which the call writes back to its root, and the result. A
/// `diagnostic` of the function appends its record to `log`.
fn call_mut(
    def: &MutFn,
    root: Value,
    arg: Value,
    scope: &Scope,
    log: &mut Vec<Logged>,
) -> Result<(Value, Value), Fault> {
    let mut inner = Env::default();
    inner.statics.insert("x1".to_owned(), arg);
    inner.statics.insert("a0".to_owned(), root);
    for s in &def.pre {
        exec_in(s, &mut inner, scope, log, Some(&def.name))?;
    }
    let v = typed(&STy::Int, eval(&def.update, &inner, scope)?)?;
    if def.root == STy::Int {
        inner.statics.insert("a0".to_owned(), v);
    } else {
        let Some(Value::List(_, xs)) = inner.statics.get_mut("a0") else {
            return Err(Fault::Type);
        };
        xs.push(v);
        if xs.len() > MAX_LIST {
            return Err(Fault::Bound);
        }
    }
    if let Some((message, value)) = &def.diag {
        log.push(Logged::new(message, &eval(value, &inner, scope)?));
    }
    let result = typed(&STy::Int, eval(&def.ret, &inner, scope)?)?;
    let new = inner.statics.remove("a0").ok_or(Fault::Type)?;
    Ok((new, result))
}

/// Executes a static statement on `env`: a `let`, a `push`, or a `pop`. The
/// builder and the twin both run the static statements of a frame with it.
/// They drop the records of a `diagnostic`; `exec_logged` keeps them.
pub(crate) fn exec_static(s: &Stmt, env: &mut Env, scope: &Scope) -> Result<(), Fault> {
    exec_logged(s, env, scope, &mut Vec::new())
}

/// `exec_static`, and the records of the `diagnostic` calls that the
/// statement runs, appended to `log` in evaluation order.
pub(crate) fn exec_logged(
    s: &Stmt,
    env: &mut Env,
    scope: &Scope,
    log: &mut Vec<Logged>,
) -> Result<(), Fault> {
    exec_in(s, env, scope, log, None)
}

/// `exec_logged` for a statement in the body of the function `within`, or
/// in a module body if none.
fn exec_in(
    s: &Stmt,
    env: &mut Env,
    scope: &Scope,
    log: &mut Vec<Logged>,
    within: Option<&str>,
) -> Result<(), Fault> {
    match s {
        Stmt::Diagnostic(message, value) => {
            log.push(Logged::new(message, &eval(value, env, scope)?));
        }
        Stmt::StaticLet(name, _, value) => {
            let v = eval_effects(value, env, scope, log, (within, name))?;
            env.statics.insert(name.clone(), v);
        }
        Stmt::MutLet(name, _, value) => {
            let v = eval(value, env, scope)?;
            env.statics.insert(name.clone(), v);
        }
        Stmt::Push(list, value) => {
            let v = eval(value, env, scope)?;
            let Some(Value::List(t, xs)) = env.statics.get_mut(list) else {
                return Err(Fault::Type);
            };
            xs.push(typed(t, v)?);
            if xs.len() > MAX_LIST {
                return Err(Fault::Bound);
            }
        }
        Stmt::MutCall {
            name,
            root,
            f,
            args,
            ..
        } => {
            let def = scope
                .mut_fns
                .get(callee(f, env, scope)?)
                .ok_or(Fault::Type)?;
            let [arg] = args.as_slice() else {
                return Err(Fault::Type);
            };
            let arg = typed(&STy::Int, eval(arg, env, scope)?)?;
            let old = env.statics.get(root).cloned().ok_or(Fault::Type)?;
            let start = log.len();
            let (new, result) = call_mut(def, typed(&def.root, old)?, arg, scope, log)?;
            let frame = Frame {
                key: false,
                callee: def.name.clone(),
                within: within.map(str::to_owned),
                result: name.clone(),
            };
            for logged in log.iter_mut().skip(start) {
                logged.frames.insert(0, frame.clone());
            }
            env.statics.insert(root.clone(), new);
            env.statics.insert(name.clone(), result);
        }
        Stmt::PlaceCall {
            name,
            place,
            f,
            arg,
        } => {
            let def = scope.mut_fns.get(f.as_str()).ok_or(Fault::Type)?;
            let frame = Frame {
                key: false,
                callee: def.name.clone(),
                within: within.map(str::to_owned),
                result: name.clone(),
            };
            let mut ev = Evaluator::new(scope);
            ev.within.clone_from(&frame.within);
            ev.tag.clone_from(name);
            let (root, new_root, result) = ev.place_call(place, def, arg, env, &frame)?;
            env.statics.extend(ev.writes);
            env.statics.insert(root, new_root);
            env.statics.insert(name.clone(), result);
            log.append(&mut ev.log);
        }
        Stmt::PopLet(name, list) => {
            let Some(Value::List(_, xs)) = env.statics.get_mut(list) else {
                return Err(Fault::Type);
            };
            let v = xs.pop().ok_or(Fault::Bound)?;
            env.statics.insert(name.clone(), v);
        }
        _ => return Err(Fault::Type),
    }
    Ok(())
}

/// The value of a static expression, as both front ends compute it, or the
/// first fault in evaluation order.
pub(crate) fn eval(e: &SExpr, env: &Env, scope: &Scope) -> Result<Value, Fault> {
    Evaluator::new(scope).eval(e, env)
}

/// `eval` of the expression of the statement `tag` in the function `within`
/// (none: a module body). A `KeyCall` writes its root back to `env`, and
/// its records go to `log` in evaluation order, with the frame of the call.
fn eval_effects(
    e: &SExpr,
    env: &mut Env,
    scope: &Scope,
    log: &mut Vec<Logged>,
    (within, tag): (Option<&str>, &str),
) -> Result<Value, Fault> {
    let mut ev = Evaluator::new(scope);
    ev.within = within.map(str::to_owned);
    tag.clone_into(&mut ev.tag);
    let v = ev.eval(e, env)?;
    env.statics.extend(ev.writes);
    log.append(&mut ev.log);
    Ok(v)
}

/// The specialization of the struct `name` at `args`: each argument at the
/// type `Nat`, each field type with its width evaluated.
pub(crate) fn record_ty(name: &str, args: &[Value], scope: &Scope) -> Result<RecTy, Fault> {
    let def = scope.structs.get(name).ok_or(Fault::Type)?;
    if def.params.len() != args.len() {
        return Err(Fault::Type);
    }
    let mut env = Env::default();
    for (p, a) in def.params.iter().zip(args) {
        env.statics.insert(p.clone(), typed(&STy::Nat, a.clone())?);
    }
    let mut fields = Vec::new();
    for (f, t) in &def.fields {
        let t = match t {
            FieldTy::Static(t) => t.clone(),
            FieldTy::UInt(w) => STy::UInt(field_width(w, &env, scope)?),
            FieldTy::SInt(w) => STy::SInt(field_width(w, &env, scope)?),
            // A struct of handles has no static value.
            FieldTy::Handle(_) => return Err(Fault::Type),
        };
        fields.push((f.clone(), t));
    }
    Ok(RecTy {
        name: name.to_owned(),
        args: args.to_vec(),
        fields,
    })
}

fn field_width(w: &SExpr, env: &Env, scope: &Scope) -> Result<u32, Fault> {
    let w = int(eval(w, env, scope)?)?;
    u32::try_from(&w)
        .ok()
        .filter(|w| (1..=MAX_WIDTH).contains(w))
        .ok_or(Fault::Bound)
}

/// The number of bits of a type of hardware data.
fn bits(t: &STy) -> Result<u32, Fault> {
    match t {
        STy::Bool => Ok(1),
        STy::UInt(w) | STy::SInt(w) => Ok(*w),
        STy::Tuple(ts) => ts.iter().map(bits).sum(),
        STy::Array(t, n) => Ok(bits(t)?.saturating_mul(*n)),
        STy::Record(r) => r.fields.iter().map(|(_, t)| bits(t)).sum(),
        STy::Enum(d) => Ok(d.data_bits()),
        STy::Nat | STy::Int | STy::Str | STy::List(_) | STy::Fn(_) => Err(Fault::Type),
    }
}

/// The zero of a type of `Bool` and finite integer fields.
fn zero(t: &STy) -> Result<Value, Fault> {
    match t {
        STy::Bool => Ok(Value::Bool(false)),
        STy::UInt(w) => Ok(Value::UInt(*w, BigInt::ZERO)),
        STy::SInt(w) => Ok(Value::SInt(*w, BigInt::ZERO)),
        _ => Err(Fault::Type),
    }
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
        Ty::Enum(_) => return Err(Fault::Type),
        Ty::Query(t, _) => concrete(t, env, scope)?,
    })
}

/// The entries of the port `name` of type `t`, in packing order. A scalar
/// port is one entry.
pub(crate) fn leaves(
    name: &str,
    t: &Ty,
    env: &Env,
    scope: &Scope,
) -> Result<Vec<(String, Scalar)>, Fault> {
    let Ty::Enum(e) = t else {
        return Ok(vec![(name.to_owned(), concrete(t, env, scope)?)]);
    };
    let def = scope.enums.get(e).ok_or(Fault::Type)?;
    let mut out = vec![(format!("{name}.tag"), Scalar::UInt(def.tag_width))];
    if def.payload_bits() > 0 {
        out.push((format!("{name}.payload"), Scalar::UInt(def.payload_bits())));
    }
    Ok(out)
}

struct Evaluator<'a> {
    scope: &'a Scope,
    calls: u32,
    depth: u32,
    /// The roots that a `KeyCall` wrote back, which a later name reads
    /// before the env.
    writes: BTreeMap<String, Value>,
    /// The records of the `diagnostic` calls that a `KeyCall` made.
    log: Vec<Logged>,
    /// The function that holds the statement, and the name that it binds.
    within: Option<String>,
    tag: String,
}

impl<'a> Evaluator<'a> {
    fn new(scope: &'a Scope) -> Evaluator<'a> {
        Evaluator {
            scope,
            calls: 0,
            depth: 0,
            writes: BTreeMap::new(),
            log: Vec::new(),
            within: None,
            tag: String::new(),
        }
    }

    /// The call of `def` on the place `place` with the explicit argument
    /// `arg`: the keys of the place evaluate from the root outward, then
    /// the argument, then the call runs on the part and the part takes its
    /// final value. Gives the name of the root, its new value, and the
    /// result.
    fn place_call(
        &mut self,
        place: &SExpr,
        def: &MutFn,
        arg: &SExpr,
        env: &Env,
        frame: &Frame,
    ) -> Result<(String, Value, Value), Fault> {
        let mut steps = Vec::new();
        let mut at = place;
        let root = loop {
            match at {
                SExpr::Name(n) => break n.clone(),
                SExpr::Index(b, k) | SExpr::At(b, k) => {
                    steps.push(Step::Key(k));
                    at = b;
                }
                SExpr::Select(b, k, _) => {
                    steps.push(Step::Pos(*k));
                    at = b;
                }
                SExpr::Field(b, f) => {
                    steps.push(Step::Name(f));
                    at = b;
                }
                _ => return Err(Fault::Type),
            }
        };
        steps.reverse();
        let top = env.statics.get(&root).cloned().ok_or(Fault::Type)?;
        let mut cur = top.clone();
        let mut path = Vec::new();
        for step in steps {
            let sel = match step {
                Step::Pos(k) => Sel::Pos(k as usize),
                Step::Name(f) => Sel::Name(f.clone()),
                Step::Key(k) => match self.eval(k, env)? {
                    Value::Str(f) => Sel::Name(f),
                    Value::Int(n) => {
                        if n.sign() == Sign::Minus {
                            return Err(Fault::Nat);
                        }
                        Sel::Pos(usize::try_from(&n).map_err(|_| Fault::Bound)?)
                    }
                    _ => return Err(Fault::Type),
                },
            };
            cur = part(&cur, &sel)?.clone();
            path.push(sel);
        }
        let arg = typed(&STy::Int, self.eval(arg, env)?)?;
        let start = self.log.len();
        let (new, result) = call_mut(def, typed(&def.root, cur)?, arg, self.scope, &mut self.log)?;
        for logged in self.log.iter_mut().skip(start) {
            logged.frames.insert(0, frame.clone());
        }
        let mut top = top;
        *part_mut(&mut top, &path)? = new;
        Ok((root, top, result))
    }

    /// `f(root, arg)`: the call runs on the current value of the root,
    /// writes the new value back, and gives its result.
    fn key_call(&mut self, f: &str, root: &str, arg: &SExpr, env: &Env) -> Result<Value, Fault> {
        let def = self.scope.mut_fns.get(f).ok_or(Fault::Type)?;
        let arg = typed(&STy::Int, self.eval(arg, env)?)?;
        let old = self
            .writes
            .get(root)
            .or_else(|| env.statics.get(root))
            .cloned()
            .ok_or(Fault::Type)?;
        let start = self.log.len();
        let (new, result) = call_mut(def, typed(&def.root, old)?, arg, self.scope, &mut self.log)?;
        let frame = Frame {
            key: true,
            callee: def.name.clone(),
            within: self.within.clone(),
            result: self.tag.clone(),
        };
        for logged in self.log.iter_mut().skip(start) {
            logged.frames.insert(0, frame.clone());
        }
        self.writes.insert(root.to_owned(), new);
        Ok(result)
    }

    fn eval(&mut self, e: &SExpr, env: &Env) -> Result<Value, Fault> {
        let v = match e {
            // The twin reads the three parts of a `PortKey`.
            SExpr::PortKey(..) => return Err(Fault::Type),
            SExpr::Int(n, _) => Value::Int(n.clone()),
            SExpr::Bool(b) => Value::Bool(*b),
            SExpr::KeyCall(f, root, arg) => self.key_call(f, root, arg, env)?,
            SExpr::Query(q) => self.eval(&q.value, env)?,
            SExpr::Name(n) => match self
                .writes
                .get(n)
                .or_else(|| env.statics.get(n))
                .or_else(|| self.scope.consts.get(n))
            {
                Some(v) => v.clone(),
                None => Value::Function(n.clone(), self.scope.fn_ty(n).ok_or(Fault::Type)?),
            },
            SExpr::Call(f, args) => self.call(f, args, env)?,
            SExpr::Tuple(xs) => Value::Tuple(self.all(xs, env)?),
            SExpr::Array(xs) if xs.is_empty() => return Err(Fault::Type),
            SExpr::Array(xs) => Value::Array(self.all(xs, env)?),
            SExpr::Index(base, index) => {
                let base = self.eval(base, env)?;
                let index = int(self.eval(index, env)?)?;
                let at = usize::try_from(&index).map_err(|_| Fault::Bound);
                match base {
                    Value::Array(xs) | Value::List(_, xs) => {
                        xs.into_iter().nth(at?).ok_or(Fault::Bound)?
                    }
                    Value::Str(s) => {
                        Value::Str(s.chars().nth(at?).ok_or(Fault::Bound)?.to_string())
                    }
                    _ => return Err(Fault::Type),
                }
            }
            SExpr::Select(base, k, _) => match self.eval(base, env)? {
                Value::Tuple(xs) => xs.into_iter().nth(*k as usize).ok_or(Fault::Bound)?,
                _ => return Err(Fault::Type),
            },
            SExpr::At(base, key) => {
                let base = self.eval(base, env)?;
                selected(base, self.eval(key, env)?)?
            }
            SExpr::Len(base) => match self.eval(base, env)? {
                Value::Array(xs) | Value::List(_, xs) => Value::Int(BigInt::from(xs.len())),
                Value::Str(s) => Value::Int(BigInt::from(s.chars().count())),
                _ => return Err(Fault::Type),
            },
            SExpr::Str(s) => Value::Str(s.clone()),
            SExpr::StrOf(n) => Value::Str(int(self.eval(n, env)?)?.to_string()),
            SExpr::Convert(t, e) => self.conversion(t, e, env)?,
            SExpr::NewList(t) => match t {
                STy::Int | STy::Nat => Value::List(t.clone(), Vec::new()),
                _ => return Err(Fault::Type),
            },
            SExpr::Zero(name, _) | SExpr::DataBits(name, _)
                if self.scope.enums.contains_key(name) =>
            {
                self.enum_form(e, env)?
            }
            SExpr::Ctor(..) | SExpr::Unpack(..) | SExpr::Pack(..) | SExpr::BitsConv(..) => {
                self.enum_form(e, env)?
            }
            SExpr::Record(..) | SExpr::Zero(..) | SExpr::DataBits(..) | SExpr::Field(..) => {
                self.record_form(e, env)?
            }
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
            SExpr::Match(m) => self.static_match(m, env)?,
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

    /// A `match` on a static scrutinee: the first arm whose pattern holds
    /// is the only one that runs. A binder of a variant pattern gets the
    /// unpack of the payload at the leaf offsets.
    fn static_match(&mut self, m: &Match<SExpr, SExpr>, env: &Env) -> Result<Value, Fault> {
        let scrutinee = self.eval(&m.scrutinee, env)?;
        for (pattern, arm) in &m.arms {
            let Some(binds) = selects(pattern, &scrutinee)? else {
                continue;
            };
            let mut inner = env.clone();
            inner.statics.extend(binds);
            return self.eval(arm, &inner);
        }
        // The arms cover each value by construction.
        Err(Fault::Type)
    }

    /// The forms of records: a constructor, the zero, `data_bits`, and a
    /// field.
    fn record_form(&mut self, e: &SExpr, env: &Env) -> Result<Value, Fault> {
        Ok(match e {
            SExpr::Record(name, targs, fields) => {
                let ty = self.specialize(name, targs, env)?;
                let xs = self.all(fields, env)?;
                if xs.len() != ty.fields.len() {
                    return Err(Fault::Type);
                }
                let tys = ty.fields.iter().map(|(_, t)| t);
                Value::Record(Box::new(ty.clone()), typed_all(tys, xs.into_iter())?)
            }
            SExpr::Zero(name, targs) => {
                let ty = self.specialize(name, targs, env)?;
                let xs = ty
                    .fields
                    .iter()
                    .map(|(_, t)| zero(t))
                    .collect::<Result<_, _>>()?;
                Value::Record(Box::new(ty), xs)
            }
            SExpr::DataBits(name, targs) => {
                let ty = self.specialize(name, targs, env)?;
                Value::Int(BigInt::from(bits(&STy::Record(Box::new(ty)))?))
            }
            SExpr::Field(base, field) => match self.eval(base, env)? {
                Value::Record(ty, xs) => ty
                    .fields
                    .iter()
                    .position(|(f, _)| f == field)
                    .and_then(|k| xs.into_iter().nth(k))
                    .ok_or(Fault::Type)?,
                _ => return Err(Fault::Type),
            },
            _ => return Err(Fault::Type),
        })
    }

    /// The forms of enums: a constructor, the zero, `data_bits`, and the
    /// conversions between an enum and its bits.
    fn enum_form(&mut self, e: &SExpr, env: &Env) -> Result<Value, Fault> {
        let def_of = |name: &String| self.scope.enums.get(name).ok_or(Fault::Type);
        Ok(match e {
            SExpr::Zero(name, _) => Value::Enum(
                Box::new(def_of(name)?.clone()),
                BigUint::ZERO,
                BigUint::ZERO,
            ),
            SExpr::DataBits(name, _) => Value::Int(BigInt::from(def_of(name)?.data_bits())),
            SExpr::Ctor(name, variant, args) => self.ctor(name, variant, args, env)?,
            SExpr::Unpack(name, e) => {
                let def = def_of(name)?.clone();
                let Value::UInt(w, n) = self.eval(e, env)? else {
                    return Err(Fault::Type);
                };
                if w != def.data_bits() {
                    return Err(Fault::Type);
                }
                let n = n.magnitude();
                let tag = n & ((BigUint::from(1u8) << def.tag_width) - 1u8);
                Value::Enum(Box::new(def.clone()), tag, n >> def.tag_width)
            }
            SExpr::Pack(name, e) => {
                let def = def_of(name)?.clone();
                let v = self.eval(e, env)?;
                if v.ty() != STy::Enum(Box::new(def.clone())) {
                    return Err(Fault::Type);
                }
                Value::UInt(def.data_bits(), BigInt::from(v.bits()))
            }
            SExpr::BitsConv(name, e) => {
                let width = def_of(name)?.data_bits();
                let n = match &**e {
                    SExpr::Int(n, _) => n.clone(),
                    e => int(self.eval(e, env)?)?,
                };
                convert(&STy::UInt(width), Value::Int(n))?
            }
            _ => return Err(Fault::Type),
        })
    }

    /// `E::V(args)`: each argument has its typed use at its payload type,
    /// and the leaves pack with the first in the low bits.
    fn ctor(
        &mut self,
        name: &str,
        variant: &str,
        args: &[SExpr],
        env: &Env,
    ) -> Result<Value, Fault> {
        let def = self.scope.enums.get(name).ok_or(Fault::Type)?;
        let v = def.variant(variant).ok_or(Fault::Type)?;
        if v.payload.len() != args.len() {
            return Err(Fault::Type);
        }
        let mut payload = BigUint::ZERO;
        for (arg, (at, t)) in args.iter().zip(v.leaves()) {
            let value = self.eval(arg, env)?;
            payload |= leaf_bits(t, value)? << at;
        }
        Ok(Value::Enum(Box::new(def.clone()), v.tag.clone(), payload))
    }

    /// `T(e)`. The bound limits the results of operations. The literal of
    /// a conversion is the builder's choice, and a wide finite type needs a
    /// wide one.
    fn conversion(&mut self, t: &STy, e: &SExpr, env: &Env) -> Result<Value, Fault> {
        match e {
            SExpr::Int(n, _) => convert(t, Value::Int(n.clone())),
            e => convert(t, self.eval(e, env)?),
        }
    }

    /// The call of a list builder: the list of the elements for the binder
    /// `j0` over `0..x0`. The first formal is the length.
    fn list_call(&mut self, def: &ListFn, args: &[SExpr], env: &Env) -> Result<Value, Fault> {
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
        let count = def
            .params
            .first()
            .and_then(|(name, _)| inner.statics.get(name))
            .cloned()
            .ok_or(Fault::Type)?;
        let Value::Int(count) = count else {
            return Err(Fault::Type);
        };
        if count > BigInt::from(MAX_LIST) {
            return Err(Fault::Bound);
        }
        let mut xs = Vec::new();
        for j in loop_values(&BigInt::ZERO, &count) {
            inner.statics.insert("j0".to_owned(), j);
            self.depth += 1;
            let v = self.eval(&def.element, &inner);
            self.depth -= 1;
            xs.push(typed(&def.elem, v?)?);
        }
        Ok(Value::List(def.elem.clone(), xs))
    }

    /// The specialization of a struct at the arguments `targs`.
    fn specialize(&mut self, name: &str, targs: &[SExpr], env: &Env) -> Result<RecTy, Fault> {
        let args = self.all(targs, env)?;
        record_ty(name, &args, self.scope)
    }

    /// The values of `xs`, left to right.
    fn all(&mut self, xs: &[SExpr], env: &Env) -> Result<Vec<Value>, Fault> {
        xs.iter().map(|x| self.eval(x, env)).collect()
    }

    /// The template of `ComptimeFn`: the base when the first formal is 0,
    /// else the step. Each formal and the result check their type.
    fn call(&mut self, f: &str, args: &[SExpr], env: &Env) -> Result<Value, Fault> {
        let scope = self.scope;
        let f = callee(f, env, scope)?;
        if let Some(def) = scope.list_fns.get(f) {
            return self.list_call(def, args, env);
        }
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

/// The binders of `pattern` if it holds for `value`, else `None`.
fn selects(pattern: &Pattern, value: &Value) -> Result<Option<Vec<(String, Value)>>, Fault> {
    Ok(match (pattern, value) {
        (Pattern::Wild, _) => Some(Vec::new()),
        (Pattern::Int(k, _), Value::Int(n) | Value::UInt(_, n) | Value::SInt(_, n)) => {
            (k == n).then(Vec::new)
        }
        (Pattern::Bool(k), Value::Bool(b)) => (k == b).then(Vec::new),
        (Pattern::Variant(e, v, binders), Value::Enum(def, tag, payload)) => {
            if def.name != *e {
                return Err(Fault::Type);
            }
            let variant = def.variant(v).ok_or(Fault::Type)?;
            if variant.tag != *tag {
                return Ok(None);
            }
            if binders.len() != variant.payload.len() {
                return Err(Fault::Type);
            }
            let leaves = variant.leaves();
            Some(
                binders
                    .iter()
                    .zip(leaves)
                    .filter_map(|(b, (at, t))| {
                        b.as_ref().map(|b| (b.clone(), unpack_leaf(t, at, payload)))
                    })
                    .collect(),
            )
        }
        _ => return Err(Fault::Type),
    })
}

/// The unsigned bits of a payload leaf of type `t`: the typed use of
/// `value` at the leaf type, and its two's complement.
pub(crate) fn leaf_bits(t: Scalar, value: Value) -> Result<BigUint, Fault> {
    let (ty, w) = match t {
        Scalar::Bool => (STy::Bool, 1),
        Scalar::UInt(w) => (STy::UInt(w), w),
        Scalar::SInt(w) => (STy::SInt(w), w),
    };
    Ok(match convert(&ty, value)? {
        Value::Bool(b) => BigUint::from(u8::from(b)),
        Value::UInt(_, n) => n.magnitude().clone(),
        Value::SInt(_, n) => (n + (BigInt::from(1) << w)).magnitude() % (BigUint::from(1u8) << w),
        _ => return Err(Fault::Type),
    })
}

/// The leaf of type `t` in the payload `bits` at `at`: the inverse of
/// `leaf_bits`, with the sign extension of an `SInt`.
pub(crate) fn unpack_leaf(t: Scalar, at: u32, payload: &BigUint) -> Value {
    let bits = (payload >> at) & ((BigUint::from(1u8) << t.bits()) - 1u8);
    match t {
        Scalar::Bool => Value::Bool(bits != BigUint::ZERO),
        Scalar::UInt(w) => Value::UInt(w, BigInt::from(bits)),
        Scalar::SInt(w) => {
            let n = BigInt::from(bits);
            let half = BigInt::from(1) << (w - 1);
            Value::SInt(
                w,
                if n >= half {
                    n - (BigInt::from(1) << w)
                } else {
                    n
                },
            )
        }
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
        (Value::Str(x), Value::Str(y)) => match op {
            SBin::Eq => x == y,
            SBin::Ne => x != y,
            SBin::Add => return Ok(Value::Str(x + &y)),
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
        Value::Str(s) if s.chars().count() > MAX_STRING => Err(Fault::Bound),
        Value::List(_, xs) if xs.len() > MAX_LIST => Err(Fault::Bound),
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
        (STy::Nat | STy::Int, Value::Int(_))
        | (STy::Bool, Value::Bool(_))
        | (STy::Str, Value::Str(_)) => Ok(v),
        (STy::Tuple(ts), Value::Tuple(xs)) if ts.len() == xs.len() => {
            Ok(Value::Tuple(typed_all(ts.iter(), xs.iter().cloned())?))
        }
        (STy::Array(t, n), Value::Array(xs)) if *n as usize == xs.len() => Ok(Value::Array(
            typed_all(std::iter::repeat_n(&**t, xs.len()), xs.iter().cloned())?,
        )),
        (STy::List(t), Value::List(have, xs)) if **t == *have => Ok(Value::List(
            have.clone(),
            typed_all(std::iter::repeat_n(&**t, xs.len()), xs.iter().cloned())?,
        )),
        (STy::Fn(want), Value::Function(_, have)) if **want == *have => Ok(v),
        (STy::UInt(w), Value::UInt(x, _)) | (STy::SInt(w), Value::SInt(x, _)) if w == x => Ok(v),
        (STy::Record(want), Value::Record(have, _)) if want == have => Ok(v),
        (STy::Enum(want), Value::Enum(have, ..)) if want == have => Ok(v),
        _ => Err(Fault::Type),
    }
}

/// The typed use of a module argument or of `T(n)` at a finite type: an
/// integer that fits converts, and any other value has `typed`.
pub(crate) fn convert(ty: &STy, v: Value) -> Result<Value, Fault> {
    let fit = |w: u32, n: &BigInt, signed: bool| {
        if signed {
            let half = BigInt::from(1) << (w - 1);
            -half.clone() <= *n && *n < half
        } else {
            BigInt::ZERO <= *n && *n < (BigInt::from(1) << w)
        }
    };
    match (ty, v) {
        (STy::UInt(w), Value::Int(n)) if fit(*w, &n, false) => Ok(Value::UInt(*w, n)),
        (STy::SInt(w), Value::Int(n)) if fit(*w, &n, true) => Ok(Value::SInt(*w, n)),
        (STy::UInt(_) | STy::SInt(_), Value::Int(_)) => Err(Fault::Bound),
        (ty, v) => typed(ty, v),
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

    /// A module argument converts to its finite type when it fits.
    #[test]
    fn a_conversion_fits_or_faults() {
        let uint = |w, n| convert(&STy::UInt(w), Value::Int(BigInt::from(n)));
        assert_eq!(uint(8, 255), Ok(Value::UInt(8, BigInt::from(255))));
        assert_eq!(uint(8, 256), Err(Fault::Bound));
        assert_eq!(uint(8, -1), Err(Fault::Bound));
        let sint = |w, n| convert(&STy::SInt(w), Value::Int(BigInt::from(n)));
        assert_eq!(sint(8, -128), Ok(Value::SInt(8, BigInt::from(-128))));
        assert_eq!(sint(8, 128), Err(Fault::Bound));
        assert_eq!(sint(1, 0), Ok(Value::SInt(1, BigInt::ZERO)));
        let wide = SExpr::Convert(
            STy::UInt(257),
            Box::new(SExpr::Int(BigInt::from(1) << 200, Radix::Hex)),
        );
        assert_eq!(run(&wide), Ok(Value::UInt(257, BigInt::from(1) << 200)));
        assert_eq!(convert(&STy::Int, Value::Bool(true)), Err(Fault::Type));
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

    /// `struct S0(comptime W0: Nat) { m0: UInt[(W0 + 1)], m1: Bool }`,
    /// `struct S1 { m0: Int, m1: (Int, Bool) }`, and
    /// `struct S2(comptime W0: Nat) { m0: UInt[W0] }`.
    fn structs() -> Scope {
        let hardware = StructDef {
            name: "S0".to_owned(),
            params: vec!["W0".to_owned()],
            fields: vec![
                (
                    "m0".to_owned(),
                    FieldTy::UInt(bin(SBin::Add, name("W0"), int(1))),
                ),
                ("m1".to_owned(), FieldTy::Static(STy::Bool)),
            ],
        };
        let value = StructDef {
            name: "S1".to_owned(),
            params: Vec::new(),
            fields: vec![
                ("m0".to_owned(), FieldTy::Static(STy::Int)),
                (
                    "m1".to_owned(),
                    FieldTy::Static(STy::Tuple(vec![STy::Int, STy::Bool])),
                ),
            ],
        };
        let narrow = StructDef {
            name: "S2".to_owned(),
            params: vec!["W0".to_owned()],
            fields: vec![("m0".to_owned(), FieldTy::UInt(name("W0")))],
        };
        let items = [
            Item::Struct(hardware),
            Item::Struct(value),
            Item::Struct(narrow),
        ];
        Scope::new(&items).unwrap_or_default()
    }

    fn run_in(scope: &Scope, e: &SExpr) -> Result<Value, Fault> {
        eval(e, &Env::default(), scope)
    }

    #[test]
    fn records_evaluate_like_the_front_ends() {
        let scope = structs();
        let zero = SExpr::Zero("S0".to_owned(), vec![int(7)]);
        // The example of front-end spec 7.1, with the zero in place of `3`.
        assert_eq!(
            run_in(&scope, &zero).map(|v| v.serialize()),
            Ok("(record (struct root S0 ((int 7))) ((uint 8 0) (bool false)))".to_owned())
        );
        let bits = SExpr::DataBits("S0".to_owned(), vec![int(7)]);
        assert_eq!(run_in(&scope, &bits), value(9));
        let negative = SExpr::DataBits("S0".to_owned(), vec![int(-1)]);
        assert_eq!(run_in(&scope, &negative), Err(Fault::Nat));
        let record = SExpr::Record(
            "S1".to_owned(),
            Vec::new(),
            vec![int(5), tuple(vec![int(-1), SExpr::Bool(true)])],
        );
        assert_eq!(
            run_in(&scope, &record).map(|v| v.serialize()),
            Ok("(record (struct root S1 ()) ((int 5) (tuple ((int -1) (bool true)))))".to_owned())
        );
        let field = |e: SExpr, f: &str| SExpr::Field(Box::new(e), f.to_owned());
        assert_eq!(run_in(&scope, &field(record.clone(), "m0")), value(5));
        assert_eq!(
            run_in(&scope, &select(field(record.clone(), "m1"), 0)),
            value(-1)
        );
        assert_eq!(run_in(&scope, &field(zero, "m1")), Ok(Value::Bool(false)));
        assert_eq!(run_in(&scope, &field(record, "m9")), Err(Fault::Type));
    }

    #[test]
    fn field_selects_like_an_ordinary_selection() {
        let scope = structs();
        let at = |b: SExpr, k: SExpr| SExpr::At(Box::new(b), Box::new(k));
        let key = |f: &str| SExpr::Str(f.to_owned());
        let record = SExpr::Record(
            "S1".to_owned(),
            Vec::new(),
            vec![int(5), tuple(vec![int(-1), SExpr::Bool(true)])],
        );
        assert_eq!(run_in(&scope, &at(record.clone(), key("m0"))), value(5));
        // A key that joins two strings names the field too.
        let joined = bin(SBin::Add, key("m"), SExpr::StrOf(Box::new(int(0))));
        assert_eq!(run_in(&scope, &at(record.clone(), joined)), value(5));
        let inner = at(record.clone(), key("m1"));
        assert_eq!(run_in(&scope, &at(inner, int(0))), value(-1));
        assert_eq!(run_in(&scope, &at(record, key("m9"))), Err(Fault::Type));
        let a = array(vec![int(10), int(20), int(30)]);
        assert_eq!(run_in(&scope, &at(a.clone(), int(2))), value(30));
        assert_eq!(run_in(&scope, &at(a.clone(), int(3))), Err(Fault::Bound));
        assert_eq!(run_in(&scope, &at(a.clone(), int(-1))), Err(Fault::Nat));
        assert_eq!(run_in(&scope, &at(a.clone(), key("m0"))), Err(Fault::Type));
        let t = tuple(vec![int(7), SExpr::Bool(true)]);
        assert_eq!(run_in(&scope, &at(t, int(1))), Ok(Value::Bool(true)));
        // The base evaluates before the key: a fault of the base wins.
        let faulty = at(index(a, int(9)), bin(SBin::Div, int(1), int(0)));
        assert_eq!(run_in(&scope, &faulty), Err(Fault::Bound));
    }

    #[test]
    fn records_reject_what_the_builder_never_makes() {
        let scope = structs();
        let few = SExpr::Record("S1".to_owned(), Vec::new(), vec![int(5)]);
        assert_eq!(run_in(&scope, &few), Err(Fault::Type));
        let wrong = SExpr::Record(
            "S1".to_owned(),
            Vec::new(),
            vec![SExpr::Bool(true), tuple(vec![int(1), SExpr::Bool(true)])],
        );
        assert_eq!(run_in(&scope, &wrong), Err(Fault::Type));
        // The zero needs hardware data in each field.
        assert_eq!(
            run_in(&scope, &SExpr::Zero("S1".to_owned(), Vec::new())),
            Err(Fault::Type)
        );
        // The arguments are the parameters, no fewer and no more.
        assert_eq!(
            run_in(&scope, &SExpr::Zero("S0".to_owned(), Vec::new())),
            Err(Fault::Type)
        );
        // A width of 0 bits is out of the bounds of the generator.
        let zero_width = SExpr::DataBits("S2".to_owned(), vec![int(0)]);
        assert_eq!(run_in(&scope, &zero_width), Err(Fault::Bound));
        assert_eq!(
            run_in(&scope, &SExpr::DataBits("S2".to_owned(), vec![int(1)])),
            value(1)
        );
    }

    fn text(s: &str) -> SExpr {
        SExpr::Str(s.to_owned())
    }

    #[test]
    fn strings_count_scalars_and_join() {
        let joined = bin(SBin::Add, text("h\u{e9}"), SExpr::StrOf(Box::new(int(-12))));
        assert_eq!(
            run(&joined).map(|v| v.serialize()),
            Ok("(string \"h\u{e9}-12\")".to_owned())
        );
        let len = |s: &str| SExpr::Len(Box::new(text(s)));
        assert_eq!(run(&len("\u{e9}\u{1f600}x")), value(3));
        assert_eq!(run(&len("")), value(0));
        let second = index(text("a\u{e9}b"), int(1));
        assert_eq!(run(&second), Ok(Value::Str("\u{e9}".to_owned())));
        assert_eq!(run(&index(text("ab"), int(2))), Err(Fault::Bound));
        assert_eq!(run(&index(text("ab"), int(-1))), Err(Fault::Bound));
        let same = bin(SBin::Eq, text("a"), text("a"));
        assert_eq!(run(&same), Ok(Value::Bool(true)));
        let order = bin(SBin::Lt, text("a"), text("b"));
        assert_eq!(run(&order), Err(Fault::Type));
        let mixed = bin(SBin::Add, text("a"), int(1));
        assert_eq!(run(&mixed), Err(Fault::Type));
        // The grammar escapes of a message print in the serialization.
        assert_eq!(
            run(&text("a\"b\\\n")).map(|v| v.serialize()),
            Ok("(string \"a\\\"b\\\\\\n\")".to_owned())
        );
        // More than 16 scalars is out of the bounds of the generator.
        let long = bin(SBin::Add, text("0123456789abcdef"), text("g"));
        assert_eq!(run(&long), Err(Fault::Bound));
        assert_eq!(
            run(&bin(SBin::Add, text("0123456789abcde"), text("f"))).map(|_| ()),
            Ok(())
        );
    }

    /// `comptime fn b0(x0: Nat) -> List[Int]` with the element `(j0 - 1)`,
    /// and `b1` the same with `List[Nat]`.
    fn builders() -> Scope {
        let f = |name: &str, elem: STy| ListFn {
            name: name.to_owned(),
            params: vec![("x0".to_owned(), STy::Nat)],
            elem,
            element: bin(SBin::Sub, name_expr("j0"), int(1)),
        };
        let items = [
            Item::ListFn(f("b0", STy::Int)),
            Item::ListFn(f("b1", STy::Nat)),
        ];
        Scope::new(&items).unwrap_or_default()
    }

    fn name_expr(n: &str) -> SExpr {
        SExpr::Name(n.to_owned())
    }

    #[test]
    fn list_builders_push_in_a_loop() {
        let scope = builders();
        let call = |f: &str, n: i64| SExpr::Call(f.to_owned(), vec![int(n)]);
        assert_eq!(
            run_in(&scope, &call("b0", 3)).map(|v| v.serialize()),
            Ok("(list int ((int -1) (int 0) (int 1)))".to_owned())
        );
        assert_eq!(
            run_in(&scope, &call("b0", 0)).map(|v| v.serialize()),
            Ok("(list int ())".to_owned())
        );
        // The element -1 is no `Nat`.
        assert_eq!(run_in(&scope, &call("b1", 2)), Err(Fault::Nat));
        assert_eq!(
            run_in(&scope, &call("b1", 0)).map(|v| v.serialize()),
            Ok("(list nat ())".to_owned())
        );
        assert_eq!(run_in(&scope, &call("b0", 9)), Err(Fault::Bound));
        assert_eq!(run_in(&scope, &call("b0", -1)), Err(Fault::Nat));
        let at = |n: i64| index(call("b0", 3), int(n));
        assert_eq!(run_in(&scope, &at(2)), value(1));
        assert_eq!(run_in(&scope, &at(3)), Err(Fault::Bound));
        assert_eq!(
            run_in(&scope, &SExpr::Len(Box::new(call("b0", 5)))),
            value(5)
        );
    }

    #[test]
    fn static_statements_change_the_env() {
        let scope = Scope::default();
        let mut env = Env::default();
        let list = |t: STy| {
            Stmt::MutLet(
                "s0".to_owned(),
                STy::List(Box::new(t)),
                SExpr::NewList(STy::Nat),
            )
        };
        let push = |n: i64| Stmt::Push("s0".to_owned(), int(n));
        let pop = Stmt::PopLet("s1".to_owned(), "s0".to_owned());
        assert_eq!(exec_static(&pop, &mut env, &scope), Err(Fault::Type));
        assert_eq!(exec_static(&list(STy::Nat), &mut env, &scope), Ok(()));
        assert_eq!(exec_static(&pop, &mut env, &scope), Err(Fault::Bound));
        assert_eq!(exec_static(&push(4), &mut env, &scope), Ok(()));
        assert_eq!(exec_static(&push(5), &mut env, &scope), Ok(()));
        assert_eq!(exec_static(&push(-1), &mut env, &scope), Err(Fault::Nat));
        assert_eq!(exec_static(&pop, &mut env, &scope), Ok(()));
        assert_eq!(env.statics.get("s1"), Some(&Value::Int(BigInt::from(5))));
        assert_eq!(
            env.statics.get("s0").map(Value::serialize),
            Some("(list nat ((int 4)))".to_owned())
        );
        for _ in 0..7 {
            assert_eq!(exec_static(&push(1), &mut env, &scope), Ok(()));
        }
        assert_eq!(exec_static(&push(1), &mut env, &scope), Err(Fault::Bound));
    }

    /// `k0(mut a0: Int, x1: Int) -> Int { a0 = (a0 + x1); return (a0 * 2); }`
    /// and `k1(mut a0: List[Int], x1: Int) -> Int { a0.push(x1); return (x1 + len(a0)); }`.
    fn mutators() -> Scope {
        let k0 = MutFn {
            name: "k0".to_owned(),
            root: STy::Int,
            pre: Vec::new(),
            update: bin(SBin::Add, name_expr("a0"), name_expr("x1")),
            ret: bin(SBin::Mul, name_expr("a0"), int(2)),
            diag: None,
        };
        let k1 = MutFn {
            name: "k1".to_owned(),
            root: STy::List(Box::new(STy::Int)),
            pre: Vec::new(),
            update: name_expr("x1"),
            ret: bin(
                SBin::Add,
                name_expr("x1"),
                SExpr::Len(Box::new(name_expr("a0"))),
            ),
            diag: None,
        };
        Scope::new(&[Item::MutFn(k0), Item::MutFn(k1)]).unwrap_or_default()
    }

    fn mut_call(f: &str, root: &str, arg: i64) -> Stmt {
        Stmt::MutCall {
            name: "r".to_owned(),
            root: root.to_owned(),
            f: f.to_owned(),
            args: vec![int(arg)],
            receiver: false,
        }
    }

    #[test]
    fn a_call_writes_its_formal_back_to_the_root() {
        let scope = mutators();
        let mut env = Env::default();
        env.statics
            .insert("n".to_owned(), Value::Int(BigInt::from(5)));
        env.statics
            .insert("xs".to_owned(), Value::List(STy::Int, Vec::new()));
        assert_eq!(
            exec_static(&mut_call("k0", "n", 3), &mut env, &scope),
            Ok(())
        );
        assert_eq!(env.statics.get("n"), Some(&Value::Int(BigInt::from(8))));
        assert_eq!(env.statics.get("r"), Some(&Value::Int(BigInt::from(16))));
        assert_eq!(
            exec_static(&mut_call("k1", "xs", 7), &mut env, &scope),
            Ok(())
        );
        assert_eq!(
            env.statics.get("xs").map(Value::serialize),
            Some("(list int ((int 7)))".to_owned())
        );
        assert_eq!(env.statics.get("r"), Some(&Value::Int(BigInt::from(8))));
        // A root of the wrong type, a missing root, and a full list.
        assert_eq!(
            exec_static(&mut_call("k0", "xs", 1), &mut env, &scope),
            Err(Fault::Type)
        );
        assert_eq!(
            exec_static(&mut_call("k0", "none", 1), &mut env, &scope),
            Err(Fault::Type)
        );
        for _ in 0..7 {
            assert_eq!(
                exec_static(&mut_call("k1", "xs", 1), &mut env, &scope),
                Ok(())
            );
        }
        assert_eq!(
            exec_static(&mut_call("k1", "xs", 1), &mut env, &scope),
            Err(Fault::Bound)
        );
        // The root keeps its value when the call faults.
        assert!(matches!(
            env.statics.get("xs"),
            Some(Value::List(_, xs)) if xs.len() == 8
        ));
        let no_arg = Stmt::MutCall {
            name: "r".to_owned(),
            root: "n".to_owned(),
            f: "k0".to_owned(),
            args: Vec::new(),
            receiver: true,
        };
        assert_eq!(exec_static(&no_arg, &mut env, &scope), Err(Fault::Type));
    }

    fn fn_ty(params: &[(bool, STy)], ret: STy) -> STy {
        STy::Fn(Box::new(FnTy {
            params: params.to_vec(),
            ret,
        }))
    }

    /// `f` of `twice()`, `k0` of `mutators()`, and the consts that hold them.
    fn values() -> Vec<Item> {
        let mut items = twice();
        items.retain(|i| !matches!(i, Item::Const { .. }));
        let mut_fn = MutFn {
            name: "k0".to_owned(),
            root: STy::Int,
            pre: Vec::new(),
            update: bin(SBin::Add, name_expr("a0"), name_expr("x1")),
            ret: name_expr("a0"),
            diag: None,
        };
        let consts = [
            (
                "F0",
                fn_ty(&[(false, STy::Nat), (false, STy::Int)], STy::Int),
                "f",
            ),
            (
                "F1",
                fn_ty(&[(true, STy::Int), (false, STy::Int)], STy::Int),
                "k0",
            ),
        ];
        items.push(Item::MutFn(mut_fn));
        for (n, ty, target) in consts {
            items.push(Item::Const {
                name: n.to_owned(),
                ty,
                value: name_expr(target),
            });
        }
        items
    }

    #[test]
    fn a_call_through_a_function_value_runs_its_item() {
        let Ok(scope) = Scope::new(&values()) else {
            panic!("the scope faults");
        };
        let call = |f: &str| SExpr::Call(f.to_owned(), vec![int(3), int(1)]);
        assert_eq!(run_in(&scope, &call("F0")), run_in(&scope, &call("f")));
        assert_eq!(run_in(&scope, &call("F0")), value(11));
        assert_eq!(
            run_in(&scope, &name_expr("F0")).map(|v| v.serialize()),
            Ok("(function root f)".to_owned())
        );
        // The item name is a value too, with its own type.
        assert_eq!(
            run_in(&scope, &name_expr("f")).map(|v| v.ty()),
            Ok(fn_ty(&[(false, STy::Nat), (false, STy::Int)], STy::Int))
        );
        // A call of a name that holds a value that is no function.
        let items = [Item::Const {
            name: "C0".to_owned(),
            ty: STy::Int,
            value: int(1),
        }];
        let Ok(plain) = Scope::new(&items) else {
            panic!("the scope faults");
        };
        let c0 = SExpr::Call("C0".to_owned(), Vec::new());
        assert_eq!(run_in(&plain, &c0), Err(Fault::Type));
    }

    #[test]
    fn a_value_has_the_exact_type_of_its_const() {
        let mut items = values();
        // `F0` has the mark `mut` on `x0`, which `f` has not.
        items.push(Item::Const {
            name: "F2".to_owned(),
            ty: fn_ty(&[(true, STy::Nat), (false, STy::Int)], STy::Int),
            value: name_expr("f"),
        });
        assert_eq!(Scope::new(&items).map(|_| ()), Err(Fault::Type));
    }

    #[test]
    fn a_mut_call_through_a_value_writes_back() {
        let Ok(scope) = Scope::new(&values()) else {
            panic!("the scope faults");
        };
        let mut env = Env::default();
        env.statics
            .insert("n".to_owned(), Value::Int(BigInt::from(4)));
        assert_eq!(
            exec_static(&mut_call("F1", "n", 5), &mut env, &scope),
            Ok(())
        );
        assert_eq!(env.statics.get("n"), Some(&Value::Int(BigInt::from(9))));
        // A parameter that holds a function takes the same path.
        let f = scope
            .fn_ty("k0")
            .map(|t| Value::Function("k0".to_owned(), t));
        env.statics.extend(f.map(|f| ("P0".to_owned(), f)));
        assert_eq!(
            exec_static(&mut_call("P0", "n", 1), &mut env, &scope),
            Ok(())
        );
        assert_eq!(env.statics.get("n"), Some(&Value::Int(BigInt::from(10))));
    }

    #[test]
    fn values_serialize_like_eval() {
        assert_eq!(Value::Int(BigInt::from(-5)).serialize(), "(int -5)");
        assert_eq!(Value::Bool(true).serialize(), "(bool true)");
        assert_eq!(Value::Bool(false).serialize(), "(bool false)");
    }

    fn variant(name: &str, tag: u32, payload: &[Scalar]) -> crate::program::Variant {
        crate::program::Variant {
            name: name.to_owned(),
            tag: BigUint::from(tag),
            payload: payload.to_vec(),
        }
    }

    /// `enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4]) = 2 }`
    /// of the elaborator tests.
    fn op() -> EnumDef {
        EnumDef {
            name: "Op".to_owned(),
            tag_width: 2,
            variants: vec![
                variant("Add", 0, &[]),
                variant("Load", 1, &[Scalar::UInt(8)]),
                variant("Pair", 2, &[Scalar::Bool, Scalar::UInt(4)]),
            ],
        }
    }

    fn run_enum(def: EnumDef, e: &SExpr) -> Result<String, Fault> {
        let Ok(scope) = Scope::new(&[Item::Enum(def)]) else {
            panic!("the scope faults");
        };
        eval(e, &Env::default(), &scope).map(|v| v.serialize())
    }

    fn ctor(e: &str, v: &str, args: Vec<SExpr>) -> SExpr {
        SExpr::Ctor(e.to_owned(), v.to_owned(), args)
    }

    /// The payload packs its leaves with the first in the low bits (ADR
    /// 0025). The values are those of `crates/elab/src/tests_enum.rs`.
    #[test]
    fn a_payload_packs_the_first_leaf_low() {
        let pair = |a: bool, b: i64| ctor("Op", "Pair", vec![SExpr::Bool(a), int(b)]);
        let want = |tag: u32, bits: u32| format!("(enum (enum root Op ()) {tag} (uint 8 {bits}))");
        assert_eq!(run_enum(op(), &pair(true, 5)), Ok(want(2, 11)));
        assert_eq!(run_enum(op(), &pair(false, 15)), Ok(want(2, 30)));
        assert_eq!(run_enum(op(), &ctor("Op", "Add", vec![])), Ok(want(0, 0)));
        assert_eq!(
            run_enum(op(), &ctor("Op", "Load", vec![int(5)])),
            Ok(want(1, 5))
        );
        assert_eq!(run_enum(op(), &pair(true, 16)), Err(Fault::Bound));
        assert_eq!(run_enum(op(), &pair(true, -1)), Err(Fault::Bound));
    }

    /// A signed leaf packs its two's complement.
    #[test]
    fn a_signed_leaf_packs_its_twos_complement() {
        let def = EnumDef {
            name: "E".to_owned(),
            tag_width: 1,
            variants: vec![variant("A", 1, &[Scalar::SInt(4), Scalar::Bool])],
        };
        let e = ctor("E", "A", vec![int(-1), SExpr::Bool(true)]);
        assert_eq!(
            run_enum(def.clone(), &e),
            Ok("(enum (enum root E ()) 1 (uint 5 31))".to_owned())
        );
        let e = ctor("E", "A", vec![int(-8), SExpr::Bool(false)]);
        assert_eq!(
            run_enum(def.clone(), &e),
            Ok("(enum (enum root E ()) 1 (uint 5 8))".to_owned())
        );
        let e = ctor("E", "A", vec![int(8), SExpr::Bool(false)]);
        assert_eq!(run_enum(def, &e), Err(Fault::Bound));
    }

    /// An unpack gives back the leaves, with the sign extension of an `SInt`.
    #[test]
    fn a_leaf_unpacks_with_its_sign() {
        let payload = BigUint::from(0b1_1001u8);
        assert_eq!(
            unpack_leaf(Scalar::SInt(4), 0, &payload),
            Value::SInt(4, BigInt::from(-7))
        );
        assert_eq!(unpack_leaf(Scalar::Bool, 4, &payload), Value::Bool(true));
        assert_eq!(
            unpack_leaf(Scalar::UInt(3), 1, &payload),
            Value::UInt(3, BigInt::from(4))
        );
    }

    /// `E()` and `reinterpret` can make a tag that no variant declares.
    #[test]
    fn zero_and_reinterpret_make_any_tag() {
        let bits = |n: i64| {
            SExpr::Unpack(
                "Op".to_owned(),
                Box::new(SExpr::BitsConv("Op".to_owned(), Box::new(int(n)))),
            )
        };
        let zero = SExpr::Zero("Op".to_owned(), Vec::new());
        assert_eq!(
            run_enum(op(), &zero),
            Ok("(enum (enum root Op ()) 0 (uint 8 0))".to_owned())
        );
        assert_eq!(
            run_enum(op(), &bits(2 + (11 << 2))),
            Ok("(enum (enum root Op ()) 2 (uint 8 11))".to_owned())
        );
        assert_eq!(
            run_enum(op(), &bits(3)),
            Ok("(enum (enum root Op ()) 3 (uint 8 0))".to_owned())
        );
        assert_eq!(run_enum(op(), &bits(1 << 10)), Err(Fault::Bound));
        let pack = SExpr::Pack("Op".to_owned(), Box::new(bits(2 + (11 << 2))));
        assert_eq!(run_enum(op(), &pack), Ok("(uint 10 46)".to_owned()));
        let empty = EnumDef {
            name: "E".to_owned(),
            tag_width: 3,
            variants: vec![variant("A", 5, &[])],
        };
        assert_eq!(
            run_enum(empty.clone(), &SExpr::Zero("E".to_owned(), Vec::new())),
            Ok("(enum (enum root E ()) 0)".to_owned())
        );
        let size = SExpr::DataBits("Op".to_owned(), Vec::new());
        assert_eq!(run_enum(op(), &size), Ok("(int 10)".to_owned()));
    }

    fn arm_match(scrutinee: SExpr, arms: Vec<(Pattern, SExpr)>) -> SExpr {
        SExpr::Match(Match {
            scrutinee: Box::new(scrutinee),
            arms,
        })
    }

    /// Only the selected arm runs: a fault in another arm is no fault.
    #[test]
    fn a_static_match_runs_the_selected_arm_only() {
        let lit = |n: i64| Pattern::Int(BigInt::from(n), Radix::Dec);
        let boom = bin(SBin::Div, int(1), int(0));
        let m = arm_match(
            int(2),
            vec![
                (lit(1), boom.clone()),
                (lit(2), int(7)),
                (Pattern::Wild, boom),
            ],
        );
        assert_eq!(run(&m), value(7));
        let none = arm_match(int(5), vec![(lit(1), int(1))]);
        assert_eq!(run(&none), Err(Fault::Type));
        let b = arm_match(
            SExpr::Bool(true),
            vec![
                (Pattern::Bool(false), int(0)),
                (Pattern::Bool(true), int(1)),
            ],
        );
        assert_eq!(run(&b), value(1));
    }

    /// A variant pattern binds the unpacked leaves, with sign extension.
    #[test]
    fn a_static_match_unpacks_binders() {
        let def = EnumDef {
            name: "E".to_owned(),
            tag_width: 1,
            variants: vec![variant("A", 1, &[Scalar::SInt(4), Scalar::Bool])],
        };
        let pattern = Pattern::Variant(
            "E".to_owned(),
            "A".to_owned(),
            vec![Some("B0".to_owned()), Some("B1".to_owned())],
        );
        let scrutinee = ctor("E", "A", vec![int(-3), SExpr::Bool(true)]);
        let m = arm_match(scrutinee.clone(), vec![(pattern.clone(), name("B0"))]);
        assert_eq!(run_enum(def.clone(), &m), Ok("(sint 4 -3)".to_owned()));
        let m = arm_match(scrutinee, vec![(pattern, name("B1"))]);
        assert_eq!(run_enum(def, &m), Ok("(bool true)".to_owned()));
    }
}
