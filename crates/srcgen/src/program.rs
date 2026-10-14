// SPDX-License-Identifier: Apache-2.0
//! The typed form of a generated slice-1 program and its one printer.
//!
//! A static expression (`SExpr`) has a static `Int` or `Bool` value, and the
//! evaluator of `super::eval` computes it. A hardware expression (`HExpr`)
//! makes a graph node. The two forms take different operator sets, so a
//! wrapping operator on `Int` or a mathematical one on hardware cannot occur.
//!
//! The printer puts each unary, binary, and `if` expression in parentheses,
//! so no precedence rule and no non-associative comparison can change the
//! parse. A negative literal prints in parentheses too.

use super::eval::Value;
use num_bigint::{BigInt, Sign};

/// The spelling of a non-negative literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Radix {
    Dec,
    Hex,
    Bin,
}

/// The type of a static parameter, formal, result, or binding. A container
/// type holds `Int` and `Bool` leaves only: the serialization of an array
/// names the element type, and `Nat` is a check on an `Int`, not a type of
/// its value. `UInt` and `SInt` are the types of the hardware fields of a
/// record, with their width evaluated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum STy {
    Nat,
    Int,
    Bool,
    /// `(T, U)`, or `(T,)` for one element.
    Tuple(Vec<STy>),
    /// `[T; N]` with `N >= 1`.
    Array(Box<STy>, u32),
    UInt(u32),
    SInt(u32),
    Record(Box<RecTy>),
    /// A string of at most 16 scalars.
    Str,
    /// `List[Int]` or `List[Nat]`.
    List(Box<STy>),
}

/// A struct specialization: the struct, its arguments, and its field types
/// with the widths evaluated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RecTy {
    pub(crate) name: String,
    pub(crate) args: Vec<Value>,
    pub(crate) fields: Vec<(String, STy)>,
}

impl RecTy {
    /// Whether `T()` makes a zero of the type: each field is hardware data
    /// that is a `Bool` or a finite integer.
    pub(crate) fn zeroable(&self) -> bool {
        self.fields
            .iter()
            .all(|(_, t)| matches!(t, STy::Bool | STy::UInt(_) | STy::SInt(_)))
    }
}

impl STy {
    /// The source spelling of the type.
    pub(crate) fn text(&self) -> String {
        match self {
            STy::Nat => "Nat".to_owned(),
            STy::Int => "Int".to_owned(),
            STy::Bool => "Bool".to_owned(),
            STy::Tuple(ts) if ts.len() == 1 => format!("({},)", ts[0].text()),
            STy::Tuple(ts) => format!(
                "({})",
                ts.iter().map(STy::text).collect::<Vec<_>>().join(", ")
            ),
            STy::Array(t, n) => format!("[{}; {n}]", t.text()),
            STy::UInt(w) => format!("UInt[{w}]"),
            STy::SInt(w) => format!("SInt[{w}]"),
            STy::Str => "String".to_owned(),
            STy::List(t) => format!("List[{}]", t.text()),
            STy::Record(r) if r.args.is_empty() => r.name.clone(),
            STy::Record(r) => {
                let args: Vec<String> = r.args.iter().map(Value::spelling).collect();
                format!("{}[{}]", r.name, args.join(", "))
            }
        }
    }

    /// Whether the type is a tuple, an array, a record, or a list.
    pub(crate) fn is_container(&self) -> bool {
        matches!(
            self,
            STy::Tuple(_) | STy::Array(..) | STy::Record(_) | STy::List(_)
        )
    }
}

/// A hardware data type. A width is a static expression.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Ty {
    Bool,
    UInt(SExpr),
    SInt(SExpr),
}

/// The unary operators, static and hardware: `-`, `~`, `!`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Un {
    Neg,
    Inv,
    Not,
}

/// The operators on static `Int` and `Bool`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SBin {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Land,
    Lor,
}

/// The operators on hardware values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HBin {
    Addw,
    Subw,
    Mulw,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Land,
    Lor,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum SExpr {
    Int(BigInt, Radix),
    Bool(bool),
    Name(String),
    /// A call of a `comptime fn`.
    Call(String, Vec<SExpr>),
    /// A tuple literal.
    Tuple(Vec<SExpr>),
    /// An array literal with at least one element.
    Array(Vec<SExpr>),
    /// `base[index]` of an array.
    Index(Box<SExpr>, Box<SExpr>),
    /// `base.N` of a tuple, with the spelling of `N`.
    Select(Box<SExpr>, u32, Radix),
    /// `len(base)` of an array.
    Len(Box<SExpr>),
    /// `S[args](fields)`, or `S(fields)` of a struct without parameters.
    Record(String, Vec<SExpr>, Vec<SExpr>),
    /// The zero `S[args]()` of a struct of hardware data.
    Zero(String, Vec<SExpr>),
    /// `data_bits(S[args])`.
    DataBits(String, Vec<SExpr>),
    /// `base.f` of a record.
    Field(Box<SExpr>, String),
    /// A string literal.
    Str(String),
    /// `str(n)`.
    StrOf(Box<SExpr>),
    /// `list(T)`.
    NewList(STy),
    Unary(Un, Box<SExpr>),
    Binary(SBin, Box<SExpr>, Box<SExpr>),
    If(Box<SExpr>, Box<SExpr>, Box<SExpr>),
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum HExpr {
    Name(String),
    /// An output `u.q` of an instance.
    Field(String, String),
    /// A static value next to a finite operand, or a static condition.
    Static(SExpr),
    /// `T(n)`.
    Make(Ty, SExpr),
    Unary(Un, Box<HExpr>),
    Binary(HBin, Box<HExpr>, Box<HExpr>),
    If(Box<HExpr>, Box<HExpr>, Box<HExpr>),
    Resize(Ty, Box<HExpr>),
    Reinterpret(Ty, Box<HExpr>),
    /// A call of a helper `fn`.
    Call(String, Vec<HExpr>),
}

/// The target of `:=`.
#[derive(Clone, Debug)]
pub(crate) enum Place {
    Name(String),
    /// An input `u.p` of an instance.
    Field(String, String),
}

#[derive(Clone, Debug)]
pub(crate) enum Stmt {
    Input(String, Ty),
    Output(String, Ty),
    /// A register with its reset value.
    Reg(String, Ty, SExpr),
    Wire(String, Ty),
    Let {
        name: String,
        mutable: bool,
        ty: Option<Ty>,
        value: HExpr,
    },
    StaticLet(String, STy, SExpr),
    /// `name = value;` of a `let mut`.
    Assign(String, HExpr),
    Connect(Place, HExpr),
    Instance(String, String, Vec<SExpr>),
    If(SExpr, Vec<Stmt>, Option<Vec<Stmt>>),
    /// `comptime for binder in lo..hi { body }`.
    For(String, SExpr, SExpr, Vec<Stmt>),
    Assert(SExpr, String),
    Error(String),
    /// `let mut name: T = value;` of a static value.
    MutLet(String, STy, SExpr),
    /// `list.push(value);`
    Push(String, SExpr),
    /// `let name: Int = list.pop();`: the new name, then the list.
    PopLet(String, String),
    /// A block `{ ... }`. The twin writes a selected `comptime if` branch
    /// and each iteration of a `comptime for` as one.
    Block(Vec<Stmt>),
}

/// A `comptime fn` that builds a list:
///
/// ```text
/// comptime fn name(x0: Nat, ...) -> List[T] {
///     let mut r0 = list(T);
///     comptime for j0 in 0..x0 { r0.push(element); }
///     return r0;
/// }
/// ```
#[derive(Clone, Debug)]
pub(crate) struct ListFn {
    pub(crate) name: String,
    /// The first formal is the length `Nat`.
    pub(crate) params: Vec<(String, STy)>,
    /// `Int` or `Nat`.
    pub(crate) elem: STy,
    /// Over the formals and the binder `j0`.
    pub(crate) element: SExpr,
}

/// The type of a field in the declaration of a struct.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum FieldTy {
    /// A static type: `Int`, `Bool`, or a container of them.
    Static(STy),
    /// `UInt[W]` over the parameters of the struct.
    UInt(SExpr),
    SInt(SExpr),
}

/// `struct name(comptime W0: Nat, ...) { m0: T0, ... }`. A struct without
/// parameters has no parentheses.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct StructDef {
    pub(crate) name: String,
    pub(crate) params: Vec<String>,
    pub(crate) fields: Vec<(String, FieldTy)>,
}

/// `comptime fn name(params) -> ret { comptime if ((x == 0)) { return base; } return step; }`,
/// where `x` is the first formal.
#[derive(Clone, Debug)]
pub(crate) struct ComptimeFn {
    pub(crate) name: String,
    pub(crate) params: Vec<(String, STy)>,
    pub(crate) ret: STy,
    pub(crate) base: SExpr,
    pub(crate) step: SExpr,
}

#[derive(Clone, Debug)]
pub(crate) enum Item {
    Const {
        name: String,
        ty: STy,
        value: SExpr,
    },
    ComptimeFn(ComptimeFn),
    ListFn(ListFn),
    Struct(StructDef),
    Helper {
        name: String,
        params: Vec<(String, Ty)>,
        ret: Ty,
        body: Vec<Stmt>,
        result: HExpr,
    },
    /// A module with `comptime` parameters. A clocked module has no domain
    /// clause, so its domain is `clock`; a combinational one has `domains()`.
    Module {
        name: String,
        params: Vec<(String, STy)>,
        clocked: bool,
        body: Vec<Stmt>,
    },
}

/// A scalar type with a known width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scalar {
    Bool,
    UInt(u32),
    SInt(u32),
}

/// The ports of the top instantiation, each list byte-sorted by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ports {
    pub clocked: bool,
    pub inputs: Vec<(String, Scalar)>,
    pub outputs: Vec<(String, Scalar)>,
}

/// A generated program: its items, the top selection, the ports of the top,
/// and an `eval` probe with the value that the generator computes.
#[derive(Clone, Debug)]
pub struct Program {
    pub(crate) items: Vec<Item>,
    pub(crate) top: String,
    pub(crate) args: Vec<Value>,
    pub(crate) ports: Ports,
    pub(crate) probe: (SExpr, Value),
}

impl Program {
    /// The source text.
    #[must_use]
    pub fn text(&self) -> String {
        render_items(&self.items)
    }

    /// The top selection, for example `M0(3, -5, true)`.
    #[must_use]
    pub fn top(&self) -> String {
        let args: Vec<String> = self.args.iter().map(Value::spelling).collect();
        format!("{}({})", self.top, args.join(", "))
    }

    #[must_use]
    pub fn ports(&self) -> &Ports {
        &self.ports
    }

    /// The `eval` expression of the file scope and its serialization.
    #[must_use]
    pub fn probe(&self) -> (String, String) {
        (sexpr(&self.probe.0), self.probe.1.serialize())
    }
}

const INDENT: &str = "    ";

/// The source text of the items, in their order.
pub(crate) fn render_items(items: &[Item]) -> String {
    let mut out = String::new();
    for item in items {
        render_item(&mut out, item);
    }
    out
}

fn render_item(out: &mut String, item: &Item) {
    match item {
        Item::Const { name, ty, value } => {
            line(
                out,
                0,
                &format!("const {name}: {} = {};", ty.text(), sexpr(value)),
            );
        }
        Item::ComptimeFn(f) => {
            let params = formals(f.params.iter().map(|(n, t)| (n, t.text())));
            let first = f.params.first().map_or("", |(n, _)| n.as_str());
            line(
                out,
                0,
                &format!("comptime fn {}({params}) -> {} {{", f.name, f.ret.text()),
            );
            line(out, 1, &format!("comptime if (({first} == 0)) {{"));
            line(out, 2, &format!("return {};", sexpr(&f.base)));
            line(out, 1, "}");
            line(out, 1, &format!("return {};", sexpr(&f.step)));
            line(out, 0, "}");
        }
        Item::ListFn(f) => {
            let params = formals(f.params.iter().map(|(n, t)| (n, t.text())));
            let count = f.params.first().map_or("0", |(n, _)| n.as_str());
            let elem = f.elem.text();
            line(
                out,
                0,
                &format!("comptime fn {}({params}) -> List[{elem}] {{", f.name),
            );
            line(out, 1, &format!("let mut r0 = list({elem});"));
            line(out, 1, &format!("comptime for j0 in 0..{count} {{"));
            line(out, 2, &format!("r0.push({});", sexpr(&f.element)));
            line(out, 1, "}");
            line(out, 1, "return r0;");
            line(out, 0, "}");
        }
        Item::Struct(def) => {
            let params: Vec<String> = def
                .params
                .iter()
                .map(|p| format!("comptime {p}: Nat"))
                .collect();
            let head = if params.is_empty() {
                def.name.clone()
            } else {
                format!("{}({})", def.name, params.join(", "))
            };
            line(out, 0, &format!("struct {head} {{"));
            for (f, t) in &def.fields {
                let t = match t {
                    FieldTy::Static(t) => t.text(),
                    FieldTy::UInt(w) => format!("UInt[{}]", sexpr(w)),
                    FieldTy::SInt(w) => format!("SInt[{}]", sexpr(w)),
                };
                line(out, 1, &format!("{f}: {t},"));
            }
            line(out, 0, "}");
        }
        Item::Helper {
            name,
            params,
            ret,
            body,
            result,
        } => {
            let params = formals(params.iter().map(|(n, t)| (n, ty(t))));
            line(out, 0, &format!("fn {name}({params}) -> {} {{", ty(ret)));
            stmts(out, 1, body);
            line(out, 1, &format!("return {};", hexpr(result)));
            line(out, 0, "}");
        }
        Item::Module {
            name,
            params,
            clocked,
            body,
        } => {
            let params: Vec<String> = params
                .iter()
                .map(|(n, t)| format!("comptime {n}: {}", t.text()))
                .collect();
            let domains = if *clocked { "" } else { " domains()" };
            line(
                out,
                0,
                &format!("module {name}({}){domains} {{", params.join(", ")),
            );
            stmts(out, 1, body);
            line(out, 0, "}");
        }
    }
}

fn formals<'a>(params: impl Iterator<Item = (&'a String, String)>) -> String {
    params
        .map(|(n, t)| format!("{n}: {t}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn line(out: &mut String, depth: usize, text: &str) {
    out.push_str(&INDENT.repeat(depth));
    out.push_str(text);
    out.push('\n');
}

fn stmts(out: &mut String, depth: usize, body: &[Stmt]) {
    for s in body {
        stmt(out, depth, s);
    }
}

fn stmt(out: &mut String, depth: usize, s: &Stmt) {
    let text = match s {
        Stmt::Input(n, t) => format!("input {n}: {};", ty(t)),
        Stmt::Output(n, t) => format!("output {n}: {};", ty(t)),
        Stmt::Reg(n, t, reset) => format!("reg {n}: {} = {};", ty(t), sexpr(reset)),
        Stmt::Wire(n, t) => format!("wire {n}: {};", ty(t)),
        Stmt::Let {
            name,
            mutable,
            ty: t,
            value,
        } => {
            let m = if *mutable { "mut " } else { "" };
            let t = t.as_ref().map_or(String::new(), |t| format!(": {}", ty(t)));
            format!("let {m}{name}{t} = {};", hexpr(value))
        }
        Stmt::StaticLet(n, t, v) => format!("let {n}: {} = {};", t.text(), sexpr(v)),
        Stmt::MutLet(n, t, v) => format!("let mut {n}: {} = {};", t.text(), sexpr(v)),
        Stmt::Push(n, v) => format!("{n}.push({});", sexpr(v)),
        Stmt::PopLet(n, list) => format!("let {n}: Int = {list}.pop();"),
        Stmt::Assign(n, v) => format!("{n} = {};", hexpr(v)),
        Stmt::Connect(place, v) => {
            let place = match place {
                Place::Name(n) => n.clone(),
                Place::Field(inst, port) => format!("{inst}.{port}"),
            };
            format!("{place} := {};", hexpr(v))
        }
        Stmt::Instance(n, m, args) => format!("instance {n} = {m}({});", list(args, sexpr)),
        Stmt::If(c, then, els) => {
            line(out, depth, &format!("comptime if ({}) {{", sexpr(c)));
            stmts(out, depth + 1, then);
            if let Some(els) = els {
                line(out, depth, "} else {");
                stmts(out, depth + 1, els);
            }
            "}".to_owned()
        }
        Stmt::For(b, lo, hi, body) => {
            line(
                out,
                depth,
                &format!("comptime for {b} in {}..{} {{", sexpr(lo), sexpr(hi)),
            );
            stmts(out, depth + 1, body);
            "}".to_owned()
        }
        Stmt::Assert(c, m) => format!("static_assert({}, {});", sexpr(c), string(m)),
        Stmt::Error(m) => format!("error({});", string(m)),
        Stmt::Block(body) => {
            line(out, depth, "{");
            stmts(out, depth + 1, body);
            "}".to_owned()
        }
    };
    line(out, depth, &text);
}

fn ty(t: &Ty) -> String {
    match t {
        Ty::Bool => "Bool".to_owned(),
        Ty::UInt(w) => format!("UInt[{}]", sexpr(w)),
        Ty::SInt(w) => format!("SInt[{}]", sexpr(w)),
    }
}

fn list<T>(xs: &[T], f: fn(&T) -> String) -> String {
    xs.iter().map(f).collect::<Vec<_>>().join(", ")
}

/// A string literal with the escapes of the grammar. The lexer has no escape
/// for another control character, so a message of the builder has none.
pub(crate) fn string(m: &str) -> String {
    let mut out = String::from("\"");
    for c in m.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn literal(n: &BigInt, radix: Radix) -> String {
    let magnitude = n.magnitude();
    let digits = match radix {
        Radix::Dec => magnitude.to_string(),
        Radix::Hex => format!("0x{magnitude:x}"),
        Radix::Bin => format!("0b{magnitude:b}"),
    };
    if n.sign() == Sign::Minus {
        format!("(-{digits})")
    } else {
        digits
    }
}

fn un(op: Un) -> &'static str {
    match op {
        Un::Neg => "-",
        Un::Inv => "~",
        Un::Not => "!",
    }
}

fn sbin(op: SBin) -> &'static str {
    match op {
        SBin::Add => "+",
        SBin::Sub => "-",
        SBin::Mul => "*",
        SBin::Div => "/",
        SBin::Rem => "%",
        SBin::And => "&",
        SBin::Or => "|",
        SBin::Xor => "^",
        SBin::Shl => "<<",
        SBin::Shr => ">>",
        SBin::Eq => "==",
        SBin::Ne => "!=",
        SBin::Lt => "<",
        SBin::Le => "<=",
        SBin::Gt => ">",
        SBin::Ge => ">=",
        SBin::Land => "&&",
        SBin::Lor => "||",
    }
}

fn hbin(op: HBin) -> &'static str {
    match op {
        HBin::Addw => "+%",
        HBin::Subw => "-%",
        HBin::Mulw => "*%",
        HBin::And => "&",
        HBin::Or => "|",
        HBin::Xor => "^",
        HBin::Shl => "<<",
        HBin::Shr => ">>",
        HBin::Eq => "==",
        HBin::Ne => "!=",
        HBin::Lt => "<",
        HBin::Le => "<=",
        HBin::Gt => ">",
        HBin::Ge => ">=",
        HBin::Land => "&&",
        HBin::Lor => "||",
    }
}

pub(crate) fn sexpr(e: &SExpr) -> String {
    match e {
        SExpr::Int(n, radix) => literal(n, *radix),
        SExpr::Bool(b) => b.to_string(),
        SExpr::Name(n) => n.clone(),
        SExpr::Call(f, args) => format!("{f}({})", list(args, sexpr)),
        SExpr::Tuple(xs) if xs.len() == 1 => format!("({},)", list(xs, sexpr)),
        SExpr::Tuple(xs) => format!("({})", list(xs, sexpr)),
        SExpr::Array(xs) => format!("[{}]", list(xs, sexpr)),
        SExpr::Index(b, i) => format!("{}[{}]", postfix_base(b), sexpr(i)),
        SExpr::Select(b, k, radix) => {
            format!("{}.{}", postfix_base(b), literal(&BigInt::from(*k), *radix))
        }
        SExpr::Len(b) => format!("len({})", sexpr(b)),
        SExpr::Record(s, targs, fields) => {
            format!("{}({})", struct_use(s, targs), list(fields, sexpr))
        }
        SExpr::Zero(s, targs) => format!("{}()", struct_use(s, targs)),
        SExpr::DataBits(s, targs) => format!("data_bits({})", struct_use(s, targs)),
        SExpr::Field(b, f) => format!("{}.{f}", postfix_base(b)),
        SExpr::Str(s) => string(s),
        SExpr::StrOf(n) => format!("str({})", sexpr(n)),
        SExpr::NewList(t) => format!("list({})", t.text()),
        SExpr::Unary(op, a) => format!("({}{})", un(*op), sexpr(a)),
        SExpr::Binary(op, a, b) => format!("({} {} {})", sexpr(a), sbin(*op), sexpr(b)),
        SExpr::If(c, t, e) => {
            format!(
                "(if ({}) {{ {} }} else {{ {} }})",
                sexpr(c),
                sexpr(t),
                sexpr(e)
            )
        }
    }
}

/// `S` or `S[args]`: the use of a struct as a type.
fn struct_use(name: &str, targs: &[SExpr]) -> String {
    if targs.is_empty() {
        name.to_owned()
    } else {
        format!("{name}[{}]", list(targs, sexpr))
    }
}

/// The base of an index or a selector. A selector after a selector would
/// read `a.0.1` as one number, so it takes parentheses.
fn postfix_base(e: &SExpr) -> String {
    match e {
        SExpr::Select(..) => format!("({})", sexpr(e)),
        _ => sexpr(e),
    }
}

fn hexpr(e: &HExpr) -> String {
    match e {
        HExpr::Name(n) => n.clone(),
        HExpr::Field(u, n) => format!("{u}.{n}"),
        HExpr::Static(s) => sexpr(s),
        HExpr::Make(t, s) => format!("{}({})", ty(t), sexpr(s)),
        HExpr::Unary(op, a) => format!("({}{})", un(*op), hexpr(a)),
        HExpr::Binary(op, a, b) => format!("({} {} {})", hexpr(a), hbin(*op), hexpr(b)),
        HExpr::If(c, t, e) => {
            format!(
                "(if ({}) {{ {} }} else {{ {} }})",
                hexpr(c),
                hexpr(t),
                hexpr(e)
            )
        }
        HExpr::Resize(t, a) => format!("resize({}, {})", ty(t), hexpr(a)),
        HExpr::Reinterpret(t, a) => format!("reinterpret({}, {})", ty(t), hexpr(a)),
        HExpr::Call(f, args) => format!("{f}({})", list(args, hexpr)),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::super::eval::{Env, Scope, eval};
    use super::*;

    fn int(n: i64, radix: Radix) -> SExpr {
        SExpr::Int(BigInt::from(n), radix)
    }

    fn dec(n: i64) -> SExpr {
        int(n, Radix::Dec)
    }

    fn sname(n: &str) -> SExpr {
        SExpr::Name(n.to_owned())
    }

    fn hname(n: &str) -> HExpr {
        HExpr::Name(n.to_owned())
    }

    fn sbin(op: SBin, a: SExpr, b: SExpr) -> SExpr {
        SExpr::Binary(op, Box::new(a), Box::new(b))
    }

    fn hbin(op: HBin, a: HExpr, b: HExpr) -> HExpr {
        HExpr::Binary(op, Box::new(a), Box::new(b))
    }

    fn u8() -> Ty {
        Ty::UInt(dec(8))
    }

    /// The top module: one statement of each kind.
    fn m0() -> Item {
        let width = sbin(SBin::Add, sname("P0"), dec(1));
        let shifted = hbin(
            HBin::Shl,
            hbin(
                HBin::Addw,
                hname("i0"),
                HExpr::Make(u8(), int(15, Radix::Hex)),
            ),
            HExpr::Static(sbin(SBin::Add, dec(-1), dec(2))),
        );
        let select = HExpr::If(
            Box::new(hbin(HBin::Lt, hname("i0"), HExpr::Static(dec(3)))),
            Box::new(HExpr::Unary(Un::Inv, Box::new(hname("i0")))),
            Box::new(HExpr::Resize(
                u8(),
                Box::new(HExpr::Reinterpret(
                    Ty::UInt(dec(4)),
                    Box::new(HExpr::Field("u0".to_owned(), "o0".to_owned())),
                )),
            )),
        );
        Item::Module {
            name: "M0".to_owned(),
            params: vec![
                ("P0".to_owned(), STy::Nat),
                ("P1".to_owned(), STy::Int),
                ("P2".to_owned(), STy::Bool),
            ],
            clocked: true,
            body: vec![
                Stmt::Input("i0".to_owned(), u8()),
                Stmt::Output("o0".to_owned(), u8()),
                Stmt::Output("o1".to_owned(), Ty::Bool),
                Stmt::StaticLet(
                    "s0".to_owned(),
                    STy::Int,
                    SExpr::Call("f0".to_owned(), vec![sname("P0"), dec(-3)]),
                ),
                Stmt::Reg("r0".to_owned(), Ty::SInt(width), dec(-3)),
                Stmt::Instance("u0".to_owned(), "M1".to_owned(), vec![int(2, Radix::Bin)]),
                Stmt::Wire("w0".to_owned(), u8()),
                Stmt::Connect(Place::Name("w0".to_owned()), select),
                Stmt::Connect(
                    Place::Field("u0".to_owned(), "i0".to_owned()),
                    HExpr::Call("h0".to_owned(), vec![hname("i0")]),
                ),
                Stmt::Let {
                    name: "v0".to_owned(),
                    mutable: true,
                    ty: Some(u8()),
                    value: hname("w0"),
                },
                Stmt::For(
                    "j0".to_owned(),
                    dec(0),
                    sname("P0"),
                    vec![Stmt::Assign(
                        "v0".to_owned(),
                        hbin(HBin::Subw, hname("v0"), HExpr::Static(sname("j0"))),
                    )],
                ),
                Stmt::If(
                    sbin(SBin::Lt, sname("s0"), dec(0)),
                    vec![Stmt::Assert(SExpr::Bool(true), "a \"b\"".to_owned())],
                    Some(vec![Stmt::Error("dead".to_owned())]),
                ),
                Stmt::If(SExpr::Bool(false), vec![], None),
                Stmt::Connect(
                    Place::Name("r0".to_owned()),
                    HExpr::Unary(Un::Neg, Box::new(hname("r0"))),
                ),
                Stmt::Connect(Place::Name("o0".to_owned()), shifted),
                Stmt::Connect(
                    Place::Name("o1".to_owned()),
                    HExpr::Unary(Un::Not, Box::new(HExpr::Static(SExpr::Bool(false)))),
                ),
            ],
        }
    }

    /// A program with each construct of the printer.
    pub(crate) fn program() -> Program {
        let helper = Item::Helper {
            name: "h0".to_owned(),
            params: vec![("x0".to_owned(), u8())],
            ret: Ty::UInt(dec(4)),
            body: vec![Stmt::Let {
                name: "l0".to_owned(),
                mutable: false,
                ty: None,
                value: hname("x0"),
            }],
            result: HExpr::Resize(Ty::UInt(dec(4)), Box::new(hname("l0"))),
        };
        let f0 = Item::ComptimeFn(ComptimeFn {
            name: "f0".to_owned(),
            params: vec![("x0".to_owned(), STy::Nat), ("x1".to_owned(), STy::Int)],
            ret: STy::Int,
            base: sname("x1"),
            step: sbin(
                SBin::Add,
                SExpr::Call(
                    "f0".to_owned(),
                    vec![sbin(SBin::Sub, sname("x0"), dec(1)), sname("x1")],
                ),
                SExpr::If(
                    Box::new(SExpr::Bool(true)),
                    Box::new(SExpr::Unary(Un::Neg, Box::new(dec(1)))),
                    Box::new(sname("C0")),
                ),
            ),
        });
        let child = Item::Module {
            name: "M1".to_owned(),
            params: vec![("P0".to_owned(), STy::Nat)],
            clocked: false,
            body: vec![
                Stmt::Input("i0".to_owned(), Ty::UInt(dec(4))),
                Stmt::Output("o0".to_owned(), Ty::UInt(dec(4))),
                Stmt::Connect(Place::Name("o0".to_owned()), hname("i0")),
            ],
        };
        Program {
            items: vec![
                Item::Const {
                    name: "C0".to_owned(),
                    ty: STy::Nat,
                    value: dec(4),
                },
                f0,
                helper,
                m0(),
                child,
            ],
            top: "M0".to_owned(),
            args: vec![
                Value::Int(BigInt::from(3)),
                Value::Int(BigInt::from(-5)),
                Value::Bool(true),
            ],
            ports: Ports {
                clocked: true,
                inputs: vec![("i0".to_owned(), Scalar::UInt(8))],
                outputs: vec![
                    ("o0".to_owned(), Scalar::UInt(8)),
                    ("o1".to_owned(), Scalar::Bool),
                ],
            },
            probe: (
                SExpr::Call("f0".to_owned(), vec![dec(2), dec(-1)]),
                Value::Int(BigInt::from(-3)),
            ),
        }
    }

    pub(crate) const TEXT: &str = "\
const C0: Nat = 4;
comptime fn f0(x0: Nat, x1: Int) -> Int {
    comptime if ((x0 == 0)) {
        return x1;
    }
    return (f0((x0 - 1), x1) + (if (true) { (-1) } else { C0 }));
}
fn h0(x0: UInt[8]) -> UInt[4] {
    let l0 = x0;
    return resize(UInt[4], l0);
}
module M0(comptime P0: Nat, comptime P1: Int, comptime P2: Bool) {
    input i0: UInt[8];
    output o0: UInt[8];
    output o1: Bool;
    let s0: Int = f0(P0, (-3));
    reg r0: SInt[(P0 + 1)] = (-3);
    instance u0 = M1(0b10);
    wire w0: UInt[8];
    w0 := (if ((i0 < 3)) { (~i0) } else { resize(UInt[8], reinterpret(UInt[4], u0.o0)) });
    u0.i0 := h0(i0);
    let mut v0: UInt[8] = w0;
    comptime for j0 in 0..P0 {
        v0 = (v0 -% j0);
    }
    comptime if ((s0 < 0)) {
        static_assert(true, \"a \\\"b\\\"\");
    } else {
        error(\"dead\");
    }
    comptime if (false) {
    }
    r0 := (-r0);
    o0 := ((i0 +% UInt[8](0xf)) << ((-1) + 2));
    o1 := (!false);
}
module M1(comptime P0: Nat) domains() {
    input i0: UInt[4];
    output o0: UInt[4];
    o0 := i0;
}
";

    #[test]
    fn containers_print_with_their_selectors() {
        let t = SExpr::Name("s0".to_owned());
        let sel = |e: SExpr, k: u32, radix| SExpr::Select(Box::new(e), k, radix);
        assert_eq!(super::sexpr(&sel(t.clone(), 1, Radix::Dec)), "s0.1");
        assert_eq!(super::sexpr(&sel(t.clone(), 1, Radix::Hex)), "s0.0x1");
        let nested = sel(sel(t.clone(), 0, Radix::Dec), 1, Radix::Bin);
        assert_eq!(super::sexpr(&nested), "(s0.0).0b1");
        let a = SExpr::Array(vec![dec(1), dec(-2)]);
        let at = SExpr::Index(Box::new(a.clone()), Box::new(dec(0)));
        assert_eq!(super::sexpr(&at), "[1, (-2)][0]");
        assert_eq!(super::sexpr(&SExpr::Len(Box::new(a))), "len([1, (-2)])");
        assert_eq!(super::sexpr(&SExpr::Tuple(vec![dec(1)])), "(1,)");
        assert_eq!(
            super::sexpr(&SExpr::Tuple(vec![dec(1), SExpr::Bool(false)])),
            "(1, false)"
        );
        let ty = STy::Array(Box::new(STy::Tuple(vec![STy::Int, STy::Bool])), 2);
        assert_eq!(ty.text(), "[(Int, Bool); 2]");
        assert_eq!(STy::Tuple(vec![STy::Int]).text(), "(Int,)");
    }

    #[test]
    fn structs_print_and_construct() {
        let def = |params: &[&str], fields: Vec<(&str, FieldTy)>| {
            Item::Struct(StructDef {
                name: "S0".to_owned(),
                params: params.iter().map(|p| (*p).to_owned()).collect(),
                fields: fields.into_iter().map(|(f, t)| (f.to_owned(), t)).collect(),
            })
        };
        let wide = SExpr::Binary(SBin::Add, Box::new(sname("W0")), Box::new(dec(1)));
        let items = [
            def(
                &["W0", "W1"],
                vec![
                    ("m0", FieldTy::UInt(wide)),
                    ("m1", FieldTy::SInt(dec(3))),
                    ("m2", FieldTy::Static(STy::Bool)),
                ],
            ),
            def(&[], vec![("m0", FieldTy::Static(STy::Int))]),
        ];
        assert_eq!(
            render_items(&items),
            "struct S0(comptime W0: Nat, comptime W1: Nat) {\n    m0: UInt[(W0 + 1)],\n    m1: SInt[3],\n    m2: Bool,\n}\nstruct S0 {\n    m0: Int,\n}\n"
        );
        let args = vec![dec(8), dec(2)];
        let record = SExpr::Record(
            "S0".to_owned(),
            args.clone(),
            vec![dec(1), SExpr::Bool(true)],
        );
        assert_eq!(super::sexpr(&record), "S0[8, 2](1, true)");
        let plain = SExpr::Record("S0".to_owned(), Vec::new(), vec![dec(1)]);
        assert_eq!(super::sexpr(&plain), "S0(1)");
        assert_eq!(
            super::sexpr(&SExpr::Zero("S0".to_owned(), args.clone())),
            "S0[8, 2]()"
        );
        assert_eq!(
            super::sexpr(&SExpr::DataBits("S0".to_owned(), args)),
            "data_bits(S0[8, 2])"
        );
        let field = SExpr::Field(Box::new(record), "m1".to_owned());
        assert_eq!(super::sexpr(&field), "S0[8, 2](1, true).m1");
        let rec_ty = RecTy {
            name: "S0".to_owned(),
            args: vec![Value::Int(BigInt::from(8))],
            fields: vec![("m0".to_owned(), STy::UInt(8))],
        };
        assert_eq!(STy::Record(Box::new(rec_ty)).text(), "S0[8]");
    }

    #[test]
    fn lists_and_strings_print() {
        let build = Item::ListFn(ListFn {
            name: "b0".to_owned(),
            params: vec![("x0".to_owned(), STy::Nat), ("x1".to_owned(), STy::Int)],
            elem: STy::Nat,
            element: SExpr::Binary(SBin::Add, Box::new(sname("j0")), Box::new(sname("x1"))),
        });
        assert_eq!(
            render_items(&[build]),
            "comptime fn b0(x0: Nat, x1: Int) -> List[Nat] {\n    let mut r0 = list(Nat);\n    comptime for j0 in 0..x0 {\n        r0.push((j0 + x1));\n    }\n    return r0;\n}\n"
        );
        let body = vec![
            Stmt::MutLet(
                "s0".to_owned(),
                STy::List(Box::new(STy::Int)),
                SExpr::Call("b0".to_owned(), vec![dec(3), dec(1)]),
            ),
            Stmt::Push("s0".to_owned(), dec(-2)),
            Stmt::PopLet("s1".to_owned(), "s0".to_owned()),
            Stmt::StaticLet(
                "s2".to_owned(),
                STy::Str,
                SExpr::Binary(
                    SBin::Add,
                    Box::new(SExpr::Str("a\"".to_owned())),
                    Box::new(SExpr::StrOf(Box::new(sname("s1")))),
                ),
            ),
        ];
        let mut out = String::new();
        stmts(&mut out, 0, &body);
        assert_eq!(
            out,
            "let mut s0: List[Int] = b0(3, 1);\ns0.push((-2));\nlet s1: Int = s0.pop();\nlet s2: String = (\"a\\\"\" + str(s1));\n"
        );
    }

    #[test]
    fn strings_take_the_escapes_of_the_grammar() {
        assert_eq!(string("a\"b\\c\nd\re\tf"), r#""a\"b\\c\nd\re\tf""#);
    }

    #[test]
    fn the_printer_parenthesizes() {
        let p = program();
        assert_eq!(p.text(), TEXT);
        assert_eq!(p.top(), "M0(3, -5, true)");
        assert_eq!(p.probe(), ("f0(2, (-1))".to_owned(), "(int -3)".to_owned()));
        let scope = Scope::new(&p.items).map(|s| eval(&p.probe.0, &Env::default(), &s));
        assert_eq!(scope, Ok(Ok(p.probe.1.clone())));
        assert_eq!(p.ports().inputs, vec![("i0".to_owned(), Scalar::UInt(8))]);
        assert!(p.ports().clocked);
        assert_eq!(p.ports().outputs.len(), 2);
    }
}
