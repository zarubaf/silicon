// SPDX-License-Identifier: Apache-2.0
//! The lowering of section 7 of the front-end spec, as Lean `Source.Flatten` defines it.
//! `lower` maps the hardware descriptions of an elaborated design to a core design, and
//! `check` runs the core checker on it, as pass 6.
//!
//! Each instantiation gives one core module with its emitted name. Each name of a description
//! is its structural path. The expressions follow the table of section 7.4, and the
//! statements, the ports, and the domain follow section 7.5.
//!
//! The lowering charges the fuel that elaboration leaves. Each core node charges 1 unit: the
//! design, a module, a port, a statement, a reset, a connection, or an expression node. Each
//! field of a core name charges its length in bytes, at least 1, at each place where it
//! occurs. A made field that holds an integer charges the square of the size of the integer
//! instead. A charge comes before the node or the name that it pays. Above the fuel, the
//! result is `S015` at the source position of the node.
//!
//! A node whose effective height reaches 64 binds to a temporary, unless it is the value of
//! its statement. An operand that a rule uses twice binds to a temporary unless it is a leaf.
//! A leaf is copied, and the copy charges as a new node. The temporaries of one node bind
//! after its operands lower, in operand order.
//!
//! The lowering recurses over the hardware values, so it runs on a thread with a stack for
//! the highest of them. The core design that it makes is at most 256 levels deep.

use crate::agg::Agg;
use crate::eval::{Bind, Design, Inst, Sink};
use crate::hw::{HwId, Kind, Op};
use crate::int::{Nat, constant, nat};
use crate::layout;
use crate::names::{Field, Name, PathId, Role, Sym, encode};
use crate::types::Ty;
use crate::value::{Value, int_size};
use crate::{Code, Error};
use core_ir::Pred;
use core_ir::ast::{
    BinOp as CBin, Conn, Design as CDesign, Dir, Expr, Item, Module, Name as CName, Num, Port,
    Reset, Stmt, Ty as CTy, UnOp as CUn,
};
use core_ir::diag::{ErrorCode, Span};
use parse::StackError;
use parse::ast::{BinOp, Pos, UnOp};
use std::collections::BTreeMap;
use std::fmt::Write;

/// The failure of a lowering or of its check: a source error, or a defect of this elaborator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Failure {
    Source(Error),
    Defect(String),
}

/// A lowered design: the core design, the emitted name and the units of each instantiation
/// in the order they finish, and the fuel of the elaboration with the lowering.
pub struct Lowered {
    pub design: CDesign,
    units: Vec<(String, u64)>,
    used: u64,
}

impl Lowered {
    /// The fuel of the elaboration with the lowering.
    #[must_use]
    pub fn used(&self) -> u64 {
        self.used
    }

    /// The output of `cost` (section 8): the total, then the units of each instantiation,
    /// sorted by its emitted name.
    #[must_use]
    pub fn cost(&self) -> String {
        cost_lines(self.used, self.units.clone())
    }
}

/// The lines of `cost` for the total `total` and the units of each emitted name.
pub(crate) fn cost_lines(total: u64, mut lines: Vec<(String, u64)>) -> String {
    lines.sort();
    let mut out = format!("total {total}\n");
    for (x, u) in lines {
        let _ = writeln!(out, "{x} {u}");
    }
    out
}

/// Lowers `d` with the fuel that its elaboration leaves.
pub(crate) fn lower(d: &Design) -> Result<Result<Lowered, Failure>, StackError> {
    parse::on_stack(d.graph.height(), || {
        let mut lower = Lower {
            design: d,
            fuel: d.left,
            temps: Vec::new(),
            count: 0,
            shares: BTreeMap::new(),
        };
        let lowered = lower.design();
        lowered.map(|(design, units)| Lowered {
            design,
            units,
            used: d.used() + (d.left - lower.fuel),
        })
    })
}

/// The check of pass 6. A core `E008` is `S020` at its position, and each other core error is
/// a defect.
///
/// # Errors
/// Returns the failure of the check.
pub fn check(design: &CDesign) -> Result<core_ir::typed::Design, Failure> {
    core_ir::check::check(design).map_err(|e| {
        if e.code == ErrorCode::E008 {
            Failure::Source(Error {
                code: Code::S020,
                pos: Pos {
                    line: usize::try_from(e.span.line).unwrap_or(usize::MAX),
                    col: usize::try_from(e.span.col).unwrap_or(usize::MAX),
                },
                message: "the lowered design has a combinational cycle".to_owned(),
            })
        } else {
            Failure::Defect(e.to_string())
        }
    })
}

type R<T> = Result<T, Failure>;

fn defect<T>(msg: &str) -> R<T> {
    Err(Failure::Defect(msg.to_owned()))
}

/// The hardware value of a scalar `:=` binding. An aggregate binding has no lowering here.
fn scalar(a: &Agg) -> R<HwId> {
    match a {
        Agg::Hw(h) => Ok(*h),
        _ => defect("a `:=` binding of an aggregate has no lowering by leaf"),
    }
}

/// The charge of a field: its length in bytes, at least 1. A made field that holds an
/// integer charges the square of the size of the integer instead, at least 1.
fn field_units(f: &Field) -> u128 {
    match f {
        Field::User(x) => x.len().max(1) as u128,
        Field::Int(n) | Field::Elem(n) => u128::from(int_size(n)).pow(2),
        Field::Call(_) | Field::Version(_) | Field::Temp(_) => 1,
        Field::Bool(_) => 2,
        Field::Digest(h) => 2 + h.len() as u128,
        Field::Role(r) => r.text().len() as u128,
    }
}

/// The charge of a name: the charge of each field of `encode p`, with the field `0k`.
fn name_units(p: &Name) -> u128 {
    let head = p.head.len().max(1) as u128;
    if p.keyword() {
        return head + 2;
    }
    let mut n = head;
    for f in &p.rest {
        n += field_units(f);
    }
    n
}

fn span(p: Pos) -> Span {
    Span {
        line: u32::try_from(p.line).unwrap_or(u32::MAX),
        col: u32::try_from(p.col).unwrap_or(u32::MAX),
    }
}

fn cname(text: String, c: Span) -> CName {
    CName { text, span: c }
}

fn num(value: u32, c: Span) -> Num {
    Num { value, span: c }
}

fn konst(c: Span, w: u32, v: Nat) -> Expr {
    Expr::Const {
        width: num(w, c),
        value: v,
        value_span: c,
        span: c,
    }
}

fn small(c: Span, w: u32, v: u32) -> Expr {
    konst(c, w, nat(u64::from(v)))
}

fn bin(c: Span, op: CBin, a: Expr, b: Expr) -> Expr {
    Expr::Binary {
        op,
        lhs: Box::new(a),
        rhs: Box::new(b),
        span: c,
    }
}

fn icmp(c: Span, pred: Pred, a: Expr, b: Expr) -> Expr {
    Expr::Icmp {
        pred,
        lhs: Box::new(a),
        rhs: Box::new(b),
        span: c,
    }
}

fn mux(c: Span, s: Expr, a: Expr, b: Expr) -> Expr {
    Expr::Mux {
        cond: Box::new(s),
        then: Box::new(a),
        els: Box::new(b),
        span: c,
    }
}

fn extract(c: Span, a: Expr, lo: u32, w: u32) -> Expr {
    Expr::Extract {
        arg: Box::new(a),
        lo,
        width: num(w, c),
        span: c,
    }
}

/// The width of a hardware type.
fn width(t: &Ty) -> u32 {
    match t {
        Ty::UInt(w) | Ty::SInt(w) => *w,
        _ => 1,
    }
}

fn signed(t: &Ty) -> bool {
    matches!(t, Ty::SInt(_))
}

/// The constant of a static value at a hardware use: its value modulo `2^w`.
fn const_of(c: Span, v: &Value) -> Expr {
    match v {
        Value::Bool(b) => small(c, 1, u32::from(*b)),
        Value::UInt(x) | Value::SInt(x) => konst(c, x.width(), constant(x)),
        _ => small(c, 1, 0),
    }
}

/// The core operation of a binary node that is not a shift, or its predicate.
enum Core {
    Bin(CBin),
    Pred(Pred),
}

fn bin_op(op: BinOp, signed: bool) -> Option<Core> {
    Some(match op {
        BinOp::Addw => Core::Bin(CBin::Add),
        BinOp::Subw => Core::Bin(CBin::Sub),
        BinOp::Mulw => Core::Bin(CBin::Mul),
        BinOp::And | BinOp::Land => Core::Bin(CBin::And),
        BinOp::Or | BinOp::Lor => Core::Bin(CBin::Or),
        BinOp::Xor => Core::Bin(CBin::Xor),
        BinOp::Eq => Core::Pred(Pred::Eq),
        BinOp::Ne => Core::Pred(Pred::Ne),
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Core::Pred(crate::ops::pred(op, signed)),
        _ => return None,
    })
}

/// A lowered expression and its effective height. A leaf and a reference to a temporary
/// have the height 1 and the charge of a copy of them.
struct Low {
    expr: Expr,
    copy: Option<u128>,
    height: u64,
}

fn up(height: u64) -> u64 {
    height + 1
}

/// A node that a copy cannot repeat.
fn inner(expr: Expr, height: u64) -> Low {
    Low {
        expr,
        copy: None,
        height,
    }
}

/// The core name of the target of a statement: the name of its leaf, or the name of a child
/// input with its leaf fields. Its temporaries are named after it.
type Target<'a> = &'a Name;

/// The fuel, the temporaries of the current module, and the number of the next temporary of
/// the current statement.
struct Lower<'d> {
    design: &'d Design,
    fuel: u64,
    temps: Vec<Stmt>,
    count: u64,
    /// The temporary of each shared condition (`Op::Share`) that a statement of the current
    /// module already bound.
    shares: BTreeMap<u64, Name>,
}

/// A node that a rule uses twice: its two uses and its effective height.
struct Twice {
    first: Expr,
    second: Expr,
    height: u64,
}

impl Lower<'_> {
    fn charge(&mut self, pos: Pos, units: u128) -> R<()> {
        match u64::try_from(units) {
            Ok(units) if units <= self.fuel => {
                self.fuel -= units;
                Ok(())
            }
            _ => Err(Failure::Source(Error {
                code: Code::S015,
                pos,
                message: format!(
                    "the fuel cannot pay {units} unit(s) of the lowering; {} remain",
                    self.fuel
                ),
            })),
        }
    }

    fn text(&self, sym: Sym) -> String {
        self.design.texts.get(sym).cloned().unwrap_or_default()
    }

    fn path(&self, path: PathId) -> Name {
        self.design.paths.name(path, &self.design.texts)
    }

    /// The domain port `<domain>$<role>`.
    fn role(&self, domain: Sym, role: Role) -> Name {
        Name {
            head: self.text(domain),
            rest: vec![Field::Role(role)],
        }
    }

    fn ty(&self, hw: HwId) -> Ty {
        self.design.graph.ty(hw)
    }

    fn pos(&self, hw: HwId, or: Pos) -> Pos {
        self.design.graph.node(hw).map_or(or, |node| node.pos)
    }

    /// The core name of `name`. It charges the fields first.
    fn name(&mut self, pos: Pos, name: &Name) -> R<CName> {
        self.charge(pos, name_units(name))?;
        Ok(cname(encode(name), span(pos)))
    }

    /// Binds `expr` of width `width` to the next temporary of `target` at `at`.
    fn bind_temp(&mut self, pos: Pos, target: Target, width: u32, at: Pos, expr: Expr) -> R<Name> {
        let mut temp = target.clone();
        temp.rest.push(Field::Temp(self.count));
        self.count += 1;
        self.charge(pos, 1)?;
        let name = self.name(pos, &temp)?;
        let at = span(at);
        self.temps.push(Stmt::Let {
            name: CName { span: at, ..name },
            width: num(width, at),
            expr,
            span: at,
        });
        Ok(temp)
    }

    /// A reference to the temporary `temp`.
    fn temp_ref(&mut self, pos: Pos, temp: &Name) -> R<Expr> {
        self.charge(pos, 1)?;
        Ok(Expr::Ref(self.name(pos, temp)?))
    }

    /// The operand `low` of width `width` for a rule that uses it twice. A leaf is copied.
    /// Another operand binds to a temporary at `at`, both uses refer to it, and its effective
    /// height is 1.
    fn twice(&mut self, pos: Pos, target: Target, width: u32, at: Pos, low: Low) -> R<Twice> {
        if let Some(units) = low.copy {
            self.charge(pos, units)?;
            return Ok(Twice {
                first: low.expr.clone(),
                second: low.expr,
                height: low.height,
            });
        }
        let temp = self.bind_temp(pos, target, width, at, low.expr)?;
        Ok(Twice {
            first: self.temp_ref(pos, &temp)?,
            second: self.temp_ref(pos, &temp)?,
            height: 1,
        })
    }

    /// A node whose effective height reaches 64 binds to a temporary, unless it is the value
    /// of the statement.
    fn deep(&mut self, pos: Pos, target: Target, width: u32, root: bool, low: Low) -> R<Low> {
        if root || low.height < 64 {
            return Ok(low);
        }
        let temp = self.bind_temp(pos, target, width, pos, low.expr)?;
        Ok(Low {
            expr: self.temp_ref(pos, &temp)?,
            copy: Some(1 + name_units(&temp)),
            height: 1,
        })
    }

    /// An operand of a node of the statement of `target`.
    fn operand(&mut self, target: Target, hw: HwId) -> R<Low> {
        self.lower(target, false, hw)
    }

    /// The lowering of the hardware value `hw` for the statement of `target`. Each case
    /// charges its own core nodes, then lowers its operands from left to right. `root` marks
    /// the value of the statement.
    fn lower(&mut self, target: Target, root: bool, hw: HwId) -> R<Low> {
        let graph = &self.design.graph;
        let Some(node) = graph.node(hw) else {
            return defect("a hardware id is outside its arena");
        };
        let (pos, ty) = (node.pos, node.ty.clone());
        let at = span(pos);
        let low = match (&node.op, node.args.as_slice()) {
            (op, []) => self.leaf(pos, op)?,
            (Op::Un(op), [arg]) => self.unary(target, pos, &ty, *op, *arg)?,
            (Op::Bin(op @ (BinOp::Shl | BinOp::Shr)), [arg, count]) => {
                self.shift(target, pos, &ty, *op, *arg, *count)?
            }
            (Op::Bin(op), [lhs, rhs]) => {
                let Some(core) = bin_op(*op, signed(&graph.ty(*lhs))) else {
                    return defect("a binary node has no core operation");
                };
                self.charge(pos, 1)?;
                let lhs = self.operand(target, *lhs)?;
                let rhs = self.operand(target, *rhs)?;
                let height = up(lhs.height.max(rhs.height));
                let expr = match core {
                    Core::Bin(op) => bin(at, op, lhs.expr, rhs.expr),
                    Core::Pred(pred) => icmp(at, pred, lhs.expr, rhs.expr),
                };
                inner(expr, height)
            }
            (Op::Mux, [sel, then, els]) => {
                self.charge(pos, 1)?;
                let sel = self.operand(target, *sel)?;
                let then = self.operand(target, *then)?;
                let els = self.operand(target, *els)?;
                let height = up(sel.height.max(then.height).max(els.height));
                inner(mux(at, sel.expr, then.expr, els.expr), height)
            }
            (Op::Share(k), [arg]) => self.share(target, pos, *k, *arg)?,
            (Op::Resize, [arg]) => self.resize(target, pos, &ty, *arg)?,
            (Op::Reinterpret, [arg]) => {
                let arg = self.operand(target, *arg)?;
                Low {
                    height: up(arg.height),
                    ..arg
                }
            }
            _ => return defect("a hardware node has the wrong number of operands"),
        };
        self.deep(pos, target, width(&ty), root, low)
    }

    /// A shared condition. Its first lowering in the module binds it to a temporary of that
    /// statement, after the temporaries of the condition itself. Each later use refers to it.
    fn share(&mut self, target: Target, pos: Pos, k: u64, arg: HwId) -> R<Low> {
        let temp = if let Some(temp) = self.shares.get(&k) {
            temp.clone()
        } else {
            let (width, at) = (width(&self.ty(arg)), self.pos(arg, pos));
            let low = self.operand(target, arg)?;
            let temp = self.bind_temp(pos, target, width, at, low.expr)?;
            self.shares.insert(k, temp.clone());
            temp
        };
        Ok(Low {
            expr: self.temp_ref(pos, &temp)?,
            copy: Some(1 + name_units(&temp)),
            height: 1,
        })
    }

    /// A reference to the core name `name`, and the charge of a copy of it.
    fn ref_leaf(&mut self, pos: Pos, name: &Name) -> R<(Expr, u128)> {
        let units = 1 + name_units(name);
        self.charge(pos, 1)?;
        Ok((Expr::Ref(self.name(pos, name)?), units))
    }

    /// A reference to the output `port` of the child `inst`, and the charge of a copy of it.
    fn out_leaf(&mut self, pos: Pos, inst: &Name, port: &Name) -> R<(Expr, u128)> {
        let units = 1 + name_units(inst) + name_units(port);
        self.charge(pos, 1)?;
        let inst = self.name(pos, inst)?;
        let port = self.name(pos, port)?;
        let expr = Expr::InstOut {
            inst,
            port,
            span: span(pos),
        };
        Ok((expr, units))
    }

    /// A node without operands: a name, a child output, or a constant.
    fn leaf(&mut self, pos: Pos, op: &Op) -> R<Low> {
        let at = span(pos);
        let (expr, units) = match op {
            Op::Ref(path) => self.ref_leaf(pos, &self.path(*path))?,
            Op::Out(inst, port) => self.out_leaf(pos, &self.path(*inst), port)?,
            Op::Lit(v) => {
                self.charge(pos, 1)?;
                (const_of(at, v), 1)
            }
            Op::Count { .. } => {
                self.charge(pos, 1)?;
                (small(at, 1, 0), 1)
            }
            _ => return defect("a hardware node has the wrong number of operands"),
        };
        Ok(Low {
            expr,
            copy: Some(units),
            height: 1,
        })
    }

    /// `!a`, `~a`, and `-a`.
    fn unary(&mut self, target: Target, pos: Pos, ty: &Ty, op: UnOp, arg: HwId) -> R<Low> {
        let at = span(pos);
        self.charge(pos, if op == UnOp::Inv { 1 } else { 2 })?;
        let arg = self.operand(target, arg)?;
        let expr = match op {
            UnOp::Not => bin(at, CBin::Xor, arg.expr, small(at, 1, 1)),
            UnOp::Inv => Expr::Unary {
                op: CUn::Not,
                arg: Box::new(arg.expr),
                span: at,
            },
            UnOp::Neg => bin(at, CBin::Sub, small(at, width(ty), 0), arg.expr),
        };
        Ok(inner(expr, up(arg.height)))
    }

    /// A shift of `arg` by `count`, with the rows of section 7.4 for the width of the count.
    fn shift(
        &mut self,
        target: Target,
        pos: Pos,
        ty: &Ty,
        op: BinOp,
        arg: HwId,
        count: HwId,
    ) -> R<Low> {
        let at = span(pos);
        let w = width(ty);
        let core = match (op, signed(ty)) {
            (BinOp::Shl, _) => CBin::Shl,
            (_, true) => CBin::Shrs,
            (_, false) => CBin::Shru,
        };
        if let Some(Op::Count { amount, .. }) = self.design.graph.node(count).map(|n| &n.op) {
            let amount = (*amount).min(w);
            self.charge(pos, 2)?;
            let arg = self.operand(target, arg)?;
            let expr = bin(at, core, arg.expr, small(at, w, amount));
            return Ok(inner(expr, up(arg.height)));
        }
        let wc = width(&self.ty(count));
        if wc <= w {
            self.charge(pos, if wc == w { 1 } else { 3 })?;
            let arg = self.operand(target, arg)?;
            let amount = self.operand(target, count)?;
            let height = up(arg.height.max(amount.height));
            let amount = if wc == w {
                amount.expr
            } else {
                bin(at, CBin::Concat, small(at, w - wc, 0), amount.expr)
            };
            return Ok(inner(bin(at, core, arg.expr, amount), height));
        }
        let shrs = core == CBin::Shrs;
        self.charge(pos, if shrs { 7 } else { 6 })?;
        let lowered = self.operand(target, arg)?;
        let amount = self.operand(target, count)?;
        let (fill, arg, arg_height) = if shrs {
            let at_arg = self.pos(arg, pos);
            let arg = self.twice(pos, target, w, at_arg, lowered)?;
            let fill = bin(at, CBin::Shrs, arg.first, small(at, w, w - 1));
            (fill, arg.second, arg.height)
        } else {
            (small(at, w, 0), lowered.expr, lowered.height)
        };
        let at_count = self.pos(count, pos);
        let amount = self.twice(pos, target, wc, at_count, amount)?;
        let over = icmp(at, Pred::Uge, amount.first, small(at, wc, w));
        let shifted = bin(at, core, arg, extract(at, amount.second, 0, w));
        let height = up(arg_height.max(amount.height));
        Ok(inner(mux(at, over, fill, shifted), height))
    }

    /// `resize` of `arg` to the type `ty`.
    fn resize(&mut self, target: Target, pos: Pos, ty: &Ty, arg: HwId) -> R<Low> {
        let at = span(pos);
        let (to, from) = (width(ty), width(&self.ty(arg)));
        if to == from {
            let arg = self.operand(target, arg)?;
            return Ok(Low {
                height: up(arg.height),
                ..arg
            });
        }
        if to < from {
            self.charge(pos, 1)?;
            let arg = self.operand(target, arg)?;
            return Ok(inner(extract(at, arg.expr, 0, to), up(arg.height)));
        }
        if !signed(ty) {
            self.charge(pos, 2)?;
            let arg = self.operand(target, arg)?;
            let expr = bin(at, CBin::Concat, small(at, to - from, 0), arg.expr);
            return Ok(inner(expr, up(arg.height)));
        }
        self.charge(pos, 3)?;
        let lowered = self.operand(target, arg)?;
        let at_arg = self.pos(arg, pos);
        let arg = self.twice(pos, target, from, at_arg, lowered)?;
        let sign = Expr::Replicate {
            arg: Box::new(extract(at, arg.first, from - 1, 1)),
            count: num(to - from, at),
            span: at,
        };
        Ok(inner(
            bin(at, CBin::Concat, sign, arg.second),
            up(arg.height),
        ))
    }

    /// The value of one statement with the target `target`. Its temporaries count from 0.
    fn value(&mut self, target: Target, hw: HwId) -> R<Expr> {
        self.count = 0;
        Ok(self.lower(target, true, hw)?.expr)
    }

    /// A reference to a domain port.
    fn domain_ref(&mut self, pos: Pos, name: &Name) -> R<Expr> {
        self.charge(pos, 1)?;
        Ok(Expr::Ref(self.name(pos, name)?))
    }

    /// The connections of the domain of a child with the domain `child` in a parent with
    /// the domain `parent`.
    fn domain_conns(&mut self, pos: Pos, child: Option<Sym>, parent: Option<Sym>) -> R<Vec<Conn>> {
        let (Some(child), Some(parent)) = (child, parent) else {
            return match child {
                None => Ok(Vec::new()),
                Some(_) => defect("a clocked child in a combinational module"),
            };
        };
        let mut conns = Vec::with_capacity(2);
        for role in [Role::Clk, Role::Rst] {
            self.charge(pos, 1)?;
            let port = self.name(pos, &self.role(child, role))?;
            let expr = self.domain_ref(pos, &self.role(parent, role))?;
            conns.push(Conn {
                port,
                expr,
                span: span(pos),
            });
        }
        Ok(conns)
    }

    /// The ports of `inst` in the port layout. They lower in declaration order.
    fn ports(&mut self, inst: &Inst) -> R<Vec<Port>> {
        let body = &inst.body;
        let at = span(inst.pos);
        let mut domain = Vec::new();
        if let Some(d) = body.domain {
            for (role, ty) in [(Role::Clk, CTy::Clock), (Role::Rst, CTy::Bits(num(1, at)))] {
                self.charge(inst.pos, 1)?;
                let name = self.name(inst.pos, &self.role(d, role))?;
                domain.push(Port {
                    dir: Dir::Input,
                    name: CName { span: at, ..name },
                    ty,
                    span: at,
                });
            }
        }
        let mut ports = Vec::with_capacity(body.ports.len());
        for decl in &body.ports {
            let at = span(decl.pos);
            let source = self.text(decl.sym);
            let mut leaves = Vec::new();
            layout::for_each_leaf(&source, &decl.ty, |leaf| {
                self.charge(decl.pos, 1)?;
                let name = self.name(decl.pos, &leaf.name)?;
                leaves.push(Port {
                    dir: if decl.input { Dir::Input } else { Dir::Output },
                    name,
                    ty: CTy::Bits(num(width(&leaf.ty), at)),
                    span: at,
                });
                Ok(())
            })?;
            ports.push(layout::Declared {
                name: source,
                input: decl.input,
                leaves,
            });
        }
        let layout = layout::arrange(domain, ports);
        let mut ports = layout.inputs;
        ports.extend(layout.outputs);
        Ok(ports)
    }

    /// The registers of `inst`, each with the reset of its domain.
    fn regs(&mut self, inst: &Inst, stmts: &mut Vec<Stmt>) -> R<()> {
        for reg in &inst.body.regs {
            let Some(domain) = inst.body.domain else {
                return defect("a register in a combinational module");
            };
            if !matches!(reg.ty, Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) {
                return defect("a register of an aggregate type has no lowering by leaf");
            }
            let at = span(reg.pos);
            self.charge(reg.pos, 2)?;
            let name = self.name(reg.pos, &self.path(reg.path))?;
            let clk = self.name(reg.pos, &self.role(domain, Role::Clk))?;
            let signal = self.domain_ref(reg.pos, &self.role(domain, Role::Rst))?;
            self.charge(reg.pos, 1)?;
            stmts.push(Stmt::Reg {
                name,
                width: num(width(&reg.ty), at),
                clk,
                reset: Some(Reset {
                    signal,
                    value: const_of(at, &reg.init),
                    span: at,
                }),
                span: at,
            });
        }
        Ok(())
    }

    /// The core module of one instantiation, and its emitted name.
    fn module(&mut self, inst: &Inst) -> R<(Module, String)> {
        let body = &inst.body;
        let at = span(inst.pos);
        self.charge(inst.pos, 1)?;
        let name = self.name(inst.pos, &inst.iface.name)?;
        self.temps.clear();
        self.shares.clear();
        let ports = self.ports(inst)?;
        let mut stmts = Vec::new();
        self.regs(inst, &mut stmts)?;
        for local in &body.lets {
            let at = span(local.pos);
            self.charge(local.pos, 1)?;
            let x = self.name(local.pos, &self.path(local.path))?;
            let w = width(&self.ty(local.value));
            let expr = self.value(&self.path(local.path), local.value)?;
            stmts.push(Stmt::Let {
                name: x,
                width: num(w, at),
                expr,
                span: at,
            });
        }
        let mut conns: Vec<Vec<Conn>> = body.children.iter().map(|_| Vec::new()).collect();
        for bind in &body.binds {
            self.bind(bind, &mut stmts, &mut conns)?;
        }
        for (child, conns) in body.children.iter().zip(&mut conns) {
            let Some(done) = self.design.insts.get(child.inst) else {
                return defect("a child is not a done instantiation");
            };
            self.charge(child.pos, 1)?;
            let x = self.name(child.pos, &self.path(child.path))?;
            let module = self.name(child.pos, &done.iface.name)?;
            let mut all = self.domain_conns(child.pos, done.iface.domain, body.domain)?;
            all.append(conns);
            stmts.push(Stmt::Inst {
                name: x,
                module,
                conns: all,
                span: span(child.pos),
            });
        }
        stmts.append(&mut self.temps);
        let text = name.text.clone();
        let module = Module {
            name: CName { span: at, ..name },
            ports,
            stmts,
            span: at,
        };
        Ok((module, text))
    }

    /// One `:=` binding: a statement of an own resource, or a connection of a child input.
    fn bind(&mut self, bind: &Bind, stmts: &mut Vec<Stmt>, conns: &mut [Vec<Conn>]) -> R<()> {
        let at = span(bind.pos);
        self.charge(bind.pos, 1)?;
        match bind.sink {
            Sink::Own { kind, ref ty, path } => {
                let x = self.name(bind.pos, &self.path(path))?;
                let expr = self.value(&self.path(path), scalar(&bind.value)?)?;
                stmts.push(match kind {
                    Kind::Reg => Stmt::Next {
                        reg: x,
                        expr,
                        span: at,
                    },
                    Kind::Wire => Stmt::Let {
                        name: x,
                        width: num(width(ty), at),
                        expr,
                        span: at,
                    },
                    Kind::Output => Stmt::Assign {
                        out: x,
                        expr,
                        span: at,
                    },
                });
            }
            Sink::Child {
                index,
                inst,
                ref port,
                ..
            } => {
                let x = self.name(bind.pos, port)?;
                let mut target = self.path(inst);
                target.rest.push(Field::User(port.head.clone()));
                target.rest.extend(port.rest.iter().cloned());
                let expr = self.value(&target, scalar(&bind.value)?)?;
                let Some(conns) = conns.get_mut(index) else {
                    return defect("a connection names no child");
                };
                conns.push(Conn {
                    port: x,
                    expr,
                    span: at,
                });
            }
        }
        Ok(())
    }

    /// The core design: the modules in the order the instantiations finish, then the name of
    /// the top at the top selection. The units of each module count toward its
    /// instantiation.
    fn design(&mut self) -> R<(CDesign, Vec<(String, u64)>)> {
        let design = self.design;
        let mut items = Vec::with_capacity(design.insts.len());
        let mut units = Vec::with_capacity(design.insts.len());
        for inst in &design.insts {
            let start = self.fuel;
            let (module, name) = self.module(inst)?;
            items.push(Item::Module(module));
            units.push((name, inst.units + (start - self.fuel)));
        }
        self.charge(design.pos, 1)?;
        let Some(top) = design.insts.get(design.top) else {
            return defect("the top is not a done instantiation");
        };
        let top = self.name(design.pos, &top.iface.name)?;
        Ok((
            CDesign {
                top,
                items,
                span: span(design.pos),
            },
            units,
        ))
    }
}
