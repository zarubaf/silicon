//! The resolved form of the expressions and statements of a module, which
//! pass 3 builds. Each name is an index, and each node that a later pass
//! checks carries what that pass needs: the declared width of a reference,
//! the position of a form. A clock read stays a node, so that pass 5 can report
//! it; no other pass can lower it.

use super::error;
use super::scope::Sig;
use crate::Bits;
use crate::Pred;
use crate::ast::{BinOp, Name, Num, UnOp};
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::typed::{self, Callee, InputIdx, InstIdx, LetIdx, MemIdx, OutputIdx, RegIdx};
use num_bigint::BigUint;

pub(super) enum Rx<'a> {
    Input(InputIdx, u32),
    Let(LetIdx, u32),
    Reg(RegIdx, u32),
    InstOut(InstIdx, OutputIdx, u32),
    /// A name of a clock in a value position.
    Clock(Span),
    Const {
        width: Num,
        value: &'a BigUint,
        value_span: Span,
    },
    Un(UnOp, Box<Rx<'a>>),
    Bin {
        op: BinOp,
        lhs: Box<Rx<'a>>,
        rhs: Box<Rx<'a>>,
        span: Span,
    },
    Icmp {
        pred: Pred,
        lhs: Box<Rx<'a>>,
        rhs: Box<Rx<'a>>,
        span: Span,
    },
    Mux {
        cond: Box<Rx<'a>>,
        then: Box<Rx<'a>>,
        els: Box<Rx<'a>>,
        span: Span,
    },
    Extract {
        arg: Box<Rx<'a>>,
        lo: u32,
        width: Num,
        span: Span,
    },
    Replicate {
        arg: Box<Rx<'a>>,
        count: Num,
        span: Span,
    },
    Read {
        mem: MemIdx,
        data_width: u32,
        depth: u32,
        addr: Box<Rx<'a>>,
        span: Span,
    },
}

/// The constant of a `const` form. `E005` is the error for a width of 0 and
/// for a value that does not fit, at the number that breaks the rule.
pub(super) fn const_bits(
    width: Num,
    value: &BigUint,
    value_span: Span,
) -> Result<Bits, Diagnostic> {
    Bits::new(width.value, value.clone()).ok_or_else(|| {
        if width.value == 0 {
            error(ErrorCode::E005, width.span, "the constant width is 0")
        } else {
            error(
                ErrorCode::E005,
                value_span,
                format!("the constant {value} does not fit in {} bits", width.value),
            )
        }
    })
}

impl Rx<'_> {
    /// The typed expression. A clock read fails with the `E009` that pass 5
    /// reports at the same position, and a bad constant with the `E005` of
    /// pass 4.
    pub fn finish(&self) -> Result<typed::Expr, Diagnostic> {
        use typed::Expr as T;
        let boxed = |e: &Rx| e.finish().map(Box::new);
        Ok(match self {
            Rx::Input(i, _) => T::Input(*i),
            Rx::Let(i, _) => T::Let(*i),
            Rx::Reg(i, _) => T::Reg(*i),
            Rx::InstOut(i, o, _) => T::InstOut(*i, *o),
            Rx::Clock(span) => {
                return Err(error(ErrorCode::E009, *span, "a value reads a clock"));
            }
            Rx::Const {
                width,
                value,
                value_span,
            } => T::Const(const_bits(*width, value, *value_span)?),
            Rx::Un(op, arg) => T::Un(*op, boxed(arg)?),
            Rx::Bin { op, lhs, rhs, .. } => T::Bin(*op, boxed(lhs)?, boxed(rhs)?),
            Rx::Icmp { pred, lhs, rhs, .. } => T::Icmp(*pred, boxed(lhs)?, boxed(rhs)?),
            Rx::Mux {
                cond, then, els, ..
            } => T::Mux(boxed(cond)?, boxed(then)?, boxed(els)?),
            Rx::Extract { arg, lo, width, .. } => T::Extract(boxed(arg)?, *lo, width.value),
            Rx::Replicate { arg, count, .. } => T::Replicate(boxed(arg)?, count.value),
            Rx::Read { mem, addr, .. } => T::Read(*mem, boxed(addr)?),
        })
    }

    /// Adds the position of each clock read in the expression.
    pub fn clock_reads(&self, out: &mut Vec<Span>) {
        match self {
            Rx::Clock(span) => out.push(*span),
            Rx::Input(..) | Rx::Let(..) | Rx::Reg(..) | Rx::InstOut(..) | Rx::Const { .. } => {}
            Rx::Un(_, arg) | Rx::Extract { arg, .. } | Rx::Replicate { arg, .. } => {
                arg.clock_reads(out);
            }
            Rx::Read { addr, .. } => addr.clock_reads(out),
            Rx::Bin { lhs, rhs, .. } | Rx::Icmp { lhs, rhs, .. } => {
                lhs.clock_reads(out);
                rhs.clock_reads(out);
            }
            Rx::Mux {
                cond, then, els, ..
            } => {
                cond.clock_reads(out);
                then.clock_reads(out);
                els.clock_reads(out);
            }
        }
    }
}

/// A `let` with its declared width.
pub(super) struct RxLet<'a> {
    pub width: u32,
    pub span: Span,
    pub expr: Rx<'a>,
}

pub(super) struct RxReset<'a> {
    pub span: Span,
    pub signal: Rx<'a>,
    pub value: Rx<'a>,
}

pub(super) struct RxReg<'a> {
    pub width: u32,
    pub reset: Option<RxReset<'a>>,
}

/// A `next` or an `assign`: the expression for a target of a width.
pub(super) struct Target<'a, I> {
    pub slot: I,
    pub width: u32,
    pub span: Span,
    pub expr: Rx<'a>,
}

pub(super) struct RxWrite<'a> {
    pub mem: MemIdx,
    pub port: u32,
    pub span: Span,
    pub data_width: u32,
    pub depth: u32,
    pub addr: Rx<'a>,
    pub data: Rx<'a>,
    pub en: Rx<'a>,
}

pub(super) enum ConnArg<'a> {
    /// A connection to a data input.
    Data {
        input: InputIdx,
        width: u32,
        expr: Rx<'a>,
    },
    /// A single name of a clock input, connected to a clock input.
    ClockName,
    /// Anything else connected to a clock input.
    ClockOther { expr_span: Span, expr: Rx<'a> },
}

pub(super) struct RxConn<'a> {
    pub port: &'a Name,
    pub span: Span,
    pub arg: ConnArg<'a>,
}

pub(super) struct RxInst<'a> {
    pub callee: Callee,
    pub sig: &'a Sig<'a>,
    pub span: Span,
    pub conns: Vec<RxConn<'a>>,
}

/// Everything pass 3 resolved in one module.
pub(super) struct RxModule<'a> {
    pub lets: Vec<RxLet<'a>>,
    pub regs: Vec<RxReg<'a>>,
    pub nexts: Vec<Target<'a, RegIdx>>,
    pub assigns: Vec<Target<'a, OutputIdx>>,
    pub writes: Vec<RxWrite<'a>>,
    pub insts: Vec<RxInst<'a>>,
}

/// One expression with the width it must have, if it has a target.
pub(super) struct Obligation<'r, 'a> {
    pub expr: &'r Rx<'a>,
    pub want: Option<u32>,
    pub span: Span,
    pub what: &'static str,
}

impl<'a> RxModule<'a> {
    /// All expressions of the module.
    pub fn obligations(&self) -> Vec<Obligation<'_, 'a>> {
        let mut all = Vec::new();
        let mut add = |expr, want, span, what| {
            all.push(Obligation {
                expr,
                want,
                span,
                what,
            });
        };
        for l in &self.lets {
            add(&l.expr, Some(l.width), l.span, "the `let`");
        }
        for r in &self.regs {
            if let Some(reset) = &r.reset {
                add(&reset.signal, Some(1), reset.span, "the reset signal");
                add(&reset.value, Some(r.width), reset.span, "the register");
            }
        }
        for n in &self.nexts {
            add(&n.expr, Some(n.width), n.span, "the register");
        }
        for a in &self.assigns {
            add(&a.expr, Some(a.width), a.span, "the output");
        }
        for w in &self.writes {
            let addr = super::types::address_width(w.depth);
            add(&w.addr, Some(addr), w.span, "the address");
            add(&w.data, Some(w.data_width), w.span, "the memory word");
            add(&w.en, Some(1), w.span, "the write enable");
        }
        for inst in &self.insts {
            for conn in &inst.conns {
                match &conn.arg {
                    ConnArg::Data { width, expr, .. } => {
                        add(expr, Some(*width), conn.span, "the input");
                    }
                    ConnArg::ClockOther { expr, .. } => add(expr, None, conn.span, "the clock"),
                    ConnArg::ClockName => {}
                }
            }
        }
        all
    }
}
