//! The resolved form of the expressions and statements of a module, which
//! pass 3 builds. Each name is an index, and each node that a later pass
//! checks carries what that pass needs: the declared width of a reference,
//! the position of a form. Pass 4 turns each constant into [`Bits`], and pass 5
//! removes the clock reads, so that the last form converts without an error.

use super::scope::Sig;
use crate::Bits;
use crate::Pred;
use crate::ast::{BinOp, Name, Num, UnOp};
use crate::diag::Span;
use crate::typed::{self, Callee, InputIdx, InstIdx, LetIdx, MemIdx, OutputIdx, RegIdx};
use num_bigint::BigUint;

/// A clock read that cannot happen: the type of the clock slot after pass 5.
pub(super) enum Never {}

/// A constant before pass 4 checks it.
pub(super) struct RawConst<'a> {
    pub value: &'a BigUint,
    pub value_span: Span,
}

/// The expression tree. The type `K` of a clock read and the type `C` of a
/// constant change as the passes check them:
/// - After pass 3: `K` is the position, and `C` is the raw constant.
/// - After pass 4: `C` is [`Bits`].
/// - After pass 5: `K` is [`Never`]. The tree then converts to the typed
///   expression without an error path.
pub(super) enum Rx<K, C> {
    Input(InputIdx, u32),
    Let(LetIdx, u32),
    Reg(RegIdx, u32),
    InstOut(InstIdx, OutputIdx, u32),
    /// A name of a clock in a value position.
    Clock(K),
    Const {
        width: Num,
        value: C,
    },
    Un(UnOp, Box<Rx<K, C>>),
    Bin {
        op: BinOp,
        lhs: Box<Rx<K, C>>,
        rhs: Box<Rx<K, C>>,
        span: Span,
    },
    Icmp {
        pred: Pred,
        lhs: Box<Rx<K, C>>,
        rhs: Box<Rx<K, C>>,
        span: Span,
    },
    Mux {
        cond: Box<Rx<K, C>>,
        then: Box<Rx<K, C>>,
        els: Box<Rx<K, C>>,
        span: Span,
    },
    Extract {
        arg: Box<Rx<K, C>>,
        lo: u32,
        width: Num,
        span: Span,
    },
    Replicate {
        arg: Box<Rx<K, C>>,
        count: Num,
        span: Span,
    },
    Read {
        mem: MemIdx,
        data_width: u32,
        depth: u32,
        addr: Box<Rx<K, C>>,
        span: Span,
    },
}

/// The tree after pass 3.
pub(super) type RawRx<'a> = Rx<Span, RawConst<'a>>;
/// The tree after pass 5.
pub(super) type Ex = Rx<Never, Bits>;

/// `Some` of all items if there is no `None`. The caller looked at every item
/// before, so that each one recorded its errors.
fn all<T>(items: Vec<Option<T>>) -> Option<Vec<T>> {
    items.into_iter().collect()
}

impl<K, C> Rx<K, C> {
    /// Rebuilds the tree with new clock and constant slots. A slot function
    /// returns `None` after it recorded an error. The whole tree is visited
    /// before the result is `None`.
    pub fn map<K2, C2>(
        self,
        fk: &mut impl FnMut(K) -> Option<K2>,
        fc: &mut impl FnMut(Num, C) -> Option<C2>,
    ) -> Option<Rx<K2, C2>> {
        Some(match self {
            Rx::Input(i, w) => Rx::Input(i, w),
            Rx::Let(i, w) => Rx::Let(i, w),
            Rx::Reg(i, w) => Rx::Reg(i, w),
            Rx::InstOut(i, o, w) => Rx::InstOut(i, o, w),
            Rx::Clock(k) => Rx::Clock(fk(k)?),
            Rx::Const { width, value } => Rx::Const {
                width,
                value: fc(width, value)?,
            },
            Rx::Un(op, arg) => Rx::Un(op, Box::new(arg.map(fk, fc)?)),
            Rx::Bin { op, lhs, rhs, span } => {
                let (lhs, rhs) = (lhs.map(fk, fc), rhs.map(fk, fc));
                Rx::Bin {
                    op,
                    lhs: Box::new(lhs?),
                    rhs: Box::new(rhs?),
                    span,
                }
            }
            Rx::Icmp {
                pred,
                lhs,
                rhs,
                span,
            } => {
                let (lhs, rhs) = (lhs.map(fk, fc), rhs.map(fk, fc));
                Rx::Icmp {
                    pred,
                    lhs: Box::new(lhs?),
                    rhs: Box::new(rhs?),
                    span,
                }
            }
            Rx::Mux {
                cond,
                then,
                els,
                span,
            } => {
                let (cond, then, els) = (cond.map(fk, fc), then.map(fk, fc), els.map(fk, fc));
                Rx::Mux {
                    cond: Box::new(cond?),
                    then: Box::new(then?),
                    els: Box::new(els?),
                    span,
                }
            }
            Rx::Extract {
                arg,
                lo,
                width,
                span,
            } => Rx::Extract {
                arg: Box::new(arg.map(fk, fc)?),
                lo,
                width,
                span,
            },
            Rx::Replicate { arg, count, span } => Rx::Replicate {
                arg: Box::new(arg.map(fk, fc)?),
                count,
                span,
            },
            Rx::Read {
                mem,
                data_width,
                depth,
                addr,
                span,
            } => Rx::Read {
                mem,
                data_width,
                depth,
                addr: Box::new(addr.map(fk, fc)?),
                span,
            },
        })
    }
}

impl Ex {
    /// The typed expression.
    pub fn finish(&self) -> typed::Expr {
        use typed::Expr as T;
        let boxed = |e: &Ex| Box::new(e.finish());
        match self {
            Rx::Input(i, _) => T::Input(*i),
            Rx::Let(i, _) => T::Let(*i),
            Rx::Reg(i, _) => T::Reg(*i),
            Rx::InstOut(i, o, _) => T::InstOut(*i, *o),
            Rx::Clock(never) => match *never {},
            Rx::Const { value, .. } => T::Const(value.clone()),
            Rx::Un(op, arg) => T::Un(*op, boxed(arg)),
            Rx::Bin { op, lhs, rhs, .. } => T::Bin(*op, boxed(lhs), boxed(rhs)),
            Rx::Icmp { pred, lhs, rhs, .. } => T::Icmp(*pred, boxed(lhs), boxed(rhs)),
            Rx::Mux {
                cond, then, els, ..
            } => T::Mux(boxed(cond), boxed(then), boxed(els)),
            Rx::Extract { arg, lo, width, .. } => T::Extract(boxed(arg), *lo, width.value),
            Rx::Replicate { arg, count, .. } => T::Replicate(boxed(arg), count.value),
            Rx::Read { mem, addr, .. } => T::Read(*mem, boxed(addr)),
        }
    }
}

/// A `let` with its declared width.
pub(super) struct RxLet<K, C> {
    pub width: u32,
    pub span: Span,
    pub expr: Rx<K, C>,
}

pub(super) struct RxReset<K, C> {
    pub span: Span,
    pub signal: Rx<K, C>,
    pub value: Rx<K, C>,
}

pub(super) struct RxReg<K, C> {
    pub width: u32,
    pub reset: Option<RxReset<K, C>>,
}

/// A `next` or an `assign`: the expression for a slot of a width.
pub(super) struct Target<I, K, C> {
    pub slot: I,
    pub width: u32,
    pub span: Span,
    pub expr: Rx<K, C>,
}

pub(super) struct RxWrite<K, C> {
    pub mem: MemIdx,
    pub port: u32,
    pub span: Span,
    pub data_width: u32,
    pub depth: u32,
    pub addr: Rx<K, C>,
    pub data: Rx<K, C>,
    pub en: Rx<K, C>,
}

pub(super) enum ConnArg<K, C> {
    /// A connection to a data input.
    Data {
        input: InputIdx,
        width: u32,
        expr: Rx<K, C>,
    },
    /// A single name of a clock input, connected to a clock input.
    ClockName,
    /// Anything else connected to a clock input.
    ClockOther { expr_span: Span, expr: Rx<K, C> },
}

pub(super) struct RxConn<'a, K, C> {
    pub port: &'a Name,
    pub span: Span,
    pub arg: ConnArg<K, C>,
}

pub(super) struct RxInst<'a, K, C> {
    pub callee: Callee,
    pub sig: &'a Sig<'a>,
    pub span: Span,
    pub conns: Vec<RxConn<'a, K, C>>,
}

/// Everything pass 3 resolved in one module.
pub(super) struct RxModule<'a, K, C> {
    pub lets: Vec<RxLet<K, C>>,
    pub regs: Vec<RxReg<K, C>>,
    pub nexts: Vec<Target<RegIdx, K, C>>,
    pub assigns: Vec<Target<OutputIdx, K, C>>,
    pub writes: Vec<RxWrite<K, C>>,
    pub insts: Vec<RxInst<'a, K, C>>,
}

pub(super) type RawModule<'a> = RxModule<'a, Span, RawConst<'a>>;
pub(super) type SizedModule<'a> = RxModule<'a, Span, Bits>;
pub(super) type ExModule<'a> = RxModule<'a, Never, Bits>;
pub(super) type ExInst<'a> = RxInst<'a, Never, Bits>;
pub(super) type ExWrite = RxWrite<Never, Bits>;
pub(super) type ExAssign = Target<OutputIdx, Never, Bits>;

impl<'a, K, C> RxModule<'a, K, C> {
    /// Rebuilds the module with `f` applied to each expression. `f` returns
    /// `None` after it recorded an error. Each category is mapped in full
    /// before any `None` stops the result, so every expression is visited.
    pub fn map_exprs<K2, C2>(
        self,
        f: &mut impl FnMut(Rx<K, C>) -> Option<Rx<K2, C2>>,
    ) -> Option<RxModule<'a, K2, C2>> {
        let lets = all(self
            .lets
            .into_iter()
            .map(|l| {
                Some(RxLet {
                    width: l.width,
                    span: l.span,
                    expr: f(l.expr)?,
                })
            })
            .collect());
        let regs = all(self
            .regs
            .into_iter()
            .map(|r| {
                let reset = match r.reset {
                    None => None,
                    Some(reset) => {
                        let (signal, value) = (f(reset.signal), f(reset.value));
                        Some(RxReset {
                            span: reset.span,
                            signal: signal?,
                            value: value?,
                        })
                    }
                };
                Some(RxReg {
                    width: r.width,
                    reset,
                })
            })
            .collect());
        let nexts = all(self.nexts.into_iter().map(|t| target(t, f)).collect());
        let assigns = all(self.assigns.into_iter().map(|t| target(t, f)).collect());
        let writes = all(self
            .writes
            .into_iter()
            .map(|w| {
                let (addr, data, en) = (f(w.addr), f(w.data), f(w.en));
                Some(RxWrite {
                    mem: w.mem,
                    port: w.port,
                    span: w.span,
                    data_width: w.data_width,
                    depth: w.depth,
                    addr: addr?,
                    data: data?,
                    en: en?,
                })
            })
            .collect());
        let insts = all(self
            .insts
            .into_iter()
            .map(|inst| {
                let conns = all(inst
                    .conns
                    .into_iter()
                    .map(|c| {
                        let arg = match c.arg {
                            ConnArg::Data { input, width, expr } => ConnArg::Data {
                                input,
                                width,
                                expr: f(expr)?,
                            },
                            ConnArg::ClockName => ConnArg::ClockName,
                            ConnArg::ClockOther { expr_span, expr } => ConnArg::ClockOther {
                                expr_span,
                                expr: f(expr)?,
                            },
                        };
                        Some(RxConn {
                            port: c.port,
                            span: c.span,
                            arg,
                        })
                    })
                    .collect())?;
                Some(RxInst {
                    callee: inst.callee,
                    sig: inst.sig,
                    span: inst.span,
                    conns,
                })
            })
            .collect());
        Some(RxModule {
            lets: lets?,
            regs: regs?,
            nexts: nexts?,
            assigns: assigns?,
            writes: writes?,
            insts: insts?,
        })
    }
}

fn target<I, K, C, K2, C2>(
    t: Target<I, K, C>,
    f: &mut impl FnMut(Rx<K, C>) -> Option<Rx<K2, C2>>,
) -> Option<Target<I, K2, C2>> {
    Some(Target {
        slot: t.slot,
        width: t.width,
        span: t.span,
        expr: f(t.expr)?,
    })
}

/// One expression with the width it must have, if it has a target.
pub(super) struct Obligation<'r> {
    pub expr: &'r Ex,
    pub want: Option<u32>,
    pub span: Span,
    pub what: &'static str,
}

impl ExModule<'_> {
    /// All expressions of the module.
    pub fn obligations(&self) -> Vec<Obligation<'_>> {
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
