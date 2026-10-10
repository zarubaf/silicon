//! The untyped AST of the core IR. Every node carries its source position.
//! Names are not resolved here.

use crate::Pred;
use crate::diag::Span;
use num_bigint::BigUint;

/// True if `text` matches `[A-Za-z_][A-Za-z0-9_]*(\$[A-Za-z0-9_]+)*`: fields
/// joined by one `$`. No core name contains `$$`, so the backend names, which
/// do, never collide with one (spec 3.4).
#[must_use]
pub fn is_core_name(text: &str) -> bool {
    let mut fields = text.split('$');
    let field = |f: &str| f.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    fields.next().is_some_and(|first| {
        first.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && field(first)
    }) && fields.all(|f| !f.is_empty() && field(f))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Name {
    pub text: String,
    pub span: Span,
}

/// A number of the source with the position of its digits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Num {
    pub value: u32,
    pub span: Span,
}

impl Num {
    fn without_spans(self) -> Num {
        Num {
            value: self.value,
            span: Span::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Design {
    pub top: Name,
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Module(Module),
    Extern(Extern),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    pub name: Name,
    pub ports: Vec<Port>,
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extern {
    pub name: Name,
    pub ports: Vec<Port>,
    pub deps: Vec<Dep>,
    pub span: Span,
}

/// `(deps OUT (IN*))`: the combinational inputs of one extern output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dep {
    pub out: Name,
    pub ins: Vec<Name>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    Input,
    Output,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Clock,
    Bits(Num),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Port {
    pub dir: Dir,
    pub name: Name,
    pub ty: Ty,
    pub span: Span,
}

/// `(reset sync SIGNAL VALUE)`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reset {
    pub signal: Expr,
    pub value: Expr,
    pub span: Span,
}

/// `(PORT expr)` of an instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conn {
    pub port: Name,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Let {
        name: Name,
        width: Num,
        expr: Expr,
        span: Span,
    },
    Reg {
        name: Name,
        width: Num,
        clk: Name,
        reset: Option<Reset>,
        span: Span,
    },
    Next {
        reg: Name,
        expr: Expr,
        span: Span,
    },
    Mem {
        name: Name,
        width: Num,
        depth: Num,
        clk: Name,
        span: Span,
    },
    Write {
        mem: Name,
        port: u32,
        addr: Expr,
        data: Expr,
        en: Expr,
        span: Span,
    },
    Inst {
        name: Name,
        module: Name,
        conns: Vec<Conn>,
        span: Span,
    },
    Assign {
        out: Name,
        expr: Expr,
        span: Span,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    Shru,
    Shrs,
    Concat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// `NAME`
    Ref(Name),
    /// `NAME.PORT`: an output of an instance.
    InstOut { inst: Name, port: Name, span: Span },
    Const {
        width: Num,
        value: BigUint,
        /// The position of the value.
        value_span: Span,
        span: Span,
    },
    Unary {
        op: UnOp,
        arg: Box<Expr>,
        span: Span,
    },
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: Span,
    },
    Icmp {
        pred: Pred,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: Span,
    },
    Mux {
        cond: Box<Expr>,
        then: Box<Expr>,
        els: Box<Expr>,
        span: Span,
    },
    Extract {
        arg: Box<Expr>,
        lo: u32,
        width: Num,
        span: Span,
    },
    Replicate {
        arg: Box<Expr>,
        count: Num,
        span: Span,
    },
    Read {
        mem: Name,
        addr: Box<Expr>,
        span: Span,
    },
}

impl Expr {
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Expr::Ref(name) => name.span,
            Expr::InstOut { span, .. }
            | Expr::Const { span, .. }
            | Expr::Unary { span, .. }
            | Expr::Binary { span, .. }
            | Expr::Icmp { span, .. }
            | Expr::Mux { span, .. }
            | Expr::Extract { span, .. }
            | Expr::Replicate { span, .. }
            | Expr::Read { span, .. } => *span,
        }
    }
}

// `without_spans` erases every position, so that two designs compare equal
// when they differ only in layout.

impl Name {
    fn without_spans(&self) -> Name {
        Name {
            text: self.text.clone(),
            span: Span::default(),
        }
    }
}

impl Design {
    #[must_use]
    pub fn without_spans(&self) -> Design {
        Design {
            top: self.top.without_spans(),
            items: self.items.iter().map(Item::without_spans).collect(),
            span: Span::default(),
        }
    }
}

impl Item {
    fn without_spans(&self) -> Item {
        match self {
            Item::Module(m) => Item::Module(Module {
                name: m.name.without_spans(),
                ports: m.ports.iter().map(Port::without_spans).collect(),
                stmts: m.stmts.iter().map(Stmt::without_spans).collect(),
                span: Span::default(),
            }),
            Item::Extern(e) => Item::Extern(Extern {
                name: e.name.without_spans(),
                ports: e.ports.iter().map(Port::without_spans).collect(),
                deps: e
                    .deps
                    .iter()
                    .map(|d| Dep {
                        out: d.out.without_spans(),
                        ins: d.ins.iter().map(Name::without_spans).collect(),
                        span: Span::default(),
                    })
                    .collect(),
                span: Span::default(),
            }),
        }
    }
}

impl Port {
    fn without_spans(&self) -> Port {
        Port {
            dir: self.dir,
            name: self.name.without_spans(),
            ty: match self.ty {
                Ty::Clock => Ty::Clock,
                Ty::Bits(n) => Ty::Bits(n.without_spans()),
            },
            span: Span::default(),
        }
    }
}

impl Stmt {
    fn without_spans(&self) -> Stmt {
        let s = Span::default();
        match self {
            Stmt::Let {
                name, width, expr, ..
            } => Stmt::Let {
                name: name.without_spans(),
                width: width.without_spans(),
                expr: expr.without_spans(),
                span: s,
            },
            Stmt::Reg {
                name,
                width,
                clk,
                reset,
                ..
            } => Stmt::Reg {
                name: name.without_spans(),
                width: width.without_spans(),
                clk: clk.without_spans(),
                reset: reset.as_ref().map(|r| Reset {
                    signal: r.signal.without_spans(),
                    value: r.value.without_spans(),
                    span: s,
                }),
                span: s,
            },
            Stmt::Next { reg, expr, .. } => Stmt::Next {
                reg: reg.without_spans(),
                expr: expr.without_spans(),
                span: s,
            },
            Stmt::Mem {
                name,
                width,
                depth,
                clk,
                ..
            } => Stmt::Mem {
                name: name.without_spans(),
                width: width.without_spans(),
                depth: depth.without_spans(),
                clk: clk.without_spans(),
                span: s,
            },
            Stmt::Write {
                mem,
                port,
                addr,
                data,
                en,
                ..
            } => Stmt::Write {
                mem: mem.without_spans(),
                port: *port,
                addr: addr.without_spans(),
                data: data.without_spans(),
                en: en.without_spans(),
                span: s,
            },
            Stmt::Inst {
                name,
                module,
                conns,
                ..
            } => Stmt::Inst {
                name: name.without_spans(),
                module: module.without_spans(),
                conns: conns
                    .iter()
                    .map(|c| Conn {
                        port: c.port.without_spans(),
                        expr: c.expr.without_spans(),
                        span: s,
                    })
                    .collect(),
                span: s,
            },
            Stmt::Assign { out, expr, .. } => Stmt::Assign {
                out: out.without_spans(),
                expr: expr.without_spans(),
                span: s,
            },
        }
    }
}

impl Expr {
    fn without_spans(&self) -> Expr {
        let s = Span::default();
        let bx = |e: &Expr| Box::new(e.without_spans());
        match self {
            Expr::Ref(n) => Expr::Ref(n.without_spans()),
            Expr::InstOut { inst, port, .. } => Expr::InstOut {
                inst: inst.without_spans(),
                port: port.without_spans(),
                span: s,
            },
            Expr::Const { width, value, .. } => Expr::Const {
                width: width.without_spans(),
                value: value.clone(),
                value_span: s,
                span: s,
            },
            Expr::Unary { op, arg, .. } => Expr::Unary {
                op: *op,
                arg: bx(arg),
                span: s,
            },
            Expr::Binary { op, lhs, rhs, .. } => Expr::Binary {
                op: *op,
                lhs: bx(lhs),
                rhs: bx(rhs),
                span: s,
            },
            Expr::Icmp { pred, lhs, rhs, .. } => Expr::Icmp {
                pred: *pred,
                lhs: bx(lhs),
                rhs: bx(rhs),
                span: s,
            },
            Expr::Mux {
                cond, then, els, ..
            } => Expr::Mux {
                cond: bx(cond),
                then: bx(then),
                els: bx(els),
                span: s,
            },
            Expr::Extract { arg, lo, width, .. } => Expr::Extract {
                arg: bx(arg),
                lo: *lo,
                width: width.without_spans(),
                span: s,
            },
            Expr::Replicate { arg, count, .. } => Expr::Replicate {
                arg: bx(arg),
                count: count.without_spans(),
                span: s,
            },
            Expr::Read { mem, addr, .. } => Expr::Read {
                mem: mem.without_spans(),
                addr: bx(addr),
                span: s,
            },
        }
    }
}
