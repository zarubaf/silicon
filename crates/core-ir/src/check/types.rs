//! Pass 4 (`E005`, declared sizes) and pass 7 (`E004`, operation widths).

use super::error;
use super::scope::{Binding, Env, PortRef, Scope, stmt_exprs, visit};
use crate::ast::{BinOp, Design, Expr, Item, Num, Port, Stmt, Ty};
use crate::diag::{Diagnostic, ErrorCode};

/// The largest width of a declared or computed value.
const MAX_WIDTH: u32 = 65536;
/// The largest memory depth.
const MAX_DEPTH: u32 = 16_777_216;

/// The address width of a memory: `max(1, ceil(log2 depth))`.
pub(super) fn address_width(depth: u32) -> u32 {
    (u32::BITS - depth.saturating_sub(1).leading_zeros()).max(1)
}

fn valid_width(width: u32) -> bool {
    (1..=MAX_WIDTH).contains(&width)
}

// Pass 4.

pub(super) fn declared(design: &Design) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for item in &design.items {
        match item {
            Item::Module(m) => {
                port_sizes(&m.ports, &mut errors);
                for stmt in &m.stmts {
                    stmt_sizes(stmt, &mut errors);
                }
            }
            Item::Extern(e) => port_sizes(&e.ports, &mut errors),
        }
    }
    errors
}

fn port_sizes(ports: &[Port], errors: &mut Vec<Diagnostic>) {
    for port in ports {
        if let Ty::Bits(n) = port.ty
            && !valid_width(n.value)
        {
            errors.push(bad_width(port.span, "the port", n.value));
        }
    }
}

fn bad_width(span: crate::diag::Span, what: &str, width: u32) -> Diagnostic {
    error(
        ErrorCode::E005,
        span,
        format!("{what} has the width {width}; a width is 1 to {MAX_WIDTH}"),
    )
}

fn stmt_sizes(stmt: &Stmt, errors: &mut Vec<Diagnostic>) {
    match stmt {
        Stmt::Let { width, span, .. } | Stmt::Reg { width, span, .. } => {
            if !valid_width(width.value) {
                errors.push(bad_width(*span, "the declaration", width.value));
            }
        }
        Stmt::Mem {
            width, depth, span, ..
        } => {
            if !valid_width(width.value) {
                errors.push(bad_width(*span, "the memory", width.value));
            }
            let depth = &depth.value;
            if !(1..=MAX_DEPTH).contains(depth) {
                errors.push(error(
                    ErrorCode::E005,
                    *span,
                    format!("the memory depth {depth} is not 1 to {MAX_DEPTH}"),
                ));
            }
        }
        Stmt::Next { .. } | Stmt::Write { .. } | Stmt::Inst { .. } | Stmt::Assign { .. } => {}
    }
    for root in stmt_exprs(stmt) {
        visit(root, &mut |e| expr_sizes(e, errors));
    }
}

fn expr_sizes(expr: &Expr, errors: &mut Vec<Diagnostic>) {
    match expr {
        Expr::Const {
            width, value, span, ..
        } => {
            let width = &width.value;
            if !valid_width(*width) {
                errors.push(bad_width(*span, "the constant", *width));
            } else if value.bits() > u64::from(*width) {
                errors.push(error(
                    ErrorCode::E005,
                    *span,
                    format!("the constant {value} does not fit in {width} bits"),
                ));
            }
        }
        Expr::Replicate {
            count: Num { value: 0, .. },
            span,
            ..
        } => {
            errors.push(error(ErrorCode::E005, *span, "the replication count is 0"));
        }
        Expr::Extract {
            width: Num { value: 0, .. },
            span,
            ..
        } => {
            errors.push(error(ErrorCode::E005, *span, "the extracted width is 0"));
        }
        _ => {}
    }
}

// Pass 7.

pub(super) fn operations(env: &Env, scopes: &[Scope]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for scope in scopes {
        let mut typer = Typer {
            env,
            scope,
            errors: &mut errors,
        };
        typer.module();
    }
    errors
}

struct Typer<'e, 'a> {
    env: &'e Env<'a>,
    scope: &'e Scope<'a>,
    errors: &'e mut Vec<Diagnostic>,
}

impl Typer<'_, '_> {
    fn fail(&mut self, span: crate::diag::Span, message: impl Into<String>) {
        self.errors.push(error(ErrorCode::E004, span, message));
    }

    /// Checks that an expression has the width of its target.
    fn target(&mut self, expr: &Expr, want: u32, span: crate::diag::Span, what: &str) {
        if let Some(got) = self.width(expr)
            && got != want
        {
            self.fail(
                span,
                format!("{what} has the width {want}, but its value has {got}"),
            );
        }
    }

    fn module(&mut self) {
        let scope = self.scope;
        for decl in &scope.lets {
            self.target(decl.expr, decl.width, decl.span, "the `let`");
        }
        for reg in &scope.regs {
            if let Some(reset) = reg.reset {
                self.target(&reset.signal, 1, reset.span, "the reset signal");
                self.target(&reset.value, reg.width, reset.span, "the register");
            }
        }
        for stmt in &scope.module.stmts {
            match stmt {
                Stmt::Next { reg, expr, span } => {
                    if let Some(Binding::Reg(i)) = scope.lookup(&reg.text)
                        && let Some(decl) = scope.regs.get(i.index())
                    {
                        self.target(expr, decl.width, *span, "the register");
                    } else {
                        self.width(expr);
                    }
                }
                Stmt::Assign { out, expr, span } => {
                    let width = match scope.lookup(&out.text) {
                        Some(Binding::Output(o)) => self
                            .env
                            .module_sig(scope.index)
                            .and_then(|sig| sig.outputs.get(o.index()))
                            .map(|p| p.width),
                        _ => None,
                    };
                    match width {
                        Some(w) => self.target(expr, w, *span, "the output"),
                        None => {
                            self.width(expr);
                        }
                    }
                }
                Stmt::Write {
                    mem,
                    addr,
                    data,
                    en,
                    span,
                    ..
                } => {
                    if let Some(Binding::Mem(i)) = scope.lookup(&mem.text)
                        && let Some(decl) = scope.mems.get(i.index())
                    {
                        self.target(addr, address_width(decl.depth), *span, "the address");
                        self.target(data, decl.width, *span, "the memory word");
                        self.target(en, 1, *span, "the write enable");
                    } else {
                        for e in [addr, data, en] {
                            self.width(e);
                        }
                    }
                }
                Stmt::Let { .. } | Stmt::Reg { .. } | Stmt::Mem { .. } | Stmt::Inst { .. } => {}
            }
        }
        for inst in &scope.insts {
            let sig = inst.callee.and_then(|c| self.env.sig(c));
            for conn in inst.conns {
                let want = sig.and_then(|s| match s.port(&conn.port.text) {
                    Some(PortRef::Input(i)) => s.inputs.get(i.index()).map(|p| p.width),
                    _ => None,
                });
                match want {
                    Some(w) => self.target(&conn.expr, w, conn.span, "the input"),
                    None => {
                        self.width(&conn.expr);
                    }
                }
            }
        }
    }

    /// The width of an expression. An error in an operand gives `None`: the
    /// operand is reported, and its parent has no width to check.
    fn width(&mut self, expr: &Expr) -> Option<u32> {
        match expr {
            Expr::Ref(name) => self.binding_width(self.scope.lookup(&name.text)?),
            Expr::InstOut { inst, port, .. } => {
                let Binding::Inst(i) = self.scope.lookup(&inst.text)? else {
                    return None;
                };
                let sig = self.env.sig(self.scope.insts.get(i.index())?.callee?)?;
                match sig.port(&port.text)? {
                    PortRef::Output(o) => sig.outputs.get(o.index()).map(|p| p.width),
                    _ => None,
                }
            }
            Expr::Const { width, .. } => Some(width.value),
            Expr::Unary { arg, .. } => self.width(arg),
            Expr::Binary {
                op, lhs, rhs, span, ..
            } => {
                let (l, r) = (self.width(lhs), self.width(rhs));
                let (l, r) = (l?, r?);
                if *op == BinOp::Concat {
                    let sum = l.saturating_add(r);
                    if sum > MAX_WIDTH {
                        self.fail(*span, format!("the concatenation has the width {sum}"));
                        return None;
                    }
                    return Some(sum);
                }
                self.equal(l, r, *span).then_some(l)
            }
            Expr::Icmp { lhs, rhs, span, .. } => {
                let (l, r) = (self.width(lhs), self.width(rhs));
                self.equal(l?, r?, *span).then_some(1)
            }
            Expr::Mux {
                cond,
                then,
                els,
                span,
            } => {
                let (c, t, e) = (self.width(cond), self.width(then), self.width(els));
                let (c, t, e) = (c?, t?, e?);
                if c != 1 {
                    self.fail(*span, format!("the condition has the width {c}, not 1"));
                    return None;
                }
                self.equal(t, e, *span).then_some(t)
            }
            Expr::Extract {
                arg,
                lo,
                width,
                span,
            } => {
                let width = &width.value;
                let w = self.width(arg)?;
                if u64::from(*lo) + u64::from(*width) > u64::from(w) {
                    self.fail(
                        *span,
                        format!(
                            "the bits {lo} to {} are outside {w} bits",
                            u64::from(*lo) + u64::from(*width)
                        ),
                    );
                    return None;
                }
                Some(*width)
            }
            Expr::Replicate { arg, count, span } => {
                let count = &count.value;
                let w = self.width(arg)?;
                let total = u64::from(w) * u64::from(*count);
                if total > u64::from(MAX_WIDTH) {
                    self.fail(*span, format!("the replication has the width {total}"));
                    return None;
                }
                u32::try_from(total).ok()
            }
            Expr::Read { mem, addr, span } => {
                let a = self.width(addr);
                let Binding::Mem(i) = self.scope.lookup(&mem.text)? else {
                    return None;
                };
                let decl = self.scope.mems.get(i.index())?;
                let want = address_width(decl.depth);
                let a = a?;
                if a != want {
                    self.fail(
                        *span,
                        format!(
                            "the address has the width {a}, but `{}` needs {want}",
                            mem.text
                        ),
                    );
                    return None;
                }
                Some(decl.width)
            }
        }
    }

    fn equal(&mut self, l: u32, r: u32, span: crate::diag::Span) -> bool {
        if l != r {
            self.fail(span, format!("the operand widths {l} and {r} differ"));
        }
        l == r
    }

    fn binding_width(&self, binding: Binding) -> Option<u32> {
        let scope = self.scope;
        match binding {
            Binding::Input(i) => self
                .env
                .module_sig(scope.index)?
                .inputs
                .get(i.index())
                .map(|p| p.width),
            Binding::Let(i) => scope.lets.get(i.index()).map(|d| d.width),
            Binding::Reg(i) => scope.regs.get(i.index()).map(|d| d.width),
            _ => None,
        }
    }
}
