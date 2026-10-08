//! Pass 2 (`E002`, unique names) and pass 3 (`E003`, name resolution).

use super::error;
use super::scope::{Binding, Env, PortRef, Scope, stmt_exprs, visit};
use crate::ast::{Design, Expr, Item, Name, Port, Stmt};
use crate::diag::{Diagnostic, ErrorCode};
use crate::typed::Callee;
use std::collections::HashSet;

/// The names defined in one scope.
#[derive(Default)]
struct Defs<'a> {
    seen: HashSet<&'a str>,
    errors: Vec<Diagnostic>,
}

impl<'a> Defs<'a> {
    fn define(&mut self, name: &'a Name) {
        if !self.seen.insert(&name.text) {
            self.errors.push(error(
                ErrorCode::E002,
                name.span,
                format!("`{}` is already defined in this scope", name.text),
            ));
        }
    }

    fn ports(&mut self, ports: &'a [Port]) {
        for port in ports {
            self.define(&port.name);
        }
    }
}

/// Pass 2.
pub(super) fn duplicates(design: &Design) -> Vec<Diagnostic> {
    let mut items = Defs::default();
    let mut errors = Vec::new();
    for item in &design.items {
        match item {
            Item::Module(m) => {
                items.define(&m.name);
                let mut body = Defs::default();
                body.ports(&m.ports);
                for stmt in &m.stmts {
                    match stmt {
                        Stmt::Let { name, .. }
                        | Stmt::Reg { name, .. }
                        | Stmt::Mem { name, .. }
                        | Stmt::Inst { name, .. } => body.define(name),
                        Stmt::Next { .. } | Stmt::Write { .. } | Stmt::Assign { .. } => {}
                    }
                }
                errors.extend(body.errors);
            }
            Item::Extern(e) => {
                items.define(&e.name);
                let mut body = Defs::default();
                body.ports(&e.ports);
                errors.extend(body.errors);
            }
        }
    }
    errors.extend(items.errors);
    errors
}

/// Pass 3.
pub(super) fn unresolved(design: &Design, env: &Env, scopes: &[Scope]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    if !matches!(env.callee(&design.top.text), Some(Callee::Module(_))) {
        errors.push(error(
            ErrorCode::E003,
            design.top.span,
            format!("`{}` is not a module", design.top.text),
        ));
    }
    for scope in scopes {
        Resolver {
            env,
            scope,
            errors: &mut errors,
        }
        .module();
    }
    errors
}

struct Resolver<'e, 'a> {
    env: &'e Env<'a>,
    scope: &'e Scope<'a>,
    errors: &'e mut Vec<Diagnostic>,
}

impl Resolver<'_, '_> {
    fn unknown(&mut self, name: &Name, what: &str) {
        self.errors.push(error(
            ErrorCode::E003,
            name.span,
            format!("`{}` is not {what}", name.text),
        ));
    }

    fn module(&mut self) {
        for inst in &self.scope.insts {
            if inst.callee.is_none() {
                self.unknown(inst.module, "a module or an extern");
            }
        }
        for stmt in &self.scope.module.stmts {
            match stmt {
                Stmt::Reg { clk, .. } | Stmt::Mem { clk, .. } => self.defined(clk),
                Stmt::Next { reg: name, .. } | Stmt::Assign { out: name, .. } => {
                    self.defined(name);
                }
                Stmt::Write { mem, .. } => self.memory(mem),
                Stmt::Let { .. } | Stmt::Inst { .. } => {}
            }
            for root in stmt_exprs(stmt) {
                visit(root, &mut |e| self.expr(e));
            }
        }
    }

    /// A name whose kind a later pass checks.
    fn defined(&mut self, name: &Name) {
        if self.scope.lookup(&name.text).is_none() {
            self.unknown(name, "defined");
        }
    }

    fn memory(&mut self, name: &Name) {
        if !matches!(self.scope.lookup(&name.text), Some(Binding::Mem(_))) {
            self.unknown(name, "a memory");
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Ref(name) => {
                if !matches!(
                    self.scope.lookup(&name.text),
                    Some(
                        Binding::Input(_)
                            | Binding::Clock
                            | Binding::Stray
                            | Binding::Let(_)
                            | Binding::Reg(_)
                    )
                ) {
                    self.unknown(name, "a value");
                }
            }
            Expr::InstOut { inst, port, .. } => self.inst_out(inst, port),
            Expr::Read { mem, .. } => self.memory(mem),
            _ => {}
        }
    }

    fn inst_out(&mut self, inst: &Name, port: &Name) {
        let Some(Binding::Inst(i)) = self.scope.lookup(&inst.text) else {
            self.unknown(inst, "an instance");
            return;
        };
        let Some(callee) = self.scope.insts.get(i.index()).and_then(|d| d.callee) else {
            // The unresolved module is reported on its own.
            return;
        };
        let is_output = self
            .env
            .sig(callee)
            .and_then(|sig| sig.port(&port.text))
            .is_some_and(|p| matches!(p, PortRef::Output(_) | PortRef::Stray));
        if !is_output {
            self.errors.push(error(
                ErrorCode::E003,
                inst.span,
                format!("`{}` is not an output of `{}`", port.text, inst.text),
            ));
        }
    }
}
