//! One walk over the AST. It declares each name, resolves each use, and collects the errors
//! of passes 2 and 3 apart, because pass 2 errors rank before pass 3 errors (design
//! section 6.2). It recurses over the AST, so it runs on the front-end thread.

use crate::prelude::{Prelude, later_slice};
use crate::scope::Scopes;
use crate::{Code, Decl, DeclId, Error, Kind, Table, Target};
use parse::ast::{Expr, Ident, Item, Param, Pos, Stmt, TypeExpr};
use std::collections::BTreeMap;

/// Resolves the names of the items. Returns the table, or the errors of the first pass with
/// an error.
pub(crate) fn run(items: &[Item]) -> Result<Table, Vec<Error>> {
    let mut walker = Walker::default();
    for item in items {
        walker.declare_item(item);
    }
    for item in items {
        walker.item(item);
    }
    let Walker {
        decls,
        names,
        scopes,
        duplicates,
        unresolved,
    } = walker;
    let mut errors = if duplicates.is_empty() {
        unresolved
    } else {
        duplicates
    };
    if errors.is_empty() {
        return Ok(Table {
            decls,
            items: scopes.into_items(),
            names,
        });
    }
    errors.sort_by_key(|e| e.pos);
    Err(errors)
}

#[derive(Default)]
struct Walker {
    decls: Vec<Decl>,
    names: BTreeMap<Pos, Target>,
    scopes: Scopes,
    /// `S002`, pass 2.
    duplicates: Vec<Error>,
    /// `S003`, pass 3.
    unresolved: Vec<Error>,
}

impl Walker {
    fn new_decl(&mut self, name: &Ident, kind: Kind) -> DeclId {
        let id = DeclId(self.decls.len());
        self.decls.push(Decl {
            kind,
            name: name.name.clone(),
            pos: name.pos,
        });
        self.names.insert(name.pos, Target::Decl(id));
        id
    }

    fn duplicate(&mut self, name: &Ident, first: DeclId) {
        let at = self.decls[first.0].pos;
        self.duplicates.push(Error {
            code: Code::S002,
            pos: name.pos,
            message: format!(
                "`{}` is already declared at {}:{}",
                name.name, at.line, at.col
            ),
        });
    }

    fn declare_item(&mut self, item: &Item) {
        let (name, kind) = match item {
            Item::Const { name, .. } => (name, Kind::Const),
            Item::Fn { name, .. } => (name, Kind::Fn),
            Item::Module { name, .. } => (name, Kind::Module),
        };
        let id = self.new_decl(name, kind);
        if let Err(first) = self.scopes.declare_item(&name.name, id) {
            self.duplicate(name, first);
        }
    }

    /// Declares a name in the innermost scope. A use resolves to it only after this call.
    fn declare(&mut self, name: &Ident, kind: Kind) {
        let id = self.new_decl(name, kind);
        if let Err(first) = self.scopes.declare_local(&name.name, id) {
            self.duplicate(name, first);
        }
    }

    /// Declares a name that has no token. Its position is the module, so no token points to it.
    fn declare_implicit(&mut self, name: &Ident, kind: Kind) {
        let id = DeclId(self.decls.len());
        self.decls.push(Decl {
            kind,
            name: name.name.clone(),
            pos: name.pos,
        });
        // The scope is new, so the name cannot repeat.
        let _ = self.scopes.declare_local(&name.name, id);
    }

    fn item(&mut self, item: &Item) {
        match item {
            Item::Const { ty, value, .. } => {
                self.ty(ty);
                self.expr(value);
            }
            Item::Fn {
                params, ret, body, ..
            } => {
                // The parameters and the top statements of the body share one scope.
                self.scopes.open();
                self.params(params);
                self.ty(ret);
                self.stmts(body);
                self.scopes.close();
            }
            Item::Module {
                pos,
                params,
                domains,
                body,
                ..
            } => {
                self.scopes.open();
                // Without a `domains` clause, the module has the default domain `clock`. It
                // comes first, so a repeat of the name is an error at the later declaration.
                if domains.is_none() {
                    let clock = Ident {
                        pos: *pos,
                        name: "clock".to_owned(),
                    };
                    self.declare_implicit(&clock, Kind::Domain);
                }
                self.params(params);
                for domain in domains.iter().flatten() {
                    self.declare(domain, Kind::Domain);
                }
                self.stmts(body);
                self.scopes.close();
            }
        }
    }

    /// A parameter type can use the parameters before it.
    fn params(&mut self, params: &[Param]) {
        for param in params {
            self.ty(&param.ty);
            self.declare(&param.name, Kind::Param);
        }
    }

    fn stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }

    fn block(&mut self, stmts: &[Stmt]) {
        self.scopes.open();
        self.stmts(stmts);
        self.scopes.close();
    }

    /// A name is in scope after its statement, so the type and the value cannot use it.
    fn stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Local {
                name, ty, value, ..
            } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                self.expr(value);
                self.declare(name, Kind::Local);
            }
            Stmt::Assign { target, value, .. } | Stmt::Connect { target, value, .. } => {
                self.expr(target);
                self.expr(value);
            }
            Stmt::Reg { name, ty, init, .. } => {
                self.ty(ty);
                self.expr(init);
                self.declare(name, Kind::Reg);
            }
            Stmt::Wire { name, ty, .. } => {
                self.ty(ty);
                self.declare(name, Kind::Wire);
            }
            Stmt::Input { name, ty, .. } => {
                self.ty(ty);
                self.declare(name, Kind::Input);
            }
            Stmt::Output { name, ty, .. } => {
                self.ty(ty);
                self.declare(name, Kind::Output);
            }
            Stmt::Inst {
                name, module, args, ..
            } => {
                self.module_name(module.pos, &module.name);
                for arg in args {
                    self.expr(arg);
                }
                self.declare(name, Kind::Instance);
            }
            Stmt::Ret { value, .. } => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            Stmt::CtIf { cond, yes, no, .. } => {
                self.expr(cond);
                self.block(yes);
                if let Some(no) = no {
                    self.block(no);
                }
            }
            Stmt::CtFor {
                var, lo, hi, body, ..
            } => {
                self.expr(lo);
                self.expr(hi);
                // The variable and the top statements of the body share one scope.
                self.scopes.open();
                self.declare(var, Kind::Loop);
                self.stmts(body);
                self.scopes.close();
            }
            Stmt::Block { body, .. } => self.block(body),
            Stmt::Expr { value, .. } => self.expr(value),
        }
    }

    fn ty(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Name { pos, name } => self.type_name(*pos, name),
            TypeExpr::Index { base, args, .. } => {
                self.ty(base);
                for arg in args {
                    self.expr(arg);
                }
            }
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } => {}
            Expr::Name { pos, name } => self.value_name(*pos, name),
            Expr::Unary { arg, .. } => self.expr(arg),
            Expr::Binary { lhs, rhs, .. } => {
                self.expr(lhs);
                self.expr(rhs);
            }
            Expr::Cond { cond, yes, no, .. } => {
                self.expr(cond);
                self.expr(yes);
                self.expr(no);
            }
            Expr::Call { callee, args, .. } => {
                self.expr(callee);
                for arg in args {
                    self.expr(arg);
                }
            }
            Expr::Index { base, args, .. } => {
                self.expr(base);
                for arg in args {
                    self.expr(arg);
                }
            }
            Expr::Field { base, .. } => self.expr(base),
        }
    }

    fn lookup(&self, name: &str) -> Option<Target> {
        match self.scopes.lookup(name) {
            Some(id) => Some(Target::Decl(id)),
            None => Prelude::of(name).map(Target::Prelude),
        }
    }

    fn is_module(&self, target: Target) -> bool {
        matches!(target, Target::Decl(id) if self.decls[id.0].kind == Kind::Module)
    }

    fn reject(&mut self, pos: Pos, message: String) {
        self.unresolved.push(Error {
            code: Code::S003,
            pos,
            message,
        });
    }

    fn unknown(&mut self, pos: Pos, name: &str) {
        let message = match later_slice(name) {
            Some(slice) => format!("`{name}` is not in slice 1; it comes in slice {slice}"),
            None => format!("`{name}` is not declared"),
        };
        self.reject(pos, message);
    }

    /// A name in an expression is anything but a module.
    fn value_name(&mut self, pos: Pos, name: &str) {
        match self.lookup(name) {
            Some(target) if self.is_module(target) => self.reject(
                pos,
                format!("`{name}` is not a value; a module is used only in an `instance`"),
            ),
            Some(target) => {
                self.names.insert(pos, target);
            }
            None => self.unknown(pos, name),
        }
    }

    /// A type name is a prelude type. Slice 1 has no type item.
    fn type_name(&mut self, pos: Pos, name: &str) {
        match self.lookup(name) {
            Some(target @ Target::Prelude(p)) if p.is_type() => {
                self.names.insert(pos, target);
            }
            Some(_) => self.reject(pos, format!("`{name}` is not a type")),
            None => self.unknown(pos, name),
        }
    }

    /// The module of an `instance` is a module item.
    fn module_name(&mut self, pos: Pos, name: &str) {
        match self.lookup(name) {
            Some(target) if self.is_module(target) => {
                self.names.insert(pos, target);
            }
            Some(_) => self.reject(pos, format!("`{name}` is not a module")),
            None => self.unknown(pos, name),
        }
    }
}
