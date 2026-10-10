//! One walk over the AST. It declares each name, resolves each use, and collects the errors
//! of passes 2 and 3 apart, because pass 2 errors rank before pass 3 errors (design
//! section 6.2). It recurses over the AST, so it runs on the front-end thread.

use crate::prelude::{Class, Prelude};
use crate::scope::Scopes;
use crate::{Code, Decl, DeclId, Error, Kind, Table, Target};
use parse::ast::{Expr, Ident, Item, Param, Pos, Stmt, TypeExpr};
use std::collections::BTreeMap;

/// The kind of name that a position needs.
#[derive(Clone, Copy)]
enum Want {
    /// A variable, a constant, a port, or an instance.
    Value,
    /// The callee of a call: a function, or a type for a conversion such as `UInt[8](3)`.
    Callee,
    /// A type, or the family that an index applies to.
    Type,
    /// An argument of a type family: a value, or a type as in `Reg[Bool]`.
    Argument,
    /// The module of an `instance` statement.
    Module,
}

impl Want {
    fn accepts(self, class: Class) -> bool {
        match self {
            Want::Value => class == Class::Value,
            Want::Callee => matches!(class, Class::Function | Class::Type),
            Want::Type => class == Class::Type,
            Want::Argument => matches!(class, Class::Value | Class::Type),
            Want::Module => class == Class::Module,
        }
    }

    fn describe(self) -> &'static str {
        match self {
            Want::Value => Class::Value.describe(),
            Want::Callee => "a function or a type",
            Want::Type => Class::Type.describe(),
            Want::Argument => "a value or a type",
            Want::Module => Class::Module.describe(),
        }
    }
}

fn class_of(kind: Kind) -> Class {
    match kind {
        Kind::Fn => Class::Function,
        Kind::Module => Class::Module,
        Kind::Domain => Class::Domain,
        Kind::Const
        | Kind::Param
        | Kind::Local
        | Kind::Loop
        | Kind::Reg
        | Kind::Wire
        | Kind::Input
        | Kind::Output
        | Kind::Instance => Class::Value,
    }
}

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

    fn item(&mut self, item: &Item) {
        match item {
            Item::Const { ty, value, .. } => {
                self.ty(ty);
                self.expr(value, Want::Value);
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
                params,
                domains,
                body,
                ..
            } => {
                self.scopes.open();
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
                self.expr(value, Want::Value);
                self.declare(name, Kind::Local);
            }
            Stmt::Assign { target, value, .. } | Stmt::Connect { target, value, .. } => {
                self.expr(target, Want::Value);
                self.expr(value, Want::Value);
            }
            Stmt::Reg { name, ty, init, .. } => {
                self.ty(ty);
                self.expr(init, Want::Value);
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
                self.use_name(module.pos, &module.name, Want::Module);
                for arg in args {
                    self.expr(arg, Want::Value);
                }
                self.declare(name, Kind::Instance);
            }
            Stmt::Ret { value, .. } => {
                if let Some(value) = value {
                    self.expr(value, Want::Value);
                }
            }
            Stmt::CtIf { cond, yes, no, .. } => {
                self.expr(cond, Want::Value);
                self.block(yes);
                if let Some(no) = no {
                    self.block(no);
                }
            }
            Stmt::CtFor {
                var, lo, hi, body, ..
            } => {
                self.expr(lo, Want::Value);
                self.expr(hi, Want::Value);
                // The variable and the top statements of the body share one scope.
                self.scopes.open();
                self.declare(var, Kind::Loop);
                self.stmts(body);
                self.scopes.close();
            }
            Stmt::Block { body, .. } => self.block(body),
            Stmt::Expr { value, .. } => self.expr(value, Want::Value),
        }
    }

    fn ty(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Name { pos, name } => self.use_name(*pos, name, Want::Type),
            TypeExpr::Index { base, args, .. } => {
                self.ty(base);
                for arg in args {
                    self.expr(arg, Want::Argument);
                }
            }
        }
    }

    /// `want` applies to a name. Another node passes the kind it needs to its parts.
    fn expr(&mut self, expr: &Expr, want: Want) {
        match expr {
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } => {}
            Expr::Name { pos, name } => self.use_name(*pos, name, want),
            Expr::Unary { arg, .. } => self.expr(arg, Want::Value),
            Expr::Binary { lhs, rhs, .. } => {
                self.expr(lhs, Want::Value);
                self.expr(rhs, Want::Value);
            }
            Expr::Cond { cond, yes, no, .. } => {
                self.expr(cond, Want::Value);
                self.expr(yes, Want::Value);
                self.expr(no, Want::Value);
            }
            Expr::Call { callee, args, .. } => {
                self.expr(callee, Want::Callee);
                for arg in args {
                    self.expr(arg, Want::Value);
                }
            }
            // Slice 1 indexes only a type family, such as `UInt[8]`.
            Expr::Index { base, args, .. } => {
                self.expr(base, Want::Type);
                for arg in args {
                    self.expr(arg, Want::Argument);
                }
            }
            Expr::Field { base, .. } => self.expr(base, Want::Value),
        }
    }

    fn use_name(&mut self, pos: Pos, name: &str, want: Want) {
        let found = match self.scopes.lookup(name) {
            Some(id) => Some((Target::Decl(id), class_of(self.decls[id.0].kind))),
            None => Prelude::of(name).map(|p| (Target::Prelude(p), p.class())),
        };
        let message = match found {
            Some((target, class)) if want.accepts(class) => {
                self.names.insert(pos, target);
                return;
            }
            Some((_, class)) => format!(
                "`{name}` is {}, but this position needs {}",
                class.describe(),
                want.describe()
            ),
            None => format!("unknown name `{name}`"),
        };
        self.unresolved.push(Error {
            code: Code::S003,
            pos,
            message,
        });
    }
}
