// SPDX-License-Identifier: Apache-2.0
//! One walk over the AST. It declares each name, resolves each use, and collects the errors
//! of passes 2 and 3 apart, because pass 2 errors rank before pass 3 errors (design
//! section 6.2). It recurses over the AST, so it runs on the front-end thread.

use crate::prelude::{Prelude, RESPONSE, later_slice, node};
use crate::scope::Scopes;
use crate::{
    Call, Code, Decl, DeclId, Error, Kind, Resolved, Table, Target, VariantNames, VariantRef,
};
use parse::ast::{
    Expr, FnParam, Ident, Item, NodeId, Param, ParamMode, Pos, Stmt, StructField, TypeExpr, Variant,
};
use std::collections::{BTreeMap, BTreeSet};

/// Resolves the names of the items. Returns the table, or the errors of the first pass with
/// an error.
pub(crate) fn run(items: &[Item]) -> Result<Table, Vec<Error>> {
    let mut walker = Walker::default();
    for item in items {
        walker.declare_item(item);
    }
    let response = walker.declare_response();
    for item in items {
        walker.item(item);
    }
    let Walker {
        decls,
        names,
        scopes,
        duplicates,
        unresolved,
        calls,
        variants,
        variant_names,
        ..
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
            calls,
            variants,
            variant_names,
            response,
        });
    }
    errors.sort_by_key(|e| e.pos);
    Err(errors)
}

/// Resolves the names of an expression in the file scope of `resolved`. Returns the map from
/// the id of each name node of the expression to its target and the id of each call node to
/// its call site, or the `S003` errors.
pub(crate) fn run_expr(resolved: &Resolved, expr: &Expr) -> Result<ExprTable, Vec<Error>> {
    let mut walker = Walker {
        decls: resolved.decls.clone(),
        scopes: Scopes::of_items(resolved.items.clone()),
        variant_names: resolved.variant_names.clone(),
        response: Some(resolved.response),
        ..Walker::default()
    };
    walker.expr(expr);
    let mut errors = walker.unresolved;
    if errors.is_empty() {
        return Ok((walker.names, walker.calls, walker.variants));
    }
    errors.sort_by_key(|e| e.pos);
    Err(errors)
}

/// The targets of the name nodes and the call sites of the call nodes.
pub(crate) type ExprTable = (
    BTreeMap<NodeId, Target>,
    BTreeMap<NodeId, Call>,
    BTreeMap<NodeId, VariantRef>,
);

#[derive(Default)]
struct Walker {
    decls: Vec<Decl>,
    names: BTreeMap<NodeId, Target>,
    scopes: Scopes,
    /// `S002`, pass 2.
    duplicates: Vec<Error>,
    /// `S003`, pass 3.
    unresolved: Vec<Error>,
    /// The call site of each call node and method node, and the receiver parameter.
    calls: BTreeMap<NodeId, Call>,
    /// The variant that each variant path names, by the id of the first name of the path.
    variants: BTreeMap<NodeId, VariantRef>,
    /// For each enum item, the first variant with each name.
    variant_names: VariantNames,
    /// The next call site of the current item body.
    next_site: usize,
    /// How many names so far resolved to a parameter. A `fn` item reads the change over its
    /// signature to tell whether it is generic.
    param_uses: usize,
    /// The declaration of the prelude struct `ReadResponse`.
    response: Option<DeclId>,
}

impl Walker {
    fn new_decl(&mut self, name: &Ident, kind: Kind, receiver: Option<usize>) -> DeclId {
        let id = DeclId(self.decls.len());
        self.decls.push(Decl {
            kind,
            receiver,
            name: name.name.clone(),
            pos: name.pos,
            generic: false,
        });
        self.names.insert(name.id, Target::Decl(id));
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
        let (name, kind, receiver) = match item {
            Item::Const { name, .. } => (name, Kind::Const, None),
            Item::Fn { name, params, .. } => (
                name,
                Kind::Fn,
                params.iter().position(|q| q.mode != ParamMode::Comptime),
            ),
            Item::Module { name, .. } => (name, Kind::Module, None),
            Item::Struct { name, .. } => (name, Kind::Struct, None),
            Item::Alias { name, .. } => (name, Kind::Alias, None),
            Item::Enum { name, .. } => (name, Kind::Enum, None),
        };
        let id = self.new_decl(name, kind, receiver);
        if let Err(first) = self.scopes.declare_item(&name.name, id) {
            self.duplicate(name, first);
        }
        if let Item::Enum { variants, .. } = item {
            let mut names = BTreeMap::new();
            for (j, v) in variants.iter().enumerate() {
                names.entry(v.name.name.clone()).or_insert(j);
            }
            self.variant_names.insert(id, names);
        }
    }

    /// Declares the prelude struct and gives the names of its item their targets, past the item
    /// scope. The name `ReadResponse` is not in the item scope, so a user item shadows it.
    fn declare_response(&mut self) -> DeclId {
        let pos = Pos { line: 0, col: 0 };
        let decl = |walker: &mut Walker, k: usize, name: &str, kind: Kind| {
            let id = DeclId(walker.decls.len());
            walker.decls.push(Decl {
                kind,
                receiver: None,
                name: name.to_owned(),
                pos,
                generic: false,
            });
            walker.names.insert(NodeId::prelude(k), Target::Decl(id));
            id
        };
        let response = decl(self, node::NAME, RESPONSE, Kind::Struct);
        let t = decl(self, node::PARAM, "T", Kind::Param);
        self.names.insert(
            NodeId::prelude(node::PARAM_TYPE),
            Target::Prelude(Prelude::Type),
        );
        self.names
            .insert(NodeId::prelude(node::DATA_TYPE), Target::Decl(t));
        self.names.insert(
            NodeId::prelude(node::VALID_TYPE),
            Target::Prelude(Prelude::Bool),
        );
        self.response = Some(response);
        response
    }

    /// Declares a name in the innermost scope. A use resolves to it only after this call.
    fn declare(&mut self, name: &Ident, kind: Kind) {
        let id = self.new_decl(name, kind, None);
        if let Err(first) = self.scopes.declare_local(&name.name, id) {
            self.duplicate(name, first);
        }
    }

    /// Declares a name that has no token. Its position is the module, and no node points to it.
    fn declare_implicit(&mut self, pos: Pos, name: &str, kind: Kind) {
        let id = DeclId(self.decls.len());
        self.decls.push(Decl {
            kind,
            receiver: None,
            name: name.to_owned(),
            pos,
            generic: false,
        });
        // The scope is new, so the name cannot repeat.
        let _ = self.scopes.declare_local(name, id);
    }

    fn item(&mut self, item: &Item) {
        match item {
            Item::Const { ty, value, .. } => {
                self.ty(ty);
                self.expr(value);
            }
            Item::Fn {
                name,
                params,
                ret,
                body,
                ..
            } => {
                // The parameters and the top statements of the body share one scope.
                self.scopes.open();
                let before = self.param_uses;
                self.params(params);
                self.ty(ret);
                // A function is generic when it has a `comptime` parameter, or when a
                // parameter type or the result type names a parameter.
                let generic = self.param_uses > before
                    || params.iter().any(|q| q.mode == ParamMode::Comptime);
                if let Some(Target::Decl(id)) = self.names.get(&name.id) {
                    self.decls[id.0].generic = generic;
                }
                self.next_site = 0;
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
                    self.declare_implicit(*pos, "clock", Kind::Domain);
                }
                self.params(params);
                for domain in domains.iter().flatten() {
                    self.declare(domain, Kind::Domain);
                }
                self.next_site = 0;
                self.stmts(body);
                self.scopes.close();
            }
            Item::Struct { params, fields, .. } => {
                // The parameters and the field types share one scope.
                self.scopes.open();
                self.params(params);
                self.fields(fields);
                self.scopes.close();
            }
            Item::Alias { ty, .. } => self.ty(ty),
            Item::Enum { tag, variants, .. } => {
                self.ty(tag);
                self.variants(variants);
            }
        }
    }

    /// A variant name is in no scope: only a second variant with the name is an error.
    fn variants(&mut self, variants: &[Variant]) {
        let mut seen = BTreeSet::new();
        for variant in variants {
            if !seen.insert(variant.name.name.as_str()) {
                self.duplicates.push(Error {
                    code: Code::S002,
                    pos: variant.name.pos,
                    message: format!(
                        "the variant `{}` is already declared in this enum; rename one of the \
                         two variants",
                        variant.name.name
                    ),
                });
            }
            for ty in &variant.payload {
                self.ty(ty);
            }
            self.expr(&variant.tag);
        }
    }

    /// A parameter type can use the parameters before it.
    fn params(&mut self, params: &[Param]) {
        for param in params {
            self.ty(&param.ty);
            self.declare(&param.name, Kind::Param);
        }
    }

    /// A field name is in no scope: only a second field with the name is an error.
    fn fields(&mut self, fields: &[StructField]) {
        let mut seen = BTreeSet::new();
        for field in fields {
            if !seen.insert(field.name.name.as_str()) {
                self.duplicates.push(Error {
                    code: Code::S002,
                    pos: field.name.pos,
                    message: format!("the field `{}` is already declared", field.name.name),
                });
            }
            self.ty(&field.ty);
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
            Stmt::Mem {
                name, word, depth, ..
            } => {
                self.ty(word);
                self.expr(depth);
                self.declare(name, Kind::Mem);
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
                self.module_name(module.pos, module.id, &module.name);
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
            Stmt::Alias { name, ty, .. } => {
                self.ty(ty);
                self.declare(name, Kind::Alias);
            }
        }
    }

    fn ty(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Name { pos, id, name } => self.type_name(*pos, *id, name),
            TypeExpr::Index { base, args, .. } => {
                self.ty(base);
                for arg in args {
                    self.expr(arg);
                }
            }
            TypeExpr::Unit { .. } => {}
            TypeExpr::Tuple { elems, .. } => {
                for elem in elems {
                    self.ty(elem);
                }
            }
            TypeExpr::Array { elem, len, .. } => {
                self.ty(elem);
                self.expr(len);
            }
            TypeExpr::Fn { params, ret, .. } => self.fn_type(params, ret),
        }
    }

    /// The parameter types and the result type of a function type. They declare no name.
    fn fn_type(&mut self, params: &[FnParam], ret: &TypeExpr) {
        for param in params {
            self.ty(&param.ty);
        }
        self.ty(ret);
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Num { .. } | Expr::Bool { .. } | Expr::Str { .. } | Expr::Unit { .. } => {}
            Expr::Name { pos, id, name } => self.value_name(*pos, *id, name),
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
            Expr::Call {
                id, callee, args, ..
            } => {
                self.site(*id);
                self.expr(callee);
                for arg in args {
                    self.expr(arg);
                }
            }
            Expr::Method {
                id,
                recv,
                name,
                args,
                ..
            } => {
                self.site(*id);
                self.expr(recv);
                self.method_name(name);
                self.bind_receiver(*id, name);
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
            Expr::Field { base, .. } | Expr::Select { base, .. } => self.expr(base),
            Expr::ArrayType { elem, len, .. } => {
                self.ty(elem);
                self.expr(len);
            }
            Expr::FnType { params, ret, .. } => self.fn_type(params, ret),
            Expr::Tuple { elems, .. } | Expr::Array { elems, .. } => {
                for elem in elems {
                    self.expr(elem);
                }
            }
            Expr::Path { pos, ty, variant } => self.variant_path(*pos, ty, variant),
        }
    }

    /// The variant path `ty::variant`. The first part resolves by the ordinary scoping, so a
    /// local shadows an enum item. A first part that is no enum item is `S003` at the path, and
    /// a second part that names no variant is `S003` at that part.
    fn variant_path(&mut self, pos: Pos, ty: &Ident, variant: &Ident) {
        let item = self
            .scopes
            .lookup(&ty.name)
            .filter(|id| self.decls[id.0].kind == Kind::Enum);
        let Some(item) = item else {
            self.reject(
                pos,
                format!(
                    "`{}` is not an enum, so `{}::{}` names no variant; use the name of an enum",
                    ty.name, ty.name, variant.name
                ),
            );
            return;
        };
        let index = self
            .variant_names
            .get(&item)
            .and_then(|names| names.get(&variant.name));
        match index {
            Some(&index) => {
                self.variants.insert(
                    ty.id,
                    VariantRef {
                        item: item.0,
                        index,
                    },
                );
            }
            None => self.reject(
                variant.pos,
                format!(
                    "`{}` has no variant `{}`; use a variant that `{}` declares",
                    ty.name, variant.name, ty.name
                ),
            ),
        }
    }

    /// Gives the call node or the method node with the id the next call site of the body.
    fn site(&mut self, id: NodeId) {
        let site = self.next_site;
        self.calls.insert(
            id,
            Call {
                site,
                receiver: None,
            },
        );
        self.next_site += 1;
    }

    /// Records the parameter that the receiver of the method node `id` binds to, from the
    /// function that its name points to.
    fn bind_receiver(&mut self, id: NodeId, name: &Ident) {
        let receiver = match self.names.get(&name.id) {
            Some(Target::Decl(d)) => self.decls[d.0].receiver,
            Some(Target::Prelude(p)) => p.receiver(),
            None => None,
        };
        if let Some(call) = self.calls.get_mut(&id) {
            call.receiver = receiver;
        }
    }

    /// The function of a receiver call: a `fn` item, else a prelude function. A local does not
    /// hide it.
    fn method_name(&mut self, name: &Ident) {
        let target = match self.scopes.item(&name.name) {
            Some(id) => Some(Target::Decl(id)),
            None => self.prelude_target(&name.name),
        };
        let is_fn = match target {
            Some(Target::Decl(id)) => self.decls[id.0].kind == Kind::Fn,
            Some(Target::Prelude(p)) => p.is_fn(),
            None => {
                self.unknown(name.pos, &name.name);
                return;
            }
        };
        if let (true, Some(target)) = (is_fn, target) {
            self.names.insert(name.id, target);
        } else {
            self.reject(name.pos, format!("`{}` is not a function", name.name));
        }
    }

    fn lookup(&self, name: &str) -> Option<Target> {
        match self.scopes.lookup(name) {
            Some(id) => Some(Target::Decl(id)),
            None => self.prelude_target(name),
        }
    }

    /// The prelude declaration of a name: a prelude name, else the prelude struct.
    fn prelude_target(&self, name: &str) -> Option<Target> {
        match Prelude::of(name) {
            Some(p) => Some(Target::Prelude(p)),
            None if name == RESPONSE => self.response.map(Target::Decl),
            None => None,
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
            Some(slice) => format!("`{name}` is not supported yet; it comes in slice {slice}"),
            None => format!("`{name}` is not declared"),
        };
        self.reject(pos, message);
    }

    /// A name in an expression is anything but a module.
    fn value_name(&mut self, pos: Pos, id: NodeId, name: &str) {
        match self.lookup(name) {
            Some(target) if self.is_module(target) => self.reject(
                pos,
                format!("`{name}` is not a value; a module is used only in an `instance`"),
            ),
            Some(target) => self.bind(id, target),
            None => self.unknown(pos, name),
        }
    }

    /// Points the name node `id` at its target.
    fn bind(&mut self, id: NodeId, target: Target) {
        if matches!(target, Target::Decl(d) if self.decls[d.0].kind == Kind::Param) {
            self.param_uses += 1;
        }
        self.names.insert(id, target);
    }

    /// Whether a name can stand in a type position: a prelude type, a `struct` item, a `type`
    /// item, or a local. Only elaboration knows whether a local holds a type.
    fn is_type(&self, target: Target) -> bool {
        match target {
            Target::Prelude(p) => p.is_type(),
            Target::Decl(id) => {
                !matches!(self.decls[id.0].kind, Kind::Const | Kind::Fn | Kind::Module)
            }
        }
    }

    fn type_name(&mut self, pos: Pos, id: NodeId, name: &str) {
        match self.lookup(name) {
            Some(target) if self.is_type(target) => self.bind(id, target),
            Some(_) => self.reject(pos, format!("`{name}` is not a type")),
            None => self.unknown(pos, name),
        }
    }

    /// The module of an `instance` is a module item.
    fn module_name(&mut self, pos: Pos, id: NodeId, name: &str) {
        match self.lookup(name) {
            Some(target) if self.is_module(target) => {
                self.names.insert(id, target);
            }
            Some(_) => self.reject(pos, format!("`{name}` is not a module")),
            None => self.unknown(pos, name),
        }
    }
}
