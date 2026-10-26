// SPDX-License-Identifier: Apache-2.0
//! One walk over the AST. It declares each name, resolves each use, and collects the errors
//! of passes 2 and 3 apart, because pass 2 errors rank before pass 3 errors (design
//! section 6.2). It recurses over the AST, so it runs on the front-end thread.

use crate::prelude::{Built, DOMAIN_TEXT, INSTANCE_TEXT, Leaf, Prelude, STRUCTS};
use crate::scope::Scopes;
use crate::{
    Call, Code, Decl, DeclId, Error, Kind, Resolved, Table, Target, VariantNames, VariantRef,
};
use parse::ast::{
    Arm, Expr, FnParam, Ident, Item, NodeId, Param, ParamMode, Pattern, PortForm, Pos, Stmt,
    StructField, TypeExpr, Variant,
};
use std::collections::{BTreeMap, BTreeSet};

/// Resolves the names of the items. Returns the table, or the errors of the first pass with
/// an error.
pub(crate) fn run(items: &[Item], built: &[Built]) -> Result<Table, Vec<Error>> {
    let mut walker = Walker::default();
    for item in items {
        walker.declare_item(item);
    }
    walker.declare_prelude(built);
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
        prelude,
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
            prelude,
        });
    }
    errors.sort_by_key(|e| e.pos);
    Err(errors)
}

/// Resolves the names of an expression in the file scope of `resolved`. Returns the map from
/// the id of each name node of the expression to its target and the id of each call node to
/// its call site, or the errors of the first pass with an error.
pub(crate) fn run_expr(resolved: &Resolved, expr: &Expr) -> Result<ExprTable, Vec<Error>> {
    let mut walker = Walker {
        decls: resolved.decls.clone(),
        scopes: Scopes::of_items(resolved.items.clone()),
        variant_names: resolved.variant_names.clone(),
        prelude: resolved.prelude.clone(),
        ..Walker::default()
    };
    walker.expr(expr);
    let mut errors = if walker.duplicates.is_empty() {
        walker.unresolved
    } else {
        walker.duplicates
    };
    if errors.is_empty() {
        let extra = walker.decls.split_off(resolved.decls.len());
        return Ok((walker.names, walker.calls, walker.variants, extra));
    }
    errors.sort_by_key(|e| e.pos);
    Err(errors)
}

/// The targets of the name nodes, the call sites of the call nodes, the variants of the paths,
/// and the declarations of the binders.
pub(crate) type ExprTable = (
    BTreeMap<NodeId, Target>,
    BTreeMap<NodeId, Call>,
    BTreeMap<NodeId, VariantRef>,
    Vec<Decl>,
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
    /// The declaration of each prelude struct, in the order of `STRUCTS`.
    prelude: Vec<DeclId>,
    /// The port names of the module body or the `fn` body that the walk is in (`families`). A
    /// `comptime fn` has none.
    ports: BTreeMap<String, PortName>,
}

/// What the family walk of a module body knows of one port name: its family, as the position
/// of its first indexed declaration, its binder, and whether that declaration is an input, and
/// the position of its first scalar port.
#[derive(Default)]
struct PortName {
    family: Option<(Pos, DeclId, bool)>,
    scalar: Option<Pos>,
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

    fn duplicate(&mut self, name: &Ident) {
        self.duplicate_at(name, name.pos);
    }

    /// `S002` for the name at `pos`.
    fn duplicate_at(&mut self, name: &Ident, pos: Pos) {
        self.duplicates.push(Error {
            code: Code::S002,
            pos,
            message: format!("`{}` is already declared in this scope", name.name),
        });
    }

    /// `S002` for a name that the innermost scope has. The error is at the later of the two
    /// names: the family walk declares a family before the statements, so the earlier name in
    /// the source can be the one that fails.
    fn duplicate_here(&mut self, name: &Ident) {
        let at = self
            .scopes
            .here(&name.name)
            .and_then(|other| self.decls.get(other.0))
            .map_or(name.pos, |other| name.pos.max(other.pos));
        self.duplicate_at(name, at);
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
        if !self.scopes.declare_item(&name.name, id) {
            self.duplicate(name);
        }
        if let Item::Enum { variants, .. } = item {
            let mut names = BTreeMap::new();
            for (j, v) in variants.iter().enumerate() {
                names.entry(v.name.name.clone()).or_insert(j);
            }
            self.variant_names.insert(id, names);
        }
    }

    /// Declares the prelude structs and gives the names of their items their targets, past the
    /// item scope. Their names are not in the item scope, so a user item shadows them. All
    /// structs are declared first, because a field type can name a later struct.
    fn declare_prelude(&mut self, built: &[Built]) {
        let decls: Vec<DeclId> = built
            .iter()
            .map(|b| self.declare_hidden(&b.name, Kind::Struct))
            .collect();
        for b in built {
            let params: Vec<DeclId> = b
                .params
                .iter()
                .map(|p| self.declare_hidden(p, Kind::Param))
                .collect();
            for &(id, leaf) in &b.uses {
                let target = match leaf {
                    Leaf::Prim(name) => Prelude::of(name).map(Target::Prelude),
                    Leaf::Param => params.first().copied().map(Target::Decl),
                    Leaf::Struct(k) => decls.get(k).copied().map(Target::Decl),
                };
                if let Some(target) = target {
                    self.names.insert(id, target);
                }
            }
        }
        self.prelude = decls;
    }

    /// Declares a name of a prelude struct, which has no source position.
    fn declare_hidden(&mut self, name: &Ident, kind: Kind) -> DeclId {
        let id = DeclId(self.decls.len());
        self.decls.push(Decl {
            kind,
            receiver: None,
            name: name.name.clone(),
            pos: Pos { line: 0, col: 0 },
            generic: false,
        });
        self.names.insert(name.id, Target::Decl(id));
        id
    }

    /// Declares a name in the innermost scope. A use resolves to it only after this call.
    fn declare(&mut self, name: &Ident, kind: Kind) {
        let id = self.new_decl(name, kind, None);
        if !self.scopes.declare_local(&name.name, id) {
            self.duplicate_here(name);
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
                comptime,
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
                self.ports.clear();
                // A helper has the scope of its own family names, as a module body has. In a
                // `comptime fn`, `typeck` rejects a port (`S006`).
                if !comptime {
                    self.families(body);
                }
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
                self.ports.clear();
                self.families(body);
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

    /// The family walk of a module body or of the body of a `fn` without `comptime` (section
    /// 5.6): one pre-order walk of each statement at
    /// each block depth, before the statements resolve. It enters a block, both arms of a
    /// `comptime if`, and the body of a `comptime for`, and no nested item. An explicit stack
    /// holds the open lists, so a deep nest of blocks needs no recursion.
    fn families(&mut self, body: &[Stmt]) {
        let mut open = vec![body.iter()];
        while let Some(list) = open.last_mut() {
            let Some(stmt) = list.next() else {
                open.pop();
                continue;
            };
            match stmt {
                Stmt::Input { name, form, .. } => self.see_form(name, form, true),
                Stmt::Output { name, form, .. } => self.see_form(name, form, false),
                Stmt::CtIf { yes, no, .. } => {
                    if let Some(no) = no {
                        open.push(no.iter());
                    }
                    open.push(yes.iter());
                }
                Stmt::CtFor { body, .. } | Stmt::Block { body, .. } => open.push(body.iter()),
                _ => {}
            }
        }
    }

    /// The family walk sees a port of the form `form`. A port with an `as` key is no port name of
    /// the walk: its binder is a name of the body only.
    fn see_form(&mut self, name: &Ident, form: &PortForm, input: bool) {
        match form {
            PortForm::Scalar => self.see_port(name, false, input),
            PortForm::Indexed(_) => self.see_port(name, true, input),
            PortForm::Keyed(_) => {}
        }
    }

    /// The family walk sees the port name `name`, with a key if `indexed`, as an input if
    /// `input`. The walk runs in source order, so each `S002` is at the later name. The first
    /// indexed declaration of a name takes a declaration and binds the family in the scope of
    /// the body.
    fn see_port(&mut self, name: &Ident, indexed: bool, input: bool) {
        let seen = self.ports.get(name.name.as_str());
        let (family, scalar) = seen.map_or((None, None), |e| (e.family, e.scalar));
        let clash = match (indexed, family, scalar) {
            (false, Some((b, ..)), _) | (true, _, Some(b)) => Some((false, b)),
            (true, Some((b, _, first)), None) if first != input => Some((true, b)),
            _ => None,
        };
        if let Some((directions, b)) = clash {
            let x = &name.name;
            let (line, col) = (b.line, b.col);
            self.duplicates.push(if directions {
                Error {
                    code: Code::S002,
                    pos: name.pos,
                    message: format!(
                        "the port family `{x}` has an input entry and an output entry, here and \
                         at {line}:{col}; give the entries of one direction another name"
                    ),
                }
            } else {
                Error {
                    code: Code::S002,
                    pos: name.pos,
                    message: format!(
                        "`{x}` names a port family and a scalar port, here and at {line}:{col}; \
                         use one form for the name"
                    ),
                }
            });
        }
        if !indexed {
            if scalar.is_none() {
                self.note(&name.name, |e| e.scalar = Some(name.pos));
            }
            return;
        }
        if family.is_none() {
            let id = self.new_decl(name, Kind::Family { input }, None);
            if !self.scopes.declare_local(&name.name, id) {
                self.duplicate_here(name);
            }
            self.note(&name.name, |e| e.family = Some((name.pos, id, input)));
        }
    }

    /// Changes the entry of the port name. The first sight of the name makes the entry, so a
    /// name is copied once, not once for each use.
    fn note(&mut self, name: &str, change: impl FnOnce(&mut PortName)) {
        if let Some(entry) = self.ports.get_mut(name) {
            change(entry);
        } else {
            let mut entry = PortName::default();
            change(&mut entry);
            self.ports.insert(name.to_owned(), entry);
        }
    }

    /// The statement `input name[k]: T;` or `output name[k]: T;`, and the same without a key.
    /// An indexed declaration of a module body takes its family, and binds the name in its own
    /// block too (section 5.6). Another port declares a local.
    fn port(&mut self, name: &Ident, form: &PortForm, ty: &TypeExpr, kind: Kind) {
        if let PortForm::Indexed(key) = form {
            self.expr(key);
        }
        self.ty(ty);
        if let PortForm::Keyed(key) = form {
            self.expr(key);
        }
        let family = matches!(form, PortForm::Indexed(_))
            .then(|| self.ports.get(name.name.as_str()))
            .flatten()
            .and_then(|e| e.family);
        let Some((_, id, _)) = family else {
            self.declare(name, kind);
            return;
        };
        self.names.insert(name.id, Target::Decl(id));
        match self.scopes.here(&name.name) {
            Some(bound) if bound == id => {}
            Some(_) => self.duplicate_here(name),
            None => {
                let _ = self.scopes.declare_local(&name.name, id);
            }
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
            Stmt::Input { name, form, ty, .. } => self.port(name, form, ty, Kind::Input),
            Stmt::Output { name, form, ty, .. } => self.port(name, form, ty, Kind::Output),
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
                let inst = matches!(&**base, TypeExpr::Name { id, .. }
                    if self.names.get(id) == Some(&Target::Prelude(Prelude::Instance)));
                self.index_args(inst, args);
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
                let inst = matches!(&**base, Expr::Name { id, .. }
                    if self.names.get(id) == Some(&Target::Prelude(Prelude::Instance)));
                self.index_args(inst, args);
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
            Expr::Builtin { args, .. } => {
                for operand in args.operands() {
                    self.expr(operand);
                }
            }
            Expr::Path { pos, ty, variant } => self.variant_path(*pos, ty, variant),
            Expr::Match { scrut, arms, .. } => {
                self.expr(scrut);
                for arm in arms {
                    self.arm(arm);
                }
            }
        }
    }

    /// The arguments of an index. The first argument of the prelude `Instance` (`inst`) resolves
    /// by the ordinary scoping to a module item. Another first argument is `S003` at its start.
    /// That error replaces each `S003` in the argument, as Lean `indexArgs` does.
    fn index_args(&mut self, inst: bool, args: &[Expr]) {
        let Some((first, rest)) = args.split_first() else {
            return;
        };
        if inst {
            self.module_argument(first);
        } else {
            self.expr(first);
        }
        for arg in rest {
            self.expr(arg);
        }
    }

    fn module_argument(&mut self, arg: &Expr) {
        if let Expr::Name { id, name, .. } = arg
            && let Some(module) = self.scopes.lookup(name)
            && self.decls[module.0].kind == Kind::Module
        {
            self.names.insert(*id, Target::Decl(module));
            return;
        }
        let before = self.unresolved.len();
        // A name stays unresolved: it is the placeholder of Lean.
        if !matches!(arg, Expr::Name { .. }) {
            self.expr(arg);
        }
        self.unresolved.truncate(before);
        self.reject(arg.pos(), INSTANCE_TEXT.to_owned());
    }

    /// An arm. The path of a variant pattern resolves as a variant path in an expression. The
    /// binders are locals of a new scope that holds only the value of the arm, so a binder
    /// shadows an outer name, and a second binder with one name is `S002`.
    fn arm(&mut self, arm: &Arm) {
        match &arm.pat {
            Pattern::Variant {
                pos,
                ty,
                variant,
                binders,
            } => {
                self.variant_path(*pos, ty, variant);
                self.scopes.open();
                for binder in binders.iter().flatten() {
                    self.declare(binder, Kind::Local);
                }
                self.expr(&arm.value);
                self.scopes.close();
            }
            Pattern::Wild { .. } | Pattern::Int { .. } | Pattern::Bool { .. } => {
                self.expr(&arm.value);
            }
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
            let n = &name.name;
            self.reject(
                name.pos,
                format!(
                    "`{n}` is not a function; a receiver call `a.f()` needs a function `f`, so \
                     write `{n}(a)` to call a type or a function value"
                ),
            );
        }
    }

    fn lookup(&self, name: &str) -> Option<Target> {
        match self.scopes.lookup(name) {
            Some(id) => Some(Target::Decl(id)),
            None => self.prelude_target(name),
        }
    }

    /// The prelude declaration of a name: a prelude name, else a prelude struct.
    fn prelude_target(&self, name: &str) -> Option<Target> {
        Prelude::of(name).map(Target::Prelude).or_else(|| {
            let k = STRUCTS.iter().position(|s| s.name == name)?;
            self.prelude.get(k).copied().map(Target::Decl)
        })
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
        let message = if name == "Domain" {
            DOMAIN_TEXT.to_owned()
        } else {
            format!("`{name}` is not declared")
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
