// SPDX-License-Identifier: Apache-2.0
//! The name resolver of the Silicon front end: the item table, the scopes, and the resolved
//! AST. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.1
//! and 6.

mod prelude;
mod scope;
mod walk;

use parse::ast::{Expr, Item, NodeId, Pos};
use parse::{Parse, ParsedExpr, StackError};
use std::collections::BTreeMap;
use std::fmt;

pub use prelude::Prelude;

/// The codes of passes 2 and 3 of the front end (design section 6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    /// A name is not unique in its scope.
    S002,
    /// A name does not resolve, or it has the wrong kind for its position.
    S003,
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Code::S002 => "S002",
            Code::S003 => "S003",
        })
    }
}

/// An error of pass 2 or pass 3. Only the first one is normative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub code: Code,
    pub pos: Pos,
    pub message: String,
}

/// Why a parse has no resolved AST.
pub enum Failed {
    /// Pass 1 found an error. `Parse::errors` has it.
    Parse(Parse),
    /// Pass 2 found `S002`, or pass 3 found `S003`. The errors are in position order, and
    /// all have one code.
    Names(Vec<Error>),
    /// The machine cannot give the stack for the syntax depth.
    Stack(StackError),
}

/// The index of a declaration in its `Resolved`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclId(usize);

/// What a declaration declares.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Const,
    Fn,
    Module,
    Struct,
    /// A `type` item, or a `type` statement.
    Alias,
    Param,
    Local,
    /// The variable of a `comptime for`.
    Loop,
    Reg,
    Wire,
    Input,
    Output,
    Instance,
    Domain,
}

/// A declaration: its kind, its name, and the position of the name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub kind: Kind,
    pub name: String,
    pub pos: Pos,
}

/// What a name points to: a declaration, or a name of the prelude.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Prelude(Prelude),
    Decl(DeclId),
}

/// A parse with its names resolved. It is an owned value with no reference cycle: a name
/// points to its declaration by index.
///
/// The map from a node id to a target holds each name node of the AST: a declaration points
/// to itself, and a use points to its declaration or to the prelude. The AST is still
/// the AST of the parse, moved out of it: the lossless tree is gone. It keeps the syntax depth
/// of the parse. A pass that recurses over it runs through `parse::on_stack` with
/// [`Resolved::depth`]. Dropping it is safe on any stack.
pub struct Resolved {
    ast: Vec<Item>,
    depth: usize,
    decls: Vec<Decl>,
    items: BTreeMap<String, DeclId>,
    names: BTreeMap<NodeId, Target>,
    sites: BTreeMap<NodeId, usize>,
}

impl Resolved {
    /// The items of the file.
    #[must_use]
    pub fn ast(&self) -> &[Item] {
        &self.ast
    }

    /// The syntax depth of the parse, which sizes the stack of each pass over the AST.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// The declaration of an id from this value.
    #[must_use]
    pub fn decl(&self, id: DeclId) -> &Decl {
        &self.decls[id.0]
    }

    /// The item table: the item with a name.
    #[must_use]
    pub fn item(&self, name: &str) -> Option<DeclId> {
        self.items.get(name).copied()
    }

    /// What the name node with an id points to.
    #[must_use]
    pub fn target(&self, id: NodeId) -> Option<Target> {
        self.names.get(&id).copied()
    }

    /// The call site of the call node or the method node with an id: its rank in pre-order
    /// among the calls of its item body, from 0.
    #[must_use]
    pub fn site(&self, id: NodeId) -> Option<usize> {
        self.sites.get(&id).copied()
    }
}

/// Resolves the names of a parse. It reports the errors of the first pass with an error.
///
/// # Errors
/// Returns `Failed::Parse` if the parse has an error, `Failed::Names` for `S002` or `S003`,
/// and `Failed::Stack` if the machine cannot give the stack for the syntax depth.
pub fn resolve(parse: Parse) -> Result<Resolved, Failed> {
    let (ast, depth) = parse.into_ast().map_err(Failed::Parse)?;
    let table = parse::on_stack(depth, || walk::run(&ast)).map_err(Failed::Stack)?;
    let table = table.map_err(Failed::Names)?;
    Ok(Resolved {
        ast,
        depth,
        decls: table.decls,
        items: table.items,
        names: table.names,
        sites: table.sites,
    })
}

/// An expression in the file scope, such as the `EXPR` of `eval`, with its names resolved.
/// It is its own parse, so it has its own map from the id of each name node to its target.
/// A target indexes the declarations of the `Resolved` of its file. It keeps the syntax depth
/// of its parse. Dropping it is safe on any stack.
pub struct ResolvedExpr {
    expr: Expr,
    depth: usize,
    names: BTreeMap<NodeId, Target>,
    sites: BTreeMap<NodeId, usize>,
}

impl ResolvedExpr {
    /// The expression.
    #[must_use]
    pub fn expr(&self) -> &Expr {
        &self.expr
    }

    /// The syntax depth for a pass over the expression and the file of `resolved`.
    #[must_use]
    pub fn depth_with(&self, resolved: &Resolved) -> usize {
        self.depth.max(resolved.depth)
    }

    /// What the name node with an id of the expression points to.
    #[must_use]
    pub fn target(&self, id: NodeId) -> Option<Target> {
        self.names.get(&id).copied()
    }

    /// The call site of the call node or the method node with an id, from 0 in pre-order.
    #[must_use]
    pub fn site(&self, id: NodeId) -> Option<usize> {
        self.sites.get(&id).copied()
    }
}

/// Resolves the names of an expression in the file scope of `resolved`. A name in the
/// expression is an item or a prelude name, and never a module. The result is the resolved
/// expression, or the `S003` errors in position order.
///
/// # Errors
/// Returns an error if the machine cannot give the stack for the syntax depth of `expr`.
pub fn resolve_expr(
    resolved: &Resolved,
    expr: ParsedExpr,
) -> Result<Result<ResolvedExpr, Vec<Error>>, StackError> {
    let (expr, depth) = expr.into_parts();
    let names = parse::on_stack(depth, || walk::run_expr(resolved, &expr))?;
    Ok(names.map(|(names, sites)| ResolvedExpr {
        expr,
        depth,
        names,
        sites,
    }))
}

/// The result of a successful walk.
struct Table {
    decls: Vec<Decl>,
    items: BTreeMap<String, DeclId>,
    names: BTreeMap<NodeId, Target>,
    sites: BTreeMap<NodeId, usize>,
}

#[cfg(test)]
mod tests;
