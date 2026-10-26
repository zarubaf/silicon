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

pub use prelude::{Prelude, RESPONSE, TYPE_NAMES};

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
    Enum,
    /// A `type` item, or a `type` statement.
    Alias,
    Param,
    Local,
    /// The variable of a `comptime for`.
    Loop,
    Reg,
    Wire,
    Mem,
    Input,
    Output,
    /// The name of a port family: it holds every `input name[k]` or `output name[k]` of one
    /// module body. `input` tells if its first entry is an input.
    Family {
        input: bool,
    },
    Instance,
    Domain,
}

/// A declaration: its kind, its name, and the position of the name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub kind: Kind,
    /// For a `fn` item, the parameter that a receiver binds to; see [`Resolved::receiver`].
    pub receiver: Option<usize>,
    pub name: String,
    pub pos: Pos,
    /// For a `fn` item, whether it is generic: it has a `comptime` parameter, or a parameter
    /// type or its result type names one of its parameters. A generic function is no value.
    pub generic: bool,
}

/// The enum item and the variant that a variant path `E::V` names. The item is the index of the
/// enum in [`Resolved::ast`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VariantRef {
    pub item: usize,
    pub index: usize,
}

/// For each enum item, the index of the first variant with each name.
type VariantNames = BTreeMap<DeclId, BTreeMap<String, usize>>;

/// The call site of a call node or a method node, with the parameter that the receiver binds to.
#[derive(Clone, Copy)]
pub(crate) struct Call {
    site: usize,
    receiver: Option<usize>,
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
    calls: BTreeMap<NodeId, Call>,
    variants: BTreeMap<NodeId, VariantRef>,
    variant_names: VariantNames,
    /// The number of user items: the prelude struct items follow them in `ast`.
    users: usize,
    /// The declaration of each prelude struct, in the order of `prelude::STRUCTS`.
    prelude: Vec<DeclId>,
}

impl Resolved {
    /// The items of the file.
    #[must_use]
    pub fn ast(&self) -> &[Item] {
        &self.ast
    }

    /// Whether the item `i` of [`Resolved::ast`] is a prelude struct. The prelude structs follow
    /// the user items, so they change no index of a user item. They have no source position, so
    /// a pass that orders by position skips them.
    #[must_use]
    pub fn is_prelude_item(&self, i: usize) -> bool {
        i >= self.users
    }

    /// The index in [`Resolved::ast`] of the prelude struct with a name, such as `ReadResponse`.
    /// It reads a table of constant size, so it takes constant work.
    #[must_use]
    pub fn prelude_struct(&self, name: &str) -> Option<usize> {
        let k = prelude::STRUCTS.iter().position(|s| s.name == name)?;
        Some(self.users + k)
    }

    /// The index in [`Resolved::ast`] of the prelude struct `FieldInfo`. It always exists.
    #[must_use]
    pub fn field_info_struct(&self) -> usize {
        self.users + prelude::FIELD_INFO
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
        self.calls.get(&id).map(|c| c.site)
    }

    /// The variant that the path node with an id names. The id is the id of the first name of
    /// the path.
    #[must_use]
    pub fn variant(&self, id: NodeId) -> Option<VariantRef> {
        self.variants.get(&id).copied()
    }

    /// The parameter that the receiver of the method node with an id binds to: the first
    /// parameter of the function without a written `comptime` mark. `None` if there is none.
    #[must_use]
    pub fn receiver(&self, id: NodeId) -> Option<usize> {
        self.calls.get(&id).and_then(|c| c.receiver)
    }
}

/// Resolves the names of a parse. It reports the errors of the first pass with an error.
///
/// # Errors
/// Returns `Failed::Parse` if the parse has an error, `Failed::Names` for `S002` or `S003`,
/// and `Failed::Stack` if the machine cannot give the stack for the syntax depth.
pub fn resolve(parse: Parse) -> Result<Resolved, Failed> {
    let (mut ast, depth) = parse.into_ast().map_err(Failed::Parse)?;
    let built = prelude::build();
    let table = parse::on_stack(depth, || walk::run(&ast, &built)).map_err(Failed::Stack)?;
    let table = table.map_err(Failed::Names)?;
    let users = ast.len();
    ast.extend(built.into_iter().map(|b| b.item));
    Ok(Resolved {
        ast,
        depth,
        decls: table.decls,
        items: table.items,
        names: table.names,
        calls: table.calls,
        variants: table.variants,
        variant_names: table.variant_names,
        users,
        prelude: table.prelude,
    })
}

/// An expression in the file scope, such as the `EXPR` of `eval`, with its names resolved.
/// It is its own parse, so it has its own map from the id of each name node to its target.
/// A target indexes the declarations of the `Resolved` of its file. It keeps the syntax depth
/// of its parse. Dropping it is safe on any stack.
pub struct ResolvedExpr {
    expr: Expr,
    depth: usize,
    /// The declarations of the binders of the expression, after the declarations of its file.
    extra: Vec<Decl>,
    names: BTreeMap<NodeId, Target>,
    calls: BTreeMap<NodeId, Call>,
    variants: BTreeMap<NodeId, VariantRef>,
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

    /// The declaration of an id of this expression: a declaration of its file, or a binder of a
    /// pattern in the expression.
    #[must_use]
    pub fn decl<'a>(&'a self, file: &'a Resolved, id: DeclId) -> &'a Decl {
        match id.0.checked_sub(file.decls.len()) {
            Some(k) => self.extra.get(k).unwrap_or_else(|| file.decl(id)),
            None => file.decl(id),
        }
    }

    /// The call site of the call node or the method node with an id, from 0 in pre-order.
    #[must_use]
    pub fn site(&self, id: NodeId) -> Option<usize> {
        self.calls.get(&id).map(|c| c.site)
    }

    /// The parameter that the receiver of the method node with an id binds to, or `None`.
    #[must_use]
    pub fn receiver(&self, id: NodeId) -> Option<usize> {
        self.calls.get(&id).and_then(|c| c.receiver)
    }

    /// The variant that the path node with an id names.
    #[must_use]
    pub fn variant(&self, id: NodeId) -> Option<VariantRef> {
        self.variants.get(&id).copied()
    }
}

/// Resolves the names of an expression in the file scope of `resolved`. A name in the
/// expression is an item or a prelude name, and never a module. The result is the resolved
/// expression, or the errors in position order: the `S002` errors if there are any, else the
/// `S003` errors.
///
/// # Errors
/// Returns an error if the machine cannot give the stack for the syntax depth of `expr`.
pub fn resolve_expr(
    resolved: &Resolved,
    expr: ParsedExpr,
) -> Result<Result<ResolvedExpr, Vec<Error>>, StackError> {
    let (expr, depth) = expr.into_parts();
    let names = parse::on_stack(depth, || walk::run_expr(resolved, &expr))?;
    Ok(names.map(|(names, calls, variants, extra)| ResolvedExpr {
        expr,
        depth,
        extra,
        names,
        calls,
        variants,
    }))
}

/// The result of a successful walk.
struct Table {
    decls: Vec<Decl>,
    items: BTreeMap<String, DeclId>,
    names: BTreeMap<NodeId, Target>,
    calls: BTreeMap<NodeId, Call>,
    variants: BTreeMap<NodeId, VariantRef>,
    variant_names: VariantNames,
    prelude: Vec<DeclId>,
}

#[cfg(test)]
mod tests;
