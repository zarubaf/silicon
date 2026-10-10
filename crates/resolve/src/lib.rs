//! The name resolver of the Silicon front end: the item table, the scopes, and the resolved
//! AST. See [the front end design](../../doc/design/2026-10-09-frontend.md), sections 4.1
//! and 6.

mod prelude;
mod scope;
mod walk;

use parse::ast::{Item, Pos};
use parse::{Parse, StackError};
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
/// The map from a position to a target holds each name token of the AST: a declaration
/// points to itself, and a use points to its declaration or to the prelude. The AST is still
/// the AST of the parse, so it keeps the syntax depth of the parse. A pass that recurses over
/// it runs through `parse::on_stack` with [`Resolved::depth`]. Dropping it is safe on any
/// stack.
pub struct Resolved {
    parse: Parse,
    decls: Vec<Decl>,
    items: BTreeMap<String, DeclId>,
    names: BTreeMap<Pos, Target>,
}

impl Resolved {
    /// The items of the file.
    #[must_use]
    pub fn ast(&self) -> &[Item] {
        self.parse.ast().unwrap_or_default()
    }

    /// The syntax depth of the parse, which sizes the stack of each pass over the AST.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.parse.depth()
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

    /// What the name token at a position points to.
    #[must_use]
    pub fn target(&self, pos: Pos) -> Option<Target> {
        self.names.get(&pos).copied()
    }
}

/// Resolves the names of a parse. It reports the errors of the first pass with an error.
///
/// # Errors
/// Returns `Failed::Parse` if the parse has an error, `Failed::Names` for `S002` or `S003`,
/// and `Failed::Stack` if the machine cannot give the stack for the syntax depth.
pub fn resolve(parse: Parse) -> Result<Resolved, Failed> {
    let Some(ast) = parse.ast() else {
        return Err(Failed::Parse(parse));
    };
    let table = parse::on_stack(parse.depth(), || walk::run(ast)).map_err(Failed::Stack)?;
    let table = table.map_err(Failed::Names)?;
    Ok(Resolved {
        parse,
        decls: table.decls,
        items: table.items,
        names: table.names,
    })
}

/// The result of a successful walk.
struct Table {
    decls: Vec<Decl>,
    items: BTreeMap<String, DeclId>,
    names: BTreeMap<Pos, Target>,
}

#[cfg(test)]
mod tests;
