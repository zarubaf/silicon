//! The parser of the Silicon front end: a lossless `rowan` tree with error recovery, and
//! the typed AST of the current slice. See [the front end design](../../doc/design/2026-10-09-frontend.md).

pub mod ast;
mod error;
mod expr;
mod item;
mod lower;
mod parser;
mod stmt;

use error::LineIndex;
pub use error::{Code, Error};
use rowan::GreenNode;
use syntax::SyntaxNode;

/// The result of parsing a source text.
#[derive(Clone, Debug)]
pub struct Parse {
    green: GreenNode,
    /// The errors in position order. The first one is the normative error.
    pub errors: Vec<Error>,
    /// The AST, if the text has no error.
    pub ast: Option<Vec<ast::Item>>,
}

impl Parse {
    /// The root of the lossless syntax tree. Its text equals the input.
    #[must_use]
    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }
}

/// Parses a source text. It never fails: errors are data in the result.
#[must_use]
pub fn parse(input: &str) -> Parse {
    let lexed = syntax::lex(input);
    let (green, raw) = parser::Parser::new(input, &lexed.tokens).finish();
    let index = LineIndex::new(input);
    let mut errors: Vec<(usize, Error)> = lexed
        .errors
        .iter()
        .map(|e| {
            (
                e.offset,
                Error {
                    code: Code::S001,
                    pos: index.pos(e.offset),
                    message: e.message.to_owned(),
                },
            )
        })
        .chain(raw.into_iter().map(|e| {
            (
                e.offset,
                Error {
                    code: e.code,
                    pos: index.pos(e.offset),
                    message: e.message,
                },
            )
        }))
        .collect();
    errors.sort_by_key(|(offset, _)| *offset);
    let errors: Vec<Error> = errors.into_iter().map(|(_, e)| e).collect();
    let ast = if errors.is_empty() {
        let root = SyntaxNode::new_root(green.clone());
        let lowered = lower::Lower { index }.source(&root);
        debug_assert!(lowered.is_some(), "the tree of a valid text lowers");
        lowered
    } else {
        None
    };
    Parse { green, errors, ast }
}

#[cfg(test)]
mod tests;
