//! The parser of the Silicon front end: a lossless `rowan` tree with error recovery, and
//! the typed AST of the current slice. See [the front end design](../../doc/design/2026-10-09-frontend.md).

pub mod ast;
mod dump;
mod error;
mod expr;
mod item;
mod lower;
mod parser;
mod stmt;

use error::LineIndex;
pub use error::{Code, Error, StackError};
use rowan::{GreenNode, Language};
use syntax::{SiliconLanguage, SyntaxKind, SyntaxNode};

/// The result of parsing a source text.
#[derive(Clone, Debug)]
pub struct Parse {
    green: GreenNode,
    /// The syntax depth of the parse, which sizes the stack of each pass over the result.
    depth: usize,
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

    /// The dump of the AST, or `None` if the text has an error. The dump recurses, so it runs
    /// on a stack for the syntax depth of the parse.
    ///
    /// # Errors
    /// Returns an error if the machine cannot give the stack.
    pub fn dump(&self) -> Result<Option<String>, StackError> {
        on_stack(self.depth, || self.ast.as_deref().map(dump::dump))
    }
}

impl Drop for Parse {
    /// Freeing the tree and the AST recurses, so it runs on a stack for the depth, as the
    /// parse does.
    fn drop(&mut self) {
        let empty = GreenNode::new(SiliconLanguage::kind_to_raw(SyntaxKind::Root), []);
        let green = std::mem::replace(&mut self.green, empty);
        let ast = self.ast.take();
        // If the thread does not start, the closure drops both here.
        let spawned = std::thread::Builder::new()
            .stack_size(stack_for(self.depth))
            .spawn(move || drop((green, ast)));
        if let Ok(handle) = spawned {
            handle.join().ok();
        }
    }
}

/// The default syntax depth N: the most depth of brackets, and the most height of an
/// outermost expression or type. It is far above the depth of written or generated code.
pub const DEFAULT_SYNTAX_DEPTH: usize = 4096;

/// Parses a source text with the default syntax depth. Errors in the text are data in the
/// result.
///
/// # Errors
/// Returns an error if the machine cannot give the stack for the depth.
pub fn parse(input: &str) -> Result<Parse, StackError> {
    parse_with_depth(input, DEFAULT_SYNTAX_DEPTH)
}

/// The stack for each level of the syntax depth. The lexer bounds the recursion of the parser
/// by the depth of brackets, and the check after the parse bounds the recursion over the
/// result by about two levels for each level of the depth.
const STACK_PER_LEVEL: usize = 64 * 1024;

/// Parses a source text with a syntax depth. A bracket above the depth, and an outermost
/// expression or type that is higher than the depth, are `S001`.
///
/// The parser is recursive, so it runs on its own thread with a stack for the depth. The
/// stack is virtual memory, and the pages of it that the parse does not touch cost nothing.
///
/// # Errors
/// Returns an error, before it parses, if the machine cannot give the stack for the depth.
pub fn parse_with_depth(input: &str, depth: usize) -> Result<Parse, StackError> {
    on_stack(depth, || parse_here(input, depth))
}

/// The size of a stack for the syntax depth. It is virtual memory: the pages that a pass
/// does not touch cost nothing.
fn stack_for(depth: usize) -> usize {
    depth
        .saturating_mul(STACK_PER_LEVEL)
        .saturating_add(1 << 20)
}

/// Runs a function on a thread with a stack for the syntax depth.
fn on_stack<T: Send>(depth: usize, f: impl FnOnce() -> T + Send) -> Result<T, StackError> {
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .stack_size(stack_for(depth))
            .spawn_scoped(scope, f)
            .map_err(|_| StackError {
                depth,
                bytes: stack_for(depth),
            })?;
        Ok(handle
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic)))
    })
}

fn parse_here(input: &str, depth: usize) -> Parse {
    let lexed = syntax::lex(input, depth);
    let (green, raw, high) = parser::Parser::new(input, &lexed.tokens, depth).finish();
    let index = LineIndex::new(input);
    let mut raw_all: Vec<(usize, Code, String)> = lexed
        .errors
        .iter()
        .map(|e| (e.offset, Code::S001, e.message.to_owned()))
        .chain(raw.into_iter().map(|e| (e.offset, e.code, e.message)))
        .collect();
    // A height error ranks below every other error, so it exists only without them.
    if let (true, Some(offset)) = (raw_all.is_empty(), high) {
        let message = format!("expression is higher than {depth} levels");
        raw_all.push((offset, Code::S001, message));
    }
    raw_all.sort_by_key(|(offset, ..)| *offset);
    let errors: Vec<Error> = raw_all
        .into_iter()
        .map(|(offset, code, message)| Error {
            code,
            pos: index.pos(offset),
            message,
        })
        .collect();
    let ast = if errors.is_empty() {
        let root = SyntaxNode::new_root(green.clone());
        let lowered = lower::Lower { index }.source(&root);
        debug_assert!(lowered.is_some(), "the tree of a valid text lowers");
        lowered
    } else {
        None
    };
    Parse {
        green,
        depth,
        errors,
        ast,
    }
}

#[cfg(test)]
mod tests;
