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

pub use dump::dump;
use error::LineIndex;
pub use error::{Code, Error};
use rowan::{GreenNode, Language};
use syntax::{SiliconLanguage, SyntaxKind, SyntaxNode};

/// The result of parsing a source text.
#[derive(Clone, Debug)]
pub struct Parse {
    green: GreenNode,
    /// The syntax depth of the parse, which sizes the stack that frees the tree.
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
}

impl Drop for Parse {
    /// Freeing a deep tree recurses, so it runs on a stack for the depth, as the parse does.
    fn drop(&mut self) {
        let empty = GreenNode::new(SiliconLanguage::kind_to_raw(SyntaxKind::Root), []);
        let green = std::mem::replace(&mut self.green, empty);
        // If the thread does not start, the closure drops the tree here.
        let spawned = std::thread::Builder::new()
            .stack_size(stack_for(self.depth))
            .spawn(move || drop(green));
        if let Ok(handle) = spawned {
            handle.join().ok();
        }
    }
}

/// The default syntax depth: the most height of an expression or a type, and the most nesting
/// of blocks. It is far above the depth of written or generated code.
pub const DEFAULT_SYNTAX_DEPTH: usize = 4096;

/// Parses a source text with the default syntax depth. It never fails: errors are data in
/// the result.
#[must_use]
pub fn parse(input: &str) -> Parse {
    parse_with_depth(input, DEFAULT_SYNTAX_DEPTH)
}

/// The stack for each level of the syntax depth. The parser stops when its nesting is above
/// the depth, so its recursion and the recursion over the tree go one set of frames deep for
/// each level.
const STACK_PER_LEVEL: usize = 64 * 1024;

/// Parses a source text with a syntax depth. A deeper expression, type, or block is `S001`.
///
/// The parser is recursive, so it runs on its own thread with a stack for the depth. The
/// stack is virtual memory, and the pages of it that the parse does not touch cost nothing.
#[must_use]
pub fn parse_with_depth(input: &str, depth: usize) -> Parse {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(stack_for(depth))
            .spawn_scoped(scope, || parse_here(input, depth))
            .map_or_else(
                // No thread for such a stack: the depth is absurd, so use the stack at hand.
                |_| parse_here(input, depth),
                |handle| {
                    handle
                        .join()
                        .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
                },
            )
    })
}

/// The size of a stack for the syntax depth. The parse, the free of its tree, and a recursive
/// pass over the AST, such as `dump`, fit in it. It is virtual memory: the pages that a pass
/// does not touch cost nothing.
#[must_use]
pub fn stack_for(depth: usize) -> usize {
    depth
        .saturating_mul(STACK_PER_LEVEL)
        .saturating_add(1 << 20)
}

fn parse_here(input: &str, depth: usize) -> Parse {
    let lexed = syntax::lex(input);
    let (green, raw) = parser::Parser::new(input, &lexed.tokens, depth).finish();
    let index = LineIndex::new(input);
    let mut raw_all: Vec<(usize, Code, String)> = lexed
        .errors
        .iter()
        .map(|e| (e.offset, Code::S001, e.message.to_owned()))
        .chain(raw.into_iter().map(|e| (e.offset, e.code, e.message)))
        .collect();
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
