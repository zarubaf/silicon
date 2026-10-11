// SPDX-License-Identifier: Apache-2.0
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
mod tree;

pub use dump::quote;
use error::LineIndex;
pub use error::{Code, DepthError, Error, StackError};
use syntax::SyntaxNode;

/// The result of parsing a source text.
#[cfg_attr(test, derive(Debug))]
pub struct Parse {
    /// The lossless tree. Only the tests read it, because a node of `rowan` frees the tree by
    /// recursion.
    #[cfg_attr(not(test), allow(dead_code))]
    green: tree::Green,
    /// The syntax depth of the parse, which sizes the stack of each pass over the result.
    depth: usize,
    /// The errors in position order. The first one is the normative error.
    errors: Vec<Error>,
    /// The AST, if the text has no error.
    ast: Option<Vec<ast::Item>>,
}

impl Parse {
    /// The errors in position order. The first one is the normative error.
    #[must_use]
    pub fn errors(&self) -> &[Error] {
        &self.errors
    }

    /// The AST, if the text has no error.
    #[must_use]
    pub fn ast(&self) -> Option<&[ast::Item]> {
        self.ast.as_deref()
    }

    /// Splits the AST and the syntax depth off the parse and drops the lossless tree. Gives
    /// the parse back if the text has an error.
    ///
    /// # Errors
    /// Returns the parse itself if it has no AST.
    pub fn into_ast(self) -> Result<(Vec<ast::Item>, usize), Self> {
        match self.ast {
            Some(ast) => Ok((ast, self.depth)),
            None => Err(self),
        }
    }

    /// The root of the lossless syntax tree. Its text equals the input. A node of `rowan`
    /// frees the tree by recursion, so only the tests of this crate see it.
    #[cfg(test)]
    fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.node().clone())
    }

    /// The syntax depth of the parse. A pass that recurses over the AST runs through
    /// [`on_stack`] with this depth.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.depth
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

/// The default syntax depth N: the most depth of brackets, and the most height of an
/// outermost expression or type. It is far above the depth of written or generated code.
pub const DEFAULT_SYNTAX_DEPTH: usize = 4096;

/// The largest syntax depth. The stack for the depth is virtual memory, and this cap keeps it
/// to a size that a machine gives.
pub const MAX_SYNTAX_DEPTH: usize = 65536;

/// Parses a source text with the default syntax depth. Errors in the text are data in the
/// result.
///
/// # Errors
/// Returns an error if the machine cannot give the stack for the depth.
pub fn parse(input: &str) -> Result<Parse, DepthError> {
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
/// Returns an error, before it parses, if the depth is not from 1 to `MAX_SYNTAX_DEPTH`, or
/// if the machine cannot give the stack for the depth.
pub fn parse_with_depth(input: &str, depth: usize) -> Result<Parse, DepthError> {
    if !(1..=MAX_SYNTAX_DEPTH).contains(&depth) {
        return Err(DepthError::Range(depth));
    }
    on_stack(depth, || parse_here(input, depth)).map_err(DepthError::Stack)
}

/// The size of a stack for the syntax depth. It is virtual memory: the pages that a pass
/// does not touch cost nothing.
fn stack_for(depth: usize) -> usize {
    depth
        .saturating_mul(STACK_PER_LEVEL)
        .saturating_add(1 << 20)
}

/// Runs a function on a thread with a stack for the syntax depth. This is the one place that
/// sizes the stack: each later pass that recurses over the AST of a parse calls it with
/// [`Parse::depth`].
///
/// # Errors
/// Returns an error if the machine cannot give the stack.
pub fn on_stack<T: Send>(depth: usize, f: impl FnOnce() -> T + Send) -> Result<T, StackError> {
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

/// The levels of stack of a group of nesting levels, in levels of the syntax depth.
const GROUP_LEVELS: u64 = 256;

/// The stack of a pass whose recursion starts again at each nesting level, such as the
/// evaluator at each active call. A group of nesting levels runs on each thread, so the stack
/// of each thread stays small for any nesting depth.
#[derive(Clone, Copy, Debug)]
pub struct NestedStack {
    /// The nesting levels that each thread runs.
    levels_per_thread: u64,
    /// The stack of each thread, in levels of the syntax depth.
    thread_depth: usize,
}

impl NestedStack {
    /// The stack for a pass whose highest node is at `height`, and whose highest node that
    /// starts a nesting level is at `per_level`. A thread has room for the first height once
    /// and for the second height at each level of its group.
    #[must_use]
    pub fn new(height: usize, per_level: usize) -> NestedStack {
        let per_level = u64::try_from(per_level)
            .unwrap_or(u64::MAX)
            .saturating_add(2);
        let base = u64::try_from(height).unwrap_or(u64::MAX).saturating_add(2);
        let levels_per_thread = (GROUP_LEVELS / per_level).max(1);
        let levels = levels_per_thread
            .saturating_mul(per_level)
            .saturating_add(base);
        NestedStack {
            levels_per_thread,
            thread_depth: usize::try_from(levels).unwrap_or(usize::MAX),
        }
    }

    /// Whether the nesting level `level` starts a new thread.
    #[must_use]
    pub fn starts_thread(&self, level: u64) -> bool {
        level.is_multiple_of(self.levels_per_thread)
    }

    /// Runs a function on a new thread with the stack of a group.
    ///
    /// # Errors
    /// Returns an error if the machine cannot give the stack.
    pub fn run<T: Send>(&self, f: impl FnOnce() -> T + Send) -> Result<T, StackError> {
        on_stack(self.thread_depth, f)
    }
}

fn parse_here(input: &str, depth: usize) -> Parse {
    let lexed = syntax::lex(input, depth);
    let (green, raw, high) = parser::Parser::new(input, &lexed.tokens, depth).finish();
    let index = LineIndex::new(input);
    let errors = all_errors(&index, depth, &lexed, raw, high);
    let ast = if errors.is_empty() {
        let root = SyntaxNode::new_root(green.clone());
        let lowered = lower::Lower { index }.source(&root);
        debug_assert!(lowered.is_some(), "the tree of a valid text lowers");
        lowered
    } else {
        None
    };
    Parse {
        green: tree::Green::new(green),
        depth,
        errors,
        ast,
    }
}

/// An expression of the command line with the syntax depth of its parse. A pass that
/// recurses over it runs through [`on_stack`] with this depth. Dropping it is safe on any
/// stack.
pub struct ParsedExpr {
    expr: ast::Expr,
    depth: usize,
}

impl ParsedExpr {
    /// The expression.
    #[must_use]
    pub fn expr(&self) -> &ast::Expr {
        &self.expr
    }

    /// The syntax depth of the parse, which sizes the stack of each pass over the expression.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Splits the expression and the syntax depth.
    #[must_use]
    pub fn into_parts(self) -> (ast::Expr, usize) {
        (self.expr, self.depth)
    }
}

/// Parses an expression of the command line, such as the `EXPR` of `eval`, with a syntax
/// depth. The positions are in the text of the expression. A token after the expression is
/// `S001`. The result is the expression with the depth, or the errors in position order.
///
/// # Errors
/// Returns an error, before it parses, if the depth is not from 1 to `MAX_SYNTAX_DEPTH`, or
/// if the machine cannot give the stack for the depth.
pub fn parse_expr(input: &str, depth: usize) -> Result<Result<ParsedExpr, Vec<Error>>, DepthError> {
    if !(1..=MAX_SYNTAX_DEPTH).contains(&depth) {
        return Err(DepthError::Range(depth));
    }
    let parsed = on_stack(depth, || parse_expr_here(input, depth)).map_err(DepthError::Stack)?;
    Ok(parsed.map(|expr| ParsedExpr { expr, depth }))
}

fn parse_expr_here(input: &str, depth: usize) -> Result<ast::Expr, Vec<Error>> {
    let lexed = syntax::lex(input, depth);
    let (green, raw, high) = parser::Parser::new(input, &lexed.tokens, depth).finish_expr();
    let index = LineIndex::new(input);
    let errors = all_errors(&index, depth, &lexed, raw, high);
    // The tree drops here, on the stack for the depth.
    let green = tree::Green::new(green);
    if !errors.is_empty() {
        return Err(errors);
    }
    let root = SyntaxNode::new_root(green.node().clone());
    let lowered = lower::Lower { index }.source_expr(&root);
    debug_assert!(lowered.is_some(), "the tree of a valid expression lowers");
    lowered.ok_or_else(|| {
        vec![Error {
            code: Code::S001,
            pos: ast::Pos { line: 1, col: 1 },
            message: "the expression does not lower".to_owned(),
        }]
    })
}

/// The errors of the lexer and the parser in position order. A height error ranks below
/// every other error, so it exists only without them.
fn all_errors(
    index: &LineIndex<'_>,
    depth: usize,
    lexed: &syntax::Lexed,
    raw: Vec<parser::RawError>,
    high: Option<usize>,
) -> Vec<Error> {
    let mut raw_all: Vec<(usize, Code, String)> = lexed
        .errors
        .iter()
        .map(|e| (e.offset, Code::S001, e.message.to_owned()))
        .chain(raw.into_iter().map(|e| (e.offset, e.code, e.message)))
        .collect();
    if let (true, Some(offset)) = (raw_all.is_empty(), high) {
        let message = format!("expression is higher than {depth} levels");
        raw_all.push((offset, Code::S001, message));
    }
    raw_all.sort_by_key(|(offset, ..)| *offset);
    raw_all
        .into_iter()
        .map(|(offset, code, message)| Error {
            code,
            pos: index.pos(offset),
            message,
        })
        .collect()
}

#[cfg(test)]
mod tests;
