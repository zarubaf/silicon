//! The parser state: the cursor over the tokens, the tree builder, and the errors.
//! The grammar is in `item`, `stmt`, and `expr`.

use crate::error::Code;
use rowan::{Checkpoint, GreenNode, GreenNodeBuilder, Language};
use syntax::{SiliconLanguage, SyntaxKind, Token};

/// The most levels of nesting of an expression, and of a block.
pub(crate) const MAX_DEPTH: usize = 64;

/// The result of a parse function: `None` means it reported an error and the caller recovers.
pub(crate) type Res = Option<()>;

/// An error before it gets a line and a column.
pub(crate) struct RawError {
    pub code: Code,
    pub offset: usize,
    pub message: String,
}

pub(crate) struct Parser<'a> {
    input: &'a str,
    tokens: &'a [Token],
    /// The index of the next token that the builder has not got.
    at: usize,
    builder: GreenNodeBuilder<'static>,
    pub errors: Vec<RawError>,
    /// The nesting of expressions and blocks now open.
    depth: usize,
    /// The height of the last expression or type that a parse function completed.
    pub height: usize,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(input: &'a str, tokens: &'a [Token]) -> Self {
        Parser {
            input,
            tokens,
            at: 0,
            builder: GreenNodeBuilder::new(),
            errors: Vec::new(),
            depth: 0,
            height: 0,
        }
    }

    /// Parses the whole input into a tree with the node `Root`.
    pub(crate) fn finish(mut self) -> (GreenNode, Vec<RawError>) {
        // The first trivia belong inside the root, so the root starts the tree.
        self.builder
            .start_node(SiliconLanguage::kind_to_raw(SyntaxKind::Root));
        self.source();
        self.flush_trivia();
        self.builder.finish_node();
        (self.builder.finish(), self.errors)
    }

    // The cursor.

    fn significant(&self, n: usize) -> Option<&'a Token> {
        self.tokens[self.at..]
            .iter()
            .filter(|t| !t.kind.is_trivia())
            .nth(n)
    }

    /// The kind of the current token, or `None` at the end of the input.
    pub(crate) fn cur(&self) -> Option<SyntaxKind> {
        self.significant(0).map(|t| t.kind)
    }

    /// The kind of the token after the current one.
    pub(crate) fn next(&self) -> Option<SyntaxKind> {
        self.significant(1).map(|t| t.kind)
    }

    pub(crate) fn is(&self, kind: SyntaxKind) -> bool {
        self.cur() == Some(kind)
    }

    /// The text of the token after the current one.
    pub(crate) fn next_text(&self) -> &'a str {
        self.significant(1)
            .map_or("", |t| &self.input[t.range.clone()])
    }

    /// The byte offset of the current token, or the end of the input.
    pub(crate) fn offset(&self) -> usize {
        self.offset_of(0)
    }

    /// The byte offset of the token `n` places after the current one.
    pub(crate) fn offset_of(&self, n: usize) -> usize {
        self.significant(n)
            .map_or(self.input.len(), |t| t.range.start)
    }

    /// The kinds of the tokens that follow the current one, for a short look ahead.
    pub(crate) fn kinds_from(&self, n: usize) -> impl Iterator<Item = SyntaxKind> + '_ {
        self.tokens[self.at..]
            .iter()
            .filter(|t| !t.kind.is_trivia())
            .skip(n)
            .map(|t| t.kind)
    }

    // The tree.

    fn flush_trivia(&mut self) {
        while let Some(token) = self.tokens.get(self.at).filter(|t| t.kind.is_trivia()) {
            self.builder.token(
                SiliconLanguage::kind_to_raw(token.kind),
                &self.input[token.range.clone()],
            );
            self.at += 1;
        }
    }

    /// Moves the current token into the tree.
    pub(crate) fn bump(&mut self) {
        self.flush_trivia();
        if let Some(token) = self.tokens.get(self.at) {
            self.builder.token(
                SiliconLanguage::kind_to_raw(token.kind),
                &self.input[token.range.clone()],
            );
            self.at += 1;
        }
    }

    /// Moves the current token into the tree if it has the kind.
    pub(crate) fn eat(&mut self, kind: SyntaxKind) -> bool {
        let found = self.is(kind);
        if found {
            self.bump();
        }
        found
    }

    /// Opens a node. Trivia before the node stay outside of it.
    pub(crate) fn start(&mut self, kind: SyntaxKind) {
        self.flush_trivia();
        self.builder.start_node(SiliconLanguage::kind_to_raw(kind));
    }

    pub(crate) fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    pub(crate) fn checkpoint(&mut self) -> Checkpoint {
        self.flush_trivia();
        self.builder.checkpoint()
    }

    /// Runs the parts of a node and closes the node also when they fail.
    pub(crate) fn node(&mut self, kind: SyntaxKind, parts: impl FnOnce(&mut Self) -> Res) -> Res {
        self.start(kind);
        let res = parts(self);
        self.finish_node();
        res
    }

    /// Like `node`, but the node starts at the checkpoint and holds what came after it.
    pub(crate) fn node_at(
        &mut self,
        checkpoint: Checkpoint,
        kind: SyntaxKind,
        parts: impl FnOnce(&mut Self) -> Res,
    ) -> Res {
        self.builder
            .start_node_at(checkpoint, SiliconLanguage::kind_to_raw(kind));
        let res = parts(self);
        self.finish_node();
        res
    }

    /// Runs `parts` one level deeper, or reports a nesting that is too deep.
    pub(crate) fn nested(&mut self, parts: impl FnOnce(&mut Self) -> Res) -> Res {
        if self.depth >= MAX_DEPTH {
            self.syntax_error("the nesting is deeper than 64 levels");
            return None;
        }
        self.depth += 1;
        let res = parts(self);
        self.depth -= 1;
        res
    }

    // The errors.

    fn report(&mut self, code: Code, offset: usize, message: String) {
        // One error for each place is enough, and an error token has its lexical error.
        let on_error_token = code == Code::S001
            && self
                .significant(0)
                .is_some_and(|t| t.range.start == offset && t.kind == SyntaxKind::Error);
        if on_error_token || self.errors.iter().any(|e| e.offset == offset) {
            return;
        }
        self.errors.push(RawError {
            code,
            offset,
            message,
        });
    }

    /// A syntax error `S001` at the current token.
    pub(crate) fn syntax_error(&mut self, message: &str) {
        self.report(Code::S001, self.offset(), message.to_owned());
    }

    /// A syntax error `S001` at an offset.
    pub(crate) fn syntax_error_at(&mut self, offset: usize, message: &str) {
        self.report(Code::S001, offset, message.to_owned());
    }

    /// The syntax of a later slice, `S004`, at an offset.
    pub(crate) fn later_slice(&mut self, offset: usize, what: &str) {
        self.report(
            Code::S004,
            offset,
            format!("{what} belongs to a later slice"),
        );
    }

    /// Moves the current token into the tree, or reports that the kind is missing.
    pub(crate) fn expect(&mut self, kind: SyntaxKind, what: &str) -> Res {
        if self.eat(kind) {
            Some(())
        } else {
            self.syntax_error(&format!("expected {what}"));
            None
        }
    }

    /// Reports a nesting that is too deep, when the height is above the limit.
    pub(crate) fn check_height(&mut self, height: usize, offset: usize) -> Res {
        if height > MAX_DEPTH {
            self.syntax_error_at(offset, "the nesting is deeper than 64 levels");
            None
        } else {
            Some(())
        }
    }
}
