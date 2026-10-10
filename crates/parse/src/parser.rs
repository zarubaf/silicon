//! The parser state: the cursor over the tokens, the tree builder, and the errors.
//! The grammar is in `item`, `stmt`, and `expr`.

use crate::error::Code;
use rowan::{Checkpoint, GreenNode, GreenNodeBuilder, Language};
use std::collections::BTreeSet;
use syntax::{SiliconLanguage, SyntaxKind, Token};

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
    /// The syntax depth: the most height of an expression or a type, and the most nesting
    /// of blocks.
    depth: usize,
    /// The index of the next token that the builder has not got.
    at: usize,
    builder: GreenNodeBuilder<'static>,
    pub errors: Vec<RawError>,
    /// The offsets with an error, so that one place gets one error.
    reported: BTreeSet<usize>,
    /// The start of the outermost expression or type that is open now: one that is not part
    /// of another.
    top: Option<usize>,
    /// The number of forms of an expression or a type that are open now.
    open: usize,
    /// The nesting of the blocks now open.
    blocks: usize,
    /// For each opening bracket, the index of the bracket that closes it.
    closer: Vec<Option<usize>>,
    /// For each opening bracket, whether a `,` comes before its closing bracket.
    comma: Vec<bool>,
    /// The height of the last expression or type that a parse function completed.
    pub height: usize,
    /// Whether the last postfix form is a place of slice 1: a name, or a field of a place.
    pub place: bool,
    /// Whether the last postfix form has an index.
    pub indexed: bool,
}

impl<'a> Parser<'a> {
    pub(crate) fn new(input: &'a str, tokens: &'a [Token], depth: usize) -> Self {
        let (closer, comma) = bracket_tables(tokens);
        Parser {
            input,
            tokens,
            depth,
            at: 0,
            builder: GreenNodeBuilder::new(),
            errors: Vec::new(),
            reported: BTreeSet::new(),
            top: None,
            open: 0,
            blocks: 0,
            closer,
            comma,
            height: 0,
            place: false,
            indexed: false,
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

    /// The text of the current token.
    pub(crate) fn text(&self) -> &'a str {
        self.significant(0)
            .map_or("", |t| &self.input[t.range.clone()])
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

    /// Runs the parts of an expression or a type. If none is open, this one is the outermost,
    /// and it starts at `start`.
    pub(crate) fn outermost<T>(&mut self, start: usize, parts: impl FnOnce(&mut Self) -> T) -> T {
        if self.top.is_some() {
            return parts(self);
        }
        self.top = Some(start);
        let res = parts(self);
        self.top = None;
        res
    }

    /// Runs the parts of a form of an expression. A form that is open inside `depth` other
    /// forms makes the height of the outermost expression larger than `depth`, so it is an
    /// error at once, and the recursion never goes deeper than the depth.
    pub(crate) fn form(&mut self, parts: impl FnOnce(&mut Self) -> Res) -> Res {
        if self.open >= self.depth {
            self.too_deep();
            return None;
        }
        self.open += 1;
        let res = parts(self);
        self.open -= 1;
        res
    }

    /// Runs the statements of a block, which nests at most `depth` deep.
    pub(crate) fn block_level(&mut self, parts: impl FnOnce(&mut Self) -> Res) -> Res {
        if self.blocks >= self.depth {
            let message = format!("blocks nest deeper than {} levels", self.depth);
            self.syntax_error(&message);
            return None;
        }
        self.blocks += 1;
        let res = parts(self);
        self.blocks -= 1;
        res
    }

    // The look ahead.

    /// The index in the token list of the token `n` places after the current one.
    pub(crate) fn raw_index(&self, n: usize) -> Option<usize> {
        self.tokens[self.at..]
            .iter()
            .enumerate()
            .filter(|(_, t)| !t.kind.is_trivia())
            .nth(n)
            .map(|(i, _)| self.at + i)
    }

    /// The index of the first token from `from` on that is not trivia.
    fn skip_trivia(&self, from: usize) -> usize {
        from + self.tokens[from..]
            .iter()
            .take_while(|t| t.kind.is_trivia())
            .count()
    }

    fn kind_at(&self, index: usize) -> Option<SyntaxKind> {
        self.tokens.get(index).map(|t| t.kind)
    }

    /// Whether the current token is a `(` of a unit or a tuple: the next token is `)`, or a
    /// `,` comes before the matching bracket.
    pub(crate) fn at_unit_or_tuple(&self) -> bool {
        let Some(open) = self.raw_index(0) else {
            return false;
        };
        let next = self.skip_trivia(open + 1);
        self.kind_at(next) == Some(SyntaxKind::RParen) || self.comma[open]
    }

    /// Whether the name at the current token starts a place of a later slice: after the
    /// name come `.name`, `.number`, and `[...]`, then `=` or `:=`, and one of them is a
    /// `[` or a `.number`.
    pub(crate) fn at_later_place(&self) -> bool {
        #[allow(clippy::enum_glob_use)]
        use SyntaxKind::*;
        let Some(name) = self.raw_index(0) else {
            return false;
        };
        let mut seen = false;
        let mut at = self.skip_trivia(name + 1);
        loop {
            match self.kind_at(at) {
                Some(Eq | ColonEq) => return seen,
                Some(LBracket) => {
                    let Some(Some(close)) = self.closer.get(at) else {
                        return false;
                    };
                    seen = true;
                    at = self.skip_trivia(close + 1);
                }
                Some(Dot) => {
                    let selector = self.skip_trivia(at + 1);
                    match self.kind_at(selector) {
                        Some(Ident) => {}
                        Some(Dec | Hex | Bin) => seen = true,
                        _ => return false,
                    }
                    at = self.skip_trivia(selector + 1);
                }
                _ => return false,
            }
        }
    }

    // The errors.

    fn report(&mut self, code: Code, offset: usize, message: String) {
        // One error for each place is enough, and an error token has its lexical error.
        let on_error_token = code == Code::S001
            && self
                .significant(0)
                .is_some_and(|t| t.range.start == offset && t.kind == SyntaxKind::Error);
        if on_error_token || !self.reported.insert(offset) {
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

    /// Reports that the outermost expression or type is higher than the depth.
    fn too_deep(&mut self) {
        let at = self.top.unwrap_or_else(|| self.offset());
        let message = format!("expression nests deeper than {} levels", self.depth);
        self.syntax_error_at(at, &message);
    }

    /// Reports a height above the depth.
    pub(crate) fn check_height(&mut self, height: usize) -> Res {
        if height > self.depth {
            self.too_deep();
            None
        } else {
            Some(())
        }
    }
}

/// For each opening bracket (of the three kinds, as one depth), its closing bracket and
/// whether a `,` comes before it. The tables end at the first error token, because the
/// token list of the reference lexer ends there.
fn bracket_tables(tokens: &[Token]) -> (Vec<Option<usize>>, Vec<bool>) {
    #[allow(clippy::enum_glob_use)]
    use SyntaxKind::*;
    let mut closer = vec![None; tokens.len()];
    let mut comma = vec![false; tokens.len()];
    let mut open: Vec<usize> = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        match token.kind {
            Error => break,
            LParen | LBracket | LBrace => open.push(i),
            RParen | RBracket | RBrace => {
                if let Some(start) = open.pop() {
                    closer[start] = Some(i);
                }
            }
            Comma => {
                if let Some(&start) = open.last() {
                    comma[start] = true;
                }
            }
            _ => {}
        }
    }
    (closer, comma)
}
