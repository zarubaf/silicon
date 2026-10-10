//! The parser state: the cursor over the tokens, the tree builder, and the errors.
//! The grammar is in `item`, `stmt`, and `expr`.

use crate::error::Code;
use crate::tree::{Checkpoint, TreeBuilder};
use rowan::{GreenNode, Language};
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
    /// The syntax depth: the most height of an outermost expression or type.
    depth: usize,
    /// The most nodes open at once. A tree that passes the checks of the syntax depth is
    /// below it, so only an erroneous input reaches it. Deeper nodes are not made, and their
    /// tokens stay in the node around them.
    node_cap: usize,
    /// The number of nodes open now in the builder.
    nodes: usize,
    /// The number of open nodes that the cap kept out of the builder. They are the innermost.
    skipped: usize,
    /// The index of the next token that the builder has not got.
    at: usize,
    builder: TreeBuilder,
    pub errors: Vec<RawError>,
    /// The offsets with an error, so that one place gets one error.
    reported: BTreeSet<usize>,
    /// The start of the outermost expression or type that is open now: one that is not part
    /// of another.
    top: Option<usize>,
    /// The start of the first outermost expression or type whose height is above the depth.
    high: Option<usize>,
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
            node_cap: depth.saturating_mul(4).saturating_add(16),
            nodes: 0,
            skipped: 0,
            at: 0,
            builder: TreeBuilder::new(SiliconLanguage::kind_to_raw(SyntaxKind::Root)),
            errors: Vec::new(),
            reported: BTreeSet::new(),
            top: None,
            high: None,
            closer,
            comma,
            height: 0,
            place: false,
            indexed: false,
        }
    }

    /// Parses the whole input into a tree with the node `Root`. The last value is the start
    /// of the first outermost expression or type that is higher than the syntax depth.
    pub(crate) fn finish(mut self) -> (GreenNode, Vec<RawError>, Option<usize>) {
        // The first trivia belong inside the root, which the builder opens.
        self.source();
        self.flush_trivia();
        (self.builder.finish(), self.errors, self.high)
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
        if self.nodes < self.node_cap {
            self.nodes += 1;
            self.builder.start_node(SiliconLanguage::kind_to_raw(kind));
        } else {
            self.skipped += 1;
        }
    }

    pub(crate) fn finish_node(&mut self) {
        if self.skipped > 0 {
            self.skipped -= 1;
        } else {
            self.nodes -= 1;
            self.builder.finish_node();
        }
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
        if self.nodes < self.node_cap {
            self.nodes += 1;
            self.builder
                .start_node_at(checkpoint, SiliconLanguage::kind_to_raw(kind));
        } else {
            self.skipped += 1;
        }
        let res = parts(self);
        self.finish_node();
        res
    }

    /// Like `node_at`, for a node that wraps a chain. A chain that is already higher than the
    /// depth gets no more nodes: the input has a height error, and the nested nodes would make
    /// a deep tree. The tokens stay in the node around the chain.
    pub(crate) fn chain_at(
        &mut self,
        checkpoint: Checkpoint,
        kind: SyntaxKind,
        height: usize,
        parts: impl FnOnce(&mut Self) -> Res,
    ) -> Res {
        if height > self.depth {
            parts(self)
        } else {
            self.node_at(checkpoint, kind, parts)
        }
    }

    /// Runs the parts of an expression or a type. If none is open, this one is the outermost,
    /// and it starts at `start`. The height of a complete outermost one is checked after the
    /// parse, because a height error ranks below every other error.
    pub(crate) fn outermost(&mut self, start: usize, parts: impl FnOnce(&mut Self) -> Res) -> Res {
        if self.top.is_some() {
            return parts(self);
        }
        self.top = Some(start);
        let res = parts(self);
        self.top = None;
        if res.is_some() && self.height > self.depth && self.high.is_none() {
            self.high = Some(start);
        }
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
