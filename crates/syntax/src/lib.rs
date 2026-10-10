//! The lexer and the lossless syntax tree types of the Silicon front end.

mod kind;
mod lexer;
mod number;

pub use kind::{SiliconLanguage, SyntaxKind, SyntaxNode, SyntaxToken};
pub use lexer::{LexError, Lexed, Token, lex};

#[cfg(test)]
mod tests {
    use super::*;
    use rowan::{GreenNodeBuilder, Language};

    #[test]
    fn tree_text_equals_input() {
        let input = "module M() { x := 1 >> 2; } /* open";
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(SiliconLanguage::kind_to_raw(SyntaxKind::Root));
        for token in lex(input, 4096).tokens {
            builder.token(
                SiliconLanguage::kind_to_raw(token.kind),
                &input[token.range],
            );
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(builder.finish());
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.text().to_string(), input);
    }
}
