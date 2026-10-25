// SPDX-License-Identifier: Apache-2.0
//! The kinds of tokens and nodes, and the `rowan` language that names them.

use rowan::Language;

/// Declares `SyntaxKind` and the table of all kinds, in declaration order.
macro_rules! kinds {
    ($($(#[$m:meta])* $name:ident,)*) => {
        /// The kind of a token or a node of the syntax tree.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        #[repr(u16)]
        pub enum SyntaxKind {
            $($(#[$m])* $name,)*
        }

        impl SyntaxKind {
            const ALL: &'static [SyntaxKind] = &[$(SyntaxKind::$name,)*];
        }
    };
}

kinds! {
    // Trivia and errors.
    Whitespace,
    LineComment,
    BlockComment,
    /// An invalid character, an unterminated string, or an unterminated comment.
    Error,
    // Literals and names.
    Ident,
    Dec,
    Hex,
    Bin,
    Str,
    // Keywords.
    ImportKw,
    AsKw,
    PubKw,
    ConstKw,
    TypeKw,
    StructKw,
    ComptimeKw,
    FnKw,
    ModuleKw,
    ExternKw,
    LetKw,
    MutKw,
    ReturnKw,
    IfKw,
    ElseKw,
    ForKw,
    InKw,
    ConformsKw,
    UsingKw,
    TrueKw,
    FalseKw,
    RegKw,
    WireKw,
    MemKw,
    InputKw,
    OutputKw,
    InstanceKw,
    DomainsKw,
    WithKw,
    /// `enum` of slice 3 (ADR 0021).
    EnumKw,
    /// `match` of slice 3 (ADR 0021).
    MatchKw,
    // Operators of two characters.
    ColonEq,
    ColonColon,
    Arrow,
    /// `=>`: the arrow of a `match` arm (slice 3).
    FatArrow,
    DotDot,
    PlusPercent,
    MinusPercent,
    StarPercent,
    EqEq,
    BangEq,
    LtEq,
    GtEq,
    Shl,
    Shr,
    AmpAmp,
    PipePipe,
    // Punctuation and operators of one character.
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    Dot,
    Eq,
    Lt,
    Gt,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Bang,
    At,
    // Nodes.
    Root,
    /// Tokens that the parser skipped after an error.
    ErrorNode,
    ConstItem,
    FnItem,
    ModuleItem,
    /// `struct P(comptime n: Nat) { a: T, }`: the name, the `ParamList` if any, then the fields.
    StructItem,
    /// `name: T` in a struct.
    StructField,
    /// `type N = T;` at an item.
    AliasItem,
    /// `enum E: T { A(P) = 0 }`: the name, the tag type, then the `EnumVariant` children.
    EnumItem,
    /// `A(P, Q) = e` in an enum: the name, the payload types, then the tag value.
    EnumVariant,
    ParamList,
    Param,
    DomainsClause,
    Block,
    NameType,
    IndexType,
    /// `()`.
    UnitType,
    /// `(T, U)`: the element types are the children.
    TupleType,
    /// `[T; N]`: the element type, then the length expression.
    ArrayType,
    /// `[T; N]` in an expression: the element type, then the length expression.
    ArrayTypeExpr,
    /// `(T)`: a grouped type. It makes no node of the AST.
    ParenType,
    /// `fn (P, mut Q) -> R`: the `FnTypeParam` children, then the result type, which is a
    /// `FnType` for a chain.
    FnType,
    /// `fn (P) -> R` in an expression: like `FnType`, and the outermost node of a chain.
    FnTypeExpr,
    /// A parameter type of a function type, with its `mut` mark.
    FnTypeParam,
    /// The delimited arguments of a call, an index, or a type family.
    ArgList,
    Literal,
    NameExpr,
    ParenExpr,
    UnaryExpr,
    BinExpr,
    CondExpr,
    CallExpr,
    IndexExpr,
    FieldExpr,
    /// `E::V`: two names.
    PathExpr,
    /// `match (x) { p => e, }`: the scrutinee, then the `MatchArm` children.
    MatchExpr,
    /// `p => e` in a `match`: a `Pattern`, `=>`, and the expression.
    MatchArm,
    /// The pattern of an arm: a number with an optional `-`, `true`, `false`, `_`, or a
    /// variant path `E::V` with optional binders in parentheses.
    Pattern,
    /// `x.m(args)`: a receiver call. The arguments are in an `ArgList`.
    MethodExpr,
    /// `.N` after an expression.
    SelectExpr,
    /// `()`.
    UnitExpr,
    /// `(a, b)`: the elements are in an `ArgList`.
    TupleExpr,
    /// `[a, b]`: the elements are in an `ArgList`.
    ArrayExpr,
    /// `@name(args)`: a builtin. The name is a token, and the operands are in an `ArgList`.
    BuiltinExpr,
    LetStmt,
    AssignStmt,
    ConnectStmt,
    RegStmt,
    WireStmt,
    MemStmt,
    InputStmt,
    OutputStmt,
    InstStmt,
    ReturnStmt,
    CtIfStmt,
    CtForStmt,
    ExprStmt,
    /// `type N = T;` at a statement.
    AliasStmt,
}

impl SyntaxKind {
    /// The keyword that the text spells, if any.
    #[must_use]
    pub fn keyword(text: &str) -> Option<SyntaxKind> {
        Some(match text {
            "import" => Self::ImportKw,
            "as" => Self::AsKw,
            "pub" => Self::PubKw,
            "const" => Self::ConstKw,
            "type" => Self::TypeKw,
            "struct" => Self::StructKw,
            "comptime" => Self::ComptimeKw,
            "fn" => Self::FnKw,
            "module" => Self::ModuleKw,
            "extern" => Self::ExternKw,
            "let" => Self::LetKw,
            "mut" => Self::MutKw,
            "return" => Self::ReturnKw,
            "if" => Self::IfKw,
            "else" => Self::ElseKw,
            "for" => Self::ForKw,
            "in" => Self::InKw,
            "conforms" => Self::ConformsKw,
            "using" => Self::UsingKw,
            "true" => Self::TrueKw,
            "false" => Self::FalseKw,
            "reg" => Self::RegKw,
            "wire" => Self::WireKw,
            "mem" => Self::MemKw,
            "input" => Self::InputKw,
            "output" => Self::OutputKw,
            "instance" => Self::InstanceKw,
            "domains" => Self::DomainsKw,
            "with" => Self::WithKw,
            "enum" => Self::EnumKw,
            "match" => Self::MatchKw,
            _ => return None,
        })
    }

    /// Whether the kind is whitespace or a comment.
    #[must_use]
    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            SyntaxKind::Whitespace | SyntaxKind::LineComment | SyntaxKind::BlockComment
        )
    }
}

/// The `rowan` language of Silicon.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SiliconLanguage {}

impl Language for SiliconLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        // A raw kind comes only from `kind_to_raw`, so an index outside the table is a bug.
        SyntaxKind::ALL[usize::from(raw.0)]
    }

    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

pub type SyntaxNode = rowan::SyntaxNode<SiliconLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<SiliconLanguage>;
