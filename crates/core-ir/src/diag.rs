//! Source positions and the diagnostics that the tools report.

use std::fmt;

/// A 1-based source position.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    pub line: u32,
    pub col: u32,
}

/// The error codes of spec section 4.2, with `E014` for `run`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorCode {
    E001,
    E002,
    E003,
    E004,
    E005,
    E006,
    E007,
    E008,
    E009,
    E010,
    E011,
    E012,
    E013,
    E014,
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The derived Debug output is the code name.
        write!(f, "{self:?}")
    }
}

/// An error with its code, its position, and a human-readable message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: ErrorCode,
    pub span: Span,
    pub message: String,
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "error[{}]: {}:{}: {}",
            self.code, self.span.line, self.span.col, self.message
        )
    }
}

impl std::error::Error for Diagnostic {}
