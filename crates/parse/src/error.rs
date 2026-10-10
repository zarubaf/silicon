//! Errors as data, and the map from a byte offset to a source position.

use crate::ast::Pos;
use std::fmt;

/// The codes of pass 1 of the front end (design section 6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Code {
    /// The file is not valid tokens, or it does not match the grammar.
    S001,
    /// The syntax belongs to a later slice.
    S004,
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Code::S001 => "S001",
            Code::S004 => "S004",
        })
    }
}

/// An error of pass 1. The parser reports all of them in position order. Only the first one
/// is normative: later errors have no oracle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub code: Code,
    pub pos: Pos,
    pub message: String,
}

/// Maps a byte offset to a line and a column.
pub(crate) struct LineIndex<'a> {
    input: &'a str,
    line_starts: Vec<usize>,
}

impl<'a> LineIndex<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        let line_starts = std::iter::once(0)
            .chain(input.match_indices('\n').map(|(at, _)| at + 1))
            .collect();
        LineIndex { input, line_starts }
    }

    /// The position of a byte offset on a character boundary, or of the end of the input.
    pub(crate) fn pos(&self, offset: usize) -> Pos {
        let line = self.line_starts.partition_point(|&start| start <= offset) - 1;
        let start = self.line_starts[line];
        let col = self
            .input
            .get(start..offset)
            .map_or(0, |s| s.chars().count());
        Pos {
            line: line + 1,
            col: col + 1,
        }
    }
}
