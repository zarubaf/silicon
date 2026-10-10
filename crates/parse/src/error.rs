//! Errors as data, and the map from a byte offset to a source position.

use crate::ast::Pos;
use std::cell::Cell;
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

/// The machine cannot give the stack that the syntax depth needs. The recursion of the front
/// end would overflow it, so the front end does not start.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StackError {
    pub depth: usize,
    pub bytes: usize,
}

impl fmt::Display for StackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "cannot allocate a stack of {} bytes for the syntax depth {}",
            self.bytes, self.depth
        )
    }
}

impl std::error::Error for StackError {}

/// Maps a byte offset to a line and a column. It remembers the last answer, so offsets in
/// increasing order cost a linear scan of the input in total.
pub(crate) struct LineIndex<'a> {
    input: &'a str,
    line_starts: Vec<usize>,
    /// The last offset asked, and the characters from its line start to it.
    last: Cell<(usize, usize)>,
}

impl<'a> LineIndex<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        let line_starts = std::iter::once(0)
            .chain(input.match_indices('\n').map(|(at, _)| at + 1))
            .collect();
        LineIndex {
            input,
            line_starts,
            last: Cell::new((0, 0)),
        }
    }

    /// The position of a byte offset on a character boundary, or of the end of the input.
    pub(crate) fn pos(&self, offset: usize) -> Pos {
        let line = self.line_starts.partition_point(|&start| start <= offset) - 1;
        let start = self.line_starts[line];
        let (last_offset, last_chars) = self.last.get();
        // Continue from the last answer when it is on this line and not after the offset.
        let (from, chars) = if last_offset >= start && last_offset <= offset {
            (last_offset, last_chars)
        } else {
            (start, 0)
        };
        let cols = chars
            + self
                .input
                .get(from..offset)
                .map_or(0, |s| s.chars().count());
        self.last.set((offset, cols));
        Pos {
            line: line + 1,
            col: cols + 1,
        }
    }
}
