// SPDX-License-Identifier: Apache-2.0
//! The error report `error[XNNN]: L:C: message` (spec 6.4.2).

/// The code and the position of a reported error.
#[derive(Debug, PartialEq, Eq)]
pub struct Report {
    pub code: String,
    pub line: usize,
    pub col: usize,
}

/// Parses the report `error[XNNN]: L:C: message`.
#[must_use]
pub fn parse_report(stdout: &str) -> Option<Report> {
    let rest = stdout.strip_prefix("error[")?;
    let (code, rest) = rest.split_once("]: ")?;
    let (line, rest) = rest.split_once(':')?;
    let (col, _) = rest.split_once(':')?;
    Some(Report {
        code: code.to_owned(),
        line: line.parse().ok()?,
        col: col.parse().ok()?,
    })
}

/// The message of the first line of a report `error[XNNN]: L:C: message`.
#[must_use]
pub fn parse_message(stdout: &str) -> Option<&str> {
    parse_report(stdout)?;
    let (_, rest) = stdout.split_once("]: ")?;
    let (_, rest) = rest.split_once(':')?;
    let (_, rest) = rest.split_once(':')?;
    rest.lines().next()?.strip_prefix(' ')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_report_gives_code_line_and_column() {
        assert_eq!(
            parse_report("error[E004]: 3:7: x\n"),
            Some(Report {
                code: "E004".to_owned(),
                line: 3,
                col: 7
            })
        );
    }

    #[test]
    fn the_message_is_the_rest_of_the_first_line() {
        assert_eq!(
            parse_message("error[S016]: 3:7: a: b\nmore\n"),
            Some("a: b")
        );
        assert_eq!(parse_message("ok\n"), None);
    }

    #[test]
    fn text_without_a_report_gives_none() {
        assert_eq!(parse_report("ok\n"), None);
    }
}
