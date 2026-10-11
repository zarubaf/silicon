//! The `expected-error XNNN @+N` directive (spec section 9).

/// The comment marker of a source language.
#[derive(Clone, Copy)]
pub enum Marker {
    /// A `.sil` file: `; expected-error`.
    Sil,
    /// A `.si` file: `// expected-error`.
    Si,
}

impl Marker {
    /// The comment prefix.
    #[must_use]
    pub fn prefix(self) -> &'static str {
        match self {
            Marker::Sil => ";",
            Marker::Si => "//",
        }
    }
}

const KEYWORD: &str = " expected-error ";

/// The expected error of a file: its code and its 1-based line.
#[derive(Debug, PartialEq, Eq)]
pub struct Expected {
    pub code: String,
    pub line: usize,
}

/// Parses `XNNN @+N` or `XNNN @-N` on the 1-based line `at`.
fn parse_directive(rest: &str, at: usize, marker: &str) -> Result<Expected, String> {
    let bad = || format!("line {at}: malformed directive `{marker}{KEYWORD}{rest}`");
    let (code, offset) = rest.trim().split_once(" @").ok_or_else(bad)?;
    let valid_code = code.len() == 4
        && code.starts_with(|c: char| c.is_ascii_uppercase())
        && code[1..].bytes().all(|b| b.is_ascii_digit());
    if !valid_code {
        return Err(bad());
    }
    let (sign, digits) = offset.split_at_checked(1).ok_or_else(bad)?;
    let n: usize = digits.parse().map_err(|_| bad())?;
    let line = match sign {
        "+" if n >= 1 => at.checked_add(n),
        "-" if n >= 1 => at.checked_sub(n).filter(|&l| l >= 1),
        _ => None,
    }
    .ok_or_else(bad)?;
    Ok(Expected {
        code: code.to_owned(),
        line,
    })
}

/// The directive of a file. `None` means the file must pass.
///
/// # Errors
///
/// Returns a message when a directive is malformed or a file has more than one.
pub fn expected_error(source: &str, marker: Marker) -> Result<Option<Expected>, String> {
    let prefix = marker.prefix();
    let mut found = None;
    for (index, text) in source.lines().enumerate() {
        let Some(rest) = text
            .trim_start()
            .strip_prefix(prefix)
            .and_then(|r| r.strip_prefix(KEYWORD))
        else {
            continue;
        };
        if found.is_some() {
            return Err(format!("line {}: a second directive", index + 1));
        }
        found = Some(parse_directive(rest, index + 1, prefix)?);
    }
    Ok(found)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expected_error_reads_both_markers() {
        assert_eq!(
            expected_error("; expected-error E004 @+1\nx", Marker::Sil),
            Ok(Some(Expected {
                code: "E004".to_owned(),
                line: 2
            }))
        );
        assert_eq!(
            expected_error("a\nb\n// expected-error S010 @-1", Marker::Si),
            Ok(Some(Expected {
                code: "S010".to_owned(),
                line: 2
            }))
        );
    }

    #[test]
    fn a_file_without_a_directive_must_pass() {
        assert_eq!(expected_error("x\n", Marker::Sil), Ok(None));
        assert_eq!(
            expected_error("; expected-error E004 @+1", Marker::Si),
            Ok(None)
        );
    }

    #[test]
    fn a_second_directive_is_an_error() {
        let source = "; expected-error E004 @+2\n; expected-error E005 @+1\nx";
        assert_eq!(
            expected_error(source, Marker::Sil),
            Err("line 2: a second directive".to_owned())
        );
    }

    #[test]
    fn a_malformed_directive_is_an_error() {
        for source in [
            "; expected-error E004",
            "; expected-error E04 @+1",
            "; expected-error 1004 @+1",
            "; expected-error E004 @+0",
            "; expected-error E004 @*1",
            "; expected-error E004 @-1",
            "; expected-error E004 @+x",
        ] {
            assert!(expected_error(source, Marker::Sil).is_err(), "{source:?}");
        }
    }
}
