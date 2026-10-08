//! Extracts the prose of Lean files (`/-! -/` and `/-- -/` blocks) as Markdown,
//! so that vale checks it with the same rules as the Markdown docs.

/// The text of one prose block. `first_line` is the 1-based Lean line of its opener.
#[derive(Debug, PartialEq, Eq)]
pub struct ProseBlock {
    pub first_line: usize,
    pub text: String,
}

/// Finds the module and declaration doc comments of a Lean source.
/// Plain block comments, line comments, and string and character literals are not prose.
/// Block comments nest in Lean, so the scan counts `/-` and `-/` pairs.
pub fn prose_blocks(source: &str) -> Vec<ProseBlock> {
    let chars: Vec<char> = source.chars().collect();
    let at = |i: usize, c: char| chars.get(i) == Some(&c);
    let mut blocks = Vec::new();
    let (mut i, mut line) = (0, 1);
    while i < chars.len() {
        match chars[i] {
            '\n' => {
                line += 1;
                i += 1;
            }
            '-' if at(i + 1, '-') => {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            '"' => {
                i += 1;
                while i < chars.len() && chars[i] != '"' {
                    if chars[i] == '\\' {
                        // An escape takes the next character, which may be a line break.
                        i += 1;
                    }
                    if chars.get(i) == Some(&'\n') {
                        line += 1;
                    }
                    i += 1;
                }
                i += 1;
            }
            '\'' if at(i + 2, '\'') => i += 3,
            '\'' if at(i + 1, '\\') && at(i + 3, '\'') => i += 4,
            '/' if at(i + 1, '-') => {
                let is_prose = at(i + 2, '!') || at(i + 2, '-');
                let (start, first_line) = (i + if is_prose { 3 } else { 2 }, line);
                let mut depth = 1;
                i = start;
                while i < chars.len() && depth > 0 {
                    if chars[i] == '\n' {
                        line += 1;
                    }
                    if chars[i] == '/' && at(i + 1, '-') {
                        depth += 1;
                        i += 1;
                    } else if chars[i] == '-' && at(i + 1, '/') {
                        depth -= 1;
                        i += 1;
                    }
                    i += 1;
                }
                if is_prose && depth == 0 {
                    blocks.push(ProseBlock {
                        first_line,
                        text: chars[start..i - 2].iter().collect(),
                    });
                }
            }
            _ => i += 1,
        }
    }
    blocks
}

/// Joins the blocks into one Markdown text, a blank line between blocks.
/// The vector holds, for each Markdown line, the Lean line it came from.
pub fn to_markdown(blocks: &[ProseBlock]) -> (String, Vec<usize>) {
    let mut markdown = String::new();
    let mut map = Vec::new();
    for block in blocks {
        let indent = common_indent(&block.text);
        for (offset, text) in block.text.split('\n').enumerate() {
            markdown.push_str(text.chars().skip(indent).collect::<String>().trim_end());
            markdown.push('\n');
            map.push(block.first_line + offset);
        }
        markdown.push('\n');
        map.push(block.first_line);
    }
    (markdown, map)
}

/// The indentation that all non-blank lines share. Markdown reads four spaces as code,
/// so a docstring indented inside a `structure` must lose it. Extra indentation stays.
fn common_indent(text: &str) -> usize {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_module_and_declaration_docs() {
        let src =
            "/-! Module prose. -/\ndef x := 1\n/-- Doc of y. -/\ndef y := 2\n-- line comment\n";
        let b = prose_blocks(src);
        assert_eq!(b.len(), 2);
        assert_eq!((b[0].first_line, b[0].text.trim()), (1, "Module prose."));
        assert_eq!((b[1].first_line, b[1].text.trim()), (3, "Doc of y."));
    }

    #[test]
    fn ignores_plain_block_comments_and_strings() {
        assert!(prose_blocks("/- not prose -/\ndef s := \"/-! no -/\"\n").is_empty());
    }

    #[test]
    fn line_map_points_back_to_lean() {
        let src = "def a := 1\n/-!\nLine one.\nLine two.\n-/\n";
        let (_, map) = to_markdown(&prose_blocks(src));
        assert!(map.contains(&3) && map.contains(&4));
    }

    #[test]
    fn string_gap_counts_lines() {
        let src = "def s := \"a\\\n  b\"\n/-! Prose. -/\n";
        assert_eq!(prose_blocks(src)[0].first_line, 3);
    }

    #[test]
    fn indented_field_doc_is_not_a_code_block() {
        let src = "structure S where\n  /--\n    Doc text here.\n      code()\n  -/\n  x : Nat\n";
        let (md, _) = to_markdown(&prose_blocks(src));
        assert!(md.lines().any(|l| l == "Doc text here."));
        assert!(md.lines().any(|l| l == "  code()"));
    }

    #[test]
    fn line_comment_hides_prose_opener() {
        assert!(prose_blocks("-- see /-! here\ndef x := 1\n").is_empty());
    }

    #[test]
    fn nested_comments_and_char_literals() {
        let src = "def q := '\"'\n/-! Outer /- inner -/ still outer. -/\ndef z := 1\n";
        let b = prose_blocks(src);
        assert_eq!(b.len(), 1);
        assert_eq!(b[0].first_line, 2);
        assert!(b[0].text.contains("still outer"));
    }
}
