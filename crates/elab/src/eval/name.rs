// SPDX-License-Identifier: Apache-2.0
//! The name rule of design section 5.6, as Lean `Eval.nameRule` defines it. A port name of an
//! `as` key and a field name of `@Struct` share it, each with its own kind.

use crate::Code;
use crate::eval::{Res, fail};
use crate::ops::str_text;
use parse::ast::Pos;
use syntax::SyntaxKind;

/// The name rule for the name `s` of the kind `kind` at `pos`. A name that is no identifier is
/// the `S022` "Name rule", and a keyword is the `S022` "Keyword name" (section 6.2). The caller
/// charges the size of `s` first.
pub(super) fn name_rule(pos: Pos, s: &str, kind: &str) -> Res<()> {
    #[cfg(test)]
    crate::counters::add(crate::counters::Count::Scanned, s.chars().count() as u64);
    if !syntax::is_identifier(s) {
        return fail(
            Code::S022,
            pos,
            format!(
                "`{}` is not a valid {kind} name; use an ASCII letter or `_`, then letters, \
                 digits, or `_`",
                str_text(s),
            ),
        );
    }
    if SyntaxKind::keyword(s).is_some() {
        return fail(
            Code::S022,
            pos,
            format!(
                "`{}` is a keyword, so it cannot be a {kind} name; choose another name",
                str_text(s),
            ),
        );
    }
    Ok(())
}
