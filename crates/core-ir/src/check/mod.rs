//! The checker. It applies the rules of spec section 4.2 in the pass order of
//! section 6.4.1, and it reports the lowest-positioned error of the first pass
//! that has an error.

mod clocks;
mod instances;
mod lower;
mod names;
mod rx;
mod scope;
mod structure;
mod types;

use crate::ast;
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::typed;
use scope::{Env, Scope};

/// Elaborates a design into the typed core IR.
///
/// # Errors
/// Returns the first error of the first failing pass, as spec section 6.4.1
/// defines it.
pub fn check(design: &ast::Design) -> Result<typed::Design, Diagnostic> {
    // Pass 1, the syntax, is the parser's.
    first_error(names::duplicates(design))?;
    let env = Env::build(design);
    let scopes = Scope::build_all(design, &env);
    let resolved = names::resolve(design, &env, &scopes)?;
    first_error(types::declared(design))?;
    first_error(clocks::check(design, &resolved))?;
    let linked = instances::check(design, env.externs(), &resolved)?;
    first_error(types::operations(&resolved))?;
    let structures = structure::check(&scopes, &resolved)?;
    // Passes 9 and 10 (the instance and combinational cycles) and the schedule
    // are not part of this stage.
    lower::lower(design, &env, &scopes, &resolved, &structures, &linked)
}

fn error(code: ErrorCode, span: Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        code,
        span,
        message: message.into(),
    }
}

/// Fails with the error at the lowest position, if there is one.
fn first_error(errors: Vec<Diagnostic>) -> Result<(), Diagnostic> {
    match errors.into_iter().min_by_key(|d| d.span) {
        Some(d) => Err(d),
        None => Ok(()),
    }
}
