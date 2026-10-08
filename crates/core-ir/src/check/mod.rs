//! The checker. It applies the rules of spec section 4.2 in the pass order of
//! section 6.4.1, and it reports the lowest-positioned error of the first pass
//! that has an error.

mod clocks;
mod graph;
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
    let (resolved, top) = names::resolve(design, &env, &scopes)?;
    let (sized, widths) = types::declared(design, &scopes, env.externs(), resolved)?;
    let modules = clocks::check(design, sized)?;
    let linked = instances::check(design, env.externs(), &modules)?;
    first_error(types::operations(&modules))?;
    let structures = structure::check(&scopes, &modules)?;
    let order = graph::instances(&scopes, &linked)?;
    let (typed_modules, externs) = lower::lower(
        design,
        &env,
        &widths,
        &scopes,
        &modules,
        &structures,
        &linked,
    );
    let lowered = typed::Design {
        modules: typed_modules,
        externs,
        top,
    };
    let sources: Vec<graph::Sources> = scopes
        .iter()
        .zip(&modules)
        .zip(&structures)
        .map(|((scope, rx), structure)| graph::Sources {
            scope,
            rx,
            structure,
        })
        .collect();
    graph::combinational(lowered, &order, &sources)
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
