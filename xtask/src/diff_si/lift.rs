// SPDX-License-Identifier: Apache-2.0
//! The lift mode. A random core design is lifted to a source program. The
//! core interpreter is the oracle: `silicon run` and `silicon-check run` on
//! the source must print its outputs, and the Lean `validate` must accept
//! the elaboration of the source.

use std::path::Path;

use anyhow::{Context, Result, anyhow};
use core_ir::ast;
use core_ir::check::check;
use core_ir::r#gen::{self, Config};
use core_ir::interp::Sim;
use core_ir::text::print;
use core_ir::vectors::parse_input;
use proptest::strategy::{Just, Strategy};
use syntax::r#gen::{lift, vector_in, vector_out};

use super::{Tools, reproducer, run_trace, validated, verdict_of};
use crate::diff::{CYCLES, Trace, compare};

/// A core design and its `in=` lines.
pub(super) type Case = (ast::Design, Vec<String>);

/// Random designs of the source forms, each with `CYCLES` matching input
/// lines. A design that fails the checker gets no lines, so the case then
/// reports the checker error.
pub(super) fn cases() -> impl Strategy<Value = Case> {
    r#gen::design_with(Config::source()).prop_flat_map(|design| {
        let lines = check(&design)
            .ok()
            .and_then(|typed| typed.modules().get(typed.top().index()).cloned())
            .map_or_else(
                || Just(Vec::new()).boxed(),
                |top| r#gen::lines(&top, CYCLES).boxed(),
            );
        (Just(design), lines)
    })
}

/// The `in=` and `out=` lines of the source vectors for `case`, from the
/// core interpreter. The inner error is the message of the checker.
fn reference(case: &Case) -> Result<std::result::Result<Vec<(String, String)>, String>> {
    let (design, lines) = case;
    let typed = match check(design) {
        Ok(typed) => typed,
        Err(e) => {
            return Ok(Err(format!("the generated design fails the checker: {e}")));
        }
    };
    let top = typed
        .modules()
        .get(typed.top().index())
        .context("the design has no top module")?;
    let mut sim = Sim::new(&typed).map_err(|e| anyhow!("the core interpreter rejects it: {e}"))?;
    let mut steps = Vec::new();
    for line in lines {
        let inputs = parse_input(line, top).map_err(|e| anyhow!("{line}: {e}"))?;
        let outputs = sim.step(&inputs);
        steps.push((vector_in(top, &inputs), vector_out(top, &outputs)));
    }
    Ok(Ok(steps))
}

fn top_selection(design: &ast::Design) -> String {
    format!("{}()", design.top.text)
}

/// `None` if the tools agree on `case`, else the message of the
/// disagreement or of a tool failure. A tooling error is an `Err`.
pub(super) fn verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<String>> {
    verdict_of(try_verdict(tools, dir, case))
}

fn try_verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<String>> {
    let steps = match reference(case)? {
        Ok(steps) => steps,
        Err(message) => return Ok(Some(message)),
    };
    let source = lift(&case.0)
        .map_err(|e| anyhow!("the lift rejects the design: {e}\n{}", print(&case.0)))?;
    let file = dir.join("design.si");
    std::fs::write(&file, &source).with_context(|| format!("cannot write {}", file.display()))?;
    let top = top_selection(&case.0);
    let mut stdin = steps
        .iter()
        .map(|(line, _)| line.as_str())
        .collect::<Vec<_>>()
        .join("\n");
    stdin.push('\n');
    let traces = [
        Trace {
            tool: "core",
            lines: steps.iter().map(|(_, out)| out.clone()).collect(),
        },
        run_trace("silicon", &tools.silicon, &file, &top, &stdin)?,
        run_trace("lean", &tools.lean, &file, &top, &stdin)?,
    ];
    if let Some(message) = compare(&traces) {
        return Ok(Some(message));
    }
    validated(tools, &file, &top)
}

/// Prints the failure of seed `seed`: the message, the core design, and the
/// reproducer.
pub(super) fn report(seed: u64, case: &Case, message: &str) {
    println!("FAIL seed {seed}: {message}");
    println!("{}", print(&case.0));
    if let (Ok(source), Ok(Ok(steps))) = (lift(&case.0), reference(case)) {
        print!("{}", reproducer(&source, &top_selection(&case.0), &steps));
    }
    println!("Run `cargo xtask diff-si --seed {seed} --count 1` to repeat it.");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diff::runner;
    use proptest::strategy::ValueTree;

    fn case(seed: u64) -> (Case, String) {
        let case = cases().new_tree(&mut runner(seed)).unwrap().current();
        let text = print(&case.0);
        (case, text)
    }

    #[test]
    fn the_same_seed_gives_the_same_case() {
        let ((_, lines_a), text_a) = case(7);
        let ((_, lines_b), text_b) = case(7);
        assert_eq!((text_a, &lines_a), (text_b, &lines_b));
        assert_eq!(lines_a.len(), CYCLES);
    }

    #[test]
    fn cases_use_source_forms() {
        for seed in 1..=20 {
            let ((design, _), _) = case(seed);
            assert!(lift(&design).is_ok(), "seed {seed}");
        }
    }
}
