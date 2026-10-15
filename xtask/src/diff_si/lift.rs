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
use proptest::collection::vec;
use proptest::prelude::any;
use proptest::strategy::{Just, Strategy};
use srcgen::{Lifted, lift};

use super::{Mode, Tools, repeat, reproducer, run_trace, stdin, validated, verdict_of};
use crate::diff::{CYCLES, Trace, compare};

/// A core design, its `in=` lines, and the shape tape of the lift.
pub(super) type Case = (ast::Design, Vec<String>, Vec<u32>);

/// The designs that agree, and how many of them have a memory, an aggregate
/// port, an aggregate register, or an aggregate wire.
#[derive(Default)]
pub(super) struct Tally {
    lifted: u64,
    memories: u64,
    aggregates: u64,
    registers: u64,
    wires: u64,
}

impl Tally {
    /// The success line for the seeds `seed` to `last`.
    pub(super) fn summary(&self, seed: u64, last: u64) -> String {
        format!(
            "diff-si: {} lifted designs agree (seeds {seed} to {last}): {} with memories, {} with aggregate ports, {} with aggregate registers, {} with aggregate wires",
            self.lifted, self.memories, self.aggregates, self.registers, self.wires
        )
    }
}

/// The most numbers of a shape tape: a design has at most 6 modules, a
/// module has at most 17 names to group (4 inputs, 4 outputs, 3 registers,
/// and 6 `let` values), and each name takes at most 4 numbers.
const SHAPE_NUMBERS: usize = 6 * 17 * 4;

/// Random designs of the source forms, each with `CYCLES` matching input
/// lines and a shape tape. A design that fails the checker gets no lines,
/// so the case then reports the checker error.
pub(super) fn cases() -> impl Strategy<Value = Case> {
    r#gen::design_with(Config::source()).prop_flat_map(|design| {
        let lines = check(&design)
            .ok()
            .and_then(|typed| typed.modules().get(typed.top().index()).cloned())
            .map_or_else(
                || Just(Vec::new()).boxed(),
                |top| r#gen::lines(&top, CYCLES).boxed(),
            );
        (Just(design), lines, vec(any::<u32>(), 0..SHAPE_NUMBERS))
    })
}

/// The `in=` and `out=` lines of the source vectors for `case`, from the
/// core interpreter and the vector map of `lifted`. The inner error is the
/// message of the checker.
fn reference(
    case: &Case,
    lifted: &Lifted,
) -> Result<std::result::Result<Vec<(String, String)>, String>> {
    let (design, lines, _) = case;
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
        steps.push((lifted.vector_in(&inputs)?, lifted.vector_out(&outputs)?));
    }
    Ok(Ok(steps))
}

/// The lift of `case`, or the message of the rejection.
fn lifted(case: &Case) -> Result<Lifted> {
    lift(&case.0, &case.2)
        .map_err(|e| anyhow!("the lift rejects the design: {e}\n{}", print(&case.0)))
}

fn top_selection(design: &ast::Design) -> String {
    format!("{}()", design.top.text)
}

/// `None` if the tools agree on `case`, else the message of the
/// disagreement or of a tool failure. A tooling error is an `Err`.
pub(super) fn verdict(
    tools: &Tools,
    dir: &Path,
    case: &Case,
    tally: &mut Tally,
) -> Result<Option<String>> {
    let lifted = lifted(case)?;
    let message = verdict_of(try_verdict(tools, dir, case, &lifted))?;
    if message.is_none() {
        tally.lifted += 1;
        tally.memories += u64::from(lifted.memories > 0);
        tally.aggregates += u64::from(lifted.aggregates > 0);
        tally.registers += u64::from(lifted.aggregate_regs > 0);
        tally.wires += u64::from(lifted.aggregate_wires > 0);
    }
    Ok(message)
}

fn try_verdict(tools: &Tools, dir: &Path, case: &Case, lifted: &Lifted) -> Result<Option<String>> {
    let steps = match reference(case, lifted)? {
        Ok(steps) => steps,
        Err(message) => return Ok(Some(message)),
    };
    let source = &lifted.text;
    let file = dir.join("design.si");
    std::fs::write(&file, source).with_context(|| format!("cannot write {}", file.display()))?;
    let top = top_selection(&case.0);
    let stdin = stdin(steps.iter().map(|(line, _)| line.as_str()));
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
    println!("FAIL seed {seed} (lift): {message}");
    println!("{}", print(&case.0));
    if let Ok(lifted) = lifted(case)
        && let Ok(Ok(steps)) = reference(case, &lifted)
    {
        print!(
            "{}",
            reproducer(&lifted.text, &top_selection(&case.0), &steps)
        );
    }
    println!("Run `{}` to repeat it.", repeat(Mode::Lift, seed));
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
    fn the_summary_counts_memories_and_aggregates() {
        let tally = Tally {
            lifted: 100,
            memories: 41,
            aggregates: 58,
            registers: 30,
            wires: 35,
        };
        assert_eq!(
            tally.summary(1, 100),
            "diff-si: 100 lifted designs agree (seeds 1 to 100): 41 with memories, 58 with aggregate ports, 30 with aggregate registers, 35 with aggregate wires"
        );
    }

    #[test]
    fn the_same_seed_gives_the_same_case() {
        let ((_, lines_a, tape_a), text_a) = case(7);
        let ((_, lines_b, tape_b), text_b) = case(7);
        assert_eq!((text_a, &lines_a, tape_a), (text_b, &lines_b, tape_b));
        assert_eq!(lines_a.len(), CYCLES);
    }

    #[test]
    fn cases_use_source_forms() {
        for seed in 1..=20 {
            let ((design, _, tape), _) = case(seed);
            assert!(lift(&design, &tape).is_ok(), "seed {seed}");
        }
    }
}
