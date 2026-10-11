// SPDX-License-Identifier: Apache-2.0
//! The typed mode. A random typed program and its twin, which has no
//! comptime construct, go through both front ends. The oracles are the
//! front-end spec, section 11.4: `silicon-check validate` accepts the
//! elaboration of `silicon elab`; the probe `eval` gives the value of the
//! generator in both front ends; `cost` is equal in both; and the program
//! and its twin give equal outputs in `run` on the same input lines.

use std::path::Path;
use std::process::Command;

use anyhow::{Result, bail};
use proptest::strategy::{Just, Strategy};
use syntax::r#gen::{BuildFault, Program, lines, twin, typed};

use super::{Mode, Tools, repeat, reproducer, run_trace, stdin, validated, verdict_of, write};
use crate::diff::{CYCLES, Trace, compare, difference, output};

/// A typed program, or the fault of its builder, and its `in=` lines.
pub(super) type Case = (Result<Program, BuildFault>, Vec<String>);

/// Random typed programs, each with `CYCLES` input lines for its top. A
/// builder fault gets no lines; its verdict is a tooling error.
pub(super) fn cases() -> impl Strategy<Value = Case> {
    typed().prop_flat_map(|program| {
        let lines = match &program {
            Ok(program) => lines(program.ports(), CYCLES).boxed(),
            Err(_) => Just(Vec::new()).boxed(),
        };
        (Just(program), lines)
    })
}

/// `None` if the front ends agree on `case` and the generator, else the
/// message of the disagreement or of a tool failure. A tooling error, and
/// a fault of the builder, is an `Err`.
pub(super) fn verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<String>> {
    verdict_of(try_verdict(tools, dir, case))
}

fn try_verdict(tools: &Tools, dir: &Path, case: &Case) -> Result<Option<String>> {
    let (program, input) = case;
    let program = program
        .as_ref()
        .map_err(|e| anyhow::Error::new(e.clone()))?;
    let file = write(dir, "typed.si", &program.text())?;
    let top = program.top();
    if let Some(message) = validated(tools, &file, &top)? {
        return Ok(Some(message));
    }
    let (expr, value) = program.probe();
    let traces = [
        Trace {
            tool: "gen",
            lines: vec![value],
        },
        eval_trace("silicon", &tools.silicon, &file, &expr)?,
        eval_trace("lean", &tools.lean, &file, &expr)?,
    ];
    if let Some((_, message)) = difference(&traces) {
        return Ok(Some(format!("eval `{expr}`: {message}")));
    }
    let traces = [
        cost_trace("silicon", &tools.silicon, &file, &top)?,
        cost_trace("lean", &tools.lean, &file, &top)?,
    ];
    if let Some((_, message)) = difference(&traces) {
        return Ok(Some(format!("cost: {message}")));
    }
    let twin = twin(program);
    let names = twin.static_names();
    if !names.is_empty() {
        bail!(
            "the twin keeps the static names {names:?}, a fault of the builder:\n{}",
            twin.text
        );
    }
    let twin_file = write(dir, "twin.si", &twin.text)?;
    let stdin = stdin(input.iter().map(String::as_str));
    let traces = [
        run_trace("silicon", &tools.silicon, &file, &top, &stdin)?,
        run_trace("lean", &tools.lean, &file, &top, &stdin)?,
        run_trace(
            "silicon twin",
            &tools.silicon,
            &twin_file,
            &twin.top,
            &stdin,
        )?,
        run_trace("lean twin", &tools.lean, &twin_file, &twin.top, &stdin)?,
    ];
    if let Some(message) = compare(&traces) {
        return Ok(Some(format!("run: {message}")));
    }
    Ok(validated(tools, &twin_file, &twin.top)?.map(|m| format!("twin: {m}")))
}

/// The trace of `eval` for the expression `expr` in the file scope of `file`.
fn eval_trace(tool: &'static str, binary: &Path, file: &Path, expr: &str) -> Result<Trace> {
    let stdout = output(Command::new(binary).arg("eval").arg(file).arg(expr), "")?;
    Ok(Trace {
        tool,
        lines: stdout.lines().map(str::to_owned).collect(),
    })
}

/// The trace of `cost` for the top selection `top` of `file`. A nonzero
/// exit is a tool failure.
fn cost_trace(tool: &'static str, binary: &Path, file: &Path, top: &str) -> Result<Trace> {
    let stdout = output(
        Command::new(binary)
            .arg("cost")
            .arg(file)
            .args(["--top", top]),
        "",
    )?;
    Ok(Trace {
        tool,
        lines: stdout.lines().map(str::to_owned).collect(),
    })
}

/// Prints the failure of seed `seed`: the message, the reproducer of the
/// program, the twin, the probe, and the repeat command. The `STEP`
/// outputs come from `silicon-check run`, the reference elaborator. A
/// spawn or run error of it is an `Err`.
pub(super) fn report(
    tools: &Tools,
    dir: &Path,
    seed: u64,
    case: &Case,
    message: &str,
) -> Result<()> {
    println!("FAIL seed {seed} (typed): {message}");
    // A failure has a program: a builder fault is an error, not a failure.
    let (Ok(program), input) = case else {
        return Ok(());
    };
    let source = program.text();
    let top = program.top();
    let file = write(dir, "report.si", &source)?;
    let trace = run_trace(
        "lean",
        &tools.lean,
        &file,
        &top,
        &stdin(input.iter().map(String::as_str)),
    )?;
    if trace.lines.len() != input.len() {
        bail!(
            "{} gave {} output lines for {} input lines",
            tools.lean.display(),
            trace.lines.len(),
            input.len()
        );
    }
    let steps: Vec<(String, String)> = input.iter().cloned().zip(trace.lines).collect();
    print!("{}", reproducer(&source, &top, &steps));
    let twin = twin(program);
    print!("// twin\n// TOP {}\n{}", twin.top, twin.text);
    let (expr, value) = program.probe();
    println!("// probe: eval `{expr}` gives `{value}` in the generator");
    println!("Run `{}` to repeat it.", repeat(Mode::Typed, seed));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diff::runner;
    use proptest::strategy::ValueTree;

    fn case(seed: u64) -> Case {
        cases().new_tree(&mut runner(seed)).unwrap().current()
    }

    #[test]
    fn a_run_error_in_the_report_is_a_tooling_error() {
        let dir = tempfile::tempdir().unwrap();
        let missing = dir.path().join("no-such-tool");
        let tools = Tools {
            lean: missing.clone(),
            silicon: missing,
        };
        let error = report(&tools, dir.path(), 7, &case(7), "x").unwrap_err();
        assert!(format!("{error:#}").contains("no-such-tool"), "{error:#}");
    }

    #[test]
    fn typed_cases_are_deterministic() {
        let (program_a, lines_a) = case(7);
        let (program_b, lines_b) = case(7);
        assert_eq!(program_a.unwrap().text(), program_b.unwrap().text());
        assert_eq!(lines_a, lines_b);
        assert_eq!(lines_a.len(), CYCLES);
    }

    #[test]
    fn typed_lines_follow_the_top() {
        for seed in 1..=20 {
            let (program, lines) = case(seed);
            let program = program.unwrap();
            let ports = program.ports();
            for line in &lines {
                let body = line.strip_prefix("in=(").and_then(|l| l.strip_suffix(')'));
                let body = body.unwrap_or_else(|| panic!("seed {seed}: {line}"));
                let rest = if let Some(rest) = body.strip_prefix("clock$0rst ") {
                    assert!(ports.clocked, "seed {seed}: {line}");
                    rest.split_once(' ').map_or("", |(_, rest)| rest)
                } else {
                    assert!(!ports.clocked, "seed {seed}: {line}");
                    body
                };
                let words: Vec<&str> = rest.split_whitespace().collect();
                assert_eq!(words.len(), 2 * ports.inputs.len(), "seed {seed}: {line}");
            }
        }
    }
}
