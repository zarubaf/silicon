//! The differential tests of spec section 8.2. The designs of `tests/corpus`
//! and random designs, with random inputs, drive the Lean interpreter, the
//! Rust interpreter, and `arcilator` on the Lean reference MLIR. Each tool
//! starts from the all-zero state.

mod arcilator;

use std::fmt;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, anyhow};
use core_ir::check::check;
use core_ir::r#gen;
use core_ir::interp::Inputs;
use core_ir::text::{parse, print};
use core_ir::typed;
use core_ir::vectors::parse_input;
use proptest::collection::vec;
use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::{
    Config, RngAlgorithm, RngSeed, TestRng, TestRunner, noop_result_cache,
};

use crate::repo::Repo;
use crate::{corpus, lean_check, silicon};

/// The clock cycles of each design.
const CYCLES: usize = 8;

/// The `out=` lines, without LF, that one tool prints for one design.
#[derive(Debug, PartialEq, Eq)]
struct Trace {
    tool: &'static str,
    lines: Vec<String>,
}

/// One design with its input lines.
struct Case {
    /// The origin of the design, for the report.
    name: String,
    /// The command that repeats the case.
    repeat: String,
    text: String,
    top: typed::Module,
    lines: Vec<String>,
    inputs: Vec<Inputs>,
}

/// A tool ran and rejected the design or gave a malformed result. This is a
/// failure of the case, not of the tooling.
#[derive(Debug)]
struct ToolFailure(String);

impl fmt::Display for ToolFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ToolFailure {}

/// The tools under test. The Rust side is `silicon run`, not the
/// interpreter of `core-ir` in this process. Thus the test also covers the
/// shipped command: its vector parser, its output printer, and its exit code.
struct Tools {
    lean: PathBuf,
    silicon: PathBuf,
}

/// Builds the two interpreters. Then it runs each file of the corpus with
/// the inputs of `seed`, and `count` random designs from the seeds `seed`,
/// `seed + 1`, and so on. Returns whether all cases agree. The run stops at
/// the first failure. A tooling error, for example a missing tool, is an
/// error, not a failure.
pub fn run(repo: &Repo, seed: u64, count: u64) -> Result<bool> {
    let Some(lean) = lean_check::build(repo)? else {
        return Ok(false);
    };
    let Some(silicon) = silicon::build(&repo.root)? else {
        return Ok(false);
    };
    let tools = Tools { lean, silicon };
    let dir = tempfile::tempdir().context("cannot make a temporary directory")?;
    let corpus = corpus(repo, seed)?;
    let random = (0..count).map(|k| generate(seed.wrapping_add(k)));
    for case in corpus.into_iter().map(Ok).chain(random) {
        if !tools.agree(&case?, dir.path())? {
            return Ok(false);
        }
    }
    println!(
        "diff: the corpus and {count} random designs agree (seeds {seed} to {})",
        seed.wrapping_add(count - 1)
    );
    Ok(true)
}

/// A test runner with the random numbers of `seed`. Each field of the
/// configuration is explicit, so no `PROPTEST_` variable changes the cases.
fn runner(seed: u64) -> TestRunner {
    let mut bytes = [0; 32];
    bytes[..8].copy_from_slice(&seed.to_le_bytes());
    let config = Config {
        cases: 1,
        max_local_rejects: 65_536,
        max_global_rejects: 1024,
        max_flat_map_regens: 1_000_000,
        failure_persistence: None,
        source_file: None,
        test_name: None,
        max_shrink_time: 0,
        max_shrink_iters: 0,
        max_default_size_range: 100,
        result_cache: noop_result_cache,
        verbose: 0,
        rng_algorithm: RngAlgorithm::ChaCha,
        rng_seed: RngSeed::Fixed(seed),
        _non_exhaustive: (),
    };
    TestRunner::new_with_rng(config, TestRng::from_seed(RngAlgorithm::ChaCha, &bytes))
}

/// The case of the design `text` with `CYCLES` input lines from
/// `gen::inputs` and `runner`.
fn case(
    name: String,
    repeat: String,
    text: String,
    design: &typed::Design,
    runner: &mut TestRunner,
) -> Result<Case> {
    let top = design
        .modules
        .get(design.top.index())
        .with_context(|| format!("{name} has no top module"))?
        .clone();
    let lines = vec(r#gen::inputs(&top), CYCLES)
        .new_tree(runner)
        .map_err(|e| anyhow!("cannot generate inputs for {name}: {e}"))?
        .current();
    let inputs = lines
        .iter()
        .map(|line| parse_input(line, &top).map_err(|e| anyhow!("{name}: {line}: {e}")))
        .collect::<Result<_>>()?;
    Ok(Case {
        name,
        repeat,
        text,
        top,
        lines,
        inputs,
    })
}

/// The case of `seed`: a design from `gen::design` and its inputs.
fn generate(seed: u64) -> Result<Case> {
    let mut runner = runner(seed);
    let design = r#gen::design()
        .new_tree(&mut runner)
        .map_err(|e| anyhow!("cannot generate a design for seed {seed}: {e}"))?
        .current();
    let text = print(&design);
    let typed = check(&design)
        .map_err(|e| anyhow!("the generated design fails the checker: {e}\n{text}"))?;
    let name = format!("seed {seed}");
    let repeat = format!("cargo xtask diff --seed {seed} --count 1");
    case(name, repeat, text, &typed, &mut runner)
}

/// The cases of the tracked files of the corpus, with the inputs of `seed`.
/// A design with an extern is a visible skip: the interpreters reject it
/// with `E014` (spec section 5.4).
fn corpus(repo: &Repo, seed: u64) -> Result<Vec<Case>> {
    let mut runner = runner(seed);
    let mut cases = Vec::new();
    for path in &corpus::files(repo) {
        let name = path.display().to_string();
        let text = std::fs::read_to_string(repo.root.join(path))
            .with_context(|| format!("cannot read {name}"))?;
        let design = parse(&text)
            .and_then(|ast| check(&ast))
            .map_err(|e| anyhow!("{name}: {e}"))?;
        if !design.externs.is_empty() {
            println!(
                "SKIP {name}: the design has an extern, and the interpreters reject it (E014)"
            );
            continue;
        }
        let repeat = format!("cargo xtask diff --seed {seed} --count 1");
        cases.push(case(name, repeat, text, &design, &mut runner)?);
    }
    Ok(cases)
}

impl Tools {
    /// Whether the three tools agree on `case`. A failure prints the case as
    /// a `tests/run` file. The files go to `dir`.
    fn agree(&self, case: &Case, dir: &Path) -> Result<bool> {
        let failure = match self.traces(case, dir) {
            Ok(traces) => compare(&traces).map(|message| (message, Some(traces))),
            Err(error) if error.downcast_ref::<ToolFailure>().is_some() => {
                Some((format!("{error:#}"), None))
            }
            Err(error) => return Err(error),
        };
        let Some((message, traces)) = failure else {
            return Ok(true);
        };
        println!("FAIL {}: {message}", case.name);
        let expected = traces.as_deref().and_then(<[Trace]>::first);
        print!("{}", reproducer(&case.text, &case.lines, expected));
        println!("Run `{}` to repeat it.", case.repeat);
        Ok(false)
    }

    /// The traces of the three tools for `case`. The files go to `dir`.
    fn traces(&self, case: &Case, dir: &Path) -> Result<Vec<Trace>> {
        let design = dir.join("design.sil");
        std::fs::write(&design, &case.text)
            .with_context(|| format!("cannot write {}", design.display()))?;
        let mut stdin = case.lines.join("\n");
        stdin.push('\n');
        let interpreter = |tool: &'static str, binary: &Path| -> Result<Trace> {
            let stdout = output(Command::new(binary).arg("run").arg(&design), &stdin)?;
            Ok(Trace {
                tool,
                lines: stdout.lines().map(str::to_owned).collect(),
            })
        };
        let lowered = output(Command::new(&self.lean).arg("lower").arg(&design), "")?;
        let models = output(
            Command::new(&self.lean)
                .args(["lower", "--models"])
                .arg(&design),
            "",
        )?;
        let simulation = arcilator::simulation_mlir(&lowered, &models, &case.top.name);
        Ok(vec![
            interpreter("lean", &self.lean)?,
            interpreter("silicon", &self.silicon)?,
            Trace {
                tool: "arcilator",
                lines: arcilator::run(dir, &simulation, &case.top, &case.inputs)?,
            },
        ])
    }
}

/// The stdout of `command` with `stdin` as its input. A failed exit is a
/// [`ToolFailure`] with the stdout and the stderr of the command. A command
/// that does not start is a tooling error.
fn output(command: &mut Command, stdin: &str) -> Result<String> {
    let name = format!("{command:?}");
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("cannot run {name}"))?;
    let mut pipe = child.stdin.take().context("no stdin pipe")?;
    let input = stdin.to_owned();
    // A separate writer keeps a full stdout pipe from blocking the input.
    let writer = std::thread::spawn(move || pipe.write_all(input.as_bytes()));
    let result = child
        .wait_with_output()
        .with_context(|| format!("cannot wait for {name}"))?;
    let written = writer
        .join()
        .map_err(|_| anyhow!("the stdin writer of {name} panicked"))?;
    let stdout = String::from_utf8_lossy(&result.stdout).into_owned();
    // A tool that fails early closes its input, so its exit status comes
    // before the write error.
    if !result.status.success() {
        return Err(ToolFailure(format!(
            "{name} failed with {}\nstdout:\n{stdout}stderr:\n{}",
            result.status,
            String::from_utf8_lossy(&result.stderr)
        ))
        .into());
    }
    written.with_context(|| format!("cannot write the input of {name}"))?;
    Ok(stdout)
}

/// The first disagreement of a trace with the first trace, or `None`.
fn compare(traces: &[Trace]) -> Option<String> {
    let (reference, others) = traces.split_first()?;
    for other in others {
        let cycles = reference.lines.len().max(other.lines.len());
        for cycle in 0..cycles {
            let line = |trace: &'_ Trace| -> String {
                trace
                    .lines
                    .get(cycle)
                    .map_or("no line".to_owned(), String::clone)
            };
            if reference.lines.get(cycle) != other.lines.get(cycle) {
                return Some(format!(
                    "cycle {cycle}: {} prints `{}`, {} prints `{}`",
                    reference.tool,
                    line(reference),
                    other.tool,
                    line(other),
                ));
            }
        }
    }
    None
}

/// The design `text` and its input `lines` as the text of a `tests/run`
/// file, with the outputs of the trace `expected`.
fn reproducer(text: &str, lines: &[String], expected: Option<&Trace>) -> String {
    let steps = lines.iter().enumerate().map(|(cycle, line)| {
        match expected.and_then(|trace| trace.lines.get(cycle)) {
            Some(out) => format!("; STEP {line} {out}\n"),
            None => format!("; STEP {line}\n"),
        }
    });
    std::iter::once(text.to_owned()).chain(steps).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn trace(tool: &'static str, lines: &[&str]) -> Trace {
        Trace {
            tool,
            lines: lines.iter().map(|&line| line.to_owned()).collect(),
        }
    }

    #[test]
    fn equal_traces_agree() {
        let traces = [
            trace("lean", &["out=(q 0)", "out=(q 1)"]),
            trace("silicon", &["out=(q 0)", "out=(q 1)"]),
            trace("arcilator", &["out=(q 0)", "out=(q 1)"]),
        ];
        assert_eq!(compare(&traces), None);
    }

    #[test]
    fn a_wrong_value_of_one_tool_is_a_disagreement() {
        let traces = [
            trace("lean", &["out=(q 0)", "out=(q 1)"]),
            trace("silicon", &["out=(q 0)", "out=(q 1)"]),
            trace("arcilator", &["out=(q 0)", "out=(q 2)"]),
        ];
        assert_eq!(
            compare(&traces).as_deref(),
            Some("cycle 1: lean prints `out=(q 1)`, arcilator prints `out=(q 2)`")
        );
    }

    #[test]
    fn a_missing_line_is_a_disagreement() {
        let traces = [
            trace("lean", &["out=(q 0)", "out=(q 1)"]),
            trace("silicon", &["out=(q 0)"]),
        ];
        assert_eq!(
            compare(&traces).as_deref(),
            Some("cycle 1: lean prints `out=(q 1)`, silicon prints `no line`")
        );
    }

    #[test]
    fn the_same_seed_gives_the_same_case() {
        let (a, b) = (generate(7).unwrap(), generate(7).unwrap());
        assert_eq!((a.text, a.lines), (b.text, b.lines));
        assert_eq!(generate(7).unwrap().lines.len(), CYCLES);
    }

    #[test]
    fn the_reproducer_is_a_tests_run_file() {
        let lines = ["in=(a 1)".to_owned(), "in=(a 2)".to_owned()];
        let lean = trace("lean", &["out=(q 1)", "out=(q 2)"]);
        assert_eq!(
            reproducer("(design top)\n", &lines, Some(&lean)),
            "(design top)\n; STEP in=(a 1) out=(q 1)\n; STEP in=(a 2) out=(q 2)\n"
        );
        assert_eq!(
            reproducer("(design top)\n", &lines, None),
            "(design top)\n; STEP in=(a 1)\n; STEP in=(a 2)\n"
        );
    }

    #[test]
    fn a_missing_tool_is_a_tooling_error() {
        let error = output(&mut Command::new("silicon-no-such-tool"), "").unwrap_err();
        assert!(error.downcast_ref::<ToolFailure>().is_none(), "{error:#}");
    }

    #[test]
    fn a_failed_exit_is_a_failure_of_the_case() {
        let error = output(&mut Command::new("false"), "in=()\n").unwrap_err();
        assert!(error.downcast_ref::<ToolFailure>().is_some(), "{error:#}");
    }
}
