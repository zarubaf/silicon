//! `cargo xtask lec`: the LEC of spec section 8.1 over `tests/corpus`. It
//! compares the Lean reference with the Verilog of `silicon` (main), with the
//! MLIR of `silicon lower` (lowering), and each Rust memory model with the
//! Lean model of its configuration (model).

mod mlir;
mod sv;
mod tools;

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, ensure};

use crate::repo::Repo;
use crate::{corpus, lean_check, silicon};
use tools::Verdict;

/// The skip reason for a design that `--externalize-registers` cannot take.
const SELF_REGISTER: &str = "#20: a register is its own next value";

/// The result of one check of one file.
#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Pass,
    /// The tool output or the error.
    Fail(String),
    Skip(&'static str),
}

impl From<Result<Verdict>> for Outcome {
    fn from(result: Result<Verdict>) -> Self {
        match result {
            Ok(Verdict::Equal) => Outcome::Pass,
            Ok(Verdict::Differ(output)) => Outcome::Fail(output),
            Err(e) => Outcome::Fail(format!("{e:#}")),
        }
    }
}

/// The two compilers under comparison.
struct Binaries {
    lean: PathBuf,
    rust: PathBuf,
}

impl Binaries {
    fn lean(&self, args: &[&str], file: &Path) -> Result<String> {
        output(&self.lean, args, file)
    }

    /// The LEC compares `silicon` with the Lean reference itself, so the
    /// validation of `silicon` would run the same checker twice.
    fn rust(&self, args: &[&str], file: &Path) -> Result<String> {
        let args: Vec<&str> = args.iter().copied().chain(["--no-validate"]).collect();
        output(&self.rust, &args, file)
    }
}

fn output(binary: &Path, args: &[&str], file: &Path) -> Result<String> {
    let mut all: Vec<&OsStr> = args.iter().map(OsStr::new).collect();
    all.push(file.as_os_str());
    tools::run(binary, &all, "")
}

/// Runs each check on each file of the corpus and prints one line for each.
/// Returns whether no check failed.
pub fn run(repo: &Repo) -> Result<bool> {
    tools::require()?;
    let Some(lean) = lean_check::build(repo)? else {
        return Ok(false);
    };
    let Some(rust) = silicon::build(&repo.root)? else {
        return Ok(false);
    };
    let bins = Binaries { lean, rust };
    let mut seen = BTreeSet::new();
    let mut passed = true;
    for file in corpus::files(repo) {
        let checks = fetch(&bins, &repo.root.join(&file))
            .and_then(|outputs| checks(&outputs, &mut seen))
            .unwrap_or_else(|e| vec![("setup".to_owned(), Outcome::Fail(format!("{e:#}")))]);
        for (check, outcome) in checks {
            let file = file.display();
            match outcome {
                Outcome::Pass => println!("PASS {file} {check}"),
                Outcome::Skip(why) => println!("SKIP {file} {check} ({why})"),
                Outcome::Fail(why) => {
                    passed = false;
                    println!("FAIL {file} {check}\n{}", why.trim_end());
                }
            }
        }
    }
    Ok(passed)
}

/// The outputs of both compilers for one file.
struct Outputs {
    /// The declared top module of the design.
    top: String,
    /// `silicon-check lower`.
    reference: String,
    /// `silicon-check lower --models`.
    lean_models: String,
    /// `silicon lower`.
    rust_lower: String,
    /// `silicon verilog`.
    rust_verilog: String,
    /// `silicon verilog --models`.
    rust_models: String,
}

fn fetch(bins: &Binaries, file: &Path) -> Result<Outputs> {
    let src =
        std::fs::read_to_string(file).with_context(|| format!("cannot read {}", file.display()))?;
    Ok(Outputs {
        top: design_top(&src)?,
        reference: bins.lean(&["lower"], file)?,
        lean_models: bins.lean(&["lower", "--models"], file)?,
        rust_lower: bins.rust(&["lower"], file)?,
        rust_verilog: bins.rust(&["verilog"], file)?,
        rust_models: bins.rust(&["verilog", "--models"], file)?,
    })
}

/// The name in the header `(design NAME` of the source `src`. The compilers
/// are under test, so this reader parses only the header. It skips
/// whitespace and `;` comments before the header.
fn design_top(src: &str) -> Result<String> {
    let mut rest = src.trim_start();
    while rest.starts_with(';') {
        rest = rest.split_once('\n').map_or("", |(_, r)| r).trim_start();
    }
    let name = rest
        .strip_prefix('(')
        .map(str::trim_start)
        .and_then(|r| r.strip_prefix("design"))
        .filter(|r| r.starts_with(char::is_whitespace))
        .map(str::trim_start)
        .context("the source does not start with `(design NAME`")?;
    let end = name
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$'))
        .unwrap_or(name.len());
    let name = &name[..end];
    ensure!(
        name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_'),
        "the `design` header has no valid name"
    );
    Ok(name.to_owned())
}

/// The checks of one file. A memory configuration that `seen` holds has its
/// model check already.
fn checks(outputs: &Outputs, seen: &mut BTreeSet<String>) -> Result<Vec<(String, Outcome)>> {
    let top = &outputs.top;
    ensure!(
        mlir::defines(&outputs.reference, top),
        "the Lean reference has no module `{top}`, the declared top"
    );
    let models = mlir::modules(&outputs.lean_models)?;
    let lean = mlir::defined(&outputs.reference, &models).context("the Lean reference")?;
    let mut out = Vec::new();
    if mlir::has_self_register(&lean) {
        out.push(("main".to_owned(), Outcome::Skip(SELF_REGISTER)));
        out.push(("lowering".to_owned(), Outcome::Skip(SELF_REGISTER)));
    } else {
        let sv = format!(
            "{}{}{}",
            outputs.rust_verilog,
            outputs.rust_models,
            mlir::verilog_stand_ins(&outputs.reference)?
        );
        let main = tools::import(&sv, top).and_then(|rust| tools::compare(&lean, &rust, top));
        out.push(("main".to_owned(), main.into()));
        let lowering = mlir::defined(&outputs.rust_lower, &models)
            .context("the Rust lowering")
            .and_then(|rust| tools::compare(&lean, &rust, top));
        out.push(("lowering".to_owned(), lowering.into()));
    }
    out.extend(model_checks(&models, &outputs.rust_models, seen));
    Ok(out)
}

/// The third LEC: each new Rust memory model against the Lean model of its
/// configuration.
fn model_checks(
    models: &BTreeMap<String, String>,
    rust_models: &str,
    seen: &mut BTreeSet<String>,
) -> Vec<(String, Outcome)> {
    let mut out = Vec::new();
    for (name, model) in models {
        if !seen.insert(name.clone()) {
            continue;
        }
        let outcome = if mlir::has_self_register(model) {
            Outcome::Skip(SELF_REGISTER)
        } else {
            tools::import(rust_models, name)
                .and_then(|rust| tools::compare(model, &rust, name))
                .into()
        };
        out.push((format!("model {name}"), outcome));
    }
    out
}

#[cfg(test)]
mod tests {
    use backend_circt::{lower, verilog};
    use core_ir::check::check;
    use core_ir::text::parse;

    use super::*;

    const REG_STATE: &str = include_str!("../../tests/corpus/reg_state.sil");

    /// The top `top` is `q = a`. The unused module `wrap` instantiates it and
    /// discards its output. The unused module `other` is independent.
    const UNUSED: &str = "\
; An unused parent.
(design top
  (module wrap
    (input a (bits 4))
    (output z (bits 4))
    (inst t top (a a))
    (assign z (const 4 0)))
  (module other
    (input b (bits 2))
    (output w (bits 2))
    (assign w b))
  (module top
    (input a (bits 4))
    (output q (bits 4))
    (assign q a)))
";

    /// The outputs for `src`, with the Rust lowering as the reference.
    /// `rust_lower` replaces the MLIR of `silicon lower`, and `verilog_of`
    /// is the MLIR behind `silicon verilog`.
    fn outputs(src: &str, rust_lower: &str, verilog_of: &str) -> Outputs {
        Outputs {
            top: design_top(src).unwrap(),
            reference: reference(src),
            lean_models: String::new(),
            rust_lower: rust_lower.to_owned(),
            rust_verilog: verilog(verilog_of).unwrap(),
            rust_models: String::new(),
        }
    }

    fn reference(src: &str) -> String {
        lower(&check(&parse(src).unwrap()).unwrap())
    }

    fn verdicts(outputs: &Outputs) -> Vec<(String, bool)> {
        checks(outputs, &mut BTreeSet::new())
            .unwrap()
            .into_iter()
            .map(|(check, outcome)| (check, outcome == Outcome::Pass))
            .collect()
    }

    fn pass(main: bool, lowering: bool) -> Vec<(String, bool)> {
        vec![("main".to_owned(), main), ("lowering".to_owned(), lowering)]
    }

    /// Each mutation fails the check that reads the mutated output, and only
    /// that check.
    fn assert_seeded(src: &str, good: &str, bad: &str) {
        assert_ne!(bad, good);
        assert_eq!(verdicts(&outputs(src, good, good)), pass(true, true));
        assert_eq!(verdicts(&outputs(src, bad, good)), pass(true, false));
        assert_eq!(verdicts(&outputs(src, good, bad)), pass(false, true));
        assert_eq!(verdicts(&outputs(src, bad, bad)), pass(false, false));
    }

    /// The mutation of spec section 9 in the Rust lowering.
    #[test]
    fn a_seeded_bug_fails_the_check_of_its_output() {
        let good = reference(REG_STATE);
        let bad = good.replace("seq.compreg %sum,", "seq.compreg %r_state,");
        assert_seeded(REG_STATE, &good, &bad);
    }

    /// An unused module that instantiates the declared top hides no bug of
    /// the top, and an independent unused module is no setup failure.
    #[test]
    fn the_declared_top_is_compared() {
        let good = reference(UNUSED);
        let bad = good.replace(
            "hw.output %a : i4",
            "%silicon_zero = hw.constant 0 : i4\n  hw.output %silicon_zero : i4",
        );
        assert_seeded(UNUSED, &good, &bad);
    }

    #[test]
    fn the_design_header_gives_the_top() {
        assert_eq!(design_top(UNUSED).unwrap(), "top");
        assert_eq!(design_top("(design a$1_ (module x))").unwrap(), "a$1_");
        for bad in [
            "(module top)",
            "; only a comment",
            "(design (module x))",
            "(designx top",
        ] {
            assert!(design_top(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn a_model_without_a_write_port_is_skipped_once() {
        let model = "hw.module @silicon_mem_1x4_r1w0(in %clk : !seq.clock) {\n  \
                     %silicon_reg_mem = seq.compreg %silicon_reg_mem, %clk : !hw.array<2xi4>\n  \
                     hw.output\n}\n";
        let models = mlir::modules(model).unwrap();
        let mut seen = BTreeSet::new();
        assert_eq!(
            model_checks(&models, "", &mut seen),
            [(
                "model silicon_mem_1x4_r1w0".to_owned(),
                Outcome::Skip(SELF_REGISTER)
            )]
        );
        assert_eq!(model_checks(&models, "", &mut seen), []);
    }
}
