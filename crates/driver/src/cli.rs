// SPDX-License-Identifier: Apache-2.0
//! The commands of `silicon` and their exit codes (spec section 6.4.2).

use std::fmt;
use std::fs;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use backend_circt::{ToolError, lower, memory_configs, memory_model, verilog};
use clap::{Args, Parser, Subcommand};
use core_ir::check::check;
use core_ir::diag::Diagnostic;
use core_ir::interp::Sim;
use core_ir::text::{canonicalize, parse, print};
use core_ir::vectors::{parse_input, print_output};
use core_ir::{ast, typed};
use parse::ast::Pos;

use crate::validate::{Elaborated, Verdict, validate, validate_elaboration};

#[derive(Parser)]
#[command(name = "silicon", about = "The Silicon core IR tool")]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

/// The option of the commands that emit from the core IR.
#[derive(Args)]
pub struct Validation {
    /// Skip the check by the Lean `silicon-check`, whose path is in `SILICON_CHECK`.
    #[arg(long)]
    no_validate: bool,
}

#[derive(Subcommand)]
pub enum Command {
    /// Check a design: print `ok` or the first error.
    Check { file: PathBuf },
    /// Print the canonical text of a checked design.
    Fmt { file: PathBuf },
    /// Read `in=` lines from stdin and print one `out=` line for each. With `--top`, the file
    /// is a Silicon source file, and the lines are source vectors.
    Run {
        #[command(flatten)]
        budget: Budgets,
        file: PathBuf,
        /// The top selection of a source file: a module name, then literal arguments in
        /// parentheses.
        #[arg(long, allow_hyphen_values = true)]
        top: Option<String>,
    },
    /// Print the MLIR of a checked design, with each memory as an extern.
    Lower {
        #[command(flatten)]
        validation: Validation,
        file: PathBuf,
    },
    /// Print the canonical serialization of a static expression in the file scope of a
    /// Silicon source file, or the first error.
    Eval {
        #[command(flatten)]
        budget: Budgets,
        file: PathBuf,
        /// The expression, in source syntax.
        #[arg(allow_hyphen_values = true)]
        expr: String,
    },
    /// Print the canonical core IR of a Silicon source file, or the first error.
    Elab {
        #[command(flatten)]
        budget: Budgets,
        file: PathBuf,
        /// The top selection: a module name, then literal arguments in parentheses.
        #[arg(long, allow_hyphen_values = true)]
        top: String,
    },
    /// Elaborate a Silicon source file and compare the canonical core IR with `out`: print
    /// `ok`, or the first line that differs.
    Validate {
        #[command(flatten)]
        budget: Budgets,
        file: PathBuf,
        /// The core IR to compare, such as the output of `elab`.
        out: PathBuf,
        /// The top selection: a module name, then literal arguments in parentheses.
        #[arg(long, allow_hyphen_values = true)]
        top: String,
    },
    /// Elaborate a Silicon source file and write `F.sil` and `F.sv` next to it, or at `--out`.
    /// The Lean `silicon-check` validates the elaboration first. Print `validated` or
    /// `not validated`, or the first error.
    Build {
        #[command(flatten)]
        budget: Budgets,
        #[command(flatten)]
        validation: Validation,
        file: PathBuf,
        /// The top selection: a module name, then literal arguments in parentheses.
        #[arg(long, allow_hyphen_values = true)]
        top: String,
        /// The path of both artifacts without the extension `.sil` or `.sv`.
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Print the fuel that the elaboration of a Silicon source file and its lowering use, then
    /// the units of each instantiation, or the first error.
    Cost {
        #[command(flatten)]
        budget: Budgets,
        file: PathBuf,
        /// The top selection: a module name, then literal arguments in parentheses.
        #[arg(long, allow_hyphen_values = true)]
        top: String,
    },
    /// Print the AST of a Silicon source file, or the first syntax error.
    Parse {
        /// The most depth of brackets, and the most height of an expression or a type.
        #[arg(long, default_value_t = syntax_depth::DEFAULT, value_parser = syntax_depth::parse)]
        syntax_depth: usize,
        file: PathBuf,
    },
    /// Print the Verilog of a checked design through CIRCT.
    Verilog {
        /// Print one memory model for each memory configuration instead.
        #[arg(long)]
        models: bool,
        #[command(flatten)]
        validation: Validation,
        file: PathBuf,
    },
}

/// The budgets of an elaboration (front-end spec, section 5.4).
#[derive(Args)]
pub struct Budgets {
    /// The most depth of brackets, and the most height of an expression or a type.
    #[arg(long, default_value_t = syntax_depth::DEFAULT, value_parser = syntax_depth::parse)]
    syntax_depth: usize,
    /// The cost units that the elaboration can use.
    #[arg(long, default_value_t = elab::Budget::default().fuel, value_parser = natural)]
    fuel: u64,
    /// The most active calls, constants in progress, and instantiations in progress.
    #[arg(long, default_value_t = elab::Budget::default().depth, value_parser = natural)]
    depth: u64,
}

impl Budgets {
    fn elab(&self) -> elab::Budget {
        elab::Budget {
            fuel: self.fuel,
            depth: self.depth,
        }
    }
}

/// A natural number as `silicon-check` reads it: decimal digits, with one `_` between two
/// digits. A number above `u64::MAX` is `u64::MAX`, which no elaboration can use up.
fn natural(text: &str) -> Result<u64, String> {
    let groups: Vec<&str> = text.split('_').collect();
    if groups
        .iter()
        .any(|g| g.is_empty() || !g.bytes().all(|b| b.is_ascii_digit()))
    {
        return Err(format!("`{text}` is not a natural number"));
    }
    let digits: String = groups.concat();
    Ok(digits.parse::<u64>().unwrap_or(u64::MAX))
}

/// The value of `--syntax-depth`.
mod syntax_depth {
    pub const DEFAULT: usize = parse::DEFAULT_SYNTAX_DEPTH;

    /// A number from 1 to the cap of the library.
    pub fn parse(text: &str) -> Result<usize, String> {
        match text.parse::<usize>() {
            Ok(depth) if (1..=parse::MAX_SYNTAX_DEPTH).contains(&depth) => Ok(depth),
            Ok(_) => Err(format!(
                "the syntax depth must be from 1 to {}",
                parse::MAX_SYNTAX_DEPTH
            )),
            Err(e) => Err(e.to_string()),
        }
    }
}

/// The exit code of a command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Exit {
    Success,
    DesignError,
    UsageError,
    /// A core error other than a cycle in the lowered design: a defect of the elaborator.
    Defect,
}

impl From<Exit> for ExitCode {
    fn from(exit: Exit) -> ExitCode {
        match exit {
            Exit::Success => ExitCode::SUCCESS,
            Exit::DesignError => ExitCode::from(1),
            Exit::UsageError => ExitCode::from(2),
            Exit::Defect => ExitCode::from(3),
        }
    }
}

/// The output text of a command and its exit code.
type Output = (String, Exit);

/// A usage error, an input error, or an output error, with its message.
struct Usage(String);

impl From<io::Error> for Usage {
    fn from(e: io::Error) -> Usage {
        Usage(e.to_string())
    }
}

impl From<ToolError> for Usage {
    fn from(e: ToolError) -> Usage {
        Usage(e.to_string())
    }
}

/// Runs `command`. Design errors and results go to `out`; a usage error goes
/// to stderr.
pub fn execute(command: &Command, input: impl BufRead, mut out: impl Write) -> Exit {
    match dispatch(command, input, &mut out) {
        Ok(exit) => exit,
        Err(Usage(message)) => {
            // A failed write to stderr has no better channel to report to.
            let _ = writeln!(io::stderr(), "silicon: {message}");
            Exit::UsageError
        }
    }
}

fn dispatch(command: &Command, input: impl BufRead, out: &mut impl Write) -> Result<Exit, Usage> {
    match command {
        Command::Check { file } => with_design(file, out, |_, _, out| {
            writeln!(out, "ok")?;
            Ok(Exit::Success)
        }),
        // The formatter prints the canonical form of the parsed design once
        // the checker accepts it.
        Command::Fmt { file } => with_design(file, out, |ast, _, out| {
            out.write_all(print(&canonicalize(&ast)).as_bytes())?;
            Ok(Exit::Success)
        }),
        Command::Run {
            file, top: None, ..
        } => with_design(file, out, |_, design, out| simulate(&design, input, out)),
        Command::Run {
            budget,
            file,
            top: Some(top),
        } => run_source(&read_source(file)?, top, budget, input, out),
        Command::Elab { budget, file, top } => {
            let (text, exit) = elab_source(&read_source(file)?, top, budget)?;
            out.write_all(text.as_bytes())?;
            Ok(exit)
        }
        Command::Validate {
            budget,
            file,
            out: sil,
            top,
        } => {
            let source = read_source(file)?;
            let sil = read_source(sil)?;
            let (text, exit) = validate_source(&source, top, &sil, budget)?;
            out.write_all(text.as_bytes())?;
            Ok(exit)
        }
        Command::Lower { validation, file } => {
            with_validated_design(file, validation, out, |_, design, out| {
                out.write_all(lower(&design).as_bytes())?;
                Ok(Exit::Success)
            })
        }
        Command::Build {
            budget,
            validation,
            file,
            top,
            out: prefix,
        } => {
            let source = read_source(file)?;
            let prefix = prefix.clone().unwrap_or_else(|| file.with_extension(""));
            let (text, exit) = build_source(file, &source, top, budget, validation, &prefix)?;
            out.write_all(text.as_bytes())?;
            Ok(exit)
        }
        Command::Eval { budget, file, expr } => {
            let (text, exit) = eval_source(&read_source(file)?, expr, budget)?;
            out.write_all(text.as_bytes())?;
            Ok(exit)
        }
        Command::Cost { budget, file, top } => {
            let (text, exit) = cost_source(&read_source(file)?, top, budget)?;
            out.write_all(text.as_bytes())?;
            Ok(exit)
        }
        Command::Parse { syntax_depth, file } => {
            let (text, exit) = parse_source(&read_source(file)?, *syntax_depth)?;
            out.write_all(text.as_bytes())?;
            Ok(exit)
        }
        Command::Verilog {
            models,
            validation,
            file,
        } => with_validated_design(file, validation, out, |_, design, out| {
            let mlir = if *models {
                memory_configs(&design).iter().map(memory_model).collect()
            } else {
                lower(&design)
            };
            out.write_all(verilog(&mlir)?.as_bytes())?;
            Ok(Exit::Success)
        }),
    }
}

/// The output and the exit code of `parse`: the AST dump, or the first syntax error as a line.
/// The front end recurses, so `parse` runs it on a thread with a stack for the depth. If the
/// machine cannot give the stack, the command fails before it parses.
fn parse_source(source: &str, depth: usize) -> Result<Output, Usage> {
    let parsed = parse::parse_with_depth(source, depth).map_err(|e| Usage(e.to_string()))?;
    if let Some(e) = parsed.errors().first() {
        return Ok(error_line(e.code, e.pos, &e.message));
    }
    let dump = parsed.dump().map_err(|e| Usage(e.to_string()))?;
    Ok((dump.unwrap_or_default(), Exit::Success))
}

/// A source file after the passes before elaboration, or the line of its first error. Each
/// pass runs on the front-end thread. If the machine cannot give a stack, the command fails.
fn load(source: &str, depth: usize) -> Result<Result<resolve::Resolved, Output>, Usage> {
    let parsed = parse::parse_with_depth(source, depth).map_err(|e| Usage(e.to_string()))?;
    let file = match resolve::resolve(parsed) {
        Ok(file) => file,
        Err(resolve::Failed::Parse(parsed)) => {
            return Ok(Err(match parsed.errors().first() {
                Some(e) => error_line(e.code, e.pos, &e.message),
                None => (String::new(), Exit::DesignError),
            }));
        }
        Err(resolve::Failed::Names(e)) => {
            return Ok(Err(first_line(&e, |e| (e.code, e.pos, &e.message))));
        }
        Err(resolve::Failed::Stack(e)) => return Err(stack(e)),
    };
    match typeck::check(file) {
        Ok(file) => Ok(Ok(file)),
        Err(typeck::Failed::Errors(e)) => Ok(Err(first_line(&e, |e| (e.code, e.pos, &e.message)))),
        Err(typeck::Failed::Stack(e)) => Err(stack(e)),
    }
}

fn stack(e: parse::StackError) -> Usage {
    Usage(e.to_string())
}

/// The output and the exit code of `eval`: the serialization of the value of `expr` in the
/// file scope of `source`, or the first error of the file, then of the expression.
fn eval_source(source: &str, expr: &str, budget: &Budgets) -> Result<Output, Usage> {
    let depth = budget.syntax_depth;
    let file = match load(source, depth)? {
        Ok(file) => file,
        Err(line) => return Ok(line),
    };
    let expr = match parse::parse_expr(expr, depth).map_err(|e| Usage(e.to_string()))? {
        Ok(expr) => expr,
        Err(e) => return Ok(first_line(&e, |e| (e.code, e.pos, &e.message))),
    };
    let expr = match resolve::resolve_expr(&file, expr).map_err(stack)? {
        Ok(expr) => expr,
        Err(e) => return Ok(first_line(&e, |e| (e.code, e.pos, &e.message))),
    };
    let expr = match typeck::check_expr(&file, expr) {
        Ok(expr) => expr,
        Err(typeck::Failed::Errors(e)) => {
            return Ok(first_line(&e, |e| (e.code, e.pos, &e.message)));
        }
        Err(typeck::Failed::Stack(e)) => return Err(stack(e)),
    };
    Ok(
        match elab::eval(&file, &expr, budget.elab()).map_err(stack)? {
            Ok((value, _)) => (value.serialize() + "\n", Exit::Success),
            Err(e) => error_line(e.code, e.pos, &e.message),
        },
    )
}

/// The elaboration of the top selection `top` of `source` and its lowering, or the output and
/// the exit code of the first failure. A top selection that is not a module name with
/// literal arguments is a usage error.
fn lowered(
    source: &str,
    top: &str,
    budget: &Budgets,
) -> Result<Result<(elab::Design, elab::Lowered), Output>, Usage> {
    let file = match load(source, budget.syntax_depth)? {
        Ok(file) => file,
        Err(line) => return Ok(Err(line)),
    };
    let design = match elab::elaborate(&file, top, budget.syntax_depth, budget.elab()) {
        Ok(Ok(design)) => design,
        Ok(Err(e)) => return Ok(Err(error_line(e.code, e.pos, &e.message))),
        Err(elab::Abort::Usage(message)) => return Err(Usage(message)),
        Err(elab::Abort::Stack(e)) => return Err(stack(e)),
    };
    Ok(match design.lower().map_err(stack)? {
        Ok(lowered) => Ok((design, lowered)),
        Err(f) => Err(failure(f)),
    })
}

/// A lowered design that passed the core check of pass 6.
struct Checked {
    design: elab::Design,
    lowered: elab::Lowered,
    typed: typed::Design,
}

/// `lowered`, then the core check of pass 6.
fn checked(source: &str, top: &str, budget: &Budgets) -> Result<Result<Checked, Output>, Usage> {
    Ok(match lowered(source, top, budget)? {
        Ok((design, lowered)) => match elab::check(&lowered.design) {
            Ok(typed) => Ok(Checked {
                design,
                lowered,
                typed,
            }),
            Err(f) => Err(failure(f)),
        },
        Err(line) => Err(line),
    })
}

/// The output of a failure of the lowering or of its check. A defect prints on stderr.
fn failure(f: elab::Failure) -> Output {
    match f {
        elab::Failure::Source(e) => error_line(e.code, e.pos, &e.message),
        elab::Failure::Defect(message) => defect(&message),
    }
}

fn defect(message: &str) -> Output {
    // A failed write to stderr has no better channel to report to.
    let _ = writeln!(io::stderr(), "silicon: defect of the elaborator: {message}");
    (String::new(), Exit::Defect)
}

/// The output and the exit code of `cost`: the fuel that the elaboration of the top
/// selection `top` and its lowering use, then the units of each instantiation by emitted
/// name, or the first error. It does not run the core check, so a design with a cycle has a
/// cost.
fn cost_source(source: &str, top: &str, budget: &Budgets) -> Result<Output, Usage> {
    Ok(match lowered(source, top, budget)? {
        Ok((_, lowered)) => (lowered.cost(), Exit::Success),
        Err(line) => line,
    })
}

/// The output and the exit code of `elab`: the canonical text of the lowered design.
fn elab_source(source: &str, top: &str, budget: &Budgets) -> Result<Output, Usage> {
    Ok(match checked(source, top, budget)? {
        Ok(c) => (canonical(&c.lowered.design), Exit::Success),
        Err(line) => line,
    })
}

fn canonical(design: &ast::Design) -> String {
    print(&canonicalize(design))
}

/// The output and the exit code of `validate` (section 8): elaborate the source, parse and
/// check `sil` with the core checker, then compare the canonical texts.
fn validate_source(source: &str, top: &str, sil: &str, budget: &Budgets) -> Result<Output, Usage> {
    let c = match checked(source, top, budget)? {
        Ok(c) => c,
        Err(line) => return Ok(line),
    };
    let raw = match parse(sil).and_then(|raw| check(&raw).map(|_| raw)) {
        Ok(raw) => raw,
        Err(diagnostic) => return Ok((format!("{diagnostic}\n"), Exit::DesignError)),
    };
    let reference = canonical(&c.lowered.design);
    let got = canonical(&raw);
    Ok(if reference == got {
        ("ok\n".to_owned(), Exit::Success)
    } else {
        (mismatch(&reference, &got) + "\n", Exit::DesignError)
    })
}

/// The output and the exit code of `build`: the core IR in `PREFIX.sil` and the Verilog in
/// `PREFIX.sv`. The Verilog comes from the text that Lean validates, and it is written after
/// the verdict. A Lean rejection of a source that Rust accepted is a defect of the Rust front
/// end, and it leaves no artifact. Every failure removes an old `PREFIX.sv`, so the two files
/// on disk never come from two builds.
fn build_source(
    file: &Path,
    source: &str,
    top: &str,
    budget: &Budgets,
    validation: &Validation,
    prefix: &Path,
) -> Result<Output, Usage> {
    let c = match checked(source, top, budget)? {
        Ok(c) => c,
        Err(line) => return Ok(line),
    };
    let (sil_path, sv_path) = (artifact(prefix, "sil"), artifact(prefix, "sv"));
    if [&sil_path, &sv_path].contains(&&file.to_path_buf()) {
        return Err(Usage(format!(
            "{}: the output path is the input file",
            file.display()
        )));
    }
    let sil = canonical(&c.lowered.design);
    // The backend gets the text that Lean checks, as `lower` and `verilog` do.
    let typed = match parse(&sil).and_then(|raw| check(&raw)) {
        Ok(typed) => typed,
        Err(diagnostic) => return Ok(defect(&diagnostic.to_string())),
    };
    // The tool runs before any file exists, so a missing tool leaves nothing behind.
    let sv = verilog(&lower(&typed))?;
    let _ = fs::remove_file(&sv_path);
    write_artifact(&sil_path, &sil)?;
    if validation.no_validate {
        write_artifact(&sv_path, &sv)?;
        return Ok(("not validated\n".to_owned(), Exit::Success));
    }
    let flags = [
        "--syntax-depth".to_owned(),
        budget.syntax_depth.to_string(),
        "--fuel".to_owned(),
        budget.fuel.to_string(),
        "--depth".to_owned(),
        budget.depth.to_string(),
    ];
    let verdict = validate_elaboration(source.as_bytes(), top, &sil_path, &flags);
    finish(verdict, &sil_path, &sv_path, &sv, &mut io::stderr())
}

/// The step after the verdict of Lean: write `sv_path` if Lean accepted. Otherwise remove both
/// artifacts, and a rejection is a defect of the Rust front end with the Lean text on `err`.
fn finish(
    verdict: Result<Elaborated, String>,
    sil_path: &Path,
    sv_path: &Path,
    sv: &str,
    err: &mut impl Write,
) -> Result<Output, Usage> {
    let remove = || {
        let _ = fs::remove_file(sil_path);
        let _ = fs::remove_file(sv_path);
    };
    match verdict {
        Ok(Elaborated::Accepted) => {
            write_artifact(sv_path, sv)?;
            Ok(("validated\n".to_owned(), Exit::Success))
        }
        Ok(Elaborated::Defect(report)) => {
            remove();
            // A failed write to stderr has no better channel to report to.
            let _ = write!(err, "silicon: defect of the front end: Lean disagrees: ");
            let _ = err.write_all(&report);
            Ok((String::new(), Exit::Defect))
        }
        Err(message) => {
            remove();
            Err(Usage(message))
        }
    }
}

/// The path of an artifact: the prefix, then `.` and the extension.
fn artifact(prefix: &Path, extension: &str) -> PathBuf {
    let mut path = prefix.as_os_str().to_owned();
    path.push(".");
    path.push(extension);
    PathBuf::from(path)
}

fn write_artifact(path: &Path, text: &str) -> Result<(), Usage> {
    fs::write(path, text).map_err(|e| Usage(format!("{}: {e}", path.display())))
}

/// The first line that differs between the reference text and the output text, numbered from
/// 1. A missing line shows as `<end>`.
fn mismatch(reference: &str, got: &str) -> String {
    let quote = |line: Option<&str>| line.map_or_else(|| "<end>".to_owned(), |l| format!("`{l}`"));
    let mut refs = reference.split('\n');
    let mut gots = got.split('\n');
    let mut n = 1;
    loop {
        let (r, o) = (refs.next(), gots.next());
        if r != o || r.is_none() {
            return format!(
                "mismatch at line {n}: expected {}, found {}",
                quote(r),
                quote(o)
            );
        }
        n += 1;
    }
}

/// `run` of a source file: one source output line for each source input line of `input`,
/// from the zero state. A bad input line is a usage error after the earlier output lines.
fn run_source(
    source: &str,
    top: &str,
    budget: &Budgets,
    input: impl BufRead,
    out: &mut impl Write,
) -> Result<Exit, Usage> {
    let c = match checked(source, top, budget)? {
        Ok(c) => c,
        Err((text, exit)) => {
            out.write_all(text.as_bytes())?;
            return Ok(exit);
        }
    };
    let Some(schema) = c.design.schema() else {
        return Ok(defect("the top is not a done instantiation").1);
    };
    if !schema.fits(&c.lowered.design) {
        return Ok(defect("the port schema does not fit the top").1);
    }
    let Ok(top) = top_module(&c.typed) else {
        return Ok(defect("the design has no top module").1);
    };
    let mut sim = match Sim::new(&c.typed) {
        Ok(sim) => sim,
        Err(diagnostic) => return Ok(defect(&diagnostic.to_string()).1),
    };
    let lines = for_each_line(input, |number, line| {
        let values = schema
            .parse_line(line)
            .map_err(|e| Usage(format!("input line {number}: {e}")))?;
        let inputs = core_ir::vectors::inputs(top, values)
            .ok_or(Halt::Defect("the inputs do not fit the top"))?;
        out.write_all(schema.print_line(sim.step(&inputs).values()).as_bytes())
            .map_err(Usage::from)?;
        Ok(())
    });
    match lines {
        Ok(()) => Ok(Exit::Success),
        Err(Halt::Usage(usage)) => Err(usage),
        Err(Halt::Defect(message)) => Ok(defect(message).1),
    }
}

/// The reason a source `run` stops before the end of its input. A source vector that the
/// schema accepts always fits the top, so a misfit is a defect and not a usage error.
enum Halt {
    Usage(Usage),
    Defect(&'static str),
}

impl From<Usage> for Halt {
    fn from(usage: Usage) -> Halt {
        Halt::Usage(usage)
    }
}

/// The line of the first error of a list in position order.
fn first_line<E, C: fmt::Display>(errors: &[E], parts: impl Fn(&E) -> (C, Pos, &String)) -> Output {
    match errors.first() {
        Some(e) => {
            let (code, pos, message) = parts(e);
            error_line(code, pos, message)
        }
        None => (String::new(), Exit::DesignError),
    }
}

/// The line of the first error of a source command, as `silicon-check` prints it.
fn error_line(code: impl fmt::Display, pos: Pos, message: &str) -> Output {
    let line = format!("error[{code}]: {}:{}: {message}\n", pos.line, pos.col);
    (line, Exit::DesignError)
}

fn read_source(file: &Path) -> Result<String, Usage> {
    let bytes = fs::read(file).map_err(|e| Usage(format!("{}: {e}", file.display())))?;
    String::from_utf8(bytes).map_err(|_| Usage(format!("{}: not valid UTF-8", file.display())))
}

/// Reads, parses, and checks `file`, then continues with the parsed and the
/// checked design, or prints the design error.
fn with_design<W: Write>(
    file: &Path,
    out: &mut W,
    then: impl FnOnce(ast::Design, typed::Design, &mut W) -> Result<Exit, Usage>,
) -> Result<Exit, Usage> {
    with_checked(&read_source(file)?, out, then)
}

/// Like `with_design`, but the Lean checker also accepts the same source
/// before `then` runs. A Lean rejection prints the Lean error line and is a
/// design error. With `--no-validate`, stderr says so, so that nobody
/// mistakes the output for a validated one.
fn with_validated_design<W: Write>(
    file: &Path,
    validation: &Validation,
    out: &mut W,
    then: impl FnOnce(ast::Design, typed::Design, &mut W) -> Result<Exit, Usage>,
) -> Result<Exit, Usage> {
    let source = read_source(file)?;
    with_checked(&source, out, |ast, design, out| {
        if validation.no_validate {
            writeln!(io::stderr(), "silicon: not validated")?;
        } else if let Verdict::Rejected(report) = validate(source.as_bytes()).map_err(Usage)? {
            out.write_all(&report)?;
            return Ok(Exit::DesignError);
        }
        then(ast, design, out)
    })
}

fn with_checked<W: Write>(
    source: &str,
    out: &mut W,
    then: impl FnOnce(ast::Design, typed::Design, &mut W) -> Result<Exit, Usage>,
) -> Result<Exit, Usage> {
    report(
        parse(source).and_then(|ast| check(&ast).map(|design| (ast, design))),
        out,
        |(ast, design), out| then(ast, design, out),
    )
}

/// Continues with the value, or prints the design error.
fn report<T, W: Write>(
    result: Result<T, Diagnostic>,
    out: &mut W,
    then: impl FnOnce(T, &mut W) -> Result<Exit, Usage>,
) -> Result<Exit, Usage> {
    match result {
        Ok(value) => then(value, out),
        Err(diagnostic) => {
            writeln!(out, "{diagnostic}")?;
            Ok(Exit::DesignError)
        }
    }
}

fn top_module(design: &typed::Design) -> Result<&typed::Module, Usage> {
    design
        .modules()
        .get(design.top().index())
        .ok_or_else(|| Usage("internal error: the design has no top module".to_owned()))
}

/// Calls `then` with the number and the text of each line of `input`. LF alone ends a line
/// (spec section 6.4.3), so a CR stays in the line and the parser rejects it. `lines` would
/// remove a CR before an LF.
fn for_each_line<E: From<Usage>>(
    input: impl BufRead,
    mut then: impl FnMut(usize, &str) -> Result<(), E>,
) -> Result<(), E> {
    for (number, line) in input.split(b'\n').enumerate() {
        let line = line.map_err(Usage::from)?;
        let line = String::from_utf8(line)
            .map_err(|_| Usage(format!("input line {}: not valid UTF-8", number + 1)))?;
        then(number + 1, &line)?;
    }
    Ok(())
}

fn simulate(
    design: &typed::Design,
    input: impl BufRead,
    out: &mut impl Write,
) -> Result<Exit, Usage> {
    let top = top_module(design)?;
    let mut sim = match Sim::new(design) {
        Ok(sim) => sim,
        Err(diagnostic) => {
            writeln!(out, "{diagnostic}")?;
            return Ok(Exit::DesignError);
        }
    };
    for_each_line::<Usage>(input, |number, line| {
        let inputs =
            parse_input(line, top).map_err(|e| Usage(format!("input line {number}: {e}")))?;
        out.write_all(print_output(top, &sim.step(&inputs)).as_bytes())?;
        Ok(())
    })?;
    Ok(Exit::Success)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A folder with both artifacts of an earlier build.
    fn artifacts(name: &str) -> io::Result<(PathBuf, PathBuf)> {
        let dir =
            std::env::temp_dir().join(format!("silicon-finish-{}-{name}", std::process::id()));
        fs::create_dir_all(&dir)?;
        let (sil, sv) = (dir.join("x.sil"), dir.join("x.sv"));
        fs::write(&sil, "sil")?;
        fs::write(&sv, "old")?;
        Ok((sil, sv))
    }

    #[test]
    fn a_lean_rejection_is_a_defect_without_artifacts() -> io::Result<()> {
        let (sil, sv) = artifacts("defect")?;
        let mut err = Vec::new();
        let verdict = Ok(Elaborated::Defect(b"mismatch at line 1: x\n".to_vec()));
        let output =
            finish(verdict, &sil, &sv, "new", &mut err).map_err(|u| io::Error::other(u.0))?;
        assert_eq!(output, (String::new(), Exit::Defect));
        assert!(!sil.exists() && !sv.exists());
        assert_eq!(
            String::from_utf8_lossy(&err),
            "silicon: defect of the front end: Lean disagrees: mismatch at line 1: x\n"
        );
        Ok(())
    }

    #[test]
    fn a_checker_failure_is_a_usage_error_without_artifacts() -> io::Result<()> {
        let (sil, sv) = artifacts("failure")?;
        let mut err = Vec::new();
        let Err(Usage(message)) = finish(Err("no checker".to_owned()), &sil, &sv, "new", &mut err)
        else {
            return Err(io::Error::other("expected a usage error"));
        };
        assert_eq!(message, "no checker");
        assert!(!sil.exists() && !sv.exists());
        Ok(())
    }

    #[test]
    fn an_accepted_design_writes_the_verilog() -> io::Result<()> {
        let (sil, sv) = artifacts("accepted")?;
        let output = finish(Ok(Elaborated::Accepted), &sil, &sv, "new", &mut Vec::new())
            .map_err(|u| io::Error::other(u.0))?;
        assert_eq!(output, ("validated\n".to_owned(), Exit::Success));
        assert_eq!(fs::read_to_string(&sv)?, "new");
        assert!(sil.exists());
        Ok(())
    }
}
