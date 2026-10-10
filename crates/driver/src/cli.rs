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

use crate::validate::{Verdict, validate};

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
    /// Read `in=` lines from stdin and print one `out=` line for each.
    Run { file: PathBuf },
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
}

impl From<Exit> for ExitCode {
    fn from(exit: Exit) -> ExitCode {
        match exit {
            Exit::Success => ExitCode::SUCCESS,
            Exit::DesignError => ExitCode::from(1),
            Exit::UsageError => ExitCode::from(2),
        }
    }
}

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
        Command::Run { file } => {
            with_design(file, out, |_, design, out| simulate(&design, input, out))
        }
        Command::Lower { validation, file } => {
            with_validated_design(file, validation, out, |_, design, out| {
                out.write_all(lower(&design).as_bytes())?;
                Ok(Exit::Success)
            })
        }
        Command::Eval { budget, file, expr } => {
            let (text, exit) = eval_source(&read_source(file)?, expr, budget)?;
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
fn parse_source(source: &str, depth: usize) -> Result<(String, Exit), Usage> {
    let parsed = parse::parse_with_depth(source, depth).map_err(|e| Usage(e.to_string()))?;
    if let Some(e) = parsed.errors().first() {
        return Ok(error_line(e.code, e.pos, &e.message));
    }
    let dump = parsed.dump().map_err(|e| Usage(e.to_string()))?;
    Ok((dump.unwrap_or_default(), Exit::Success))
}

/// The output and the exit code of `eval`: the serialization of the value of `expr` in the
/// file scope of `source`, or the first error of the file, then of the expression. Each pass
/// runs on the front-end thread. If the machine cannot give a stack, the command fails.
fn eval_source(source: &str, expr: &str, budget: &Budgets) -> Result<(String, Exit), Usage> {
    let stack = |e: parse::StackError| Usage(e.to_string());
    let depth = budget.syntax_depth;
    let parsed = parse::parse_with_depth(source, depth).map_err(|e| Usage(e.to_string()))?;
    let file = match resolve::resolve(parsed) {
        Ok(file) => file,
        Err(resolve::Failed::Parse(parsed)) => {
            return Ok(match parsed.errors().first() {
                Some(e) => error_line(e.code, e.pos, &e.message),
                None => (String::new(), Exit::DesignError),
            });
        }
        Err(resolve::Failed::Names(e)) => {
            return Ok(first_line(&e, |e| (e.code, e.pos, &e.message)));
        }
        Err(resolve::Failed::Stack(e)) => return Err(stack(e)),
    };
    let file = match typeck::check(file) {
        Ok(file) => file,
        Err(typeck::Failed::Errors(e)) => {
            return Ok(first_line(&e, |e| (e.code, e.pos, &e.message)));
        }
        Err(typeck::Failed::Stack(e)) => return Err(stack(e)),
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

/// The line of the first error of a list in position order.
fn first_line<E, C: fmt::Display>(
    errors: &[E],
    parts: impl Fn(&E) -> (C, Pos, &String),
) -> (String, Exit) {
    match errors.first() {
        Some(e) => {
            let (code, pos, message) = parts(e);
            error_line(code, pos, message)
        }
        None => (String::new(), Exit::DesignError),
    }
}

/// The line of the first error of a source command, as `silicon-check` prints it.
fn error_line(code: impl fmt::Display, pos: Pos, message: &str) -> (String, Exit) {
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

fn simulate(
    design: &typed::Design,
    input: impl BufRead,
    out: &mut impl Write,
) -> Result<Exit, Usage> {
    let top = design
        .modules()
        .get(design.top().index())
        .ok_or_else(|| Usage("internal error: the design has no top module".to_owned()))?;
    let mut sim = match Sim::new(design) {
        Ok(sim) => sim,
        Err(diagnostic) => {
            writeln!(out, "{diagnostic}")?;
            return Ok(Exit::DesignError);
        }
    };
    // LF alone ends a line (spec section 6.4.3), so a CR stays in the line
    // and the parser rejects it. `lines` would remove a CR before an LF.
    for (number, line) in input.split(b'\n').enumerate() {
        let line = line?;
        let line = String::from_utf8(line)
            .map_err(|_| Usage(format!("input line {}: not valid UTF-8", number + 1)))?;
        let inputs = parse_input(&line, top)
            .map_err(|e| Usage(format!("input line {}: {e}", number + 1)))?;
        out.write_all(print_output(top, &sim.step(&inputs)).as_bytes())?;
    }
    Ok(Exit::Success)
}
