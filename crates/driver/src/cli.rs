//! The commands of `silicon` and their exit codes (spec section 6.4.2).

use std::fs;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use core_ir::check::check;
use core_ir::diag::Diagnostic;
use core_ir::interp::Sim;
use core_ir::text::{canonicalize, parse, print};
use core_ir::typed;
use core_ir::vectors::{parse_input, print_output};

#[derive(Parser)]
#[command(name = "silicon", about = "The Silicon core IR tool")]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Check a design: print `ok` or the first error.
    Check { file: PathBuf },
    /// Print the canonical text of a checked design.
    Fmt { file: PathBuf },
    /// Read `in=` lines from stdin and print one `out=` line for each.
    Run { file: PathBuf },
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
        Command::Check { file } => with_design(file, out, |_, out| {
            writeln!(out, "ok")?;
            Ok(Exit::Success)
        }),
        Command::Fmt { file } => {
            let source = read_source(file)?;
            // The formatter prints the canonical form of the parsed design
            // once the checker accepts it.
            report(
                parse(&source).and_then(|ast| check(&ast).map(|_| ast)),
                out,
                |ast, out| {
                    out.write_all(print(&canonicalize(&ast)).as_bytes())?;
                    Ok(Exit::Success)
                },
            )
        }
        Command::Run { file } => {
            with_design(file, out, |design, out| simulate(&design, input, out))
        }
    }
}

fn read_source(file: &Path) -> Result<String, Usage> {
    let bytes = fs::read(file).map_err(|e| Usage(format!("{}: {e}", file.display())))?;
    String::from_utf8(bytes).map_err(|_| Usage(format!("{}: not valid UTF-8", file.display())))
}

fn with_design<W: Write>(
    file: &Path,
    out: &mut W,
    then: impl FnOnce(typed::Design, &mut W) -> Result<Exit, Usage>,
) -> Result<Exit, Usage> {
    let source = read_source(file)?;
    report(parse(&source).and_then(|ast| check(&ast)), out, then)
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
    let top = &design.modules[design.top.index()];
    let mut sim = match Sim::new(design) {
        Ok(sim) => sim,
        Err(diagnostic) => {
            writeln!(out, "{diagnostic}")?;
            return Ok(Exit::DesignError);
        }
    };
    for (number, line) in input.lines().enumerate() {
        let line = line?;
        let inputs = parse_input(&line, top)
            .map_err(|e| Usage(format!("input line {}: {e}", number + 1)))?;
        out.write_all(print_output(top, &sim.step(&inputs)).as_bytes())?;
    }
    Ok(Exit::Success)
}
