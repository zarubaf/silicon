//! Runs a design in `arcilator` through an `arc.sim` testbench, so the
//! differential tests need no C++ harness.
//!
//! Each `in=` line is one clock cycle of spec section 5.2. The testbench sets
//! the inputs with the clock low and evaluates the model. It reads the
//! outputs, and then it raises the clock, which updates the state. The next
//! cycle lowers the clock again, and a falling edge updates nothing. The
//! model starts from the all-zero state, with the clock low.
//!
//! This flow does not use `--externalize-registers`, so CIRCT issue #20 does
//! not apply. A register whose next value is itself, and a memory model
//! without a write port, run as they are.

use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;

use anyhow::{Context, Result};
use num_bigint::BigUint;

use core_ir::interp::{Inputs, Outputs};
use core_ir::vectors::print_output;
use core_ir::{Bits, typed};

use super::{ToolFailure, output};

/// The function that `arcilator --run` calls. No user module can have this
/// name, because rule `E002` rejects names that start with `silicon_`.
const ENTRY: &str = "silicon_diff_entry";

/// The prefix of a module definition.
const MODULE: &str = "hw.module @";

/// The prefix of an extern declaration.
const EXTERN: &str = "hw.module.extern @";

/// True for the extern declaration of a memory module in the Lean reference
/// MLIR.
fn is_memory_extern(line: &str) -> bool {
    line.strip_prefix(EXTERN)
        .is_some_and(backend_circt::names::is_memory_module)
}

/// The module that `arcilator` simulates: the reference MLIR `lowered` with
/// each memory extern replaced by its Lean memory model from `models`. Each
/// module but `top` becomes private. `arcilator` inlines only private
/// modules. An instance of a public module stays opaque, and its outputs
/// read as 0.
pub fn simulation_mlir(lowered: &str, models: &str, top: &str) -> String {
    let root = format!("{MODULE}{top}(");
    lowered
        .lines()
        .filter(|line| !is_memory_extern(line))
        .chain(models.lines())
        .flat_map(|line| match line.strip_prefix(MODULE) {
            Some(rest) if !line.starts_with(&root) => ["hw.module private @", rest, "\n"],
            _ => [line, "", "\n"],
        })
        .collect()
}

/// The `out=` lines, without LF, of `arcilator` on the module `simulation`
/// for one cycle for each element of `cycles`. The files go to `dir`.
pub fn run(
    dir: &Path,
    simulation: &str,
    top: &typed::Module,
    cycles: &[Inputs],
) -> Result<Vec<String>> {
    let mut mlir = simulation.to_owned();
    mlir.push_str(&testbench(top, cycles)?);
    let file = dir.join("bench.mlir");
    std::fs::write(&file, &mlir).with_context(|| format!("cannot write {}", file.display()))?;
    let stdout = output(
        Command::new("arcilator")
            .arg("--run")
            .arg(format!("--jit-entry={ENTRY}"))
            .arg(&file),
        "",
    )?;
    trace(&stdout, top, cycles.len()).map_err(|e| ToolFailure(format!("arcilator: {e:#}")).into())
}

/// The `func.func @main` that simulates the module `top` for one cycle for
/// each element of `cycles`. It emits the outputs of each cycle in port order.
fn testbench(top: &typed::Module, cycles: &[Inputs]) -> Result<String> {
    let model = format!("!arc.sim.instance<@{}>", top.name);
    let mut out = format!(
        "func.func @{ENTRY}() {{\n  arc.sim.instantiate @{} as %m {{\n",
        top.name
    );
    let clock = |out: &mut String, cycle: usize, level: u8| -> Result<()> {
        if let Some(clk) = &top.clock {
            writeln!(out, "    %clk_{cycle}_{level} = hw.constant {level} : i1")?;
            writeln!(
                out,
                "    %clock_{cycle}_{level} = seq.to_clock %clk_{cycle}_{level}"
            )?;
            writeln!(
                out,
                "    arc.sim.set_input %m, \"{}\" = %clock_{cycle}_{level} : !seq.clock, {model}",
                clk.name
            )?;
            writeln!(out, "    arc.sim.step %m : {model}")?;
        }
        Ok(())
    };
    for (cycle, inputs) in cycles.iter().enumerate() {
        for (k, (value, port)) in inputs.values().iter().zip(&top.inputs).enumerate() {
            let (name, width, value) = (&port.name, port.width, value.to_biguint());
            writeln!(out, "    %in_{cycle}_{k} = hw.constant {value} : i{width}")?;
            writeln!(
                out,
                "    arc.sim.set_input %m, \"{name}\" = %in_{cycle}_{k} : i{width}, {model}"
            )?;
        }
        clock(&mut out, cycle, 0)?;
        if top.clock.is_none() {
            writeln!(out, "    arc.sim.step %m : {model}")?;
        }
        for (k, port) in top.outputs.iter().enumerate() {
            let (name, width) = (&port.name, port.width);
            writeln!(
                out,
                "    %out_{cycle}_{k} = arc.sim.get_port %m, \"{name}\" : i{width}, {model}"
            )?;
            writeln!(
                out,
                "    arc.sim.emit \"{name}\", %out_{cycle}_{k} : i{width}"
            )?;
        }
        clock(&mut out, cycle, 1)?;
    }
    out.push_str("  }\n  return\n}\n");
    Ok(out)
}

/// The `out=` lines, without LF, of the `arcilator` output `stdout` for
/// `cycles` cycles of the module `top`. Each emitted line is `NAME = HEX`.
fn trace(stdout: &str, top: &typed::Module, cycles: usize) -> Result<Vec<String>> {
    let mut lines = stdout.lines();
    let mut trace = Vec::with_capacity(cycles);
    for cycle in 0..cycles {
        let mut values = Vec::with_capacity(top.outputs.len());
        for port in &top.outputs {
            let line = lines
                .next()
                .with_context(|| format!("no value of `{}` in cycle {cycle}", port.name))?;
            let hex = line
                .strip_prefix(port.name.as_str())
                .and_then(|rest| rest.strip_prefix(" = "))
                .with_context(|| format!("expected `{} = HEX`, got `{line}`", port.name))?;
            let value = BigUint::parse_bytes(hex.as_bytes(), 16)
                .and_then(|value| Bits::new(port.width.get(), value))
                .with_context(|| format!("not a value of width {}: `{line}`", port.width))?;
            values.push(value);
        }
        let line = print_output(top, &Outputs::new(values));
        trace.push(line.trim_end_matches('\n').to_owned());
    }
    if let Some(line) = lines.next() {
        anyhow::bail!("unexpected output after the last cycle: `{line}`");
    }
    Ok(trace)
}

#[cfg(test)]
mod tests {
    use core_ir::check::check;
    use core_ir::text::parse;
    use core_ir::vectors::parse_input;

    use super::super::{Trace, compare};
    use super::*;

    fn top(source: &str) -> typed::Module {
        let design = check(&parse(source).unwrap()).unwrap();
        design.modules[design.top.index()].clone()
    }

    const COUNTER: &str = "(design top (module top (input clk clock) (input en (bits 1)) \
        (output q (bits 4)) (output w (bits 70)) (reg r (bits 4) clk) \
        (next r (mux en (add r (const 4 1)) r)) (assign q r) (assign w (const 70 0))))";

    #[test]
    fn the_memory_externs_give_way_to_private_models() {
        let lowered = "hw.module.extern @silicon_mem_2x8_r1w1(in %clk : !seq.clock)\n\
                       hw.module @child() {\n  hw.output\n}\n\
                       hw.module @top() {\n  hw.output\n}\n";
        let models = "hw.module @silicon_mem_2x8_r1w1(in %clk : !seq.clock) {\n}\n";
        assert_eq!(
            simulation_mlir(lowered, models, "top"),
            "hw.module private @child() {\n  hw.output\n}\n\
             hw.module @top() {\n  hw.output\n}\n\
             hw.module private @silicon_mem_2x8_r1w1(in %clk : !seq.clock) {\n}\n"
        );
    }

    #[test]
    fn the_testbench_reads_the_outputs_before_the_rising_edge() {
        let top = top(COUNTER);
        let bench = testbench(&top, &[parse_input("in=(en 1)", &top).unwrap()]).unwrap();
        let set = bench.find("\"en\" = %in_0_0").unwrap();
        let low = bench.find("\"clk\" = %clock_0_0").unwrap();
        let read = bench.find("get_port %m, \"q\"").unwrap();
        let high = bench.find("\"clk\" = %clock_0_1").unwrap();
        assert!(set < low && low < read && read < high, "{bench}");
    }

    #[test]
    fn the_trace_converts_hexadecimal_values_to_out_lines() {
        let stdout = "q = 0\nw = 0000000000000000001\nq = f\nw = 3fffffffffffffffff\n";
        assert_eq!(
            trace(stdout, &top(COUNTER), 2).unwrap(),
            ["out=(q 0 w 1)", "out=(q 15 w 1180591620717411303423)"]
        );
    }

    #[test]
    fn the_trace_rejects_a_missing_or_extra_value() {
        let missing = trace("q = 0\n", &top(COUNTER), 1).unwrap_err();
        assert_eq!(missing.to_string(), "no value of `w` in cycle 0");
        let extra = trace("q = 0\nw = 0\nq = 1\n", &top(COUNTER), 1).unwrap_err();
        assert_eq!(
            extra.to_string(),
            "unexpected output after the last cycle: `q = 1`"
        );
    }

    #[test]
    fn the_trace_rejects_a_value_wider_than_its_port() {
        let error = trace("q = 1f\nw = 0\n", &top(COUNTER), 1).unwrap_err();
        assert_eq!(error.to_string(), "not a value of width 4: `q = 1f`");
    }

    /// A child that adds 1, under a top that passes its input through.
    const HIERARCHY: &str = "(design top (module inc (input a (bits 4)) (output y (bits 4)) \
        (assign y (add a (const 4 1)))) (module top (input a (bits 4)) (output q (bits 4)) \
        (inst u inc (a a)) (assign q u.y)))";

    /// The reference MLIR of `HIERARCHY`, with both modules public.
    const LOWERED: &str = "hw.module @inc(in %a : i4, out y : i4) {\n\
        \x20 %one = hw.constant 1 : i4\n\
        \x20 %y = comb.add %a, %one : i4\n\
        \x20 hw.output %y : i4\n}\n\
        hw.module @top(in %a : i4, out q : i4) {\n\
        \x20 %u.y = hw.instance \"u\" @inc(a: %a: i4) -> (y: i4)\n\
        \x20 hw.output %u.y : i4\n}\n";

    /// The `out=` lines of arcilator on `simulation` for `HIERARCHY`.
    fn simulate(simulation: &str) -> Vec<String> {
        let top = top(HIERARCHY);
        let inputs = [
            parse_input("in=(a 3)", &top).unwrap(),
            parse_input("in=(a 15)", &top).unwrap(),
        ];
        let dir = tempfile::tempdir().unwrap();
        run(dir.path(), simulation, &top, &inputs).unwrap()
    }

    #[test]
    fn arcilator_agrees_on_the_simulation_module() {
        let lines = simulate(&simulation_mlir(LOWERED, "", "top"));
        let traces = [
            Trace {
                tool: "lean",
                lines: vec!["out=(q 4)".to_owned(), "out=(q 0)".to_owned()],
            },
            Trace {
                tool: "arcilator",
                lines,
            },
        ];
        assert_eq!(compare(&traces), None);
    }

    #[test]
    fn a_wrong_arcilator_result_is_a_disagreement() {
        // Without the private rewrite, arcilator reads the child output as 0.
        let traces = [
            Trace {
                tool: "lean",
                lines: vec!["out=(q 4)".to_owned(), "out=(q 0)".to_owned()],
            },
            Trace {
                tool: "arcilator",
                lines: simulate(LOWERED),
            },
        ];
        assert_eq!(
            compare(&traces).as_deref(),
            Some("cycle 0: lean prints `out=(q 4)`, arcilator prints `out=(q 0)`")
        );
    }

    #[test]
    fn a_user_module_named_main_does_not_collide_with_the_entry() {
        let top = top("(design main (module main (output q (bits 1)) (assign q (const 1 1))))");
        let lowered = "hw.module @main(out q : i1) {\n\
            \x20 %one = hw.constant 1 : i1\n\
            \x20 hw.output %one : i1\n}\n";
        let inputs = [parse_input("in=()", &top).unwrap()];
        let dir = tempfile::tempdir().unwrap();
        let simulation = simulation_mlir(lowered, "", "main");
        assert_eq!(
            run(dir.path(), &simulation, &top, &inputs).unwrap(),
            ["out=(q 1)"]
        );
    }
}
