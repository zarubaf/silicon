// SPDX-License-Identifier: Apache-2.0
//! The CIRCT tools of the LEC flow, run as processes.

use std::ffi::OsStr;
use std::io::Write as _;
use std::process::{Command, Stdio};

use anyhow::{Context, Result, bail};

use super::mlir;

/// The tools that the flow runs. The development shell has each of them.
pub const REQUIRED: [&str; 3] = ["circt-opt", "circt-verilog", "circt-lec"];

/// The environment variable with the path of the Z3 library for `circt-lec`.
pub const Z3: &str = "SILICON_Z3_LIB";

/// Fails with a message that names the first tool that does not start.
pub fn require() -> Result<()> {
    for tool in REQUIRED {
        Command::new(tool)
            .arg("--version")
            .output()
            .with_context(|| format!("cannot run `{tool}`: run `cargo xtask lec` in the development shell (`nix develop`)"))?;
    }
    std::env::var(Z3).with_context(|| {
        format!("`{Z3}` is not set: run `cargo xtask lec` in the development shell (`nix develop`)")
    })?;
    Ok(())
}

/// Runs `program` with `args` and `stdin`, and returns its stdout. A start
/// failure or an exit code other than 0 is an error that names the program.
pub fn run(program: impl AsRef<OsStr>, args: &[&OsStr], stdin: &str) -> Result<String> {
    let program = program.as_ref();
    let shown = program.to_string_lossy();
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("cannot run `{shown}`"))?;
    let pipe = child.stdin.take();
    // A thread writes stdin, so a tool that fills its stdout pipe first
    // does not block.
    let (written, out) = std::thread::scope(|s| {
        let writer = s.spawn(move || pipe.map_or(Ok(()), |mut p| p.write_all(stdin.as_bytes())));
        let out = child.wait_with_output();
        (writer.join(), out)
    });
    let out = out.with_context(|| format!("`{shown}` did not finish"))?;
    if !out.status.success() {
        bail!(
            "`{shown}` failed ({}):\n{}{}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    match written {
        Ok(Ok(())) => {}
        Ok(Err(e)) => {
            return Err(e).with_context(|| format!("cannot write the input of `{shown}`"));
        }
        Err(_) => bail!("the input writer of `{shown}` panicked"),
    }
    String::from_utf8(out.stdout).with_context(|| format!("the output of `{shown}` is not UTF-8"))
}

fn args<'a>(items: &'a [&'a str]) -> Vec<&'a OsStr> {
    items.iter().map(OsStr::new).collect()
}

/// The MLIR of the module `top` of the Verilog `sv` and of the modules
/// below it (spec section 8.1 step 3). The flag keeps the array registers of
/// the memory models as registers. The other modules stay out, because
/// `--prepare-for-bmc` converts the clocks of `top` only. The import drops
/// the initial value of a register, so a Verilog with one is an error.
pub fn import(sv: &str, top: &str) -> Result<String> {
    super::sv::reject_initial_values(sv)?;
    let top = format!("--top={top}");
    run(
        "circt-verilog",
        &args(&[
            "--format=sv",
            "--ir-hw",
            "--detect-memories=false",
            &top,
            "-",
        ]),
        sv,
    )
}

/// The passes of spec section 8.1 step 4 on `mlir` with the top module
/// `top`. The Lean modules are public, so the flattening inlines public
/// modules too. The Verilog import gives each clock as an `i1` that
/// `seq.to_clock` converts. `--prepare-for-bmc` makes it a clock port again,
/// because `--externalize-registers` accepts only a clock port. The first
/// `--canonicalize` removes a register that nothing reads, as firtool does
/// on the Rust side.
pub fn externalized(mlir: &str, top: &str) -> Result<String> {
    let prepare = format!("--prepare-for-bmc=top-module={top}");
    run(
        "circt-opt",
        &args(&[
            "--hw-flatten-modules=hw-inline-public",
            "--canonicalize",
            &prepare,
            "--externalize-registers",
            "--canonicalize",
        ]),
        mlir,
    )
}

/// The result of one equivalence check.
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    Equal,
    /// The circuits differ. The text is the output of `circt-lec`.
    Differ(String),
}

/// Proves the module `top` of `lean` equal to the module `top` of `rust`
/// (spec section 8.1 steps 4 to 6). Both are MLIR with a definition for
/// each module.
pub fn compare(lean: &str, rust: &str, top: &str) -> Result<Verdict> {
    let lean = externalized(lean, top).context("the Lean side")?;
    let rust = externalized(rust, top).context("the Rust side")?;
    let lean_ports = mlir::ports(&lean, top).context("the Lean side")?;
    let rust_ports = mlir::ports(&rust, top).context("the Rust side")?;
    let dir = tempfile::tempdir().context("cannot make a temporary directory")?;
    let mut files = Vec::new();
    for (side, ports, other, name) in [
        (&lean, &lean_ports, &rust_ports, "lean.mlir"),
        (&rust, &rust_ports, &lean_ports, "rust.mlir"),
    ] {
        let text = mlir::with_wrapper(side, &mlir::wrapper(top, ports, other)?)?;
        let path = dir.path().join(name);
        std::fs::write(&path, text).with_context(|| format!("cannot write {}", path.display()))?;
        files.push(path);
    }
    let z3 = std::env::var(Z3).with_context(|| format!("`{Z3}` is not set"))?;
    let wrapper = backend_circt::names::lec_wrapper(top);
    let c1 = format!("--c1={wrapper}");
    let c2 = format!("--c2={wrapper}");
    let libs = format!("--shared-libs={z3}");
    let stdout = run(
        "circt-lec",
        &[
            files[0].as_os_str(),
            files[1].as_os_str(),
            OsStr::new(&c1),
            OsStr::new(&c2),
            OsStr::new("--run"),
            OsStr::new(&libs),
        ],
        "",
    )?;
    match stdout.trim() {
        "c1 == c2" => Ok(Verdict::Equal),
        "c1 != c2" => Ok(Verdict::Differ(stdout)),
        other => bail!("`circt-lec` gave no verdict: {other}"),
    }
}

/// These tests need the CIRCT tools of the development shell.
#[cfg(test)]
mod tests {
    use backend_circt::{MemConfig, lower, memory_model, verilog};
    use core_ir::check::check;
    use core_ir::text::parse;

    use super::*;

    use crate::paths::corpus_file;

    fn lowered(src: &str) -> String {
        lower(&check(&parse(src).unwrap()).unwrap())
    }

    fn differs(verdict: &Verdict) -> bool {
        matches!(verdict, Verdict::Differ(_))
    }

    /// The mutation of spec section 9: one side gives the register `r` the
    /// input `r_state` as its next value.
    #[test]
    fn the_spec_mutation_fails_the_lec() {
        let mlir = lowered(&corpus_file("reg_state.sil"));
        let rust = import(&verilog(&mlir).unwrap(), "top").unwrap();
        assert_eq!(compare(&mlir, &rust, "top").unwrap(), Verdict::Equal);
        let mutated = mlir.replace("seq.compreg %sum,", "seq.compreg %r_state,");
        assert_ne!(mutated, mlir);
        assert!(differs(&compare(&mutated, &rust, "top").unwrap()));
    }

    /// firtool deletes a register that nothing reads, and the Lean side keeps
    /// it, so the comparison needs the canonicalize pass on both sides (#323).
    #[test]
    fn an_unread_register_does_not_fail_the_lec() {
        let mlir = lowered(
            "(design top
  (module top
    (input clk clock)
    (input a (bits 4))
    (output q (bits 4))
    (reg live (bits 4) clk)
    (reg dead (bits 4) clk)
    (next live (add live a))
    (next dead a)
    (assign q live)))",
        );
        let rust = import(&verilog(&mlir).unwrap(), "top").unwrap();
        assert_eq!(compare(&mlir, &rust, "top").unwrap(), Verdict::Equal);
    }

    #[test]
    fn swapped_address_bits_fail_the_model_lec() {
        let config = MemConfig {
            depth: 12,
            width: 8,
            reads: 1,
            writes: 1,
        };
        let (name, model) = (config.module_name(), memory_model(&config));
        let sv = verilog(&model).unwrap();
        let rust = import(&sv, &name).unwrap();
        assert_eq!(compare(&model, &rust, &name).unwrap(), Verdict::Equal);
        let swapped = sv.replace("reg$$mem[r0_addr]", "reg$$mem[{r0_addr[0], r0_addr[3:1]}]");
        assert_ne!(swapped, sv);
        let rust = import(&swapped, &name).unwrap();
        assert!(differs(&compare(&model, &rust, &name).unwrap()));
    }

    /// The stand-in of a black box makes each output a free input and each
    /// input an output of the comparison.
    #[test]
    fn a_black_box_connection_counts() {
        let mlir = lowered(&corpus_file("hierarchy_extern.sil"));
        let lean = mlir::defined(&mlir, &std::collections::BTreeMap::new()).unwrap();
        let sv = verilog(&mlir).unwrap() + &mlir::verilog_stand_ins(&mlir).unwrap();
        let rust = import(&sv, "top").unwrap();
        assert_eq!(compare(&lean, &rust, "top").unwrap(), Verdict::Equal);
        for (from, to) in [("assign z = _u_y;", "assign z = x;"), (".a (x)", ".a (~x)")] {
            let mutated = sv.replace(from, to);
            assert_ne!(mutated, sv, "{from}");
            let rust = import(&mutated, "top").unwrap();
            assert!(differs(&compare(&lean, &rust, "top").unwrap()), "{from}");
        }
    }

    /// Two black boxes with the same ports differ: the names of the stand-in
    /// registers hold the name of the black box.
    #[test]
    fn swapped_black_boxes_fail_the_lec() {
        let src = "\
(design top
  (extern blk_a (input c clock) (input a (bits 2)) (output y (bits 2)) (deps y (a)))
  (extern blk_b (input c clock) (input a (bits 2)) (output y (bits 2)) (deps y (a)))
  (module top
    (input clk clock)
    (input x (bits 2))
    (output p (bits 2))
    (output q (bits 2))
    (inst u blk_a (c clk) (a x))
    (inst v blk_b (c clk) (a x))
    (assign p u.y)
    (assign q v.y)))
";
        let mlir = lowered(src);
        let lean = mlir::defined(&mlir, &std::collections::BTreeMap::new()).unwrap();
        let stand_ins = mlir::verilog_stand_ins(&mlir).unwrap();
        let sv = verilog(&mlir).unwrap();
        let rust = import(&format!("{sv}{stand_ins}"), "top").unwrap();
        assert_eq!(compare(&lean, &rust, "top").unwrap(), Verdict::Equal);
        let swapped = sv
            .replace("blk_a u (", "blk_x u (")
            .replace("blk_b v (", "blk_a v (")
            .replace("blk_x u (", "blk_b u (");
        assert_ne!(swapped, sv);
        let rust = import(&format!("{swapped}{stand_ins}"), "top").unwrap();
        // The swapped stand-in registers have other names, so the wrapper
        // rejects the ports, which is a failure of the check.
        let error = compare(&lean, &rust, "top").unwrap_err();
        assert!(format!("{error:#}").contains("has no match"), "{error:#}");
    }

    /// The import would drop an initial value, so it rejects one.
    #[test]
    fn an_initial_value_fails_the_import() {
        let sv = verilog(&lowered(&corpus_file("reg_state.sil"))).unwrap();
        import(&sv, "top").unwrap();
        let mutated = sv.replace("reg  [7:0] reg$$r;", "reg  [7:0] reg$$r = 8'h0;");
        assert_ne!(mutated, sv);
        let error = import(&mutated, "top").unwrap_err().to_string();
        assert!(error.contains("initial value"), "{error}");
    }

    #[test]
    fn a_tool_failure_names_the_tool() {
        let error = run("circt-opt", &args(&["--no-such-flag"]), "").unwrap_err();
        assert!(
            error.to_string().starts_with("`circt-opt` failed"),
            "{error}"
        );
        let error = run("silicon-no-such-tool", &[], "").unwrap_err();
        assert_eq!(error.to_string(), "cannot run `silicon-no-such-tool`");
    }
}
