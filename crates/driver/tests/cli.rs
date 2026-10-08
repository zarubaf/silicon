//! Tests of the `silicon` binary: output bytes and exit codes.

mod common;

use common::spawn;
use std::path::PathBuf;
use std::process::{Command, Output};

const COUNTER: &str = "\
(design counter
  (module counter
    (input clk clock)
    (input rst (bits 1))
    (input en (bits 1))
    (output q (bits 8))
    (reg r (bits 8) clk (reset sync rst (const 8 0)))
    (let inc (bits 8) (add r (const 8 1)))
    (next r (mux en inc r))
    (assign q r)))
";

const REORDERED: &str = "\
(design counter
  (module counter
    (input clk clock)
    (input rst (bits 1))
    (input en (bits 1))
    (output q (bits 8))
    (assign q r)
    (next r (mux en inc r))
    (let inc (bits 8) (add r (const 8 1)))
    (reg r (bits 8) clk (reset sync rst (const 8 0)))))
";

const E004: &str = "\
(design d
  (module d
    (input a (bits 1))
    (input b (bits 2))
    (output q (bits 1))
    (assign q (add a b))))
";

const EXTERN: &str = "\
(design d
  (extern blk
    (input a (bits 1))
    (output y (bits 1))
    (deps y (a)))
  (module d
    (input a (bits 1))
    (output q (bits 1))
    (assign q a)))
";

/// Depth 12 needs guards. The two memories have the configurations
/// `12x8_r2w1` and `12x8_r1w0`.
const MEMORY: &str = "\
(design top
  (module top
    (input clk clock)
    (input x (bits 4))
    (input y (bits 4))
    (input d (bits 8))
    (input we (bits 1))
    (output p (bits 8))
    (output q (bits 8))
    (mem m (bits 8) 12 clk)
    (mem n (bits 8) 12 clk)
    (write m 0 x d we)
    (assign p (read m x))
    (assign q (xor (read m y) (read n y)))))
";

type Test = Result<(), Box<dyn std::error::Error>>;

fn file(name: &str, bytes: &[u8]) -> std::io::Result<PathBuf> {
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::write(&path, bytes)?;
    Ok(path)
}

fn silicon(args: &[&str], path: &PathBuf, stdin: &str) -> std::io::Result<Output> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_silicon"));
    command.args(args).arg(path);
    spawn(&mut command, stdin)
}

fn text(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn check_accepts_the_counter() -> Test {
    let out = silicon(&["check"], &file("ok.sil", COUNTER.as_bytes())?, "")?;
    assert_eq!((text(&out).as_str(), out.status.code()), ("ok\n", Some(0)));
    Ok(())
}

#[test]
fn check_reports_a_design_error() -> Test {
    let out = silicon(&["check"], &file("e004.sil", E004.as_bytes())?, "")?;
    assert!(text(&out).starts_with("error[E004]: 6:"), "{}", text(&out));
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn a_file_that_is_not_utf8_is_a_usage_error() -> Test {
    let out = silicon(&["check"], &file("bad.sil", &[0xff, 0xfe])?, "")?;
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(text(&out), "");
    Ok(())
}

#[test]
fn a_missing_file_is_a_usage_error() -> Test {
    let missing = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("missing.sil");
    let out = silicon(&["check"], &missing, "")?;
    assert_eq!(out.status.code(), Some(2));
    Ok(())
}

#[test]
fn fmt_prints_the_canonical_text() -> Test {
    let out = silicon(&["fmt"], &file("re.sil", REORDERED.as_bytes())?, "")?;
    assert_eq!(text(&out), COUNTER);
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn fmt_reports_a_checker_error() -> Test {
    let out = silicon(&["fmt"], &file("fe.sil", E004.as_bytes())?, "")?;
    assert!(text(&out).starts_with("error[E004]: 6:"), "{}", text(&out));
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn run_prints_one_line_per_input_line() -> Test {
    let input = "in=(rst 1 en 0)\nin=(rst 0 en 1)\nin=(rst 0 en 1)\nin=(rst 0 en 0)\n";
    let out = silicon(&["run"], &file("run.sil", COUNTER.as_bytes())?, input)?;
    assert_eq!(text(&out), "out=(q 0)\nout=(q 0)\nout=(q 1)\nout=(q 2)\n");
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn run_stops_at_a_bad_line() -> Test {
    let input = "in=(rst 1 en 0)\nin=(rst 0 en 1)\nin=(rst 0)\nin=(rst 0 en 1)\n";
    let out = silicon(&["run"], &file("bad_run.sil", COUNTER.as_bytes())?, input)?;
    assert_eq!(text(&out), "out=(q 0)\nout=(q 0)\n");
    assert_eq!(out.status.code(), Some(2));
    Ok(())
}

#[test]
fn run_rejects_an_extern() -> Test {
    let out = silicon(&["run"], &file("ext.sil", EXTERN.as_bytes())?, "in=(a 1)\n")?;
    assert!(
        text(&out).starts_with("error[E014]: 2:3:"),
        "{}",
        text(&out)
    );
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn run_reports_a_checker_error_before_an_extern() -> Test {
    let src = EXTERN.replace("(assign q a)", "(assign q b)");
    let out = silicon(
        &["run"],
        &file("ext_err.sil", src.as_bytes())?,
        "in=(a 1)\n",
    )?;
    assert!(text(&out).starts_with("error[E003]: "), "{}", text(&out));
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn run_rejects_a_blank_input_line() -> Test {
    for (name, input, printed) in [
        ("blank.sil", "in=(rst 1 en 0)\n\n", "out=(q 0)\n"),
        ("bare.sil", "in=\n", ""),
    ] {
        let out = silicon(&["run"], &file(name, COUNTER.as_bytes())?, input)?;
        assert_eq!(text(&out), printed, "{input:?}");
        assert_eq!(out.status.code(), Some(2), "{input:?}");
    }
    Ok(())
}

#[test]
fn an_unknown_subcommand_is_a_usage_error() -> Test {
    let out = silicon(
        &["frobnicate"],
        &file("unknown.sil", COUNTER.as_bytes())?,
        "",
    )?;
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(text(&out), "");
    Ok(())
}

#[test]
fn lower_prints_the_mlir() -> Test {
    let out = silicon(&["lower"], &file("lower.sil", COUNTER.as_bytes())?, "")?;
    assert!(
        text(&out).starts_with("hw.module @counter(in %clk : !seq.clock, "),
        "{}",
        text(&out)
    );
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn lower_reports_a_checker_error() -> Test {
    let out = silicon(&["lower"], &file("lower_e004.sil", E004.as_bytes())?, "")?;
    assert!(text(&out).starts_with("error[E004]: 6:"), "{}", text(&out));
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn lower_accepts_an_extern() -> Test {
    let out = silicon(&["lower"], &file("lower_ext.sil", EXTERN.as_bytes())?, "")?;
    assert!(
        text(&out).contains("hw.module.extern @blk("),
        "{}",
        text(&out)
    );
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn verilog_prints_the_counter() -> Test {
    let out = silicon(
        &["verilog"],
        &file("v_counter.sil", COUNTER.as_bytes())?,
        "",
    )?;
    assert!(text(&out).contains("module counter("), "{}", text(&out));
    assert!(text(&out).contains("silicon_reg_r"), "{}", text(&out));
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn verilog_instantiates_each_memory_without_a_body() -> Test {
    let out = silicon(&["verilog"], &file("v_mem.sil", MEMORY.as_bytes())?, "")?;
    let sv = text(&out);
    assert!(sv.contains("silicon_mem_12x8_r2w1 m ("), "{sv}");
    assert!(sv.contains("silicon_mem_12x8_r1w0 n ("), "{sv}");
    assert!(!sv.contains("module silicon_mem_"), "{sv}");
    assert!(!sv.contains("silicon_reg_mem"), "{sv}");
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn verilog_models_prints_one_model_per_configuration() -> Test {
    let out = silicon(
        &["verilog", "--models"],
        &file("models.sil", MEMORY.as_bytes())?,
        "",
    )?;
    let sv = text(&out);
    let modules: Vec<&str> = sv.lines().filter(|l| l.starts_with("module ")).collect();
    assert_eq!(
        modules,
        [
            "module silicon_mem_12x8_r1w0(",
            "module silicon_mem_12x8_r2w1("
        ],
        "{sv}"
    );
    assert_eq!(
        sv.matches("reg [15:0][7:0] silicon_reg_mem;").count(),
        2,
        "{sv}"
    );
    assert_eq!(out.status.code(), Some(0));
    let out = silicon(
        &["verilog", "--models"],
        &file("no_models.sil", COUNTER.as_bytes())?,
        "",
    )?;
    assert!(!text(&out).contains("module "), "{}", text(&out));
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

/// Step 3 of the LEC flow of spec section 8.1 reads both outputs together.
#[test]
fn circt_verilog_reads_the_design_and_the_models() -> Test {
    let src = file("flow.sil", MEMORY.as_bytes())?;
    let design = silicon(&["verilog"], &src, "")?;
    let models = silicon(&["verilog", "--models"], &src, "")?;
    let out_sv = file("flow_out.sv", &design.stdout)?;
    let models_sv = file("flow_models.sv", &models.stdout)?;
    let out = spawn(
        Command::new("circt-verilog")
            .args(["--ir-hw", "--detect-memories=false"])
            .arg(&out_sv)
            .arg(&models_sv),
        "",
    )?;
    let stdout = text(&out);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(stdout.contains("hw.module @top("), "{stdout}");
    assert!(stdout.contains("silicon_reg_mem"), "{stdout}");
    Ok(())
}

#[test]
fn a_missing_circt_tool_is_a_usage_error() -> Test {
    let src = file("no_tool.sil", COUNTER.as_bytes())?;
    for args in [&["verilog"][..], &["verilog", "--models"]] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_silicon"));
        command.args(args).arg(&src).env("PATH", "");
        let out = spawn(&mut command, "")?;
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        assert_eq!(text(&out), "");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.contains("firtool"), "{stderr}");
    }
    Ok(())
}
