// SPDX-License-Identifier: Apache-2.0
//! Tests of the `silicon` binary: output bytes and exit codes.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use testkit::bins::{self, CHECK_VARIABLE};
use testkit::source;
use testkit::spawn::spawn;

/// A `silicon` command that validates with the real checker.
fn silicon_command() -> Command {
    bins::silicon(Path::new(env!("CARGO_BIN_EXE_silicon")))
}

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
    let mut command = silicon_command();
    command.args(args).arg(path);
    spawn(&mut command, stdin)
}

fn text(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// `const X: T = ((...1...));` with `n` pairs of parentheses.
fn nested(n: usize) -> String {
    format!("const X: T = {}1{};\n", "(".repeat(n), ")".repeat(n))
}

/// A file with 1,000,000 open brackets in a constant of type `ty`.
fn open_brackets(ty: &str) -> String {
    format!("const X: {ty} = {}", "(".repeat(1_000_000))
}

/// A file with a chain of 1,000,000 prefix minus signs.
fn minus_chain() -> String {
    format!("const X: T = {}1;\n", "-".repeat(1_000_000))
}

/// Runs `silicon` and `silicon-check` as `COMMAND FILE ARGS...` as `testkit::source::agreed`
/// says. Returns the output of `silicon`.
fn agree(command: &str, flags: &[&str], path: &Path) -> Result<Output, Box<dyn std::error::Error>> {
    let binary = PathBuf::from(env!("CARGO_BIN_EXE_silicon"));
    Ok(source::agreed(&binary, command, path, flags)?)
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

/// LF alone ends a line (spec section 6.4.3): a CR is bad syntax.
#[test]
fn run_rejects_a_crlf_input_line() -> Test {
    let input = "in=(rst 1 en 0)\nin=(rst 0 en 1)\r\nin=(rst 0 en 1)\n";
    let out = silicon(&["run"], &file("crlf.sil", COUNTER.as_bytes())?, input)?;
    assert_eq!(text(&out), "out=(q 0)\n");
    assert_eq!(out.status.code(), Some(2));
    Ok(())
}

#[test]
fn run_accepts_a_last_line_without_lf() -> Test {
    let input = "in=(rst 1 en 0)\nin=(rst 0 en 1)";
    let out = silicon(&["run"], &file("no_lf.sil", COUNTER.as_bytes())?, input)?;
    assert_eq!(text(&out), "out=(q 0)\nout=(q 0)\n");
    assert_eq!(out.status.code(), Some(0));
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
    assert!(text(&out).contains("reg$$r"), "{}", text(&out));
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn verilog_instantiates_each_memory_without_a_body() -> Test {
    let out = silicon(&["verilog"], &file("v_mem.sil", MEMORY.as_bytes())?, "")?;
    let sv = text(&out);
    assert!(sv.contains("mem$$12x8_r2w1 m ("), "{sv}");
    assert!(sv.contains("mem$$12x8_r1w0 n ("), "{sv}");
    assert!(!sv.contains("module mem$$"), "{sv}");
    assert!(!sv.contains("reg$$mem"), "{sv}");
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
        ["module mem$$12x8_r1w0(", "module mem$$12x8_r2w1("],
        "{sv}"
    );
    assert_eq!(sv.matches("reg [15:0][7:0] reg$$mem;").count(), 2, "{sv}");
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
    assert!(stdout.contains("reg$$mem"), "{stdout}");
    Ok(())
}

#[test]
fn a_missing_circt_tool_is_a_usage_error() -> Test {
    let src = file("no_tool.sil", COUNTER.as_bytes())?;
    for args in [&["verilog"][..], &["verilog", "--models"]] {
        let mut command = silicon_command();
        command.args(args).arg(&src).env("PATH", "");
        let out = spawn(&mut command, "")?;
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        assert_eq!(text(&out), "");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.contains("firtool"), "{stderr}");
    }
    Ok(())
}

fn with_checker(checker: &str, args: &[&str], name: &str) -> std::io::Result<Output> {
    let src = file(name, COUNTER.as_bytes())?;
    let mut command = Command::new(env!("CARGO_BIN_EXE_silicon"));
    command.args(args).arg(&src).env(CHECK_VARIABLE, checker);
    spawn(&mut command, "")
}

#[test]
fn a_failing_checker_fails_lower_and_verilog() -> Test {
    for command in ["lower", "verilog"] {
        let out = with_checker("false", &[command], "reject.sil")?;
        assert_eq!(out.status.code(), Some(2), "{command}");
        assert_eq!(text(&out), "", "{command}");
    }
    Ok(())
}

#[test]
fn a_missing_checker_is_a_usage_error_that_names_the_flag() -> Test {
    for command in ["lower", "verilog"] {
        let out = with_checker("/no/such/silicon-check", &[command], "missing_checker.sil")?;
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(2), "{command}");
        assert_eq!(text(&out), "", "{command}");
        assert!(stderr.contains("/no/such/silicon-check"), "{stderr}");
        assert!(stderr.contains("--no-validate"), "{stderr}");
    }
    Ok(())
}

#[test]
fn no_validate_skips_the_checker_and_says_so() -> Test {
    for command in ["lower", "verilog"] {
        let args = [command, "--no-validate"];
        let out = with_checker("/no/such/silicon-check", &args, "skipped.sil")?;
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(0), "{command}: {stderr}");
        assert_eq!(stderr.matches("not validated").count(), 1, "{stderr}");
        assert!(!text(&out).is_empty(), "{command}");
    }
    Ok(())
}

#[test]
fn a_validated_run_does_not_say_not_validated() -> Test {
    let out = silicon(&["lower"], &file("validated.sil", COUNTER.as_bytes())?, "")?;
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&out.stderr), "");
    let src = file("validated_models.sil", MEMORY.as_bytes())?;
    let out = silicon(&["verilog", "--models"], &src, "")?;
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&out.stderr), "");
    Ok(())
}

#[test]
fn a_missing_file_is_a_usage_error_before_the_checker_runs() -> Test {
    let missing = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("none.sil");
    let out = silicon(&["lower"], &missing, "")?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(2));
    assert!(!stderr.contains("--no-validate"), "{stderr}");
    Ok(())
}

const SOURCE: &str = "\
const W: Nat = 8;
module M(comptime n: Nat) domains(clk) {
    input a: UInt[8];
    let x = a + 1;
}
";

#[test]
fn parse_prints_the_ast_dump() -> Test {
    let out = silicon(&["parse"], &file("ok.si", SOURCE.as_bytes())?, "")?;
    assert_eq!(
        text(&out),
        "(const \"W\" (name \"Nat\") (num 8))\n\
         (module \"M\" ((param true \"n\" (name \"Nat\"))) (some (\"clk\")) \
         ((input \"a\" (index (name \"UInt\") ((num 8)))) \
         (local false \"x\" none (binary add (name \"a\") (num 1)))))\n"
    );
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn parse_prints_nothing_for_an_empty_file() -> Test {
    let out = silicon(&["parse"], &file("empty.si", b"")?, "")?;
    assert_eq!((text(&out).as_str(), out.status.code()), ("", Some(0)));
    Ok(())
}

#[test]
fn parse_reports_the_first_syntax_error() -> Test {
    let out = silicon(&["parse"], &file("s001.si", b"const X: T = ;\n")?, "")?;
    assert!(
        text(&out).starts_with("error[S001]: 1:14: "),
        "{}",
        text(&out)
    );
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn parse_reports_a_later_slice_with_s004() -> Test {
    let out = silicon(&["parse"], &file("s004.si", b"import x;\n")?, "")?;
    assert!(
        text(&out).starts_with("error[S004]: 1:1: "),
        "{}",
        text(&out)
    );
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn parse_takes_the_syntax_depth() -> Test {
    // Brackets: the third pair of parentheses is the first bracket above the depth 2.
    let path = file("deep.si", b"const X: T = (((1)));\n")?;
    let out = silicon(&["parse", "--syntax-depth", "3"], &path, "")?;
    assert_eq!(out.status.code(), Some(0));
    let out = silicon(&["parse", "--syntax-depth", "2"], &path, "")?;
    assert!(
        text(&out).starts_with("error[S001]: 1:16: "),
        "{}",
        text(&out)
    );
    assert_eq!(out.status.code(), Some(1));
    // Height: the first token of the expression.
    let path = file("high.si", b"const X: T = a + b + c + d;\n")?;
    let out = silicon(&["parse", "--syntax-depth", "3"], &path, "")?;
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out).starts_with("error[S001]: 1:14: "));
    Ok(())
}

#[test]
fn parse_does_not_overflow_the_stack_at_the_default_depth() -> Test {
    let out = agree("parse", &[], &file("d4096.si", nested(4096).as_bytes())?)?;
    assert_eq!(out.status.code(), Some(0));
    assert!(text(&out).ends_with("(num 1))\n"));
    let out = agree("parse", &[], &file("d4097.si", nested(4097).as_bytes())?)?;
    assert!(text(&out).starts_with("error[S001]: 1:4110: "));
    assert_eq!(out.status.code(), Some(1));
    let open = open_brackets("T");
    let out = agree("parse", &[], &file("open.si", open.as_bytes())?)?;
    assert!(text(&out).starts_with("error[S001]: 1:4110: "));
    assert_eq!(out.status.code(), Some(1));
    let chain = minus_chain();
    let out = agree("parse", &[], &file("chain.si", chain.as_bytes())?)?;
    assert!(text(&out).starts_with("error[S001]: 1:14: "));
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn parse_does_not_overflow_the_stack_at_the_maximum_depth() -> Test {
    let flags = ["--syntax-depth", "65536"];
    let out = agree(
        "parse",
        &flags,
        &file("d65536.si", nested(65536).as_bytes())?,
    )?;
    assert_eq!(out.status.code(), Some(0));
    let out = agree(
        "parse",
        &flags,
        &file("d65537.si", nested(65537).as_bytes())?,
    )?;
    assert!(text(&out).starts_with("error[S001]: 1:65550: "));
    let open = open_brackets("T");
    let out = agree("parse", &flags, &file("open-max.si", open.as_bytes())?)?;
    assert!(text(&out).starts_with("error[S001]: 1:65550: "));
    assert_eq!(out.status.code(), Some(1));
    let chain = minus_chain();
    let out = agree("parse", &flags, &file("chain-max.si", chain.as_bytes())?)?;
    assert!(text(&out).starts_with("error[S001]: 1:14: "));
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

#[test]
fn parse_rejects_a_syntax_depth_above_the_cap() -> Test {
    let path = file("cap.si", b"const X: T = 1;\n")?;
    let out = silicon(&["parse", "--syntax-depth", "65537"], &path, "")?;
    assert_eq!((text(&out).as_str(), out.status.code()), ("", Some(2)));
    let out = silicon(&["parse", "--syntax-depth", "65536"], &path, "")?;
    assert_eq!(out.status.code(), Some(0));
    Ok(())
}

#[test]
fn parse_rejects_a_syntax_depth_of_zero() -> Test {
    let path = file("zero.si", b"")?;
    let out = silicon(&["parse", "--syntax-depth", "0"], &path, "")?;
    assert_eq!((text(&out).as_str(), out.status.code()), ("", Some(2)));
    Ok(())
}

#[test]
fn parse_of_a_missing_file_is_a_usage_error() -> Test {
    let missing = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("missing.si");
    let out = silicon(&["parse"], &missing, "")?;
    assert_eq!(out.status.code(), Some(2));
    Ok(())
}

/// Runs `silicon eval FILE EXPR` with the flags `flags` after the expression. Each call has
/// its own file, because the tests run in parallel, also in other processes.
fn eval(src: &str, expr: &str, flags: &[&str]) -> std::io::Result<(String, Option<i32>)> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = file(
        &format!("eval-{}-{n}.si", std::process::id()),
        src.as_bytes(),
    )?;
    let mut command = silicon_command();
    command.arg("eval").arg(path).arg(expr).args(flags);
    let out = spawn(&mut command, "")?;
    Ok((text(&out), out.status.code()))
}

const FACT: &str = "\
comptime fn fact(n: Nat) -> Nat {
    comptime if (n == 0) { return 1; }
    return n * fact(n - 1);
}
";

#[test]
fn eval_prints_the_serialization_of_the_value() -> Test {
    assert_eq!(
        eval(FACT, "fact(20)", &[])?,
        ("(int 2432902008176640000)\n".to_owned(), Some(0))
    );
    assert_eq!(eval("", "-5", &[])?, ("(int -5)\n".to_owned(), Some(0)));
    assert_eq!(
        eval("", "\"a\\\"b\"", &[])?,
        ("(string \"a\\\"b\")\n".to_owned(), Some(0))
    );
    Ok(())
}

/// The driver prints the result after the evaluator ends, so the serialization of a deep
/// value needs no deep stack.
#[test]
fn eval_prints_a_result_of_depth_10000() -> Test {
    let depth = 10_000;
    let expr = format!("{}0{}", "(".repeat(depth), ",)".repeat(depth));
    let flags = [
        "--syntax-depth",
        "10010",
        "--depth",
        "10010",
        "--fuel",
        "200000000",
    ];
    let (out, code) = eval("", &expr, &flags)?;
    assert_eq!(code, Some(0), "{}", &out[..out.len().min(200)]);
    let expected = format!(
        "{}(int 0){}\n",
        "(tuple (".repeat(depth),
        "))".repeat(depth)
    );
    assert!(out == expected, "{}", &out[..out.len().min(200)]);
    Ok(())
}

#[test]
fn eval_reports_the_first_error_of_the_file_then_of_the_expression() -> Test {
    let first = |r: (String, Option<i32>)| (r.0.split(": ").next().map(str::to_owned), r.1);
    let at = |s: &str| (Some(s.to_owned()), Some(1));
    assert_eq!(
        first(eval("const A: Nat = ;", "x", &[])?),
        at("error[S001]")
    );
    assert_eq!(first(eval("", "1 +", &[])?), at("error[S001]"));
    assert_eq!(first(eval("", "x", &[])?), at("error[S003]"));
    assert_eq!(first(eval("", "UInt[8, 9]", &[])?), at("error[S007]"));
    assert_eq!(first(eval(FACT, "fact(-1)", &[])?), at("error[S012]"));
    let (out, code) = eval(FACT, "fact(3)", &["--depth", "2"])?;
    assert!(out.starts_with("error[S015]: 3:16: "), "{out}");
    assert_eq!(code, Some(1));
    Ok(())
}

#[test]
fn eval_takes_the_budgets() -> Test {
    // The evaluation uses 7 units, and the result `(int 3)` pays its 7 bytes.
    assert_eq!(eval("", "1 + 2", &["--fuel", "14"])?.1, Some(0));
    assert!(
        eval("", "1 + 2", &["--fuel", "13"])?
            .0
            .starts_with("error[S015]: 1:1: ")
    );
    assert!(
        eval("", "1 + 2", &["--fuel", "6"])?
            .0
            .starts_with("error[S015]: 1:1: ")
    );
    assert_eq!(eval("", "1 + 2", &["--fuel", "1_000"])?.1, Some(0));
    assert_eq!(
        eval("", "1 + 2", &["--fuel", "99999999999999999999999"])?.1,
        Some(0)
    );
    for bad in ["_1", "1__0", "1_", "-1", ""] {
        assert_eq!(
            eval("", "1", &["--fuel", bad])?,
            (String::new(), Some(2)),
            "{bad}"
        );
    }
    assert_eq!(eval("", "(((1)))", &["--syntax-depth", "2"])?.1, Some(1));
    assert_eq!(
        eval("", "1", &["--syntax-depth", "0"])?,
        (String::new(), Some(2))
    );
    Ok(())
}

/// An empty array costs one unit but prints its element type. 1,000 references to an empty
/// array of a tuple type of 1,000 `Bool` print about 5 MB, so the result pays its length in
/// bytes before the text exists: the message names the length that the driver measured.
#[test]
fn eval_pays_the_length_of_its_result() -> Test {
    let wide = format!("({})", vec!["Bool"; 1000].join(", "));
    let src = format!(
        "fn f() -> [[{wide}; 0]; 1000] {{ let e: [{wide}; 0] = []; return [{}]; }}\n",
        vec!["e"; 1000].join(", ")
    );
    let path = file("eval-result.si", src.as_bytes())?;
    let full = agree("eval", &["f()"], &path)?;
    let len = text(&full).len() - 1;
    assert!(len > 5_000_000, "{len}");
    let short = text(&agree("eval", &["f()", "--fuel", "20000"], &path)?);
    let paid = format!("error[S015]: 1:1: the fuel cannot pay {len} unit(s) of the result; ");
    let left: u64 = short
        .strip_prefix(&paid)
        .and_then(|rest| rest.split(' ').next())
        .and_then(|n| n.parse().ok())
        .ok_or(short.clone())?;
    let used = 20_000 - left;
    let exact = (used + len as u64).to_string();
    let out = agree("eval", &["f()", "--fuel", &exact], &path)?;
    assert_eq!(out.status.code(), Some(0));
    let less = (used + len as u64 - 1).to_string();
    let out = agree("eval", &["f()", "--fuel", &less], &path)?;
    assert!(text(&out).starts_with("error[S015]: 1:1: "));
    Ok(())
}

#[test]
fn eval_of_a_missing_file_is_a_usage_error() -> Test {
    let missing = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("missing-eval.si");
    let mut command = silicon_command();
    command.arg("eval").arg(missing).arg("1");
    assert_eq!(spawn(&mut command, "")?.status.code(), Some(2));
    Ok(())
}

#[test]
fn eval_does_not_overflow_the_stack() -> Test {
    // A deep recursion with a large nesting depth, and an expression at the syntax depth.
    let deep = "comptime fn d(n: Nat) -> Nat {\n\
        \x20   comptime if (n == 0) { return 0; }\n\
        \x20   return d(n - 1);\n\
        }\n";
    assert_eq!(
        eval(deep, "d(100000)", &["--depth", "1000000"])?,
        ("(int 0)\n".to_owned(), Some(0))
    );
    let expr = format!("{}1{}", "(".repeat(4096), ")".repeat(4096));
    assert_eq!(eval("", &expr, &[])?, ("(int 1)\n".to_owned(), Some(0)));
    let expr = format!("{}1", "-".repeat(4095));
    assert_eq!(eval("", &expr, &[])?, ("(int -1)\n".to_owned(), Some(0)));
    // An argument has at most 128 KiB, so the file holds the million open brackets.
    let expr = "(".repeat(100_000);
    assert!(eval("", &expr, &[])?.0.starts_with("error[S001]: 1:4097: "));
    let open = open_brackets("Nat");
    assert!(
        eval(&open, "1", &[])?
            .0
            .starts_with("error[S001]: 1:4112: ")
    );
    let out = agree("eval", &["1"], &file("open-eval.si", open.as_bytes())?)?;
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

/// Runs `silicon cost FILE --top TOP` with the flags `flags`. Each call has its own file.
fn cost(src: &str, top: &str, flags: &[&str]) -> std::io::Result<(String, Option<i32>)> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = file(
        &format!("cost-{}-{n}.si", std::process::id()),
        src.as_bytes(),
    )?;
    let mut command = silicon_command();
    command
        .arg("cost")
        .arg(path)
        .arg("--top")
        .arg(top)
        .args(flags);
    let out = spawn(&mut command, "")?;
    Ok((text(&out), out.status.code()))
}

const TOPS: &str = "module Counter(comptime W: Nat, comptime E: Bool) {\n}\n\
    module Top() {\n    instance a = Counter(8, true);\n    instance b = Counter(8, true);\n}\n";

#[test]
fn cost_prints_the_total_and_the_units_of_each_instantiation() -> Test {
    assert_eq!(
        cost(TOPS, "Counter(8, true)", &[])?,
        ("total 114\nCounter$8$1b 34\n".to_owned(), Some(0))
    );
    assert_eq!(
        cost(TOPS, "Top", &[])?,
        ("total 325\nCounter$8$1b 34\nTop 257\n".to_owned(), Some(0))
    );
    Ok(())
}

#[test]
fn cost_reports_the_first_error_and_takes_the_budgets() -> Test {
    let first = |r: (String, Option<i32>)| (r.0.split(": ").next().map(str::to_owned), r.1);
    let at = |s: &str| (Some(s.to_owned()), Some(1));
    assert_eq!(first(cost("module M( {}", "M", &[])?), at("error[S001]"));
    assert_eq!(first(cost(TOPS, "Counter(8)", &[])?), at("error[S007]"));
    assert_eq!(
        first(cost(TOPS, "Counter(8, true)", &["--fuel", "113"])?),
        at("error[S015]")
    );
    assert_eq!(
        cost(TOPS, "Counter(8, true)", &["--fuel", "114"])?.1,
        Some(0)
    );
    assert_eq!(
        first(cost(TOPS, "Counter(8, true)", &["--depth", "0"])?),
        at("error[S015]")
    );
    let wire = "module M() {\n  wire w: Bool;\n}\n";
    let (out, code) = cost(wire, "M", &[])?;
    assert!(out.starts_with("error[S018]: 2:3: "), "{out}");
    assert_eq!(code, Some(1));
    Ok(())
}

#[test]
fn cost_of_a_bad_top_selection_is_a_usage_error() -> Test {
    for top in ["Counter(8 + 1, true)", "Nope", "1"] {
        assert_eq!(cost(TOPS, top, &[])?, (String::new(), Some(2)), "{top}");
    }
    let path = file("cost-no-top.si", TOPS.as_bytes())?;
    let mut command = silicon_command();
    command.arg("cost").arg(path);
    assert_eq!(spawn(&mut command, "")?.status.code(), Some(2));
    Ok(())
}

/// Runs `silicon COMMAND FILE ARGS --top TOP` with the input `stdin`. Each call has its own
/// file.
fn source(
    command: &str,
    src: &str,
    args: &[&str],
    top: &str,
    stdin: &str,
) -> std::io::Result<(String, Option<i32>)> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = file(
        &format!("{command}-{}-{n}.si", std::process::id()),
        src.as_bytes(),
    )?;
    let mut cmd = silicon_command();
    cmd.arg(command).arg(path).args(args).arg("--top").arg(top);
    let out = spawn(&mut cmd, stdin)?;
    Ok((text(&out), out.status.code()))
}

const COUNTER_SI: &str = "module Counter(comptime W: Nat) {\n  input i: UInt[W];\n  \
    output q: UInt[W];\n  reg r: UInt[W] = 0;\n  r := r +% i;\n  q := r;\n}\n";

/// The output of `silicon-check elab` for `COUNTER_SI` with the top `Counter(4)`.
const COUNTER_SIL: &str = "(design Counter$4\n  (module Counter$4\n    \
    (input clock$0clk clock)\n    (input clock$0rst (bits 1))\n    (input i (bits 4))\n    \
    (output q (bits 4))\n    (reg r (bits 4) clock$0clk (reset sync clock$0rst (const 4 0)))\n    \
    (next r (add r i))\n    (assign q r)))\n";

#[test]
fn elab_prints_the_canonical_core_ir() -> Test {
    assert_eq!(
        source("elab", COUNTER_SI, &[], "Counter(4)", "")?,
        (COUNTER_SIL.to_owned(), Some(0))
    );
    Ok(())
}

#[test]
fn elab_reports_the_first_error_and_takes_the_budgets() -> Test {
    assert_eq!(
        source("elab", COUNTER_SI, &[], "Counter(true)", "")?,
        (
            "error[S010]: 1:1: expected Nat, but the value is Bool\n".to_owned(),
            Some(1)
        )
    );
    let (out, code) = source("elab", COUNTER_SI, &["--fuel", "160"], "Counter(4)", "")?;
    assert!(out.starts_with("error[S015]: 1:1: "), "{out}");
    assert_eq!(code, Some(1));
    assert_eq!(
        source("elab", COUNTER_SI, &["--fuel", "161"], "Counter(4)", "")?,
        (COUNTER_SIL.to_owned(), Some(0))
    );
    assert_eq!(
        source("elab", COUNTER_SI, &[], "Counter(4 + 1)", "")?,
        (String::new(), Some(2))
    );
    Ok(())
}

#[test]
fn validate_compares_the_canonical_core_ir() -> Test {
    let validate = |sil: &str| -> std::io::Result<(String, Option<i32>)> {
        let path = file(
            &format!("validate-{}-{}.sil", std::process::id(), sil.len()),
            sil.as_bytes(),
        )?;
        let path = path.to_string_lossy().into_owned();
        source("validate", COUNTER_SI, &[&path], "Counter(4)", "")
    };
    assert_eq!(validate(COUNTER_SIL)?, ("ok\n".to_owned(), Some(0)));
    assert_eq!(
        validate(&COUNTER_SIL.replace("(add r i)", "(sub r i)"))?,
        (
            "mismatch at line 8: expected `    (next r (add r i))`, found `    (next r (sub r i))`\n"
                .to_owned(),
            Some(1)
        )
    );
    let (out, code) = validate("(design X\n")?;
    assert!(out.starts_with("error[E001]: 2:1: "), "{out}");
    assert_eq!(code, Some(1));
    Ok(())
}

#[test]
fn run_of_a_source_file_reads_source_vectors() -> Test {
    let input = "in=(clock$0rst false i 3)\nin=(clock$0rst false i 15)\n\
        in=(clock$0rst true i 1)\nin=(clock$0rst false i 0)\n";
    assert_eq!(
        source("run", COUNTER_SI, &[], "Counter(4)", input)?,
        (
            "out=(q 0)\nout=(q 3)\nout=(q 2)\nout=(q 0)\n".to_owned(),
            Some(0)
        )
    );
    assert_eq!(
        source(
            "run",
            COUNTER_SI,
            &[],
            "Counter(4)",
            "in=(clock$0rst false i 3)\nin=(i 3)\n"
        )?,
        ("out=(q 0)\n".to_owned(), Some(2))
    );
    Ok(())
}

const COMBINATIONAL_SI: &str =
    "module Id() domains() {\n  input a: UInt[4];\n  output q: UInt[4];\n  q := a;\n}\n";

/// A fresh folder for the artifacts of one build test, with `src` in it as `x.si`. Returns the
/// folder and the path of the source.
fn build_folder(name: &str, src: &str) -> std::io::Result<(PathBuf, PathBuf)> {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("build-{name}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir)?;
    let path = dir.join("x.si");
    std::fs::write(&path, src)?;
    Ok((dir, path))
}

fn build(path: &Path, top: &str, args: &[&str], checker: Option<&str>) -> std::io::Result<Output> {
    let mut command = silicon_command();
    command
        .arg("build")
        .arg(path)
        .args(args)
        .arg("--top")
        .arg(top);
    if let Some(checker) = checker {
        command.env(CHECK_VARIABLE, checker);
    }
    spawn(&mut command, "")
}

#[test]
fn build_validates_and_writes_the_artifacts() -> Test {
    let (dir, path) = build_folder("validated", COUNTER_SI)?;
    let out = build(&path, "Counter(4)", &[], None)?;
    assert_eq!(
        (text(&out).as_str(), out.status.code()),
        ("validated\n", Some(0))
    );
    assert_eq!(std::fs::read_to_string(dir.join("x.sil"))?, COUNTER_SIL);
    assert!(!std::fs::read_to_string(dir.join("x.sv"))?.is_empty());
    Ok(())
}

#[test]
fn build_without_validation_says_so() -> Test {
    let (dir, path) = build_folder("skipped", COUNTER_SI)?;
    let out = build(
        &path,
        "Counter(4)",
        &["--no-validate"],
        Some("/no/such/silicon-check"),
    )?;
    assert_eq!(
        (text(&out).as_str(), out.status.code()),
        ("not validated\n", Some(0))
    );
    assert!(dir.join("x.sil").is_file() && dir.join("x.sv").is_file());
    Ok(())
}

#[test]
fn build_out_names_the_artifacts() -> Test {
    let (dir, path) = build_folder("out", COUNTER_SI)?;
    std::fs::create_dir(dir.join("sub"))?;
    let prefix = dir.join("sub/name");
    let out = build(
        &path,
        "Counter(4)",
        &["--out", &prefix.to_string_lossy()],
        None,
    )?;
    assert_eq!(out.status.code(), Some(0));
    assert!(dir.join("sub/name.sil").is_file() && dir.join("sub/name.sv").is_file());
    assert!(!dir.join("x.sil").exists() && !dir.join("x.sv").exists());
    Ok(())
}

#[test]
fn build_of_a_bad_design_writes_nothing() -> Test {
    let (dir, path) = build_folder(
        "bad",
        "module M() domains() {\n  output q: Bool;\n  q := nope;\n}\n",
    )?;
    let out = build(&path, "M()", &[], None)?;
    assert!(text(&out).starts_with("error[S003]"), "{}", text(&out));
    assert_eq!(out.status.code(), Some(1));
    assert!(!dir.join("x.sil").exists() && !dir.join("x.sv").exists());
    Ok(())
}

#[test]
fn build_into_a_missing_folder_is_a_usage_error() -> Test {
    let (dir, path) = build_folder("missing", COUNTER_SI)?;
    let prefix = dir.join("missing/x");
    let out = build(
        &path,
        "Counter(4)",
        &["--out", &prefix.to_string_lossy()],
        None,
    )?;
    assert_eq!((text(&out).as_str(), out.status.code()), ("", Some(2)));
    assert!(String::from_utf8_lossy(&out.stderr).contains("missing/x.sil"));
    Ok(())
}

/// A folder in the place of `x.sil` makes the write fail, even for a user who may write
/// anywhere.
#[test]
fn build_with_an_unwritable_sil_is_a_usage_error_without_sv() -> Test {
    let (dir, path) = build_folder("unwritable", COUNTER_SI)?;
    std::fs::create_dir(dir.join("x.sil"))?;
    let out = build(&path, "Counter(4)", &[], None)?;
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("x.sil"));
    assert!(!dir.join("x.sv").exists());
    Ok(())
}

#[test]
fn build_with_a_missing_checker_is_a_usage_error() -> Test {
    let (dir, path) = build_folder("no-checker", COUNTER_SI)?;
    let out = build(&path, "Counter(4)", &[], Some("/nonexistent"))?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr.contains("--no-validate"), "{stderr}");
    assert!(!dir.join("x.sv").exists() && !dir.join("x.sil").exists());
    Ok(())
}

/// `false` exits with 1 and prints no line, so it is no verdict on the design.
#[test]
fn build_with_a_checker_that_gives_no_verdict_is_a_usage_error() -> Test {
    let (dir, path) = build_folder("no-verdict", COUNTER_SI)?;
    let out = build(&path, "Counter(4)", &[], Some("false"))?;
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("--no-validate"));
    assert!(!dir.join("x.sv").exists() && !dir.join("x.sil").exists());
    Ok(())
}

/// `true` exits with 0 and prints no `ok`, so it is no verdict on the design.
#[test]
fn build_with_a_checker_that_only_exits_0_is_a_usage_error() -> Test {
    let (dir, path) = build_folder("exit-0", COUNTER_SI)?;
    let out = build(&path, "Counter(4)", &[], Some("true"))?;
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("--no-validate"));
    assert!(!dir.join("x.sv").exists() && !dir.join("x.sil").exists());
    Ok(())
}

#[test]
fn a_failed_build_removes_an_old_sv() -> Test {
    let (dir, path) = build_folder("stale", COUNTER_SI)?;
    assert_eq!(
        build(&path, "Counter(4)", &[], None)?.status.code(),
        Some(0)
    );
    let out = build(&path, "Counter(4)", &[], Some("false"))?;
    assert_eq!(out.status.code(), Some(2));
    assert!(!dir.join("x.sv").exists() && !dir.join("x.sil").exists());
    Ok(())
}

#[test]
fn build_never_overwrites_its_input() -> Test {
    let (dir, _) = build_folder("input", COUNTER_SI)?;
    let path = dir.join("x.sil");
    std::fs::write(&path, COUNTER_SI)?;
    let out = build(&path, "Counter(4)", &[], None)?;
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(std::fs::read_to_string(&path)?, COUNTER_SI);
    assert!(!dir.join("x.sv").exists());
    Ok(())
}

#[test]
fn build_of_a_combinational_top_validates() -> Test {
    let (dir, path) = build_folder("combinational", COMBINATIONAL_SI)?;
    let out = build(&path, "Id()", &[], None)?;
    assert_eq!(
        (text(&out).as_str(), out.status.code()),
        ("validated\n", Some(0))
    );
    assert!(dir.join("x.sil").is_file() && dir.join("x.sv").is_file());
    Ok(())
}

#[test]
fn build_with_budgets_validates() -> Test {
    let (_, path) = build_folder("budget", COUNTER_SI)?;
    let out = build(
        &path,
        "Counter(4)",
        &["--fuel", "161", "--depth", "50", "--syntax-depth", "100"],
        None,
    )?;
    assert_eq!(
        (text(&out).as_str(), out.status.code()),
        ("validated\n", Some(0))
    );
    let out = build(&path, "Counter(4)", &["--fuel", "160"], None)?;
    assert!(text(&out).starts_with("error[S015]"), "{}", text(&out));
    assert_eq!(out.status.code(), Some(1));
    Ok(())
}

/// Runs `build` on `input` with `--out` set to the prefix, in `dir`, and checks that the
/// command refuses and that the input bytes stay.
fn build_refuses_alias(name: &str, alias: fn(&Path, &Path) -> std::io::Result<()>) -> Test {
    let (dir, path) = build_folder(name, COUNTER_SI)?;
    alias(&path, &dir.join("x.sil"))?;
    let out = build(&path, "Counter(4)", &[], None)?;
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(std::fs::read_to_string(&path)?, COUNTER_SI);
    assert!(!dir.join("x.sv").exists());
    Ok(())
}

#[test]
fn build_refuses_a_symlink_to_the_input() -> Test {
    build_refuses_alias("symlink", |input, link| {
        std::os::unix::fs::symlink(input, link)
    })
}

#[test]
fn build_refuses_a_hard_link_to_the_input() -> Test {
    build_refuses_alias("hardlink", |input, link| std::fs::hard_link(input, link))
}

#[test]
fn build_refuses_another_spelling_of_the_input() -> Test {
    let (dir, path) = build_folder("spelling", COUNTER_SI)?;
    let alias = dir.join("x.sil");
    std::fs::write(&alias, COUNTER_SI)?;
    let mut command = silicon_command();
    command
        .current_dir(&dir)
        .args(["build", "x.sil", "--top", "Counter(4)", "--out"])
        .arg(dir.join("x"));
    let out = spawn(&mut command, "")?;
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(std::fs::read_to_string(&alias)?, COUNTER_SI);
    assert!(path.exists() && !dir.join("x.sv").exists());
    Ok(())
}

/// `write_artifact` removes `PATH.tmp` first, so a temp path must not be the input either.
#[test]
fn build_refuses_an_input_at_a_temp_path() -> Test {
    for name in ["x.sil.tmp", "x.sv.tmp"] {
        let (dir, _) = build_folder(&format!("temp-{name}"), COUNTER_SI)?;
        let path = dir.join(name);
        std::fs::write(&path, COUNTER_SI)?;
        let out = build(
            &path,
            "Counter(4)",
            &["--out", &dir.join("x").to_string_lossy()],
            None,
        )?;
        assert_eq!(out.status.code(), Some(2), "{name}");
        assert_eq!(std::fs::read_to_string(&path)?, COUNTER_SI, "{name}");
        assert!(
            !dir.join("x.sil").exists() && !dir.join("x.sv").exists(),
            "{name}"
        );
    }
    Ok(())
}

/// Lean validates before the backend runs, so without `firtool` the build fails after an
/// accepted verdict and leaves no artifact, also none of an earlier build.
#[test]
fn build_without_firtool_leaves_no_artifact() -> Test {
    let (dir, path) = build_folder("no-firtool", COUNTER_SI)?;
    assert_eq!(
        build(&path, "Counter(4)", &[], None)?.status.code(),
        Some(0)
    );
    for args in [&[][..], &["--no-validate"]] {
        let mut command = silicon_command();
        command
            .arg("build")
            .arg(&path)
            .args(args)
            .args(["--top", "Counter(4)"])
            .env("PATH", "");
        let out = spawn(&mut command, "")?;
        assert_eq!(
            (text(&out).as_str(), out.status.code()),
            ("", Some(2)),
            "{args:?}"
        );
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.contains("firtool"), "{stderr}");
        assert!(
            !dir.join("x.sil").exists() && !dir.join("x.sv").exists(),
            "{args:?}"
        );
    }
    Ok(())
}
