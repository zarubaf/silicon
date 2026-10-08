//! Tests of the `silicon` binary: output bytes and exit codes.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

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

type Test = Result<(), Box<dyn std::error::Error>>;

fn file(name: &str, bytes: &[u8]) -> std::io::Result<PathBuf> {
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    std::fs::write(&path, bytes)?;
    Ok(path)
}

fn silicon(args: &[&str], path: &PathBuf, stdin: &str) -> std::io::Result<Output> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_silicon"))
        .args(args)
        .arg(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(mut pipe) = child.stdin.take() {
        // A command that fails before it reads stdin closes the pipe.
        match pipe.write_all(stdin.as_bytes()) {
            Err(e) if e.kind() != std::io::ErrorKind::BrokenPipe => return Err(e),
            _ => {}
        }
    }
    child.wait_with_output()
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
    for (name, input) in [("blank.sil", "in=(rst 1 en 0)\n\n"), ("bare.sil", "in=\n")] {
        let out = silicon(&["run"], &file(name, COUNTER.as_bytes())?, input)?;
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
