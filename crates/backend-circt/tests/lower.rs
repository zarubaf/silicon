//! Tests of the lowering to MLIR: each lowered design parses with
//! `circt-opt`, and the names and ports follow spec section 7.3.

use std::error::Error;
use std::io::Write;
use std::process::{Command, Output, Stdio};

use backend_circt::{MemConfig, lower, memory_configs};
use core_ir::check::check;
use core_ir::text::parse;
use core_ir::typed::Design;

type Test = Result<(), Box<dyn Error>>;

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

/// Depth 12 has the address width 4, so each access needs a guard. The
/// `read` of `b` comes after the `read` of `a` in the canonical text.
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
    (let b (bits 8) (read m y))
    (let a (bits 8) (read m x))
    (write m 0 x d we)
    (assign p a)
    (assign q b)))
";

const EXTERN: &str = "\
(design top
  (extern blk
    (output y (bits 4))
    (input c clock)
    (input a (bits 4))
    (deps y (a)))
  (module top
    (input clk clock)
    (input a (bits 4))
    (output q (bits 4))
    (inst u blk (c clk) (a a))
    (assign q u.y)))
";

/// The clock is the third port, and the outputs are between the inputs.
const CLOCK_LATE: &str = "\
(design top
  (module child
    (input a (bits 2))
    (output y (bits 2))
    (input k clock)
    (reg r (bits 2) k)
    (next r a)
    (assign y r))
  (module top
    (input a (bits 2))
    (output q (bits 2))
    (input clk clock)
    (output p (bits 2))
    (inst u child (k clk) (a a))
    (assign q u.y)
    (assign p (not a))))
";

/// Two memories with the same depth and width and other port counts.
const TWO_MEMORIES: &str = "\
(design top
  (module top
    (input clk clock)
    (input x (bits 3))
    (output p (bits 4))
    (mem m (bits 4) 8 clk)
    (mem n (bits 4) 8 clk)
    (write n 0 x (const 4 1) (const 1 1))
    (assign p (xor (read m x) (read n x)))))
";

/// Each operation of the core IR on a pair of inputs.
const OPERATIONS: &str = "\
(design ops
  (module ops
    (input a (bits 4))
    (input b (bits 4))
    (input c (bits 1))
    (output sum (bits 4))
    (output dif (bits 4))
    (output pro (bits 4))
    (output con (bits 4))
    (output dis (bits 4))
    (output exc (bits 4))
    (output inv (bits 4))
    (output cat (bits 8))
    (output lt (bits 1))
    (output sel (bits 4))
    (output ext (bits 2))
    (output rep (bits 8))
    (output k (bits 4))
    (assign sum (add a b))
    (assign dif (sub a b))
    (assign pro (mul a b))
    (assign con (and a b))
    (assign dis (or a b))
    (assign exc (xor a b))
    (assign inv (not a))
    (assign cat (concat a b))
    (assign lt (icmp slt a b))
    (assign sel (mux c a b))
    (assign ext (extract a 1 2))
    (assign rep (replicate a 2))
    (assign k (const 4 15))))
";

/// The shifts with a free amount: the amounts `4` and more are in range.
const SHIFTS: &str = "\
(design shifts
  (module shifts
    (input x (bits 4))
    (input s (bits 4))
    (output l (bits 4))
    (output u (bits 4))
    (output r (bits 4))
    (assign l (shl x s))
    (assign u (shru x s))
    (assign r (shrs x s))))
";

/// The meaning of spec section 4.1, with an explicit guard for an amount of
/// the width or more.
const SHIFTS_REFERENCE: &str = "
hw.module @reference(in %x : i4, in %s : i4, out l : i4, out u : i4, out r : i4) {
  %c4 = hw.constant 4 : i4
  %c3 = hw.constant 3 : i4
  %c0 = hw.constant 0 : i4
  %in = comb.icmp ult %s, %c4 : i4
  %l0 = comb.shl %x, %s : i4
  %u0 = comb.shru %x, %s : i4
  %r0 = comb.shrs %x, %s : i4
  %fill = comb.shrs %x, %c3 : i4
  %l = comb.mux %in, %l0, %c0 : i4
  %u = comb.mux %in, %u0, %c0 : i4
  %r = comb.mux %in, %r0, %fill : i4
  hw.output %l, %u, %r : i4, i4, i4
}
";

fn design(src: &str) -> Result<Design, Box<dyn Error>> {
    let ast = parse(src).map_err(|d| d.to_string())?;
    Ok(check(&ast).map_err(|d| d.to_string())?)
}

/// Runs `tool` with `args` and `stdin`.
fn run(tool: &str, args: &[&str], stdin: &str) -> Result<Output, Box<dyn Error>> {
    let mut child = Command::new(tool)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("{tool}: {e}"))?;
    if let Some(mut pipe) = child.stdin.take() {
        pipe.write_all(stdin.as_bytes())?;
    }
    Ok(child.wait_with_output()?)
}

/// Lowers `src` and checks that `circt-opt` parses and verifies the result.
fn lowered(src: &str) -> Result<String, Box<dyn Error>> {
    let mlir = lower(&design(src)?);
    let out = run("circt-opt", &[], &mlir)?;
    assert!(
        out.status.success(),
        "{}\n{mlir}",
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(mlir)
}

fn line<'a>(mlir: &'a str, start: &str) -> Result<&'a str, String> {
    mlir.lines()
        .map(str::trim)
        .find(|l| l.starts_with(start))
        .ok_or_else(|| format!("no line starts with `{start}` in\n{mlir}"))
}

#[test]
fn the_counter_parses() -> Test {
    let mlir = lowered(COUNTER)?;
    assert_eq!(
        line(&mlir, "hw.module @counter")?,
        "hw.module @counter(in %clk : !seq.clock, in %rst : i1, in %en : i1, out q : i8) {"
    );
    let reg = line(&mlir, "%silicon_reg_r = seq.compreg ")?;
    assert!(reg.contains(", %clk reset %rst, "), "{reg}");
    assert!(line(&mlir, "hw.output %silicon_reg_r : i8").is_ok());
    Ok(())
}

#[test]
fn a_memory_is_an_extern_instance_with_the_spec_ports() -> Test {
    let mlir = lowered(MEMORY)?;
    assert_eq!(
        line(&mlir, "hw.module.extern @silicon_mem_")?,
        "hw.module.extern @silicon_mem_12x8_r2w1(in %clk : !seq.clock, \
         in %r0_addr : i4, out r0_data : i8, in %r1_addr : i4, out r1_data : i8, \
         in %w0_addr : i4, in %w0_data : i8, in %w0_en : i1)"
    );
    let inst = mlir
        .lines()
        .find(|l| l.contains("hw.instance \"m\""))
        .ok_or("no memory instance")?;
    assert!(
        inst.contains("@silicon_mem_12x8_r2w1(clk: %clk: !seq.clock, r0_addr: %x: i4, r1_addr: %y: i4, w0_addr: %x: i4, w0_data: %d: i8, w0_en: "),
        "{inst}"
    );
    assert_eq!(
        memory_configs(&design(MEMORY)?),
        vec![MemConfig {
            depth: 12,
            width: 8,
            reads: 2,
            writes: 1
        }]
    );
    Ok(())
}

#[test]
fn the_guards_stay_in_the_parent() -> Test {
    let mlir = lowered(MEMORY)?;
    // One guard for each read port and one for the write port.
    let guards = mlir.lines().filter(|l| l.contains("comb.icmp ult")).count();
    assert_eq!(guards, 3, "{mlir}");
    assert!(line(&mlir, "%a = comb.mux ")?.ends_with(": i8"));
    assert!(line(&mlir, "%b = comb.mux ")?.ends_with(": i8"));
    Ok(())
}

#[test]
fn a_memory_with_a_full_address_range_has_no_guard() -> Test {
    let mlir = lowered(TWO_MEMORIES)?;
    assert!(!mlir.contains("comb.icmp"), "{mlir}");
    Ok(())
}

#[test]
fn other_port_counts_give_other_names() -> Test {
    let mlir = lowered(TWO_MEMORIES)?;
    let configs = memory_configs(&design(TWO_MEMORIES)?);
    let names: Vec<String> = configs.iter().map(MemConfig::module_name).collect();
    assert_eq!(names, ["silicon_mem_8x4_r1w0", "silicon_mem_8x4_r1w1"]);
    for name in &names {
        assert!(
            mlir.contains(&format!("hw.module.extern @{name}(")),
            "{mlir}"
        );
        assert!(mlir.contains(&format!("@{name}(clk: %clk")), "{mlir}");
    }
    Ok(())
}

#[test]
fn an_extern_is_a_module_extern_with_an_instance() -> Test {
    let mlir = lowered(EXTERN)?;
    assert_eq!(
        line(&mlir, "hw.module.extern @blk")?,
        "hw.module.extern @blk(out y : i4, in %c : !seq.clock, in %a : i4)"
    );
    assert_eq!(
        line(&mlir, "%u.y = hw.instance")?,
        "%u.y = hw.instance \"u\" @blk(c: %clk: !seq.clock, a: %a: i4) -> (y: i4)"
    );
    Ok(())
}

#[test]
fn the_ports_keep_the_source_order() -> Test {
    let mlir = lowered(CLOCK_LATE)?;
    assert_eq!(
        line(&mlir, "hw.module @child")?,
        "hw.module @child(in %a : i2, out y : i2, in %k : !seq.clock) {"
    );
    assert_eq!(
        line(&mlir, "hw.module @top")?,
        "hw.module @top(in %a : i2, out q : i2, in %clk : !seq.clock, out p : i2) {"
    );
    assert_eq!(
        line(&mlir, "%u.y = hw.instance")?,
        "%u.y = hw.instance \"u\" @child(a: %a: i2, k: %clk: !seq.clock) -> (y: i2)"
    );
    Ok(())
}

#[test]
fn each_operation_parses() -> Test {
    let mlir = lowered(OPERATIONS)?;
    for op in [
        "comb.add",
        "comb.sub",
        "comb.mul",
        "comb.and",
        "comb.or",
        "comb.xor",
        "comb.concat",
        "comb.icmp slt",
        "comb.mux",
        "comb.extract",
        "comb.replicate",
        "hw.constant 15 : i4",
        "hw.constant -1 : i4",
    ] {
        assert!(mlir.contains(op), "no `{op}` in\n{mlir}");
    }
    Ok(())
}

/// CIRCT 1.160 gives a shift amount of the width or more the meaning of
/// spec section 4.1, so the lowering emits no guard. The proof covers each
/// amount, in range and out of range.
#[test]
fn a_shift_out_of_range_matches_the_spec() -> Test {
    let mlir = lowered(SHIFTS)?;
    assert!(!mlir.contains("comb.mux"), "{mlir}");
    let z3 = std::env::var("SILICON_Z3_LIB").map_err(|_| "SILICON_Z3_LIB is not set")?;
    let input = format!("{mlir}{SHIFTS_REFERENCE}");
    let out = run(
        "circt-lec",
        &[
            "-",
            "--c1=shifts",
            "--c2=reference",
            "--run",
            &format!("--shared-libs={z3}"),
        ],
        &input,
    )?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success() && stdout.contains("c1 == c2"),
        "{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(())
}

/// The `reset` of a `reg` comes before each `let`, and an outer `read` comes
/// before the `read` in its address.
#[test]
fn the_read_ports_follow_the_canonical_text() -> Test {
    let src = "\
(design top
  (module top
    (input clk clock)
    (input x (bits 4))
    (input y (bits 4))
    (input we (bits 1))
    (output q (bits 8))
    (mem m (bits 8) 16 clk)
    (let b (bits 8) (read m y))
    (let a (bits 8) (read m (extract (read m x) 0 4)))
    (reg c (bits 8) clk (reset sync we (read m y)))
    (next c (xor a b))
    (assign q c)))
";
    let mlir = lowered(src)?;
    let inst = mlir
        .lines()
        .find(|l| l.contains("hw.instance \"m\""))
        .ok_or("no memory instance")?;
    // With depth 16 each read is in range: the data of a read is its value.
    assert!(inst.trim().starts_with("%0, %a, %1, %b = "), "{inst}");
    assert!(
        inst.contains("(clk: %clk: !seq.clock, r0_addr: %y: i4, "),
        "{inst}"
    );
    assert!(
        inst.contains(", r2_addr: %x: i4, r3_addr: %y: i4)"),
        "{inst}"
    );
    Ok(())
}
