//! The MLIR text that the LEC of spec section 8.1 reads and writes: module
//! headers, the wrappers, and the definitions that replace the externs.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};
use std::num::NonZeroU32;

use anyhow::{Context, Result, bail, ensure};

/// The name of the wrapper module on both sides. No user module can have it,
/// because rule `E002` reserves the prefix `silicon_`.
pub const WRAPPER: &str = "silicon_lec";

const CLOCK: &str = "!seq.clock";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    In,
    Out,
}

/// A port of a module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Port {
    pub dir: Dir,
    pub name: String,
    pub ty: String,
}

impl Port {
    fn is_clock(&self) -> bool {
        self.ty == CLOCK
    }
}

impl fmt::Display for Port {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dir = match self.dir {
            Dir::In => "in",
            Dir::Out => "out",
        };
        write!(f, "{dir} {:?} : {}", self.name, self.ty)
    }
}

/// The ports of the module `name` in `mlir`, in the order of its header.
pub fn ports(mlir: &str, name: &str) -> Result<Vec<Port>> {
    let line = mlir
        .lines()
        .map(str::trim_start)
        .find(|l| declares(l, name))
        .with_context(|| format!("no module `{name}` in the MLIR"))?;
    header_ports(line).with_context(|| format!("cannot read the header `{line}`"))
}

/// Whether `line` is the header of the module `name`, with or without a body.
fn declares(line: &str, name: &str) -> bool {
    ["hw.module @", "hw.module private @", "hw.module.extern @"]
        .iter()
        .filter_map(|prefix| line.strip_prefix(prefix))
        .filter_map(|rest| rest.strip_prefix(name))
        .any(|rest| rest.starts_with('('))
}

/// The ports of the header `line`.
fn header_ports(line: &str) -> Result<Vec<Port>> {
    let open = line.find('(').context("no port list")?;
    let list = &line[open + 1..];
    let close = top_level(list, ')').context("the port list does not end")?;
    let list = &list[..close];
    let mut ports = Vec::new();
    let mut rest = list;
    while !rest.trim().is_empty() {
        let end = top_level(rest, ',').unwrap_or(rest.len());
        ports.push(port(rest[..end].trim())?);
        rest = rest.get(end + 1..).unwrap_or("");
    }
    Ok(ports)
}

/// The index of the first `stop` in `text` outside of brackets and quotes.
fn top_level(text: &str, stop: char) -> Option<usize> {
    let mut depth = 0usize;
    let mut quoted = false;
    for (i, c) in text.char_indices() {
        match c {
            '"' => quoted = !quoted,
            _ if quoted => {}
            _ if c == stop && depth == 0 => return Some(i),
            '(' | '<' | '[' | '{' => depth += 1,
            ')' | '>' | ']' | '}' => depth = depth.checked_sub(1)?,
            _ => {}
        }
    }
    None
}

/// One port: `in %ssa : T`, `in %ssa "name" : T`, `out name : T`, or
/// `out "name" : T`.
fn port(entry: &str) -> Result<Port> {
    let (dir, rest) = if let Some(rest) = entry.strip_prefix("in ") {
        (Dir::In, rest)
    } else if let Some(rest) = entry.strip_prefix("out ") {
        (Dir::Out, rest)
    } else {
        bail!("the port `{entry}` has no direction");
    };
    let (names, ty) = rest
        .split_once(" : ")
        .with_context(|| format!("the port `{entry}` has no type"))?;
    let name = match (dir, names.split_once(' ')) {
        (Dir::In, Some((_, quoted))) => unquote(quoted)?,
        (Dir::In, None) => names
            .strip_prefix('%')
            .with_context(|| format!("the input `{entry}` has no value name"))?
            .to_owned(),
        (Dir::Out, _) if names.starts_with('"') => unquote(names)?,
        (Dir::Out, _) => names.to_owned(),
    };
    Ok(Port {
        dir,
        name,
        ty: ty.trim().to_owned(),
    })
}

fn unquote(text: &str) -> Result<String> {
    let inner = text
        .strip_prefix('"')
        .and_then(|t| t.strip_suffix('"'))
        .with_context(|| format!("`{text}` is not a quoted name"))?;
    ensure!(!inner.contains('\\'), "the name `{text}` has an escape");
    Ok(inner.to_owned())
}

/// The ports of `ports` with their index, sorted by name, after a check
/// against `other`, the ports of the other side. Each name occurs once on
/// each side, and each port has the same direction and type on both sides.
fn matched<'a>(ports: &'a [Port], other: &[Port]) -> Result<Vec<(usize, &'a Port)>> {
    let ours = by_name(ports)?;
    let theirs = by_name(other)?;
    for (name, (_, port)) in &ours {
        match theirs.get(name) {
            None => bail!("the port `{name}` has no match on the other side"),
            Some(&(_, them)) if them != *port => {
                bail!("the port `{port}` does not match `{them}` on the other side")
            }
            Some(_) => {}
        }
    }
    if let Some(name) = theirs.keys().find(|n| !ours.contains_key(*n)) {
        bail!("the port `{name}` of the other side has no match");
    }
    Ok(ours.into_values().collect())
}

fn by_name(ports: &[Port]) -> Result<BTreeMap<&str, (usize, &Port)>> {
    let mut map = BTreeMap::new();
    for (i, port) in ports.iter().enumerate() {
        ensure!(
            map.insert(port.name.as_str(), (i, port)).is_none(),
            "the port name `{}` occurs twice",
            port.name
        );
    }
    Ok(map)
}

/// The wrapper of the module `top`, whose ports are `ports`. `other` holds
/// the ports of the top module on the other side. The wrapper has the data
/// ports of both sides sorted by name and connects them by name. A constant
/// drives each clock port: after `--externalize-registers` the clock drives
/// nothing. `circt-lec` reads no `seq` dialect, so the clock is an `i1`.
/// The value of the port at index `i` of `top` is `%v<i>`.
pub fn wrapper(top: &str, ports: &[Port], other: &[Port]) -> Result<String> {
    let sorted: Vec<(usize, &Port)> = matched(ports, other)?
        .into_iter()
        .filter(|(_, p)| !p.is_clock())
        .collect();
    let header: Vec<String> = sorted
        .iter()
        .map(|(i, p)| match p.dir {
            Dir::In => format!("in %v{i} {:?} : {}", p.name, p.ty),
            Dir::Out => format!("out {:?} : {}", p.name, p.ty),
        })
        .collect();
    let mut args = Vec::new();
    let mut results = Vec::new();
    let mut result_types = Vec::new();
    for (i, p) in ports.iter().enumerate() {
        match p.dir {
            Dir::In if p.is_clock() => args.push(format!("{:?}: %silicon_clock: i1", p.name)),
            Dir::In => args.push(format!("{:?}: %v{i}: {}", p.name, p.ty)),
            Dir::Out => {
                results.push(format!("%v{i}"));
                result_types.push(format!("{:?}: {}", p.name, p.ty));
            }
        }
    }
    let mut out = format!("hw.module @{WRAPPER}({}) {{\n", header.join(", "));
    out.push_str("  %silicon_clock = hw.constant false\n  ");
    if !results.is_empty() {
        let _ = write!(out, "{} = ", results.join(", "));
    }
    let _ = writeln!(
        out,
        "hw.instance \"dut\" @{top}({}) -> ({})",
        args.join(", "),
        result_types.join(", ")
    );
    let (values, types): (Vec<String>, Vec<&str>) = sorted
        .iter()
        .filter(|(_, p)| p.dir == Dir::Out)
        .map(|(i, p)| (format!("%v{i}"), p.ty.as_str()))
        .unzip();
    out.push_str(&output(&values, &types));
    Ok(out)
}

/// The `hw.output` of `values` with `types`, and the end of the module.
fn output(values: &[String], types: &[impl AsRef<str>]) -> String {
    if values.is_empty() {
        return "  hw.output\n}\n".to_owned();
    }
    let types: Vec<&str> = types.iter().map(AsRef::as_ref).collect();
    format!(
        "  hw.output {} : {}\n}}\n",
        values.join(", "),
        types.join(", ")
    )
}

/// `side`, the output of `circt-opt`, with `wrapper` in its top-level module
/// and each clock as an `i1`, for `circt-lec`.
pub fn with_wrapper(side: &str, wrapper: &str) -> Result<String> {
    let body = side
        .trim_end()
        .strip_suffix('}')
        .context("the `circt-opt` output does not end with its module")?;
    Ok(format!("{body}{wrapper}}}\n").replace(CLOCK, "i1"))
}

/// The modules of `mlir` by name. Each module starts at a line
/// `hw.module @name(` and ends at a line `}`.
pub fn modules(mlir: &str) -> Result<BTreeMap<String, String>> {
    let mut modules = BTreeMap::new();
    let mut lines = mlir.lines();
    while let Some(line) = lines.next() {
        let Some(rest) = line.strip_prefix("hw.module @") else {
            ensure!(line.trim().is_empty(), "unexpected line `{line}`");
            continue;
        };
        let name = rest.split('(').next().unwrap_or(rest).to_owned();
        let mut text = format!("{line}\n");
        loop {
            let line = lines
                .next()
                .with_context(|| format!("the module `{name}` does not end"))?;
            text.push_str(line);
            text.push('\n');
            if line == "}" {
                break;
            }
        }
        ensure!(
            modules.insert(name.clone(), text).is_none(),
            "the module `{name}` occurs twice"
        );
    }
    Ok(modules)
}

/// The name of the extern that `line` declares, if `line` is a
/// `hw.module.extern` header.
fn extern_header(line: &str) -> Option<&str> {
    line.strip_prefix("hw.module.extern @")?.split('(').next()
}

/// Whether `name` is a memory module (spec section 7.3) and not a black box.
fn is_memory(name: &str) -> bool {
    backend_circt::names::is_memory_module(name)
}

/// `mlir` with a definition in place of each extern: the module of `models`
/// with the same name for a memory, and the stand-in for a black box. Each
/// model must replace an extern.
pub fn defined(mlir: &str, models: &BTreeMap<String, String>) -> Result<String> {
    let mut used = BTreeSet::new();
    let mut out = String::new();
    for line in mlir.lines() {
        match extern_header(line) {
            Some(name) if is_memory(name) => {
                let model = models
                    .get(name)
                    .with_context(|| format!("no memory model for `{name}`"))?;
                out.push_str(model);
                used.insert(name);
            }
            Some(name) => out.push_str(&stand_in(name, line)?),
            None => {
                out.push_str(line);
                out.push('\n');
            }
        }
    }
    if let Some(name) = models.keys().find(|n| !used.contains(n.as_str())) {
        bail!("the memory model `{name}` has no extern with its name");
    }
    Ok(out)
}

/// The black box with the extern `header`: its clock, and each data port
/// with its width and the name of its stand-in register.
struct BlackBox {
    clock: String,
    data: Vec<(Port, NonZeroU32, String)>,
}

/// The stand-in register of the port `port` of the black box `name`. The
/// name holds the black box, because the flattening keeps only the instance
/// path. The length of `name` separates it from `port`.
fn stand_in_register(name: &str, port: &str) -> String {
    format!("silicon_reg_{}{name}_{port}", name.len())
}

/// A stand-in needs the clock of the black box for its registers.
fn black_box(name: &str, header: &str) -> Result<BlackBox> {
    let ports = header_ports(header).with_context(|| format!("cannot read the extern `{name}`"))?;
    let clock = ports
        .iter()
        .find(|p| p.is_clock())
        .with_context(|| {
            format!("the extern `{name}` has no clock port, so LEC has no stand-in for it")
        })?
        .name
        .clone();
    let mut data = Vec::new();
    for port in ports.into_iter().filter(|p| !p.is_clock()) {
        let width = port
            .ty
            .strip_prefix('i')
            .and_then(|w| w.parse().ok())
            .with_context(|| format!("the port `{port}` of `{name}` is not an integer"))?;
        let register = stand_in_register(name, &port.name);
        data.push((port, width, register));
    }
    Ok(BlackBox { clock, data })
}

/// The MLIR stand-in for the black box with the extern `header`. A register
/// holds each data port. The register of an input takes the input, so LEC
/// compares each input. The register of an output drives the output, so LEC
/// sees each output as a free input. Its next value is 0, because a register
/// that is its own next value crashes CIRCT (#20).
///
/// `verilog_stand_ins` writes the same stand-in in Verilog. `firtool` cannot
/// make it from this MLIR, because it deletes the registers of the inputs:
/// nothing reads them.
fn stand_in(name: &str, header: &str) -> Result<String> {
    let BlackBox { clock, data } = black_box(name, header)?;
    let mut out = format!(
        "{} {{\n",
        header.replacen("hw.module.extern", "hw.module", 1)
    );
    let mut outputs = Vec::new();
    for (port, width, reg) in &data {
        let p = &port.name;
        match port.dir {
            Dir::In => {
                let _ = writeln!(out, "  %{reg} = seq.compreg %{p}, %{clock} : i{width}");
            }
            Dir::Out => {
                let _ = writeln!(out, "  %silicon_zero_{p} = hw.constant 0 : i{width}");
                let _ = writeln!(
                    out,
                    "  %{reg} = seq.compreg %silicon_zero_{p}, %{clock} : i{width}"
                );
                outputs.push((format!("%{reg}"), format!("i{width}")));
            }
        }
    }
    let (values, types): (Vec<String>, Vec<String>) = outputs.into_iter().unzip();
    out.push_str(&output(&values, &types));
    Ok(out)
}

/// The Verilog stand-in for each black box of `mlir`, with the registers and
/// the names of the MLIR stand-in.
pub fn verilog_stand_ins(mlir: &str) -> Result<String> {
    let mut out = String::new();
    for line in mlir.lines() {
        let Some(name) = extern_header(line).filter(|n| !is_memory(n)) else {
            continue;
        };
        let BlackBox { clock, data } = black_box(name, line)?;
        let _ = writeln!(out, "module {name}(\n  input {clock},");
        let ports: Vec<String> = data
            .iter()
            .map(|(p, w, _)| {
                let dir = if p.dir == Dir::In { "input" } else { "output" };
                format!("  {dir} [{}:0] {}", w.get() - 1, p.name)
            })
            .collect();
        let _ = writeln!(out, "{}\n);", ports.join(",\n"));
        for (_, width, reg) in &data {
            let _ = writeln!(out, "  reg [{}:0] {reg};", width.get() - 1);
        }
        let _ = writeln!(out, "  always_ff @(posedge {clock}) begin");
        for (port, _, reg) in &data {
            let next = if port.dir == Dir::In {
                port.name.as_str()
            } else {
                "'0"
            };
            let _ = writeln!(out, "    {reg} <= {next};");
        }
        out.push_str("  end\n");
        for (port, _, reg) in data.iter().filter(|(p, _, _)| p.dir == Dir::Out) {
            let _ = writeln!(out, "  assign {} = {reg};", port.name);
        }
        out.push_str("endmodule\n");
    }
    Ok(out)
}

/// Whether `mlir` has a `seq.compreg` whose next value is its own result.
/// CIRCT 1.160 `--externalize-registers` crashes on such a register (#20).
pub fn has_self_register(mlir: &str) -> bool {
    mlir.lines().any(|line| {
        line.trim_start()
            .split_once(" = seq.compreg ")
            .is_some_and(|(result, rest)| rest.split([',', ' ']).next() == Some(result))
    })
}

/// Whether `mlir` defines the module `name`.
pub fn defines(mlir: &str, name: &str) -> bool {
    mlir.lines().any(|l| {
        l.strip_prefix("hw.module @")
            .and_then(|r| r.strip_prefix(name))
            .is_some_and(|r| r.starts_with('('))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(dir: Dir, name: &str, ty: &str) -> Port {
        Port {
            dir,
            name: name.to_owned(),
            ty: ty.to_owned(),
        }
    }

    const HEADER: &str = r#"  hw.module @top(in %clk : !seq.clock, in %a : i4, in %m2Fsilicon_reg_mem_state "m/silicon_reg_mem_state" : !hw.array<16xi8>, out q : i8, out "m/silicon_reg_mem_next" : !hw.array<16xi8>) attributes {num_regs = 1 : i32} {"#;

    #[test]
    fn ports_read_plain_and_quoted_names() {
        assert_eq!(
            ports(HEADER, "top").unwrap(),
            [
                p(Dir::In, "clk", "!seq.clock"),
                p(Dir::In, "a", "i4"),
                p(Dir::In, "m/silicon_reg_mem_state", "!hw.array<16xi8>"),
                p(Dir::Out, "q", "i8"),
                p(Dir::Out, "m/silicon_reg_mem_next", "!hw.array<16xi8>"),
            ]
        );
    }

    #[test]
    fn ports_name_a_missing_module() {
        let error = ports(HEADER, "other").unwrap_err().to_string();
        assert_eq!(error, "no module `other` in the MLIR");
    }

    #[test]
    fn the_wrapper_sorts_by_name_and_drives_the_clock() {
        let ours = [
            p(Dir::In, "clk", "!seq.clock"),
            p(Dir::In, "b", "i1"),
            p(Dir::Out, "q", "i2"),
            p(Dir::In, "a", "i2"),
        ];
        let theirs = [
            p(Dir::In, "a", "i2"),
            p(Dir::In, "b", "i1"),
            p(Dir::In, "clk", "!seq.clock"),
            p(Dir::Out, "q", "i2"),
        ];
        assert_eq!(
            wrapper("top", &ours, &theirs).unwrap(),
            "hw.module @silicon_lec(in %v3 \"a\" : i2, in %v1 \"b\" : i1, out \"q\" : i2) {\n  \
             %silicon_clock = hw.constant false\n  \
             %v2 = hw.instance \"dut\" @top(\"clk\": %silicon_clock: i1, \"b\": %v1: i1, \"a\": %v3: i2) -> (\"q\": i2)\n  \
             hw.output %v2 : i2\n}\n"
        );
    }

    #[test]
    fn the_wrapper_rejects_a_duplicate_port() {
        let ours = [p(Dir::In, "a", "i1"), p(Dir::Out, "a", "i1")];
        let theirs = [p(Dir::In, "a", "i1")];
        let error = wrapper("top", &ours, &theirs).unwrap_err().to_string();
        assert_eq!(error, "the port name `a` occurs twice");
        let error = wrapper("top", &theirs, &ours).unwrap_err().to_string();
        assert_eq!(error, "the port name `a` occurs twice");
    }

    #[test]
    fn the_wrapper_rejects_an_unmatched_port() {
        let ours = [p(Dir::In, "a", "i1"), p(Dir::In, "b", "i1")];
        let theirs = [p(Dir::In, "a", "i1")];
        let error = wrapper("top", &ours, &theirs).unwrap_err().to_string();
        assert_eq!(error, "the port `b` has no match on the other side");
        let error = wrapper("top", &theirs, &ours).unwrap_err().to_string();
        assert_eq!(error, "the port `b` of the other side has no match");
    }

    #[test]
    fn the_wrapper_rejects_a_port_of_another_type() {
        let error = wrapper("top", &[p(Dir::In, "a", "i1")], &[p(Dir::In, "a", "i2")])
            .unwrap_err()
            .to_string();
        assert_eq!(
            error,
            "the port `in \"a\" : i1` does not match `in \"a\" : i2` on the other side"
        );
    }

    #[test]
    fn the_wrapper_goes_into_the_top_level_module() {
        let side = "module {\n  hw.module @top(in %clk : !seq.clock) {\n  }\n}\n";
        assert_eq!(
            with_wrapper(side, "W\n").unwrap(),
            "module {\n  hw.module @top(in %clk : i1) {\n  }\nW\n}\n"
        );
    }

    const LEAN: &str = "\
hw.module.extern @blk(in %c : !seq.clock, in %a : i4, out y : i2)
hw.module @top(in %clk : !seq.clock) {
  hw.output
}
hw.module.extern @silicon_mem_1x4_r0w0(in %clk : !seq.clock)
";

    #[test]
    fn a_model_replaces_its_extern_and_a_stand_in_replaces_a_black_box() {
        let model = "hw.module @silicon_mem_1x4_r0w0(in %clk : !seq.clock) {\n  hw.output\n}\n";
        let models = modules(model).unwrap();
        assert_eq!(
            defined(LEAN, &models).unwrap(),
            "hw.module @blk(in %c : !seq.clock, in %a : i4, out y : i2) {\n  \
             %silicon_reg_3blk_a = seq.compreg %a, %c : i4\n  \
             %silicon_zero_y = hw.constant 0 : i2\n  \
             %silicon_reg_3blk_y = seq.compreg %silicon_zero_y, %c : i2\n  \
             hw.output %silicon_reg_3blk_y : i2\n}\n\
             hw.module @top(in %clk : !seq.clock) {\n  hw.output\n}\n\
             hw.module @silicon_mem_1x4_r0w0(in %clk : !seq.clock) {\n  hw.output\n}\n"
        );
    }

    #[test]
    fn each_memory_needs_a_model_and_each_model_an_extern() {
        let error = defined(LEAN, &BTreeMap::new()).unwrap_err().to_string();
        assert_eq!(error, "no memory model for `silicon_mem_1x4_r0w0`");
        let models = modules("hw.module @silicon_mem_2x1_r0w0() {\n}\n").unwrap();
        let mlir = "hw.module.extern @silicon_mem_1x4_r0w0()\n";
        let error = defined(mlir, &models).unwrap_err().to_string();
        assert_eq!(error, "no memory model for `silicon_mem_1x4_r0w0`");
        let mlir =
            "hw.module.extern @silicon_mem_1x4_r0w0()\nhw.module.extern @silicon_mem_1x4_r0w0()\n";
        let models = modules(
            "hw.module @silicon_mem_1x4_r0w0() {\n}\nhw.module @silicon_mem_2x1_r0w0() {\n}\n",
        )
        .unwrap();
        let error = defined(mlir, &models).unwrap_err().to_string();
        assert_eq!(
            error,
            "the memory model `silicon_mem_2x1_r0w0` has no extern with its name"
        );
    }

    #[test]
    fn the_verilog_stand_in_has_the_registers_of_the_mlir_stand_in() {
        assert_eq!(
            verilog_stand_ins(LEAN).unwrap(),
            "module blk(\n  input c,\n  input [3:0] a,\n  output [1:0] y\n);\n  \
             reg [3:0] silicon_reg_3blk_a;\n  reg [1:0] silicon_reg_3blk_y;\n  \
             always_ff @(posedge c) begin\n    silicon_reg_3blk_a <= a;\n    silicon_reg_3blk_y <= '0;\n  end\n  \
             assign y = silicon_reg_3blk_y;\nendmodule\n"
        );
    }

    #[test]
    fn a_black_box_without_a_clock_has_no_stand_in() {
        let error = verilog_stand_ins("hw.module.extern @f(in %a : i1, out y : i1)\n")
            .unwrap_err()
            .to_string();
        assert_eq!(
            error,
            "the extern `f` has no clock port, so LEC has no stand-in for it"
        );
    }

    #[test]
    fn defines_finds_a_module_but_not_an_extern() {
        let mlir = "hw.module @topx() {\n}\nhw.module.extern @blk()\nhw.module @top() {\n}\n";
        assert!(defines(mlir, "top"));
        assert!(!defines(mlir, "blk"));
        assert!(!defines(mlir, "to"));
    }

    #[test]
    fn a_register_that_is_its_own_next_value_is_found() {
        assert!(has_self_register(
            "  %silicon_reg_r = seq.compreg %silicon_reg_r, %clk : i4\n"
        ));
        assert!(has_self_register(
            "  %silicon_reg_s = seq.compreg %silicon_reg_s, %clk reset %rst, %c : i4\n"
        ));
        assert!(!has_self_register(
            "  %silicon_reg_r = seq.compreg %silicon_reg_rx, %clk : i4\n"
        ));
    }
}
