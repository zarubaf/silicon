//! Tests of the memory models and of the Verilog through CIRCT: each model
//! parses, has the ports of the extern, and equals the memory semantics of
//! spec section 5.2.

mod common;
mod lec;

use std::error::Error;
use std::fmt::Write;

use backend_circt::{MemConfig, lower, memory_configs, memory_model, verilog};
use core_ir::check::check;
use core_ir::text::parse;
use core_ir::typed::address_width;

type Test = Result<(), Box<dyn Error>>;

const fn config(depth: u32, width: u32, reads: usize, writes: usize) -> MemConfig {
    MemConfig {
        depth,
        width,
        reads,
        writes,
    }
}

/// Depths with and without addresses out of range, and each port count from
/// 0 to 3.
const CONFIGS: [MemConfig; 5] = [
    config(12, 8, 2, 2),
    config(1, 3, 1, 1),
    config(8, 4, 1, 0),
    config(5, 2, 0, 3),
    config(16, 1, 3, 1),
];

/// A design with the memory `12x8_r2w1`: two reads and one write.
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
    (write m 0 x d we)
    (assign p (read m x))
    (assign q (read m y))))
";

#[test]
fn each_model_parses_and_has_the_extern_ports() -> Test {
    let ast = parse(MEMORY).map_err(|d| d.to_string())?;
    let design = check(&ast).map_err(|d| d.to_string())?;
    let mlir = lower(&design);
    for config in memory_configs(&design).iter().chain(&CONFIGS) {
        let model = memory_model(config);
        let out = common::run("circt-opt", &[], &model)?;
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "{stderr}\n{model}");
        let name = config.module_name();
        let header = model
            .lines()
            .find(|l| l.starts_with("hw.module @"))
            .ok_or("no module")?;
        assert!(
            header.starts_with(&format!("hw.module @{name}(")),
            "{header}"
        );
        assert!(model.contains("%silicon_reg_mem = seq.compreg "), "{model}");
        if let Some(decl) = mlir
            .lines()
            .find(|l| l.starts_with(&format!("hw.module.extern @{name}(")))
        {
            let ports = decl.trim_start_matches("hw.module.extern ");
            assert_eq!(header, format!("hw.module {ports} {{"));
        }
    }
    Ok(())
}

/// The semantics of spec section 5.2 element by element: a read gives the
/// word at its address, or 0 out of range; each write port in `order` sets
/// the word at its address if its enable is 1.
fn reference(config: &MemConfig, order: &[usize]) -> Result<String, std::fmt::Error> {
    let model = memory_model(config);
    let header = model
        .lines()
        .find(|l| l.starts_with("hw.module @"))
        .unwrap_or_default()
        .replacen(&format!("@{}(", config.module_name()), "@reference(", 1);
    let (d, w, a) = (config.depth, config.width, address_width(config.depth));
    let ty = format!("!hw.array<{d}xi{w}>");
    let mut body = format!("{header}\n  %zero = hw.constant 0 : i{w}\n");
    let mut outputs = Vec::new();
    for i in 0..d {
        writeln!(body, "  %i{i} = hw.constant {i} : i{a}")?;
        writeln!(
            body,
            "  %m{i} = hw.array_get %silicon_reg_mem[%i{i}] : {ty}, i{a}"
        )?;
    }
    for n in 0..config.reads {
        let mut acc = "%zero".to_owned();
        for i in 0..d {
            writeln!(
                body,
                "  %r{n}_at{i} = comb.icmp eq %r{n}_addr, %i{i} : i{a}"
            )?;
            writeln!(
                body,
                "  %r{n}_v{i} = comb.mux %r{n}_at{i}, %m{i}, {acc} : i{w}"
            )?;
            acc = format!("%r{n}_v{i}");
        }
        outputs.push(acc);
    }
    let mut words = Vec::new();
    for i in 0..d {
        let mut acc = format!("%m{i}");
        for &p in order {
            writeln!(
                body,
                "  %w{p}_at{i} = comb.icmp eq %w{p}_addr, %i{i} : i{a}"
            )?;
            writeln!(body, "  %w{p}_on{i} = comb.and %w{p}_en, %w{p}_at{i} : i1")?;
            writeln!(
                body,
                "  %w{p}_v{i} = comb.mux %w{p}_on{i}, %w{p}_data, {acc} : i{w}"
            )?;
            acc = format!("%w{p}_v{i}");
        }
        words.push(acc);
    }
    // `hw.array_create` takes the word of the highest index first.
    words.reverse();
    writeln!(
        body,
        "  %next = hw.array_create {} : i{w}",
        words.join(", ")
    )?;
    writeln!(body, "  %silicon_reg_mem = seq.compreg %next, %clk : {ty}")?;
    let types = vec![format!("i{w}"); outputs.len()];
    if outputs.is_empty() {
        body.push_str("  hw.output\n}\n");
    } else {
        writeln!(
            body,
            "  hw.output {} : {}\n}}",
            outputs.join(", "),
            types.join(", ")
        )?;
    }
    Ok(body)
}

/// A module `<name>_words` around the module `name` with its register as
/// ports. It gives the read data and each word of the next state.
/// `circt-lec` gives an array of a depth below a power of two free words
/// above the depth, so the proof compares the words, not the array.
fn words(config: &MemConfig, name: &str) -> Result<String, std::fmt::Error> {
    let (d, w, a) = (config.depth, config.width, address_width(config.depth));
    let ty = format!("!hw.array<{d}xi{w}>");
    let mut inputs = vec![("clk".to_owned(), "i1".to_owned())];
    for n in 0..config.reads {
        inputs.push((format!("r{n}_addr"), format!("i{a}")));
    }
    for n in 0..config.writes {
        inputs.push((format!("w{n}_addr"), format!("i{a}")));
        inputs.push((format!("w{n}_data"), format!("i{w}")));
        inputs.push((format!("w{n}_en"), "i1".to_owned()));
    }
    inputs.push(("silicon_reg_mem_state".to_owned(), ty.clone()));
    let mut outputs: Vec<(String, String)> = (0..config.reads)
        .map(|n| (format!("r{n}_data"), format!("i{w}")))
        .collect();
    let results: Vec<String> = outputs.iter().map(|(p, _)| format!("%{p}")).collect();
    let mut ports: Vec<String> = inputs
        .iter()
        .map(|(p, t)| format!("in %{p} : {t}"))
        .collect();
    ports.extend(outputs.iter().map(|(p, t)| format!("out {p} : {t}")));
    ports.extend((0..d).map(|i| format!("out word{i} : i{w}")));
    let args: Vec<String> = inputs
        .iter()
        .map(|(p, t)| format!("{p}: %{p}: {t}"))
        .collect();
    let mut kinds = outputs.clone();
    kinds.push(("silicon_reg_mem_next".to_owned(), ty.clone()));
    let kinds: Vec<String> = kinds.iter().map(|(p, t)| format!("{p}: {t}")).collect();
    let mut text = format!("hw.module @{name}_words({}) {{\n", ports.join(", "));
    let mut names = results.clone();
    names.push("%next".to_owned());
    writeln!(
        text,
        "  {} = hw.instance \"u\" @{name}({}) -> ({})",
        names.join(", "),
        args.join(", "),
        kinds.join(", ")
    )?;
    let mut values = results;
    for i in 0..d {
        writeln!(text, "  %i{i} = hw.constant {i} : i{a}")?;
        writeln!(text, "  %word{i} = hw.array_get %next[%i{i}] : {ty}, i{a}")?;
        values.push(format!("%word{i}"));
        outputs.push((format!("word{i}"), format!("i{w}")));
    }
    let types: Vec<&str> = outputs.iter().map(|(_, t)| t.as_str()).collect();
    writeln!(
        text,
        "  hw.output {} : {}\n}}",
        values.join(", "),
        types.join(", ")
    )?;
    Ok(text)
}

/// Proves the model of `config` equal to the reference with the write
/// ports in `order`, or reports a counterexample as `false`.
fn model_equals_reference(config: &MemConfig, order: &[usize]) -> Result<bool, Box<dyn Error>> {
    let name = config.module_name();
    let input = format!("{}{}", memory_model(config), reference(config, order)?);
    let flat = lec::externalized(&input)?;
    // The wrappers go into the `builtin.module` that `circt-opt` prints.
    let end = flat.rfind('}').ok_or("no module")?;
    let wrappers = format!("{}{}", words(config, &name)?, words(config, "reference")?);
    let input = format!("{}{wrappers}{}", &flat[..end], &flat[end..]);
    lec::prove(&input, &format!("{name}_words"), "reference_words")
}

/// CIRCT 1.160 cannot prove two configurations, so the proof skips them:
/// `circt-lec` rejects `hw.array_get` on an array of depth 1 (`smt.bv.cmp`
/// with operands of two types), and `--externalize-registers` crashes on a
/// register that is its own next value, which is the model without a write.
#[test]
fn each_model_equals_the_memory_semantics() -> Test {
    for config in CONFIGS.iter().filter(|c| c.depth > 1 && c.writes > 0) {
        let order: Vec<usize> = (0..config.writes).collect();
        assert!(model_equals_reference(config, &order)?, "{config:?}");
    }
    Ok(())
}

#[test]
fn the_higher_write_port_wins() -> Test {
    assert!(!model_equals_reference(&config(12, 8, 1, 2), &[1, 0])?);
    Ok(())
}

#[test]
fn the_verilog_of_a_model_has_the_array_register() -> Test {
    let sv = verilog(&memory_model(&config(12, 8, 2, 1)))?;
    assert!(sv.contains("module silicon_mem_12x8_r2w1("), "{sv}");
    assert!(sv.contains("reg [11:0][7:0] silicon_reg_mem;"), "{sv}");
    assert!(!sv.contains("RANDOM"), "{sv}");
    Ok(())
}

#[test]
fn verilog_reports_invalid_mlir() {
    let error = verilog("hw.module @broken(").err().map(|e| e.to_string());
    assert!(
        error.as_deref().is_some_and(|e| e.starts_with("firtool: ")),
        "{error:?}"
    );
}
