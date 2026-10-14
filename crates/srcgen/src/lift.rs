// SPDX-License-Identifier: Apache-2.0
//! The design, the module, and the statements of the lift, and the map from
//! core vectors to source vectors.

use super::expr::Env;
use super::memory;
use super::shape::{self, Shape};
use core_ir::ast::{Conn, Design, Dir, Expr, Item, Module, Port, Stmt, Ty};
use core_ir::r#gen::RESET;
use core_ir::{interp, typed};
use std::collections::HashMap;
use std::fmt;
use syntax::SyntaxKind;

/// A core form that has no slice-1 source form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unsupported {
    Extern(String),
    Memory(String),
    /// A register without the module reset or with a value that is not a
    /// constant, a clocked module without the input `rst`, or a connection
    /// of the reset that is not `rst`.
    Reset(String),
    /// A name with a `$` or a keyword, or a name that nothing declares.
    Name(String),
}

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unsupported::Extern(n) => write!(f, "the design has an extern {n}"),
            Unsupported::Memory(n) => write!(f, "the design has a memory {n}"),
            Unsupported::Reset(n) => write!(f, "{n} has a reset that source cannot express"),
            Unsupported::Name(n) => write!(f, "the name {n} is not a source name"),
        }
    }
}

impl std::error::Error for Unsupported {}

/// A lifted design: its source text and the map from core vectors to source
/// vectors.
pub struct Lifted {
    pub text: String,
    top: Shape,
}

impl Lifted {
    /// The `in=` line of a source run for the core inputs `inputs` of
    /// `top`: the reset first, then one entry for each leaf in the port
    /// layout. No LF.
    #[must_use]
    pub fn vector_in(&self, top: &typed::Module, inputs: &interp::Inputs) -> String {
        vector_in(top, &self.top, inputs)
    }

    /// The `out=` line for the core outputs `outputs` of `top`, with one
    /// entry for each leaf in the port layout. No LF.
    #[must_use]
    pub fn vector_out(&self, top: &typed::Module, outputs: &interp::Outputs) -> String {
        vector_out(top, &self.top, outputs)
    }
}

/// Renders the design as source text: the struct items of the record ports,
/// then one source module per core module, in item order. The numbers of
/// `tape` choose which adjacent ports of a module become one tuple, array,
/// or record port. An empty tape or zeros give scalar ports only.
///
/// # Errors
/// Returns the first core form that source cannot express.
pub fn lift(design: &Design, tape: &[u32]) -> Result<Lifted, Unsupported> {
    let mut numbers = tape.iter().copied();
    let mut ids = 0;
    let mut shapes = HashMap::new();
    for item in &design.items {
        if let Item::Module(m) = item {
            let clocked = m.ports.iter().any(|p| p.ty == Ty::Clock);
            let ports: Vec<_> = m
                .ports
                .iter()
                .filter(|p| !is_domain_reset(clocked, &p.name.text))
                .filter_map(|p| Some((p.name.text.clone(), p.dir, width(p)?)))
                .collect();
            shapes.insert(
                m.name.text.as_str(),
                shape::draw(&ports, &mut numbers, &mut ids),
            );
        }
    }
    lift_shaped(design, &shapes)
}

/// Like [`lift`], with the groups of each module given.
pub(super) fn lift_shaped(
    design: &Design,
    shapes: &HashMap<&str, Shape>,
) -> Result<Lifted, Unsupported> {
    let mut modules = HashMap::new();
    for item in &design.items {
        match item {
            Item::Module(m) => {
                modules.insert(m.name.text.as_str(), m);
            }
            Item::Extern(e) => return Err(Unsupported::Extern(e.name.text.clone())),
        }
    }
    let mut text = String::new();
    for item in &design.items {
        if let Item::Module(m) = item
            && let Some(shape) = shapes.get(m.name.text.as_str())
        {
            for group in &shape.groups {
                text.extend(group.struct_item());
            }
        }
    }
    for item in &design.items {
        if let Item::Module(m) = item {
            text.push_str(&module(m, &modules, shapes)?);
        }
    }
    Ok(Lifted {
        text,
        top: shapes
            .get(design.top.text.as_str())
            .cloned()
            .unwrap_or_default(),
    })
}

fn name(text: &str) -> Result<&str, Unsupported> {
    if text.contains('$') || SyntaxKind::keyword(text).is_some() {
        return Err(Unsupported::Name(text.to_owned()));
    }
    Ok(text)
}

fn width(port: &Port) -> Option<u32> {
    match port.ty {
        Ty::Bits(n) => Some(n.value),
        Ty::Clock => None,
    }
}

/// The lines of the body of a module, by section. Source needs a
/// declaration before every use, so the sections print in this order.
#[derive(Default)]
struct Sections {
    ports: Vec<String>,
    regs: Vec<String>,
    wires: Vec<String>,
    mems: Vec<String>,
    insts: Vec<String>,
    assigns: Vec<String>,
}

fn env_of<'a>(
    m: &'a Module,
    clocked: bool,
    modules: &HashMap<&str, &'a Module>,
    shapes: &'a HashMap<&'a str, Shape>,
) -> Result<Env<'a>, Unsupported> {
    let mut env = Env {
        widths: HashMap::new(),
        insts: HashMap::new(),
        alias: HashMap::new(),
        shapes,
    };
    for p in &m.ports {
        // The reset of a clocked module is its domain, not a value.
        if let (Some(w), false) = (width(p), is_domain_reset(clocked, &p.name.text)) {
            env.widths.insert(p.name.text.as_str(), w);
        }
    }
    for s in &m.stmts {
        match s {
            Stmt::Let { name, width, .. } | Stmt::Reg { name, width, .. } => {
                env.widths.insert(name.text.as_str(), width.value);
            }
            Stmt::Inst { name, module, .. } => {
                let child = modules
                    .get(module.text.as_str())
                    .ok_or_else(|| Unsupported::Name(module.text.clone()))?;
                env.insts.insert(name.text.as_str(), child);
            }
            _ => {}
        }
    }
    Ok(env)
}

fn module<'a>(
    m: &'a Module,
    modules: &HashMap<&str, &'a Module>,
    shapes: &'a HashMap<&'a str, Shape>,
) -> Result<String, Unsupported> {
    let clocked = m.ports.iter().any(|p| p.ty == Ty::Clock);
    if clocked && !m.ports.iter().any(|p| p.name.text == RESET) {
        return Err(Unsupported::Reset(m.name.text.clone()));
    }
    let shape = shapes
        .get(m.name.text.as_str())
        .cloned()
        .unwrap_or_default();
    let mut env = env_of(m, clocked, modules, shapes)?;
    for p in &m.ports {
        if let Some(path) = shape.read(&p.name.text) {
            env.alias.insert(p.name.text.as_str(), path);
        }
    }
    for g in &shape.groups {
        if env.widths.contains_key(g.name.as_str()) {
            return Err(Unsupported::Name(g.name.clone()));
        }
    }
    let memories = memory::find(m, &env)?;
    for mem in &memories {
        for s in &m.stmts {
            if let Stmt::Reg { name, .. } = s
                && let Some(text) = mem.alias(&name.text)
            {
                env.alias.insert(name.text.as_str(), text);
            }
        }
    }
    let mut sections = Sections::default();
    for dir in [Dir::Input, Dir::Output] {
        for p in m.ports.iter().filter(|p| p.dir == dir) {
            // The clock and the reset are the domain of the module.
            let (Some(w), false) = (width(p), is_domain_reset(clocked, &p.name.text)) else {
                continue;
            };
            let kw = if dir == Dir::Input { "input" } else { "output" };
            let line = match shape.group_of(&p.name.text) {
                None => format!("    {kw} {}: UInt[{w}];", name(&p.name.text)?),
                Some((g, 0)) => format!("    {kw} {}: {};", name(&g.name)?, g.ty()),
                Some(_) => continue,
            };
            sections.ports.push(line);
        }
    }
    for mem in &memories {
        let taken = |n: &str| env.widths.contains_key(n) || env.insts.contains_key(n);
        let lines = mem.lines(&env, &taken)?;
        sections.wires.extend(lines.wires);
        sections.mems.extend(lines.mems);
        sections.assigns.extend(lines.assigns);
    }
    for s in &m.stmts {
        let grouped = matches!(s, Stmt::Assign { out, .. } if shape.group_of(&out.text).is_some());
        if !grouped && !memories.iter().any(|mem| mem.owns(s)) {
            statement(s, &env, &mut sections)?;
        }
    }
    for g in shape.groups.iter().filter(|g| g.dir == Dir::Output) {
        let parts = g
            .members
            .iter()
            .map(|(port, width)| {
                let expr = m.stmts.iter().find_map(|s| match s {
                    Stmt::Assign { out, expr, .. } if out.text == *port => Some(expr),
                    _ => None,
                });
                element(
                    &env,
                    expr.ok_or_else(|| Unsupported::Name(port.clone()))?,
                    *width,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        sections
            .assigns
            .push(format!("    {} := {};", name(&g.name)?, g.literal(&parts)));
    }
    let domains = if clocked { "" } else { " domains()" };
    let mut text = format!("module {}(){domains} {{\n", name(&m.name.text)?);
    for line in [
        &sections.ports,
        &sections.regs,
        &sections.wires,
        &sections.mems,
        &sections.insts,
        &sections.assigns,
    ]
    .into_iter()
    .flatten()
    {
        text.push_str(line);
        text.push('\n');
    }
    text.push_str("}\n");
    Ok(text)
}

/// The source of `e` as an element of an aggregate literal. A bare name can
/// be a register, which is no element before slice 3, so `resize` makes a
/// value of it.
fn element(env: &Env<'_>, e: &Expr, width: u32) -> Result<String, Unsupported> {
    let text = env.source(e)?;
    Ok(if matches!(e, Expr::Ref(_)) {
        format!("resize(UInt[{width}], {text})")
    } else {
        text
    })
}

fn assign(target: &str, e: &Expr, env: &Env<'_>) -> Result<String, Unsupported> {
    Ok(format!("    {target} := {};", env.source(e)?))
}

fn statement(s: &Stmt, env: &Env<'_>, out: &mut Sections) -> Result<(), Unsupported> {
    match s {
        Stmt::Let {
            name: n,
            width,
            expr,
            ..
        } => {
            let n = name(&n.text)?;
            out.wires
                .push(format!("    wire {n}: UInt[{}];", width.value));
            out.assigns.push(assign(n, expr, env)?);
        }
        Stmt::Reg {
            name: n,
            width,
            reset,
            ..
        } => {
            let n = name(&n.text)?;
            let value = match reset {
                Some(r)
                    if matches!(&r.signal, Expr::Ref(s) if s.text == RESET)
                        && matches!(r.value, Expr::Const { .. }) =>
                {
                    env.source(&r.value)?
                }
                _ => return Err(Unsupported::Reset(n.to_owned())),
            };
            out.regs
                .push(format!("    reg {n}: UInt[{}] = {value};", width.value));
        }
        Stmt::Next {
            reg: target, expr, ..
        }
        | Stmt::Assign {
            out: target, expr, ..
        } => {
            out.assigns.push(assign(name(&target.text)?, expr, env)?);
        }
        Stmt::Inst {
            name: n,
            module,
            conns,
            ..
        } => {
            let n = name(&n.text)?;
            out.insts
                .push(format!("    instance {n} = {}();", name(&module.text)?));
            let child_shape = env
                .insts
                .get(n)
                .and_then(|child| env.shapes.get(child.name.text.as_str()));
            let grouped = |port: &str| child_shape.is_some_and(|s| s.group_of(port).is_some());
            for c in conns.iter().filter(|c| !grouped(&c.port.text)) {
                if let Some(line) = connection(n, c, env)? {
                    out.assigns.push(line);
                }
            }
            for g in child_shape
                .iter()
                .flat_map(|s| &s.groups)
                .filter(|g| g.dir == Dir::Input)
            {
                let parts = g
                    .members
                    .iter()
                    .map(|(port, width)| {
                        let conn = conns.iter().find(|c| c.port.text == *port);
                        let conn = conn.ok_or_else(|| Unsupported::Name(format!("{n}.{port}")))?;
                        element(env, &conn.expr, *width)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                out.assigns.push(format!(
                    "    {n}.{} := {};",
                    name(&g.name)?,
                    g.literal(&parts)
                ));
            }
        }
        Stmt::Mem { name, .. } | Stmt::Write { mem: name, .. } => {
            return Err(Unsupported::Memory(name.text.clone()));
        }
    }
    Ok(())
}

/// The statement for one connection. The clock and the reset of the parent
/// are the domain of the child, so they have no source form.
fn connection(inst: &str, c: &Conn, env: &Env<'_>) -> Result<Option<String>, Unsupported> {
    let port = c.port.text.as_str();
    let child = env
        .insts
        .get(inst)
        .ok_or_else(|| Unsupported::Name(inst.to_owned()))?;
    if matches!(&c.expr, Expr::Ref(n) if n.text == RESET) && !env.widths.contains_key(RESET) {
        let child_clocked = child.ports.iter().any(|p| p.ty == Ty::Clock);
        if !child_clocked {
            return Err(Unsupported::Reset(inst.to_owned()));
        }
    }
    let child_port = child.ports.iter().find(|p| p.name.text == port);
    if child_port.is_some_and(|p| p.ty == Ty::Clock) {
        return Ok(None);
    }
    if port == RESET && child.ports.iter().any(|p| p.ty == Ty::Clock) {
        return if matches!(&c.expr, Expr::Ref(n) if n.text == RESET) {
            Ok(None)
        } else {
            Err(Unsupported::Reset(inst.to_owned()))
        };
    }
    Ok(Some(format!(
        "    {inst}.{} := {};",
        name(port)?,
        env.source(&c.expr)?
    )))
}

/// Whether the input `name` of a module is its domain reset: the source has
/// no declaration for it.
fn is_domain_reset(clocked: bool, name: &str) -> bool {
    clocked && name == RESET
}

fn vector_in(top: &typed::Module, shape: &Shape, inputs: &interp::Inputs) -> String {
    let mut reset = None;
    let mut others = Vec::new();
    for (port, value) in top.inputs().iter().zip(inputs.values()) {
        if is_domain_reset(top.clock().is_some(), &port.name) {
            reset = Some(value.to_biguint().bits() != 0);
        } else {
            others.push((port.name.as_str(), value.to_biguint().to_string()));
        }
    }
    super::in_line(reset, shape.layout(others))
}

fn vector_out(top: &typed::Module, shape: &Shape, outputs: &interp::Outputs) -> String {
    let pairs = top
        .outputs()
        .iter()
        .zip(outputs.values())
        .map(|(port, value)| (port.name.as_str(), value.to_biguint().to_string()));
    let entries: Vec<String> = shape
        .layout(pairs)
        .into_iter()
        .map(|(n, v)| format!("{n} {v}"))
        .collect();
    format!("out=({})", entries.join(" "))
}

#[cfg(test)]
mod tests {
    use super::super::shape::{Group, Kind};
    use super::*;
    use core_ir::r#gen::{Config, design_with};
    use core_ir::{Bits, check::check, text::parse, vectors};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    use syntax::lex;

    fn lifted(core: &str) -> Result<String, Unsupported> {
        lift(&parse(core).unwrap(), &[]).map(|l| l.text)
    }

    /// The source of `expr` as the body of `o0`, over `i0: bits 8` and `i1: bits 2`.
    fn spelled(width: u32, expr: &str) -> String {
        let core = format!(
            "(design m0 (module m0 (input i0 (bits 8)) (input i1 (bits 2)) \
             (output o0 (bits {width})) (assign o0 {expr})))"
        );
        let text = lifted(&core).unwrap();
        let line = text.lines().find(|l| l.contains("o0 :=")).unwrap();
        line.trim()
            .strip_prefix("o0 := ")
            .unwrap()
            .strip_suffix(';')
            .unwrap()
            .to_owned()
    }

    fn top_of(core: &str) -> typed::Module {
        let design = check(&parse(core).unwrap()).unwrap();
        design.modules()[design.top().index()].clone()
    }

    #[test]
    fn a_combinational_module_gets_no_domain() {
        let core = "(design m0 (module m0 (input i0 (bits 8)) (output o0 (bits 8)) \
                    (assign o0 (add i0 (const 8 3)))))";
        assert_eq!(
            lifted(core).unwrap(),
            "module m0() domains() {\n    input i0: UInt[8];\n    output o0: UInt[8];\n    \
             o0 := (i0 +% UInt[8](3));\n}\n"
        );
    }

    #[test]
    fn the_clock_and_the_reset_become_the_domain() {
        let core = "(design m0 (module m0 (input clk clock) (input rst (bits 1)) \
                    (reg r0 (bits 4) clk (reset sync rst (const 4 5))) \
                    (next r0 (add r0 (const 4 1)))))";
        assert_eq!(
            lifted(core).unwrap(),
            "module m0() {\n    reg r0: UInt[4] = UInt[4](5);\n    r0 := (r0 +% UInt[4](1));\n}\n"
        );
    }

    #[test]
    fn each_core_form_has_its_source_spelling() {
        let one = "UInt[1](1)";
        let zero = "UInt[1](0)";
        let table: &[(u32, &str, String)] = &[
            (8, "(not i0)", "(~i0)".into()),
            (8, "(sub i0 i0)", "(i0 -% i0)".into()),
            (8, "(mul i0 i0)", "(i0 *% i0)".into()),
            (8, "(and i0 i0)", "(i0 & i0)".into()),
            (8, "(or i0 i0)", "(i0 | i0)".into()),
            (8, "(xor i0 i0)", "(i0 ^ i0)".into()),
            (8, "(shl i0 i0)", "(i0 << i0)".into()),
            (8, "(shru i0 i0)", "(i0 >> i0)".into()),
            (
                8,
                "(shrs i0 i0)",
                "reinterpret(UInt[8], (reinterpret(SInt[8], i0) >> i0))".into(),
            ),
            (
                1,
                "(icmp ule i0 i0)",
                format!("(if ((i0 <= i0)) {{ {one} }} else {{ {zero} }})"),
            ),
            (
                1,
                "(icmp slt i0 i0)",
                format!(
                    "(if ((reinterpret(SInt[8], i0) < reinterpret(SInt[8], i0))) \
                     {{ {one} }} else {{ {zero} }})"
                ),
            ),
            (
                8,
                "(mux (icmp eq i0 i0) i0 i0)",
                format!(
                    "(if (((if ((i0 == i0)) {{ {one} }} else {{ {zero} }}) == {one})) \
                     {{ i0 }} else {{ i0 }})"
                ),
            ),
            (3, "(extract i0 2 3)", "resize(UInt[3], (i0 >> 2))".into()),
            (3, "(extract i0 0 3)", "resize(UInt[3], i0)".into()),
            (
                10,
                "(concat i0 i1)",
                "((resize(UInt[10], i0) << 2) | resize(UInt[10], i1))".into(),
            ),
            (
                6,
                "(replicate i1 3)",
                "(resize(UInt[6], i1) *% UInt[6](21))".into(),
            ),
            (2, "(replicate i1 1)", "i1".into()),
        ];
        for (width, core, source) in table {
            assert_eq!(&spelled(*width, core), source, "{core}");
        }
    }

    #[test]
    fn nested_forms_take_the_width_of_their_operands() {
        let one = "UInt[1](1)";
        let zero = "UInt[1](0)";
        let table: &[(u32, &str, String)] = &[
            (
                1,
                "(icmp slt (concat i0 i1) (concat i0 i1))",
                format!(
                    "(if ((reinterpret(SInt[10], ((resize(UInt[10], i0) << 2) | resize(UInt[10], i1))) < \
                     reinterpret(SInt[10], ((resize(UInt[10], i0) << 2) | resize(UInt[10], i1))))) \
                     {{ {one} }} else {{ {zero} }})"
                ),
            ),
            (
                8,
                "(replicate (replicate i1 2) 2)",
                "(resize(UInt[8], (resize(UInt[4], i1) *% UInt[4](5))) *% UInt[8](17))".into(),
            ),
            (
                3,
                "(shrs (extract i0 1 3) (extract i0 1 3))",
                "reinterpret(UInt[3], (reinterpret(SInt[3], resize(UInt[3], (i0 >> 1))) >> \
                 resize(UInt[3], (i0 >> 1))))"
                    .into(),
            ),
            (
                9,
                "(concat (icmp eq i0 i0) i0)",
                format!(
                    "((resize(UInt[9], (if ((i0 == i0)) {{ {one} }} else {{ {zero} }})) << 8) | \
                     resize(UInt[9], i0))"
                ),
            ),
            (
                1,
                "(icmp slt (replicate i1 3) (replicate i1 3))",
                format!(
                    "(if ((reinterpret(SInt[6], (resize(UInt[6], i1) *% UInt[6](21))) < \
                     reinterpret(SInt[6], (resize(UInt[6], i1) *% UInt[6](21))))) \
                     {{ {one} }} else {{ {zero} }})"
                ),
            ),
            (
                10,
                "(shrs (mux (icmp eq i1 i1) (concat i0 i1) (concat i0 i1)) i0)",
                {
                    let cat = "((resize(UInt[10], i0) << 2) | resize(UInt[10], i1))";
                    format!(
                        "reinterpret(UInt[10], (reinterpret(SInt[10], (if (((if ((i1 == i1)) \
                         {{ {one} }} else {{ {zero} }}) == {one})) {{ {cat} }} else {{ {cat} }})) >> i0))"
                    )
                },
            ),
            (
                4,
                "(extract (concat i0 i1) 3 4)",
                "resize(UInt[4], (((resize(UInt[10], i0) << 2) | resize(UInt[10], i1)) >> 3))"
                    .into(),
            ),
        ];
        for (width, core, source) in table {
            assert_eq!(&spelled(*width, core), source, "{core}");
        }
    }

    #[test]
    fn each_predicate_has_its_operator() {
        let table = [
            ("eq", "==", false),
            ("ne", "!=", false),
            ("ult", "<", false),
            ("ule", "<=", false),
            ("ugt", ">", false),
            ("uge", ">=", false),
            ("slt", "<", true),
            ("sle", "<=", true),
            ("sgt", ">", true),
            ("sge", ">=", true),
        ];
        for (pred, op, signed) in table {
            let side = if signed {
                "reinterpret(SInt[8], i0)"
            } else {
                "i0"
            };
            let want =
                format!("(if (({side} {op} {side})) {{ UInt[1](1) }} else {{ UInt[1](0) }})");
            assert_eq!(spelled(1, &format!("(icmp {pred} i0 i0)")), want, "{pred}");
        }
    }

    #[test]
    fn instances_connect_data_ports_only() {
        let core = "(design m1 \
            (module m0 (input clk clock) (input rst (bits 1)) (input i0 (bits 4)) \
              (output o0 (bits 4)) (assign o0 i0)) \
            (module m1 (input clk clock) (input rst (bits 1)) (input i0 (bits 4)) \
              (output o0 (bits 4)) \
              (inst u0 m0 (clk clk) (rst rst) (i0 i0)) (assign o0 u0.o0)))";
        let text = lifted(core).unwrap();
        assert!(text.contains("    instance u0 = m0();\n"), "{text}");
        assert!(text.contains("    u0.i0 := i0;\n"), "{text}");
        assert!(text.contains("    o0 := u0.o0;\n"), "{text}");
        assert!(!text.contains("clk") && !text.contains("rst"), "{text}");
    }

    #[test]
    fn a_wire_is_declared_before_every_connection() {
        let core = "(design m0 (module m0 (input i0 (bits 4)) (output o0 (bits 4)) \
                    (let l0 (bits 4) (not l1)) (let l1 (bits 4) i0) (assign o0 l0)))";
        let text = lifted(core).unwrap();
        let last_wire = text
            .lines()
            .enumerate()
            .filter(|(_, l)| l.contains("wire "))
            .map(|(k, _)| k)
            .max()
            .unwrap();
        let first_assign = text.lines().position(|l| l.contains(":=")).unwrap();
        assert!(last_wire < first_assign, "{text}");
        assert!(text.contains("    l0 := (~l1);\n"), "{text}");
    }

    #[test]
    fn unsupported_forms_are_errors() {
        let mem = "(design m0 (module m0 (input clk clock) (input rst (bits 1)) \
                   (mem mem0 (bits 4) 4 clk)))";
        assert_eq!(lifted(mem), Err(Unsupported::Memory("mem0".into())));
        let ext = "(design m0 (module m0 (input i0 (bits 1))) \
                   (extern e0 (input i0 (bits 1))))";
        assert!(matches!(lifted(ext), Err(Unsupported::Extern(_))));
        let bare = "(design m0 (module m0 (input clk clock) (input rst (bits 1)) \
                    (reg r0 (bits 4) clk) (next r0 r0)))";
        assert_eq!(lifted(bare), Err(Unsupported::Reset("r0".into())));
        let read = "(design m0 (module m0 (input clk clock) (input rst (bits 1)) \
                    (output o0 (bits 1)) (assign o0 rst)))";
        assert_eq!(lifted(read), Err(Unsupported::Reset("rst".into())));
        let comb_child = "(design m1 (module m0 (input rst (bits 1)) (output o0 (bits 1)) \
                    (assign o0 rst)) (module m1 (input clk clock) (input rst (bits 1)) \
                    (inst u0 m0 (rst rst))))";
        assert_eq!(lifted(comb_child), Err(Unsupported::Reset("u0".into())));
        let no_rst = "(design m0 (module m0 (input clk clock)))";
        assert_eq!(lifted(no_rst), Err(Unsupported::Reset("m0".into())));
        let mut keyword = parse("(design m0 (module m0 (input i0 (bits 1))))").unwrap();
        for bad in ["in", "a$0b"] {
            let Item::Module(m) = &mut keyword.items[0] else {
                unreachable!()
            };
            m.ports[0].name.text = bad.into();
            assert_eq!(
                lift(&keyword, &[]).err(),
                Some(Unsupported::Name(bad.into()))
            );
        }
    }

    #[test]
    fn vector_in_puts_the_reset_first_and_sorts_the_inputs() {
        let top = top_of(
            "(design m0 (module m0 (input clk clock) (input silicon_i1 (bits 3)) \
             (input rst (bits 1)) (input i0 (bits 4)) \
             (reg r0 (bits 4) clk (reset sync rst (const 4 0))) (next r0 i0)))",
        );
        let inputs = vectors::parse_input("in=(silicon_i1 3 rst 1 i0 7)", &top).unwrap();
        assert_eq!(
            vector_in(&top, &Shape::default(), &inputs),
            "in=(clock$0rst true i0 7 silicon_i1 3)"
        );
        let inputs = vectors::parse_input("in=(silicon_i1 3 rst 0 i0 7)", &top).unwrap();
        assert_eq!(
            vector_in(&top, &Shape::default(), &inputs),
            "in=(clock$0rst false i0 7 silicon_i1 3)"
        );

        let comb = top_of(
            "(design m0 (module m0 (input silicon_i1 (bits 3)) (input i0 (bits 4)) \
             (output o0 (bits 1)) (assign o0 (const 1 0))))",
        );
        let inputs = vectors::parse_input("in=(silicon_i1 3 i0 7)", &comb).unwrap();
        assert_eq!(
            vector_in(&comb, &Shape::default(), &inputs),
            "in=(i0 7 silicon_i1 3)"
        );

        let none = top_of("(design m0 (module m0 (output o0 (bits 1)) (assign o0 (const 1 0))))");
        let inputs = vectors::parse_input("in=()", &none).unwrap();
        assert_eq!(vector_in(&none, &Shape::default(), &inputs), "in=()");
    }

    #[test]
    fn vector_out_sorts_the_outputs() {
        let top = top_of(
            "(design m0 (module m0 (output o1 (bits 2)) (output o0 (bits 3)) \
             (assign o1 (const 2 3)) (assign o0 (const 3 7))))",
        );
        let outputs = interp::Outputs::new(vec![
            Bits::new(2, 3u8.into()).unwrap(),
            Bits::new(3, 7u8.into()).unwrap(),
        ]);
        assert_eq!(
            vector_out(&top, &Shape::default(), &outputs),
            "out=(o0 7 o1 3)"
        );
        let none = top_of("(design m0 (module m0 (input i0 (bits 1))))");
        assert_eq!(
            vector_out(&none, &Shape::default(), &interp::Outputs::new(vec![])),
            "out=()"
        );
    }

    fn group(name: &str, dir: Dir, kind: Kind, members: &[(&str, u32)]) -> Group {
        Group {
            name: name.to_owned(),
            dir,
            kind,
            members: members.iter().map(|(n, w)| ((*n).to_owned(), *w)).collect(),
        }
    }

    fn shapes(list: Vec<(&str, Vec<Group>)>) -> HashMap<&str, Shape> {
        list.into_iter()
            .map(|(module, groups)| (module, Shape { groups }))
            .collect()
    }

    #[test]
    fn aggregate_ports_lift_to_one_literal_each() {
        let core = "(design m1 \
            (module m0 (input a (bits 4)) (input b (bits 4)) (output x (bits 4)) \
              (output y (bits 4)) (assign x b) (assign y a)) \
            (module m1 (input i0 (bits 4)) (input i1 (bits 4)) (output o0 (bits 4)) \
              (output o1 (bits 4)) (inst u m0 (a i0) (b i1)) \
              (assign o0 u.x) (assign o1 (add o0 u.y))))";
        let shapes = shapes(vec![
            (
                "m0",
                vec![
                    group("ab", Dir::Input, Kind::Array, &[("a", 4), ("b", 4)]),
                    group(
                        "xy",
                        Dir::Output,
                        Kind::Record {
                            id: 0,
                            param: false,
                        },
                        &[("x", 4), ("y", 4)],
                    ),
                ],
            ),
            (
                "m1",
                vec![
                    group("ii", Dir::Input, Kind::Tuple, &[("i0", 4), ("i1", 4)]),
                    group("oo", Dir::Output, Kind::Tuple, &[("o0", 4), ("o1", 4)]),
                ],
            ),
        ]);
        let text = lift_shaped(&parse(core).unwrap(), &shapes).unwrap().text;
        assert_eq!(
            text,
            "struct R0 {\n    f0: UInt[4],\n    f1: UInt[4],\n}\n\
             module m0() domains() {\n    input ab: [UInt[4]; 2];\n    output xy: R0;\n    \
             xy := R0(resize(UInt[4], ab[1]), resize(UInt[4], ab[0]));\n}\n\
             module m1() domains() {\n    input ii: (UInt[4], UInt[4]);\n    \
             output oo: (UInt[4], UInt[4]);\n    instance u = m0();\n    \
             u.ab := [resize(UInt[4], ii.0), resize(UInt[4], ii.1)];\n    oo := (u.xy.f0, (oo.0 +% u.xy.f1));\n}\n"
        );
    }

    #[test]
    fn a_record_with_a_width_parameter_has_a_specialized_type() {
        let core = "(design m0 (module m0 (input a (bits 8)) (input b (bits 8)) \
                    (output x (bits 8)) (output y (bits 8)) (assign x b) (assign y a)))";
        let shapes = shapes(vec![(
            "m0",
            vec![
                group(
                    "ab",
                    Dir::Input,
                    Kind::Record { id: 3, param: true },
                    &[("a", 8), ("b", 8)],
                ),
                group("xy", Dir::Output, Kind::Tuple, &[("x", 8), ("y", 8)]),
            ],
        )]);
        let text = lift_shaped(&parse(core).unwrap(), &shapes).unwrap().text;
        assert_eq!(
            text,
            "struct R3(comptime W: Nat) {\n    f0: UInt[W],\n    f1: UInt[8],\n}\n\
             module m0() domains() {\n    input ab: R3[8];\n    output xy: (UInt[8], UInt[8]);\n    \
             xy := (resize(UInt[8], ab.f1), resize(UInt[8], ab.f0));\n}\n"
        );
    }

    #[test]
    fn the_vector_map_follows_the_layout_not_the_byte_order() {
        let top = top_of(
            "(design m0 (module m0 (input z (bits 4)) (input a (bits 4)) (input c (bits 4)) \
             (output p (bits 4)) (output q (bits 4)) (assign p a) (assign q z)))",
        );
        let shape = Shape {
            groups: vec![
                group("b", Dir::Input, Kind::Tuple, &[("z", 4), ("a", 4)]),
                group("g", Dir::Output, Kind::Array, &[("q", 4), ("p", 4)]),
            ],
        };
        let inputs = vectors::parse_input("in=(z 3 a 5 c 7)", &top).unwrap();
        assert_eq!(vector_in(&top, &shape, &inputs), "in=(b.0 3 b.1 5 c 7)");
        let outputs = interp::Outputs::new(vec![
            Bits::new(4, 2u8.into()).unwrap(),
            Bits::new(4, 9u8.into()).unwrap(),
        ]);
        assert_eq!(vector_out(&top, &shape, &outputs), "out=(g.0 9 g.1 2)");
    }

    #[test]
    fn a_record_leaf_has_a_field_entry_after_the_reset() {
        let top = top_of(
            "(design m0 (module m0 (input clk clock) (input rst (bits 1)) (input x (bits 4)) \
             (input y (bits 4)) (reg r (bits 4) clk (reset sync rst (const 4 0))) (next r x)))",
        );
        let shape = Shape {
            groups: vec![group(
                "p",
                Dir::Input,
                Kind::Record {
                    id: 0,
                    param: false,
                },
                &[("y", 4), ("x", 4)],
            )],
        };
        let inputs = vectors::parse_input("in=(rst 1 x 3 y 6)", &top).unwrap();
        assert_eq!(
            vector_in(&top, &shape, &inputs),
            "in=(clock$0rst true p.f0 6 p.f1 3)"
        );
    }

    /// The lifted designs of 256 random tapes.
    fn lifted_sample() -> Vec<String> {
        let strategy = (design_with(Config::source()), vec(any::<u32>(), 0..256));
        let mut runner = TestRunner::deterministic();
        (0..256)
            .map(|_| {
                let (design, tape) = strategy.new_tree(&mut runner).unwrap().current();
                lift(&design, &tape).unwrap().text
            })
            .collect()
    }

    #[test]
    fn each_memory_and_aggregate_kind_occurs_in_a_tenth_of_the_designs() {
        type Has = fn(&str) -> bool;
        let texts = lifted_sample();
        let kinds: [(&str, Has); 5] = [
            ("memory", |t| t.contains("    mem ")),
            ("tuple", |t| t.contains(": (UInt[")),
            ("array", |t| t.contains(": [UInt[")),
            ("record", |t| {
                t.contains("struct R") && !t.contains("(comptime")
            }),
            ("record with width", |t| t.contains("(comptime W: Nat)")),
        ];
        for (kind, has) in kinds {
            let count = texts.iter().filter(|t| has(t)).count();
            assert!(count * 10 >= texts.len(), "{kind}: {count} of 256");
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]
        #[test]
        fn lifted_designs_lex(design in design_with(Config::source()), tape in vec(any::<u32>(), 0..256)) {
            let text = lift(&design, &tape).unwrap().text;
            let lexed = lex(&text, 4096);
            prop_assert!(lexed.errors.is_empty(), "{:?}\n{text}", lexed.errors);
        }
    }
}
