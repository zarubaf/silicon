// SPDX-License-Identifier: Apache-2.0
//! The MLIR text of the `hw` operations with a port list: module headers,
//! extern declarations, and instances. The text follows the layout that
//! `circt-opt` prints.

use std::fmt;

/// The type of a port.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Clock,
    Int(u32),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Clock => f.write_str("!seq.clock"),
            Ty::Int(width) => write!(f, "i{width}"),
        }
    }
}

/// The direction of a port.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    In,
    Out,
}

/// A port of a module, an extern, or an instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pin {
    pub dir: Dir,
    pub name: String,
    pub ty: Ty,
}

/// The port list of a module header, for example `(in %a : i8, out q : i8)`.
pub fn signature(pins: &[Pin]) -> String {
    let ports: Vec<String> = pins
        .iter()
        .map(|p| match p.dir {
            Dir::In => format!("in %{} : {}", p.name, p.ty),
            Dir::Out => format!("out {} : {}", p.name, p.ty),
        })
        .collect();
    format!("({})", ports.join(", "))
}

/// An `hw.module` with the ports `pins`. `body` holds the operations, each
/// on its own line with an indent of two spaces. `outputs` gives the value of
/// each output pin, in pin order.
pub fn module(name: &str, pins: &[Pin], body: &str, outputs: &[(String, Ty)]) -> String {
    let output = if outputs.is_empty() {
        "hw.output".to_owned()
    } else {
        let names: Vec<&str> = outputs.iter().map(|(v, _)| v.as_str()).collect();
        let types: Vec<String> = outputs.iter().map(|(_, ty)| ty.to_string()).collect();
        format!("hw.output {} : {}", names.join(", "), types.join(", "))
    };
    format!(
        "hw.module @{name}{} {{\n{body}  {output}\n}}\n",
        signature(pins)
    )
}

/// The declaration of an extern module.
pub fn extern_module(name: &str, pins: &[Pin]) -> String {
    format!("hw.module.extern @{name}{}\n", signature(pins))
}

/// An `hw.instance` of `callee`. `args` gives a value for each input pin, in
/// pin order, and `results` gives a value name for each output pin.
pub fn instance(
    name: &str,
    callee: &str,
    pins: &[Pin],
    args: &[String],
    results: &[String],
) -> String {
    let count = |dir| pins.iter().filter(|p| p.dir == dir).count();
    debug_assert_eq!(args.len(), count(Dir::In), "one argument per input pin");
    debug_assert_eq!(results.len(), count(Dir::Out), "one result per output pin");
    let inputs: Vec<String> = pins
        .iter()
        .filter(|p| p.dir == Dir::In)
        .zip(args)
        .map(|(p, arg)| format!("{}: {arg}: {}", p.name, p.ty))
        .collect();
    let outputs: Vec<String> = pins
        .iter()
        .filter(|p| p.dir == Dir::Out)
        .map(|p| format!("{}: {}", p.name, p.ty))
        .collect();
    let op = format!(
        "hw.instance \"{name}\" @{callee}({}) -> ({})",
        inputs.join(", "),
        outputs.join(", ")
    );
    if results.is_empty() {
        op
    } else {
        format!("{} = {op}", results.join(", "))
    }
}
