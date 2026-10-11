// SPDX-License-Identifier: Apache-2.0
//! The port layout of section 7.5 of the front-end spec: the order of the core ports of a
//! module, as Lean `Source.Layout` defines it. `flatten` and `vectors` both read it.
//!
//! The domain ports come first, then the inputs, then the outputs. In each group of inputs and
//! outputs, the ports sort by the byte order of their source names. This order equals the order
//! of the core names, because a name that `encode` changes only gets `$0k`, and `$` sorts before
//! each name character. The resolver makes the port names of a module unique, so two ports never
//! tie and the sort needs no tie break.

/// The ports of one module in layout order: the inputs, then the outputs.
pub(crate) struct Ports<T> {
    pub inputs: Vec<T>,
    pub outputs: Vec<T>,
}

/// A declared port: its source name, its direction, and its value.
pub(crate) struct Declared<T> {
    pub name: String,
    pub input: bool,
    pub value: T,
}

/// The layout of the domain ports `domain` and the declared ports `ports`. The domain ports
/// stay in their order, `d$0clk` before `d$0rst`.
pub(crate) fn arrange<T>(domain: Vec<T>, ports: Vec<Declared<T>>) -> Ports<T> {
    let mut sorted = ports;
    sorted.sort_by(|x, y| x.name.cmp(&y.name));
    let mut inputs = domain;
    let mut outputs = Vec::new();
    for port in sorted {
        if port.input {
            inputs.push(port.value);
        } else {
            outputs.push(port.value);
        }
    }
    Ports { inputs, outputs }
}
