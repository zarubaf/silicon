// SPDX-License-Identifier: Apache-2.0
//! The port layout of section 7.5 of the front-end spec: the order of the core ports of a
//! module, as Lean `Source.Layout` defines it. `flatten` and `vectors` both read it.
//!
//! The domain ports come first, then the inputs, then the outputs. In each group of inputs and
//! outputs, the ports sort by the byte order of their source names. This order equals the order
//! of the core names, because a name that `encode` changes only gets `$0k`, and `$` sorts before
//! each name character.

use crate::eval::PortDecl;

/// The ports of one module in layout order: the inputs, then the outputs.
pub(crate) struct Ports<T> {
    pub inputs: Vec<T>,
    pub outputs: Vec<T>,
}

/// The layout of the domain ports `domain` and the declared ports `ports`. Each declared port
/// comes with its value. The domain ports stay in their order, `d$0clk` before `d$0rst`. The
/// source names are the symbols of `texts`.
pub(crate) fn arrange<T>(texts: &[String], domain: Vec<T>, ports: Vec<(&PortDecl, T)>) -> Ports<T> {
    let name = |q: &PortDecl| texts.get(q.sym).map_or("", String::as_str);
    let mut sorted = ports;
    sorted.sort_by(|x, y| name(x.0).cmp(name(y.0)));
    let mut inputs = domain;
    let mut outputs = Vec::new();
    for (q, value) in sorted {
        if q.input {
            inputs.push(value);
        } else {
            outputs.push(value);
        }
    }
    Ports { inputs, outputs }
}
