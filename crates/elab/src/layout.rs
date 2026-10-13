// SPDX-License-Identifier: Apache-2.0
//! The port layout of section 7.5 of the front-end spec: the order of the core ports of a
//! module, as Lean `Source.Layout` defines it. This module also expands each port into its
//! leaves. `flatten` and `vectors` both read it. No other module expands a port.
//!
//! The domain ports come first, then the inputs, then the outputs. In each group of inputs and
//! outputs, the ports sort by the byte order of their source names. This order equals the order
//! of the core names, because a name that `encode` changes only gets `$0k`, and `$` sorts before
//! each name character. The resolver makes the port names of a module unique, so two ports never
//! tie and the sort needs no tie break.
//!
//! `for_each_leaf` streams the leaves of a port: it makes no list of them. A caller thus charges
//! each leaf before it makes the leaf. In this phase, a port has a scalar type and thus one leaf.

use crate::names::Name;
use crate::types::Ty;

/// One leaf of a port: its core name, its name in a source vector, and its scalar type.
pub(crate) struct Leaf {
    pub name: Name,
    pub entry: String,
    pub ty: Ty,
}

/// Runs `f` on each leaf of the port `name` of type `ty` in packing order. It stops at the
/// first error of `f`.
pub(crate) fn for_each_leaf<E>(
    name: &str,
    ty: &Ty,
    mut f: impl FnMut(Leaf) -> Result<(), E>,
) -> Result<(), E> {
    f(Leaf {
        name: crate::hw::port_name(name),
        entry: name.to_owned(),
        ty: ty.clone(),
    })
}

/// The ports of one module in layout order: the inputs, then the outputs.
pub(crate) struct Ports<T> {
    pub inputs: Vec<T>,
    pub outputs: Vec<T>,
}

/// A declared port: its source name, its direction, and the values of its leaves in packing
/// order.
pub(crate) struct Declared<T> {
    pub name: String,
    pub input: bool,
    pub leaves: Vec<T>,
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
            inputs.extend(port.leaves);
        } else {
            outputs.extend(port.leaves);
        }
    }
    Ports { inputs, outputs }
}
