// SPDX-License-Identifier: Apache-2.0
//! The port layout of section 7.5 of the front-end spec: the order of the core ports of a
//! module, as Lean `Source.Layout` defines it. This module also expands each port into its
//! leaves. `flatten` and `vectors` both read it. No other module expands a port.
//!
//! The domain ports come first, then the inputs, then the outputs. In each group of inputs and
//! outputs, the ports sort by the byte order of their source names. The leaves of one port
//! follow in packing order, so the layout order is not the byte order of the core names. The
//! resolver makes the port names of a module unique, so two ports never tie and the sort
//! needs no tie break.
//!
//! `Leaves` streams the leaves of a type in packing order with its own stack: it makes no
//! list of them, so a caller charges each leaf before it makes the leaf. A part without a leaf
//! takes no step: a tuple or a struct visits only the parts that the metadata of its type counts
//! as non-empty, and an array without leaves is skipped whole. A port, a register, and a `:=`
//! binding all take their leaves from it.

use crate::names::{Field, Name, Sym};
use crate::types::{ENUM_PART_NAMES, PartNames, Ty, TyId, Types};
use std::collections::BTreeMap;

/// What the walk needs to name the parts of a type: the table of types, the field symbols of
/// each struct item, and the text of each symbol.
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    pub tys: &'a Types,
    pub order: &'a [Vec<Sym>],
    pub texts: &'a [String],
}

/// A part of a tuple or struct type with at least one leaf: its index, its leaf field, and its
/// type.
struct Kid {
    index: u64,
    field: Field,
    ty: TyId,
}

/// The non-empty parts of each tuple and struct type that a walk met. A type thus builds its
/// list once, in the number of its parts, which the charges of the type paid.
#[derive(Default)]
pub(crate) struct Shapes {
    index: BTreeMap<TyId, usize>,
    kids: Vec<Vec<Kid>>,
}

impl Shapes {
    /// The number of the list of the non-empty parts of `t`, or `None` for a struct without
    /// field names.
    fn kids_of(&mut self, env: Env<'_>, t: TyId) -> Option<usize> {
        if let Some(k) = self.index.get(&t) {
            return Some(*k);
        }
        let full = |u: TyId| !env.tys.meta(u).leaves.is_zero();
        let kids: Vec<Kid> = if let Ty::Tuple(ts) = env.tys.get(t) {
            ts.iter()
                .enumerate()
                .filter(|(_, u)| full(**u))
                .map(|(k, u)| Kid {
                    index: k as u64,
                    field: Field::Elem(crate::int::Int::from_u64(k as u64)),
                    ty: *u,
                })
                .collect()
        } else {
            let parts = env.tys.parts(t)?;
            let mut kids = Vec::new();
            for (k, u) in parts.types.iter().enumerate() {
                if full(*u) {
                    let text = match parts.names {
                        PartNames::Struct(item) => env.texts.get(*env.order.get(item)?.get(k)?)?,
                        PartNames::Enum => *ENUM_PART_NAMES.get(k)?,
                    };
                    kids.push(Kid {
                        index: k as u64,
                        field: Field::User(text.to_owned()),
                        ty: *u,
                    });
                }
            }
            kids
        };
        self.kids.push(kids);
        self.index.insert(t, self.kids.len() - 1);
        Some(self.kids.len() - 1)
    }
}

/// The parts that a container frame still visits.
enum Parts {
    Array { elem: TyId, len: u64 },
    Kids(usize),
}

/// A container on the stack of the walk, the number of its next part, and the source of the
/// container. `pushed` tells if its leaf field is on the path.
struct Frame<S> {
    ty: TyId,
    parts: Parts,
    next: u64,
    src: S,
    pushed: bool,
}

/// The cursor over the leaves of a type in packing order. It keeps its own stack, so a caller
/// charges each leaf before it makes the leaf.
pub(crate) struct Leaves<S> {
    fields: Vec<Field>,
    stack: Vec<Frame<S>>,
    enter: Option<(TyId, S, bool)>,
    /// The leaf that the last step gave is a part: its leaf field leaves the path at the next
    /// step.
    leave: bool,
}

impl<S> Leaves<S> {
    /// The cursor before the first leaf of the type `root`. `src` is the source of the root.
    pub(crate) fn new(root: TyId, src: S) -> Self {
        Self {
            fields: Vec::new(),
            stack: Vec::new(),
            enter: Some((root, src, false)),
            leave: false,
        }
    }

    /// The leaf fields of the leaf that the last step gave.
    pub(crate) fn fields(&self) -> &[Field] {
        &self.fields
    }

    /// The next leaf in packing order: its scalar type and its source, or `None` after the last
    /// leaf. `down` gives the source of the part `k` of a container with the leaf field `field`,
    /// which is the last of `depth` leaf fields, and the bit offset of the part in a word of the
    /// container (`Types::offset`). A struct type without field names gives `missing`.
    pub(crate) fn next<E>(
        &mut self,
        env: Env<'_>,
        shapes: &mut Shapes,
        down: impl Fn(&S, u64, &Field, usize, u64) -> S,
        missing: impl Fn(TyId) -> E,
    ) -> Result<Option<(TyId, S)>, E> {
        if std::mem::take(&mut self.leave) {
            self.fields.pop();
        }
        loop {
            if let Some((t, s, pushed)) = self.enter.take() {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Leaves, 1);
                let parts = if env.tys.meta(t).leaves.is_zero() {
                    None
                } else {
                    match env.tys.get(t) {
                        Ty::Bool | Ty::UInt(_) | Ty::SInt(_) => {
                            self.leave = pushed;
                            return Ok(Some((t, s)));
                        }
                        Ty::Array(elem, n) => Some(Parts::Array {
                            elem: *elem,
                            len: n.to_u64().unwrap_or(u64::MAX),
                        }),
                        Ty::Tuple(_) | Ty::Struct(_) => Some(Parts::Kids(
                            shapes.kids_of(env, t).ok_or_else(|| missing(t))?,
                        )),
                        _ => None,
                    }
                };
                match parts {
                    Some(parts) => self.stack.push(Frame {
                        ty: t,
                        parts,
                        next: 0,
                        src: s,
                        pushed,
                    }),
                    None if pushed => {
                        self.fields.pop();
                    }
                    None => {}
                }
            }
            let Some(top) = self.stack.last_mut() else {
                return Ok(None);
            };
            let step = match &top.parts {
                Parts::Array { elem, len } if top.next < *len => Some((
                    top.next,
                    Field::Elem(crate::int::Int::from_u64(top.next)),
                    *elem,
                )),
                Parts::Kids(k) => shapes
                    .kids
                    .get(*k)
                    .and_then(|kids| kids.get(usize::try_from(top.next).unwrap_or(usize::MAX)))
                    .map(|kid| (kid.index, kid.field.clone(), kid.ty)),
                Parts::Array { .. } => None,
            };
            match step {
                Some((index, field, ty)) => {
                    top.next += 1;
                    let offset = env.tys.offset(top.ty, index);
                    let child = down(&top.src, index, &field, self.fields.len() + 1, offset);
                    self.fields.push(field);
                    self.enter = Some((ty, child, true));
                }
                None => {
                    if self.stack.pop().is_some_and(|frame| frame.pushed) {
                        self.fields.pop();
                    }
                }
            }
        }
    }
}

/// The core name of the leaf of the port `source` with the leaf fields `fields`.
pub(crate) fn leaf_name(source: &str, fields: &[Field]) -> Name {
    Name {
        head: source.to_owned(),
        rest: fields.to_vec(),
    }
}

/// The name of the leaf in a source vector: the source name of the port, then `.f` for a field
/// and `.k` for an element at each level.
pub(crate) fn leaf_entry(source: &str, fields: &[Field]) -> String {
    let mut entry = source.to_owned();
    for field in fields {
        entry.push('.');
        match field {
            Field::User(x) => entry.push_str(x),
            Field::Elem(k) => entry.push_str(&k.to_string()),
            other => entry.push_str(&other.encode()),
        }
    }
    entry
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
