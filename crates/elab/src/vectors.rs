// SPDX-License-Identifier: Apache-2.0
//! The source vectors of section 11.2 of the front-end spec and the port schema of the top, as
//! Lean `Source.Vectors` defines them.
//!
//! A source vector has the form of a core vector (core IR spec, section 6.4.3), with source
//! names and source values. The port schema maps each source port of the top to its core
//! port. `parse_line` maps a source input line to the core input values, and `print_line`
//! maps the core output values to a source output line.
//!
//! - Schema order is the port layout of `layout`, without the clock.
//! - An input line lists the reset `d$0rst` of the domain `d` first, as a `Bool`. A
//!   combinational top has none, and the clock has no entry.
//! - An input value has the decimal forms of a core value: leading zeros are allowed, and
//!   `-0` is 0. An output value has no leading zeros, and only a negative `SInt` has `-`.

use crate::Design;
use crate::int::Int;
use crate::layout;
use crate::names::{Field, Name, Role, encode};
use crate::types::Ty;
use core_ir::Bits;
use core_ir::ast::{Design as CDesign, Dir, Item, Ty as CTy};
use core_ir::vectors::{input_tokens, output_line};

/// One port of the schema: its name in a source vector, its core name, and its type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub name: String,
    pub core: String,
    pub ty: Ty,
}

/// The port schema of the top: the inputs and the outputs, each in schema order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    pub inputs: Vec<Entry>,
    pub outputs: Vec<Entry>,
}

impl Design {
    /// The port schema of the top. The reset of the domain comes before the inputs. The
    /// result is `None` when the top is not a done instantiation.
    #[must_use]
    pub fn schema(&self) -> Option<Schema> {
        let top = self.insts.get(self.top)?;
        let text = |s: usize| self.texts.get(s).cloned().unwrap_or_default();
        let mut reset = Vec::new();
        if let Some(d) = top.body.domain {
            let name = encode(&Name {
                head: text(d),
                rest: vec![Field::Role(Role::Rst)],
            });
            reset.push(Entry {
                name: name.clone(),
                core: name,
                ty: Ty::Bool,
            });
        }
        let env = layout::Env {
            tys: &self.tys,
            order: &self.field_order,
            texts: &self.texts,
        };
        let mut shapes = layout::Shapes::default();
        let mut ports = Vec::with_capacity(top.body.ports.len());
        for q in &top.body.ports {
            let source = self.texts.get(q.sym).map_or("", String::as_str);
            let root = self.tys.id_of(&q.ty)?;
            let mut leaves = Vec::new();
            let mut cursor = layout::Leaves::new(root, ());
            while let Some((t, ())) = cursor
                .next(env, &mut shapes, |(), _, _, _, _| (), |_| ())
                .ok()?
            {
                let fields = cursor.fields();
                leaves.push(Entry {
                    name: layout::leaf_entry(source, q.key, fields),
                    core: encode(&layout::leaf_name(source, q.key, fields)),
                    ty: self.tys.get(t).clone(),
                });
            }
            ports.push(layout::Declared {
                sym: q.sym,
                key: q.key,
                input: q.input,
                leaves,
            });
        }
        let layout::Ports { inputs, outputs } = layout::arrange(reset, ports, &self.texts);
        Some(Schema { inputs, outputs })
    }
}

impl Schema {
    /// The schema fits the core design `d` when its core names are the port names of the top
    /// module of `d`, in port order. The clock is not in the schema.
    #[must_use]
    pub fn fits(&self, d: &CDesign) -> bool {
        let Some(m) = d.items.iter().find_map(|item| match item {
            Item::Module(m) if m.name.text == d.top.text => Some(m),
            _ => None,
        }) else {
            return false;
        };
        let names = |dir: Dir| {
            m.ports
                .iter()
                .filter(move |p| p.dir == dir && p.ty != CTy::Clock)
                .map(|p| p.name.text.as_str())
        };
        names(Dir::Input).eq(self.inputs.iter().map(|e| e.core.as_str()))
            && names(Dir::Output).eq(self.outputs.iter().map(|e| e.core.as_str()))
    }

    /// The core input values of a source input line, in schema order. The tokens follow the
    /// core vector format.
    ///
    /// # Errors
    /// Returns the message of the first fault of the line.
    pub fn parse_line(&self, line: &str) -> Result<Vec<Bits>, String> {
        let tokens = input_tokens(line)?;
        let mut rest = tokens.as_slice();
        let mut values = Vec::with_capacity(self.inputs.len());
        for e in &self.inputs {
            let [name, value, tail @ ..] = rest else {
                return Err("missing input".to_owned());
            };
            if *name != e.name {
                return Err(format!("expected input {}", e.name));
            }
            values.push(parse_value(&e.name, &e.ty, value)?);
            rest = tail;
        }
        if rest.is_empty() {
            Ok(values)
        } else {
            Err("extra input tokens".to_owned())
        }
    }

    /// The source output line of the core output values `values`, in port order. The schema
    /// fits the design, so the values and the outputs of the schema agree in order.
    #[must_use]
    pub fn print_line(&self, values: &[Bits]) -> String {
        output_line(
            self.outputs
                .iter()
                .zip(values)
                .map(|(e, v)| (&e.name, value_text(&e.ty, v))),
        )
    }
}

/// A decimal natural number with at least one digit.
fn decimal(s: &str) -> Option<Int> {
    if !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) {
        Int::from_decimal(s)
    } else {
        None
    }
}

/// The core value of the source value `v` for the input `name` of type `t`.
pub(crate) fn parse_value(name: &str, t: &Ty, v: &str) -> Result<Bits, String> {
    let bad = || format!("input {name} has no value of its type");
    let wide = || format!("input {name} exceeds its width");
    let (n, w) = match t {
        Ty::Bool => match v {
            "true" => (Int::from_u64(1), 1),
            "false" => (Int::zero(), 1),
            _ => return Err(bad()),
        },
        Ty::UInt(w) => {
            let n = decimal(v).ok_or_else(bad)?;
            if !n.fits_unsigned(u64::from(*w)) {
                return Err(wide());
            }
            (n, *w)
        }
        Ty::SInt(w) => {
            let (neg, digits) = match v.strip_prefix('-') {
                Some(digits) => (true, digits),
                None => (false, v),
            };
            let n = decimal(digits).ok_or_else(bad)?;
            let n = if neg { n.neg() } else { n };
            if !n.fits_signed(u64::from(*w)) {
                return Err(wide());
            }
            (n, *w)
        }
        Ty::Nat
        | Ty::Int
        | Ty::Unit
        | Ty::Type
        | Ty::String
        | Ty::List(_)
        | Ty::Array(..)
        | Ty::Tuple(_)
        | Ty::Struct(_)
        | Ty::Enum(_)
        | Ty::Fn(..)
        | Ty::Reg(_)
        | Ty::Wire(_)
        | Ty::Input(_)
        | Ty::Mem(..)
        | Ty::Instance(_) => {
            return Err(bad());
        }
    };
    n.to_finite(w).ok_or_else(bad)
}

/// The source text of the core value `v` of type `t`.
pub(crate) fn value_text(t: &Ty, v: &Bits) -> String {
    match t {
        Ty::Bool if Int::from_unsigned(v).is_zero() => "false".to_owned(),
        Ty::Bool => "true".to_owned(),
        Ty::SInt(w) => Int::from_signed(v, *w).to_string(),
        _ => Int::from_unsigned(v).to_string(),
    }
}
