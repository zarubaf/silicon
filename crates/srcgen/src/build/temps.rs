// SPDX-License-Identifier: Apache-2.0
//! Reads of a child through a temporary container (#368). The instance
//! stands inside a tuple, an array, a struct literal, or the result of a
//! helper, and the read selects it out again: `(u, u).0.q[k]`,
//! `(Box(u),).0.h.q[k]`, `[Box(u)][0].h.y`, `HT0(u).0.h.q[k]`.
//!
//! A `:=` target cannot be a temporary (the parser rejects it), so only
//! reads occur. The reads join the pool of the port tape, which `mix_port`
//! reaches into an output. All draws come from their own tape, so a
//! program without these reads is the program of the other tapes alone.
//!
//! A struct or a helper names the type `Instance[M, args]`, which stands
//! outside the module. So these two forms occur only if each env of the
//! caller gives the same plain arguments; else the container is a tuple or
//! an array literal.

use super::handles::literal;
use super::inst::Child;
use super::{Builder, Built, Ctx, Hw, Lane};
use crate::eval::{Fault, Value};
use crate::program::{FTy, FieldTy, HExpr, Item, PTy, StructDef, Ty};

use super::ports::Dir;
use super::stat::value_expr;

/// The most layers around the instance, and the most elements of a layer.
const LAYERS: u32 = 3;
const ELEMENTS: u32 = 2;
/// The field of a struct that holds the instance.
const FIELD: &str = "h";

/// A layer around the instance, from the inside out.
#[derive(Clone, Copy)]
enum Layer {
    /// `(.., x, ..)` of `len` elements, with the instance at `at`.
    Tuple { at: u32, len: u32 },
    /// `[x, x]` of `len` elements, read at `at`.
    Array { at: u32, len: u32 },
    /// `Q<n>(x)`, read at the field `h`.
    Record,
}

/// What the read takes from the child.
struct Read {
    name: String,
    key: Option<u32>,
    ty: Ty,
}

/// A struct or a helper that names a child module, so that the file holds
/// it only if a module reaches that module.
pub(super) struct Temp<T> {
    pub(super) module: String,
    pub(super) item: T,
}

impl Builder {
    /// Runs `f` on the tape of the temporary containers.
    fn on_temp<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        self.isolated(Lane::Temp, f)
    }

    /// The reads of the child through temporary containers, if the tape
    /// says so: one or two, each joins the pool of the port tape.
    pub(super) fn temp_reads(&mut self, ctx: &mut Ctx, child: &Child) -> Built {
        self.on_temp(|b| {
            if b.tape.below(2) == 0 {
                return Ok(());
            }
            let reads = b.child_outputs(child);
            if reads.is_empty() {
                return Ok(());
            }
            for _ in 0..1 {
                let read = &reads[b.tape.index(reads.len())];
                let expr = b.temp_read(child, read)?;
                let types = b.types(&read.ty, &child.envs)?;
                ctx.port.push(Hw {
                    expr,
                    ty: None,
                    types,
                    mutable: false,
                });
            }
            Ok(())
        })
    }

    /// The scalar outputs and the output entries of the child.
    fn child_outputs(&self, child: &Child) -> Vec<Read> {
        let scalars = child.sig.outputs.iter().map(|(q, t)| Read {
            name: q.clone(),
            key: None,
            ty: t.clone(),
        });
        let declared = child.sig.plan.declared(&self.port_helpers);
        let ports = declared
            .iter()
            .filter(|d| d.dir == Dir::Out)
            .filter_map(|d| match &d.ty {
                PTy::Data(t) => Some(Read {
                    name: d.public.base.clone(),
                    key: d.public.key,
                    ty: t.clone(),
                }),
                PTy::Unit => None,
            });
        scalars.chain(ports).collect()
    }

    /// The read `read` of `child` through a container the tape draws.
    fn temp_read(&mut self, child: &Child, read: &Read) -> Built<HExpr> {
        let inst = Self::instance_ty(child);
        let layers: Vec<Layer> = (0..self.tape.between(1, LAYERS))
            .map(|_| self.layer(inst.is_some()))
            .collect();
        let through_helper = inst.is_some() && self.tape.below(3) == 0;
        let (made, ty) = self.construct(&child.name, &layers, inst.as_ref())?;
        let mut container = made;
        if through_helper {
            let (Some(formal), Some(ty)) = (inst, ty) else {
                return Err(Fault::Type);
            };
            let (result, _) = self.construct("h", &layers, Some(&formal))?;
            let name = self.temp_helper(&child.sig.name, formal, ty, result);
            container = HExpr::Call(name, vec![HExpr::Name(child.name.clone())]);
        }
        let base = Self::selected(container, &layers);
        Ok(match read.key {
            Some(k) => HExpr::ChildEntry(Box::new(base), read.name.clone(), literal(k)),
            None => HExpr::Member(Box::new(base), read.name.clone()),
        })
    }

    /// A layer: a struct only if the instance has a type outside.
    fn layer(&mut self, typed: bool) -> Layer {
        let kind = self.tape.below(if typed { 3 } else { 2 });
        let len = self.tape.between(1, ELEMENTS);
        let at = self.tape.below(len);
        match kind {
            0 => Layer::Tuple { at, len },
            1 => Layer::Array { at, len },
            _ => Layer::Record,
        }
    }

    /// The type `Instance[M, args]` of the child, if it stands outside the
    /// module: each env gives the same plain arguments.
    fn instance_ty(child: &Child) -> Option<FTy> {
        let mut args = Vec::new();
        for (name, _) in &child.sig.params {
            let mut found: Option<&Value> = None;
            for env in &child.envs {
                let v = env.statics.get(name)?;
                if found.is_some_and(|f| f != v) {
                    return None;
                }
                found = Some(v);
            }
            let v = found?;
            if !matches!(
                v,
                Value::Int(_) | Value::Bool(_) | Value::UInt(..) | Value::SInt(..)
            ) {
                return None;
            }
            args.push(value_expr(v));
        }
        Some(FTy::Instance(child.sig.name.clone(), args))
    }

    /// The literal that holds `source` in all `layers`, and its type if
    /// `inst` gives the type of the instance.
    fn construct(
        &mut self,
        source: &str,
        layers: &[Layer],
        inst: Option<&FTy>,
    ) -> Built<(HExpr, Option<FTy>)> {
        let mut value = HExpr::Name(source.to_owned());
        let mut ty = inst.cloned();
        for layer in layers {
            match *layer {
                Layer::Tuple { at, len } => {
                    // The other elements are the instance itself.
                    let items = (0..len)
                        .map(|i| {
                            if i == at {
                                value.clone()
                            } else {
                                HExpr::Name(source.to_owned())
                            }
                        })
                        .collect();
                    value = HExpr::Tuple(items);
                    ty = ty.map(|t| {
                        FTy::Tuple(
                            (0..len)
                                .map(|i| {
                                    if i == at {
                                        t.clone()
                                    } else {
                                        inst.cloned().unwrap_or_else(|| t.clone())
                                    }
                                })
                                .collect(),
                        )
                    });
                }
                Layer::Array { len, .. } => {
                    value = HExpr::Array(vec![value; len as usize]);
                    ty = ty.map(|t| FTy::Array(Box::new(t), len));
                }
                Layer::Record => {
                    let Some(inner) = ty.take() else {
                        return Err(Fault::Type);
                    };
                    let module = match &inst {
                        Some(FTy::Instance(m, _)) => m.clone(),
                        _ => return Err(Fault::Type),
                    };
                    let name = self.temp_struct(&module, inner);
                    value = HExpr::Record(name.clone(), vec![value]);
                    ty = Some(FTy::Struct(name));
                }
            }
        }
        Ok((value, ty))
    }

    /// The selections that bring the instance out of `container`, the
    /// outermost layer first.
    fn selected(container: HExpr, layers: &[Layer]) -> HExpr {
        layers
            .iter()
            .rev()
            .fold(container, |base, layer| match *layer {
                Layer::Tuple { at, .. } => HExpr::Select(Box::new(base), at),
                Layer::Array { at, .. } => HExpr::Index(Box::new(base), literal(at)),
                Layer::Record => HExpr::Member(Box::new(base), FIELD.to_owned()),
            })
    }

    /// The struct `Q<n> { h: inner }`, new if no struct has that field.
    fn temp_struct(&mut self, module: &str, inner: FTy) -> String {
        let field = vec![(FIELD.to_owned(), FieldTy::Handle(inner))];
        if let Some(found) = self
            .temp_structs
            .iter()
            .find(|s| s.module == module && s.item.fields == field)
        {
            return found.item.name.clone();
        }
        let name = format!("Q{}", self.temp_structs.len());
        self.temp_structs.push(Temp {
            module: module.to_owned(),
            item: StructDef {
                name: name.clone(),
                params: Vec::new(),
                fields: field,
            },
        });
        name
    }

    /// The helper `HT<n>(h: Instance[..]) -> ty { return result; }`, new if
    /// no helper has that result.
    fn temp_helper(&mut self, module: &str, formal: FTy, ret: FTy, result: HExpr) -> String {
        let params = vec![("h".to_owned(), formal)];
        let same = |i: &Item| matches!(i, Item::Helper { params: p, result: r, .. } if *p == params && *r == result);
        if let Some(Item::Helper { name, .. }) =
            self.temp_helpers.iter().map(|h| &h.item).find(|i| same(i))
        {
            return name.clone();
        }
        let name = format!("HT{}", self.temp_helpers.len());
        self.temp_helpers.push(Temp {
            module: module.to_owned(),
            item: Item::Helper {
                name: name.clone(),
                params,
                mut_first: false,
                ret,
                body: Vec::new(),
                result,
            },
        });
        name
    }

    /// The structs and helpers of the temporary containers whose child
    /// module a module of the file reaches.
    pub(super) fn temp_items(&self) -> (Vec<Item>, Vec<Item>) {
        let reached = |module: &str| {
            self.sigs
                .iter()
                .zip(&self.bodies)
                .any(|(s, b)| s.name == module && b.is_some())
        };
        let structs = self
            .temp_structs
            .iter()
            .filter(|t| reached(&t.module))
            .map(|t| Item::Struct(t.item.clone()))
            .collect();
        let helpers = self
            .temp_helpers
            .iter()
            .filter(|t| reached(&t.module))
            .map(|t| t.item.clone())
            .collect();
        (structs, helpers)
    }
}

/// Whether the read `e` of the pool goes through a temporary container.
#[cfg(test)]
fn through(e: &HExpr) -> bool {
    match e {
        HExpr::ChildEntry(base, ..) => !matches!(**base, HExpr::Name(_)),
        HExpr::Member(..) => true,
        _ => false,
    }
}

/// The forms of container that a read goes through, as bits.
#[cfg(test)]
const TUPLE: u8 = 1;
#[cfg(test)]
const ARRAY: u8 = 2;
#[cfg(test)]
const RECORD: u8 = 4;
#[cfg(test)]
const HELPER: u8 = 8;

/// The forms of container that the read `e` of the pool goes through.
#[cfg(test)]
fn shapes(e: &HExpr) -> u8 {
    let all = |xs: &[HExpr]| xs.iter().fold(0, |s, x| s | shapes(x));
    match e {
        HExpr::ChildEntry(b, ..)
        | HExpr::Member(b, _)
        | HExpr::Select(b, _)
        | HExpr::Index(b, _) => shapes(b),
        HExpr::Tuple(xs) => TUPLE | all(xs),
        HExpr::Array(xs) => ARRAY | all(xs),
        HExpr::Record(_, xs) => RECORD | all(xs),
        HExpr::Call(..) => HELPER,
        _ => 0,
    }
}

#[cfg(test)]
impl Builder {
    /// Counts the read `e`, which reaches an output, by its containers.
    pub(super) fn note_temp(&mut self, e: &HExpr) {
        if !through(e) {
            return;
        }
        let s = shapes(e);
        note!(self, temp_reads);
        note!(self, temp_tuples, s & TUPLE != 0);
        note!(self, temp_arrays, s & ARRAY != 0);
        note!(self, temp_records, s & RECORD != 0);
        note!(self, temp_helpers, s & HELPER != 0);
    }
}
