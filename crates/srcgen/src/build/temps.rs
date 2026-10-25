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
use super::{Builder, Built, Ctx, Hw, Lane, Module};
use crate::eval::{Fault, Value};
use crate::program::{FTy, FieldTy, HExpr, Item, PTy, SExpr, Stmt, StructDef, Ty};

use super::ports::Dir;
use super::stat::value_expr;

/// The most layers around the instance, and the most elements of a layer.
const LAYERS: u32 = 3;
const ELEMENTS: u32 = 2;
/// The field of a struct that holds the instance.
const FIELD: &str = "h";

/// An instance in scope, which can stand in a slot of a container.
#[derive(Clone, Debug)]
pub(super) struct Peer {
    pub(super) name: String,
    /// The type `Instance[M, args]`, if each env gives the same plain
    /// arguments.
    pub(super) ty: Option<FTy>,
}

/// A layer around the instance, from the inside out. A slot holds a
/// number into the pool of instances; the pool starts with the child
/// itself.
#[derive(Clone)]
enum Layer {
    /// `(.., x, ..)`: the instance at `at`, another instance in the other
    /// slots.
    Tuple { at: u32, slots: Vec<usize> },
    /// `[x, y]`: the whole inner value at `at`, the same layers over
    /// another instance of the same type in the other slots.
    Array { at: u32, slots: Vec<usize> },
    /// `Q<n>(x)`, read at the field `h`.
    Record,
}

/// What the read takes from the child.
struct Read {
    name: String,
    key: Option<u32>,
    ty: Ty,
}

/// The local `let l = <container>;` that holds the child, and the
/// selection of the child out of it. The `:=` of each input of the child
/// goes through it.
pub(super) struct Route {
    /// `l.0`, `l[1].h`, and so on.
    pub(super) base: HExpr,
}

/// A struct or a helper that names child modules, so that the file holds
/// it only if a module reaches each of them.
pub(super) struct Temp<T> {
    pub(super) modules: Vec<String>,
    pub(super) item: T,
}

impl Builder {
    /// Runs `f` on the tape of the temporary containers.
    fn on_temp<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        self.isolated(Lane::Temp, f)
    }

    /// The reads of the child through temporary containers, if the tape
    /// says so: mostly one, sometimes two, each joins the pool of the port tape.
    pub(super) fn temp_reads(&mut self, ctx: &mut Ctx, child: &Child) -> Built {
        self.on_temp(|b| {
            if b.tape.below(3) != 0 {
                return Ok(());
            }
            let reads = b.child_outputs(child);
            if reads.is_empty() {
                return Ok(());
            }
            // A second read in one of four.
            let count = 1 + u32::from(b.tape.below(3) == 0);
            #[cfg(test)]
            let before = ctx.port.len();
            for _ in 0..count {
                let read = &reads[b.tape.index(reads.len())];
                let expr = b.temp_read(ctx, child, read)?;
                let types = b.types(&read.ty, &child.envs)?;
                ctx.port.push(Hw {
                    expr,
                    ty: None,
                    types,
                    mutable: false,
                });
            }
            note!(b, temp_pairs, ctx.port.len() - before == 2);
            Ok(())
        })
    }

    /// The local container that the writes of the child go through, if the
    /// tape says so and the child has an input: `let l = (u, v);`, and the
    /// selection `l.0` of the child out of it.
    pub(super) fn temp_route(
        &mut self,
        ctx: &Ctx,
        m: &mut Module,
        child: &Child,
        out: &mut Vec<Stmt>,
    ) -> Built<Option<Route>> {
        let declared = child.sig.plan.declared(&self.port_helpers);
        let inputs = !child.sig.inputs.is_empty()
            || !child.sig.enum_inputs.is_empty()
            || declared.iter().any(|d| d.dir == Dir::In);
        self.on_temp(|b| {
            if !inputs || b.tape.below(5) != 0 {
                return Ok(None);
            }
            let pool = Self::container_pool(ctx, child);
            let layers = b.layers(&pool);
            let (value, _) = b.construct(&pool, &layers, 0)?;
            note!(b, mixed_slots, mixed(&layers));
            let name = m.names.fresh("l");
            // Each input of the child is then written through the local.
            note!(b, temp_writes);
            note!(b, write_tuples, shapes(&value) & TUPLE != 0);
            note!(b, write_arrays, shapes(&value) & ARRAY != 0);
            note!(b, write_records, shapes(&value) & RECORD != 0);
            out.push(Stmt::Let {
                name: name.clone(),
                mutable: false,
                ty: None,
                value,
            });
            Ok(Some(Route {
                base: Self::selected(HExpr::Name(name), &layers),
            }))
        })
    }

    /// The target of the input `port` (with the entry `key`) of `child`.
    pub(super) fn input_place(
        child: &Child,
        port: &str,
        key: Option<SExpr>,
    ) -> crate::program::Place {
        use crate::program::Place;
        let Some(route) = &child.via else {
            return match key {
                Some(k) => Place::ChildEntry(child.name.clone(), port.to_owned(), k),
                None => Place::Field(child.name.clone(), port.to_owned()),
            };
        };
        let base = Box::new(route.base.clone());
        Place::Path(match key {
            Some(k) => HExpr::ChildEntry(base, port.to_owned(), k),
            None => HExpr::Member(base, port.to_owned()),
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
    fn temp_read(&mut self, ctx: &Ctx, child: &Child, read: &Read) -> Built<HExpr> {
        let pool = Self::container_pool(ctx, child);
        let typed = pool.first().is_some_and(|p| p.ty.is_some());
        let layers = self.layers(&pool);
        let through_helper = typed && self.tape.below(3) == 0;
        let (made, ty) = self.construct(&pool, &layers, 0)?;
        note!(self, mixed_slots, mixed(&layers));
        let mut container = made.clone();
        if through_helper {
            let ty = ty.ok_or(Fault::Type)?;
            let name = self.temp_helper(&pool, ty, made);
            let used = self.helper_params(&name);
            container = HExpr::Call(name, used.into_iter().map(HExpr::Name).collect());
        }
        let base = Self::selected(container, &layers);
        Ok(match read.key {
            Some(k) => HExpr::ChildEntry(Box::new(base), read.name.clone(), literal(k)),
            None => HExpr::Member(Box::new(base), read.name.clone()),
        })
    }

    /// The instances that a container can hold: the child first, then the
    /// instances in scope.
    fn container_pool(ctx: &Ctx, child: &Child) -> Vec<Peer> {
        std::iter::once(Peer {
            name: child.name.clone(),
            ty: Self::instance_ty(child),
        })
        .chain(
            ctx.instances
                .iter()
                .filter(|p| p.name != child.name)
                .cloned(),
        )
        .collect()
    }

    /// The layers around the instance, from the inside out.
    fn layers(&mut self, pool: &[Peer]) -> Vec<Layer> {
        (0..self.tape.between(1, LAYERS))
            .map(|_| self.layer(pool))
            .collect()
    }

    /// A layer: a struct only if the instance has a type outside. The other
    /// slots hold other instances if the pool has them, so that a wrong
    /// index selects another instance.
    fn layer(&mut self, pool: &[Peer]) -> Layer {
        let typed = pool.first().is_some_and(|p| p.ty.is_some());
        let kind = self.tape.below(if typed { 3 } else { 2 });
        // Two elements in three of four layers.
        let len = if self.tape.below(4) == 0 { 1 } else { ELEMENTS };
        let at = self.tape.below(len);
        let slots = |b: &mut Builder, fits: &dyn Fn(&Peer) -> bool| -> Vec<usize> {
            (0..len)
                .map(|i| {
                    let others: Vec<usize> = (1..pool.len())
                        .filter(|&j| pool.get(j).is_some_and(fits))
                        .collect();
                    // The slot `at` holds the inner value, so it draws nothing.
                    if i == at || b.tape.below(4) == 0 || others.is_empty() {
                        0
                    } else {
                        others[b.tape.index(others.len())]
                    }
                })
                .collect()
        };
        match kind {
            0 => Layer::Tuple {
                at,
                slots: slots(self, &|p| !typed || p.ty.is_some()),
            },
            1 => {
                let own = pool.first().and_then(|p| p.ty.clone());
                Layer::Array {
                    at,
                    slots: slots(self, &|p| own.is_some() && p.ty == own),
                }
            }
            _ => Layer::Record,
        }
    }

    /// The type `Instance[M, args]` of the child, if it stands outside the
    /// module: each env gives the same plain arguments.
    pub(super) fn instance_ty(child: &Child) -> Option<FTy> {
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

    /// The literal that holds the instance `pool[leaf]` in all `layers`,
    /// and its type if the types of all instances in it are known.
    fn construct(
        &mut self,
        pool: &[Peer],
        layers: &[Layer],
        leaf: usize,
    ) -> Built<(HExpr, Option<FTy>)> {
        let peer = pool.get(leaf).ok_or(Fault::Type)?;
        let mut value = HExpr::Name(peer.name.clone());
        let mut ty = peer.ty.clone();
        for (k, layer) in layers.iter().enumerate() {
            match layer {
                Layer::Tuple { at, slots } => {
                    let mut items = Vec::new();
                    let mut types = Vec::new();
                    for (i, &s) in slots.iter().enumerate() {
                        if i == *at as usize {
                            items.push(value.clone());
                            types.push(ty.clone());
                        } else {
                            let other = pool.get(s).ok_or(Fault::Type)?;
                            items.push(HExpr::Name(other.name.clone()));
                            types.push(other.ty.clone());
                        }
                    }
                    value = HExpr::Tuple(items);
                    ty = types
                        .into_iter()
                        .collect::<Option<Vec<_>>>()
                        .map(FTy::Tuple);
                }
                Layer::Array { at, slots } => {
                    let mut items = Vec::new();
                    for (i, &s) in slots.iter().enumerate() {
                        if i == *at as usize {
                            items.push(value.clone());
                        } else {
                            let below = layers.get(..k).ok_or(Fault::Type)?;
                            items.push(self.construct(pool, below, s)?.0);
                        }
                    }
                    let len = u32::try_from(slots.len()).map_err(|_| Fault::Type)?;
                    value = HExpr::Array(items);
                    ty = ty.map(|t| FTy::Array(Box::new(t), len));
                }
                Layer::Record => {
                    let inner = ty.take().ok_or(Fault::Type)?;
                    let name = self.temp_struct(&inner);
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
            .fold(container, |base, layer| match layer {
                Layer::Tuple { at, .. } => HExpr::Select(Box::new(base), *at),
                Layer::Array { at, .. } => HExpr::Index(Box::new(base), literal(*at)),
                Layer::Record => HExpr::Member(Box::new(base), FIELD.to_owned()),
            })
    }

    /// The modules that the type `t` names.
    fn type_modules(&self, t: &FTy, out: &mut Vec<String>) {
        match t {
            FTy::Instance(m, _) => out.push(m.clone()),
            FTy::Tuple(xs) => xs.iter().for_each(|x| self.type_modules(x, out)),
            FTy::Array(x, _) | FTy::List(x) => self.type_modules(x, out),
            FTy::Struct(name) => {
                if let Some(s) = self.temp_structs.iter().find(|s| s.item.name == *name) {
                    out.extend(s.modules.iter().cloned());
                }
            }
            _ => {}
        }
    }

    /// The struct `Q<n> { h: inner }`, new if no struct has that field.
    fn temp_struct(&mut self, inner: &FTy) -> String {
        let field = vec![(FIELD.to_owned(), FieldTy::Handle(inner.clone()))];
        if let Some(found) = self.temp_structs.iter().find(|s| s.item.fields == field) {
            return found.item.name.clone();
        }
        let mut modules = Vec::new();
        self.type_modules(inner, &mut modules);
        let name = format!("Q{}", self.temp_structs.len());
        self.temp_structs.push(Temp {
            modules,
            item: StructDef {
                name: name.clone(),
                params: Vec::new(),
                fields: field,
            },
        });
        name
    }

    /// The helper `HT<n>(u0: Instance[..], ..) -> ty { return result; }`,
    /// with a formal for each instance that `result` names, new if no helper
    /// has these formals and this result. A formal has the name of its
    /// instance.
    fn temp_helper(&mut self, pool: &[Peer], ret: FTy, result: HExpr) -> String {
        let mut named = Vec::new();
        names(&result, &mut named);
        let params: Vec<(String, FTy)> = pool
            .iter()
            .filter(|p| named.contains(&p.name))
            .filter_map(|p| Some((p.name.clone(), p.ty.clone()?)))
            .collect();
        let same = |i: &Item| matches!(i, Item::Helper { params: p, result: r, .. } if *p == params && *r == result);
        if let Some(Item::Helper { name, .. }) =
            self.temp_helpers.iter().map(|h| &h.item).find(|i| same(i))
        {
            return name.clone();
        }
        let mut modules = Vec::new();
        for (_, t) in &params {
            self.type_modules(t, &mut modules);
        }
        self.type_modules(&ret, &mut modules);
        let name = format!("HT{}", self.temp_helpers.len());
        self.temp_helpers.push(Temp {
            modules,
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

    /// The names of the formals of the helper `name`, which are the
    /// instances of a call.
    fn helper_params(&self, name: &str) -> Vec<String> {
        self.temp_helpers
            .iter()
            .find_map(|h| match &h.item {
                Item::Helper {
                    name: n, params, ..
                } if n == name => Some(params.iter().map(|(p, _)| p.clone()).collect()),
                _ => None,
            })
            .unwrap_or_default()
    }

    /// The structs and helpers of the temporary containers whose child
    /// modules a module of the file reaches.
    pub(super) fn temp_items(&self) -> (Vec<Item>, Vec<Item>) {
        let reached = |module: &String| {
            self.sigs
                .iter()
                .zip(&self.bodies)
                .any(|(s, b)| s.name == *module && b.is_some())
        };
        let structs = self
            .temp_structs
            .iter()
            .filter(|t| t.modules.iter().all(reached))
            .map(|t| Item::Struct(t.item.clone()))
            .collect();
        let helpers = self
            .temp_helpers
            .iter()
            .filter(|t| t.modules.iter().all(reached))
            .map(|t| t.item.clone())
            .collect();
        (structs, helpers)
    }
}

/// Whether a slot of `layers` holds another instance than the child, so
/// that a wrong index selects a different instance.
#[cfg(test)]
fn mixed(layers: &[Layer]) -> bool {
    layers.iter().any(|l| match l {
        Layer::Tuple { slots, .. } | Layer::Array { slots, .. } => slots.iter().any(|&s| s != 0),
        Layer::Record => false,
    })
}

/// The names in a container literal.
fn names(e: &HExpr, out: &mut Vec<String>) {
    match e {
        HExpr::Name(n) => out.push(n.clone()),
        HExpr::Tuple(xs) | HExpr::Array(xs) | HExpr::Record(_, xs) => {
            for x in xs {
                names(x, out);
            }
        }
        _ => {}
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
