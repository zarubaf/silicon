// SPDX-License-Identifier: Apache-2.0
//! The hardware aggregate of Lean `Source.Eval.Agg` (design section 5.1): a tree of static
//! parts, hardware leaves, lazy references, and container nodes. Each node stores its type, its
//! recursive size, its depth, and its number of hardware leaves, so no charge walks the tree.
//! A reference holds its type and does not expand: its size, its depth, and its leaf count
//! come from the metadata of the type in constant work.
//!
//! Every walk over an aggregate keeps its own stack, so an aggregate of any depth is safe on
//! any stack.

use crate::hw::{Graph, HwId, Op, Seen, Val};
use crate::names::{PathId, Paths, Step};
use crate::types::{Ty, TyId, Types};
use crate::value::Value;

/// Where a reference aggregate starts: a core name, an output of a child instance, or the word
/// of a memory. A word holds the path of its memory once, as an id, and the bit offset of its
/// part (section 7.6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Base {
    Name(PathId),
    Out(PathId, PathId),
    Word(PathId, u64),
}

impl Base {
    /// The operation of a leaf of the base.
    pub(crate) fn op(&self) -> Op {
        match self {
            Base::Name(p) => Op::Ref(*p),
            Base::Out(i, q) => Op::Out(*i, *q),
            Base::Word(m, off) => Op::Word(*m, *off),
        }
    }

    /// The part of the base with the leaf field `step` (section 7.3): a user field `f`, or an
    /// element `<k>e`. A step adds one node to the path arena, in constant work, for a name and
    /// for the port name of a child output alike. A word adds `offset`, the offset of the part
    /// in its parent (`Types::offset`), and no node.
    pub(crate) fn sub(&self, paths: &mut Paths, step: Step, offset: u64) -> Base {
        match self {
            Base::Name(p) => Base::Name(paths.push(*p, step)),
            Base::Out(i, q) => Base::Out(*i, paths.push(*q, step)),
            Base::Word(m, off) => Base::Word(*m, off.saturating_add(offset)),
        }
    }
}

/// The stored numbers of a container node: its type, its recursive size, its depth, and the
/// number of its hardware leaves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Node {
    pub ty: TyId,
    pub size: u64,
    pub depth: u64,
    pub leaves: u64,
}

/// A hardware aggregate. A `Static` part holds no hardware leaf, a `Hw` part is a hardware
/// value, and a `Ref` refers to a part of a port, a register, a wire, or a child output. A node
/// built by `Agg::node` has at least one hardware leaf: a node with none is a static value.
pub(crate) enum Agg {
    Static(Value),
    Hw(HwId),
    Ref(Base, TyId),
    Array(Node, Parts),
    Tuple(Node, Parts),
    Record(Node, Parts),
}

/// The parts of a container node. Its drop keeps its own stack, as the derived drop would
/// recurse over the depth of the tree.
pub(crate) struct Parts(pub Vec<Agg>);

impl Drop for Parts {
    fn drop(&mut self) {
        let mut work: Vec<Agg> = std::mem::take(&mut self.0);
        while let Some(a) = work.pop() {
            if let Agg::Array(_, mut p) | Agg::Tuple(_, mut p) | Agg::Record(_, mut p) = a {
                work.append(&mut p.0);
            }
        }
    }
}

/// An integer of the metadata as a `u64`. The sums of the sizes saturate as well.
fn small(n: &crate::int::Int) -> u64 {
    n.to_u64().unwrap_or(u64::MAX)
}

impl Agg {
    /// The sum of the part counts of the container nodes on the path `keys`, which ends at the
    /// first part that is no container node (Lean `Agg.pathWidth`). The path length bounds the
    /// work: it reads the length of each parts vector and never walks the parts.
    pub(crate) fn path_width(&self, keys: &[usize]) -> u64 {
        let mut sum = 0u64;
        let mut cur = self;
        for &k in keys {
            let (Agg::Array(_, p) | Agg::Tuple(_, p) | Agg::Record(_, p)) = cur else {
                break;
            };
            sum = sum.saturating_add(p.0.len() as u64);
            match p.0.get(k) {
                Some(x) => cur = x,
                None => break,
            }
        }
        sum
    }

    /// The recursive size (section 5.4). A reference has the zero size of its type.
    pub(crate) fn size(&self, g: &Graph, tys: &Types) -> u64 {
        match self {
            Agg::Static(v) => v.size(),
            Agg::Hw(h) => g.size(*h),
            Agg::Ref(_, t) => small(&tys.meta(*t).zero_size),
            Agg::Array(n, _) | Agg::Tuple(n, _) | Agg::Record(n, _) => n.size,
        }
    }

    /// The depth (section 5.5). A reference has the depth of a value of its type.
    pub(crate) fn depth(&self, tys: &Types) -> u64 {
        match self {
            Agg::Static(v) => v.depth(),
            Agg::Hw(_) => 1,
            Agg::Ref(_, t) => tys.zero_depth(*t),
            Agg::Array(n, _) | Agg::Tuple(n, _) | Agg::Record(n, _) => n.depth,
        }
    }

    /// The number of hardware leaves. Each leaf of a reference is a hardware leaf.
    pub(crate) fn leaves(&self, tys: &Types) -> u64 {
        match self {
            Agg::Static(_) => 0,
            Agg::Hw(_) => 1,
            Agg::Ref(_, t) => small(&tys.meta(*t).leaves),
            Agg::Array(n, _) | Agg::Tuple(n, _) | Agg::Record(n, _) => n.leaves,
        }
    }

    /// The type that a reference or a node stores. A static part and a hardware leaf look it up.
    pub(crate) fn stored_ty(&self) -> Option<TyId> {
        match self {
            Agg::Static(_) | Agg::Hw(_) => None,
            Agg::Ref(_, t) => Some(*t),
            Agg::Array(n, _) | Agg::Tuple(n, _) | Agg::Record(n, _) => Some(n.ty),
        }
    }

    /// The type.
    pub(crate) fn ty(&self, g: &Graph, tys: &mut Types) -> TyId {
        match self {
            Agg::Static(v) => v.ty(tys),
            Agg::Hw(h) => tys.mk(g.ty(*h)),
            a => a.stored_ty().unwrap_or_else(|| tys.mk(Ty::Unit)),
        }
    }

    /// The stored numbers of the node of the container type `ty` with the parts `xs`, or
    /// `None` if `ty` is not a container type with `xs.len()` parts. It reads the stored numbers
    /// of each part once and walks no part.
    pub(crate) fn shape(g: &Graph, tys: &Types, ty: TyId, xs: &[Agg]) -> Option<Node> {
        let parts = xs
            .iter()
            .map(|x| (x.size(g, tys), x.depth(tys), x.leaves(tys)));
        Agg::shape_from(tys, ty, xs.len(), parts)
    }

    /// The same from the size, the depth, and the number of hardware leaves of each of the `n`
    /// parts, so a caller that did not build the parts yet can charge their node first.
    pub(crate) fn shape_from(
        tys: &Types,
        ty: TyId,
        n: usize,
        parts: impl IntoIterator<Item = (u64, u64, u64)>,
    ) -> Option<Node> {
        let base = match tys.get(ty) {
            Ty::Array(elem, len) if len.to_u64() == u64::try_from(n).ok() => elem.depth(),
            Ty::Tuple(types) if types.len() == n => 0,
            Ty::Struct(_) if tys.fields(ty).is_some_and(|(_, f)| f.len() == n) => ty.depth(),
            _ => return None,
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Nodes, n as u64);
        let mut node = Node {
            ty,
            size: 1,
            depth: base,
            leaves: 0,
        };
        for (size, depth, leaves) in parts {
            node.size = node.size.saturating_add(size);
            node.depth = node.depth.max(depth);
            node.leaves = node.leaves.saturating_add(leaves);
        }
        node.depth = node.depth.saturating_add(1);
        Some(node)
    }

    /// The container of type `ty` with the parts `xs`, in its normal form: with no hardware
    /// leaf it is a static value. A part is in its normal form too (`Evaluator::normalize`).
    /// The caller charged the size and checked the depth of `shape`.
    pub(crate) fn node(g: &Graph, tys: &Types, ty: TyId, xs: Vec<Agg>) -> Option<Agg> {
        let node = Agg::shape(g, tys, ty, &xs)?;
        Some(Agg::finish(tys, node, xs))
    }

    /// The container of the stored numbers `node` with the parts `xs`, in its normal form.
    pub(crate) fn finish(tys: &Types, node: Node, xs: Vec<Agg>) -> Agg {
        let ty = node.ty;
        if node.leaves == 0 && xs.iter().all(|x| matches!(x, Agg::Static(_))) {
            let vs: Vec<Value> = xs
                .into_iter()
                .filter_map(|x| match x {
                    Agg::Static(v) => Some(v),
                    _ => None,
                })
                .collect();
            return Agg::Static(match tys.get(ty) {
                Ty::Array(elem, _) => Value::Array(*elem, vs),
                Ty::Tuple(_) => Value::tuple(vs),
                _ => Value::Record(ty, vs),
            });
        }
        match tys.get(ty) {
            Ty::Array(..) => Agg::Array(node, Parts(xs)),
            Ty::Tuple(_) => Agg::Tuple(node, Parts(xs)),
            _ => Agg::Record(node, Parts(xs)),
        }
    }

    /// What the aggregate is, without a copy: a static part or a hardware leaf look like the
    /// values they hold, and every other part is an aggregate.
    pub(crate) fn seen(&self) -> Seen<'_> {
        match self {
            Agg::Static(v) => Seen::Static(v),
            Agg::Hw(h) => Seen::Hw(*h),
            a => Seen::Agg(a),
        }
    }

    /// The value that the aggregate is: a static part and a hardware leaf are values of their
    /// own, and every other part is an aggregate value.
    pub(crate) fn into_val(self) -> Val {
        match self {
            Agg::Static(v) => Val::Static(v),
            Agg::Hw(h) => Val::Hw(h),
            a => Val::Agg(Box::new(a)),
        }
    }

    /// The part that the value `v` gives, or the value itself if a handle or a literal that
    /// waits has no part.
    pub(crate) fn of_val(v: Val) -> Result<Agg, Val> {
        match v {
            Val::Static(v) => Ok(Agg::Static(v)),
            Val::Hw(h) => Ok(Agg::Hw(h)),
            Val::Agg(a) => Ok(*a),
            v @ (Val::Handle(_) | Val::Pending(..)) => Err(v),
        }
    }

    /// The same kind of node with the parts `xs`.
    fn with(&self, xs: Vec<Agg>) -> Agg {
        match self {
            Agg::Array(n, _) => Agg::Array(*n, Parts(xs)),
            Agg::Tuple(n, _) => Agg::Tuple(*n, Parts(xs)),
            Agg::Record(n, _) => Agg::Record(*n, Parts(xs)),
            Agg::Static(v) => Agg::Static(v.clone()),
            Agg::Hw(h) => Agg::Hw(*h),
            Agg::Ref(b, t) => Agg::Ref(b.clone(), *t),
        }
    }

    fn parts(&self) -> &[Agg] {
        match self {
            Agg::Array(_, xs) | Agg::Tuple(_, xs) | Agg::Record(_, xs) => &xs.0,
            _ => &[],
        }
    }
}

/// The last `n` results of the walk that clones.
fn last<T>(done: &mut Vec<T>, n: usize) -> Vec<T> {
    done.split_off(done.len().saturating_sub(n))
}

/// The derived clone recurses over the depth of the tree.
impl Clone for Agg {
    fn clone(&self) -> Agg {
        enum Step<'a> {
            Visit(&'a Agg),
            Build(&'a Agg),
        }
        let mut done: Vec<Agg> = Vec::new();
        let mut work = vec![Step::Visit(self)];
        while let Some(step) = work.pop() {
            #[cfg(test)]
            if matches!(step, Step::Visit(_)) {
                crate::counters::add(crate::counters::Count::Nodes, 1);
            }
            match step {
                Step::Visit(a) if a.parts().is_empty() => done.push(a.with(Vec::new())),
                Step::Visit(a) => {
                    work.push(Step::Build(a));
                    work.extend(a.parts().iter().rev().map(Step::Visit));
                }
                Step::Build(a) => {
                    let xs = last(&mut done, a.parts().len());
                    done.push(a.with(xs));
                }
            }
        }
        done.pop().unwrap_or(Agg::Static(Value::Unit))
    }
}
