// SPDX-License-Identifier: Apache-2.0
//! The values of the evaluator, as Lean `Source.Eval` defines them (section 5.1): a static
//! value, a hardware value, or a handle. A hardware value is a typed tree of operations over
//! core names. Its nodes live in one arena, so an operand tree is shared, not copied: a new
//! node holds the indices of its operands.

use crate::names::{PathId, Sym};
use crate::value::{Ty, Value};
use parse::ast::{BinOp, Pos, UnOp};

/// A node of a hardware value: an index into the arena of its elaboration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HwId(usize);

/// The operation of a node. Section 7.4 lowers each node to core operations.
pub(crate) enum Op {
    Ref(PathId),
    Out(PathId, Sym),
    Lit(Value),
    /// A static shift count `k`, as the `Int` constant of Lean. The lowering reads only
    /// `min k w` for a width `w` of at most 65536, so the node keeps `min k 65536`, and the
    /// size of `k` for the charges.
    Count {
        amount: u32,
        size: u64,
    },
    Un(UnOp),
    Bin(BinOp),
    Mux,
    Resize,
    Reinterpret,
}

impl Op {
    /// A name or a child output has the size 1. A constant has the size of its value.
    fn size(&self) -> u64 {
        match self {
            Op::Lit(v) => v.size(),
            Op::Count { size, .. } => *size,
            _ => 1,
        }
    }
}

/// A node keeps the position of the source node that made it, and its recursive size, so a
/// charge reads the size in one step. Its height sizes the stack of the lowering.
pub(crate) struct Node {
    pub pos: Pos,
    pub ty: Ty,
    size: u64,
    height: usize,
    pub op: Op,
    pub args: Vec<HwId>,
}

/// The nodes of the hardware values of one elaboration. It grows only with charged work.
#[derive(Default)]
pub(crate) struct Graph {
    nodes: Vec<Node>,
    height: usize,
}

impl Graph {
    /// A new node. Its size is the size of its operation plus the sizes of its operands. The
    /// caller pays a hardware operation; a reference and a constant only refer.
    pub(crate) fn mk(&mut self, pos: Pos, ty: Ty, op: Op, args: Vec<HwId>) -> HwId {
        let mut size = op.size();
        let mut height = 0;
        for a in &args {
            size = size.saturating_add(self.size(*a));
            height = height.max(self.nodes.get(a.0).map_or(0, |n| n.height));
        }
        self.height = self.height.max(height + 1);
        self.nodes.push(Node {
            pos,
            ty,
            size,
            height: height + 1,
            op,
            args,
        });
        HwId(self.nodes.len() - 1)
    }

    /// The node `h`. Each id of an elaboration indexes its arena.
    pub(crate) fn node(&self, h: HwId) -> Option<&Node> {
        self.nodes.get(h.0)
    }

    /// The height of the highest hardware value: a leaf has the height 1.
    pub(crate) fn height(&self) -> usize {
        self.height
    }

    pub(crate) fn ty(&self, h: HwId) -> Ty {
        self.nodes.get(h.0).map_or(Ty::Bool, |n| n.ty)
    }

    pub(crate) fn size(&self, h: HwId) -> u64 {
        self.nodes.get(h.0).map_or(1, |n| n.size)
    }
}

/// The resources that need one binding with `:=`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Reg,
    Wire,
    Output,
}

/// A port of an instantiation, as its parent sees it. `sym` is the symbol of its name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Port {
    pub sym: Sym,
    pub input: bool,
    pub ty: Ty,
}

/// A handle. Its number indexes the resources or the instances of its instantiation. An
/// instance also holds the index of its done instantiation, and a child input the number of
/// its instance.
#[derive(Clone, Copy)]
pub(crate) enum Handle {
    Res {
        kind: Kind,
        id: usize,
        ty: Ty,
        path: PathId,
    },
    Inst {
        id: usize,
        path: PathId,
        inst: usize,
    },
    Input {
        inst: usize,
        path: PathId,
        port: Port,
    },
    Domain,
}

/// A value of the evaluator: a static value, a hardware value, or a handle.
#[derive(Clone)]
pub(crate) enum Val {
    Static(Value),
    Hw(HwId),
    Handle(Handle),
}

impl Val {
    /// The recursive size. A handle has the size 1.
    pub(crate) fn size(&self, g: &Graph) -> u64 {
        match self {
            Val::Static(v) => v.size(),
            Val::Hw(h) => g.size(*h),
            Val::Handle(_) => 1,
        }
    }

    /// The type. A string, a type, and a handle have none.
    pub(crate) fn ty(&self, g: &Graph) -> Option<Ty> {
        match self {
            Val::Static(v) => v.ty(),
            Val::Hw(h) => Some(g.ty(*h)),
            Val::Handle(_) => None,
        }
    }

    /// What the value is, for a message.
    pub(crate) fn text(&self, g: &Graph) -> String {
        match self {
            Val::Static(v) => v.text(),
            Val::Hw(h) => format!("hardware {}", g.ty(*h).text()),
            Val::Handle(h) => match h {
                Handle::Res {
                    kind: Kind::Reg, ..
                } => "a register",
                Handle::Res {
                    kind: Kind::Wire, ..
                } => "a wire",
                Handle::Res {
                    kind: Kind::Output, ..
                } => "an output",
                Handle::Inst { .. } => "an instance",
                Handle::Input { .. } => "an input of a child",
                Handle::Domain => "a domain",
            }
            .to_owned(),
        }
    }
}
