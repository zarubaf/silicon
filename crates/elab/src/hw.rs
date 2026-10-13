// SPDX-License-Identifier: Apache-2.0
//! The values of the evaluator, as Lean `Source.Eval` defines them (section 5.1): a static
//! value, a hardware value, or a handle. A hardware value is a typed tree of operations over
//! core names. Its nodes live in one arena, so an operand tree is shared, not copied: a new
//! node holds the indices of its operands.

use crate::agg::Agg;
use crate::names::{Name, PathId, Sym};
use crate::types::{Ty, TyId, Types};
use crate::value::{Value, width_size};
use parse::ast::{BinOp, Pos, UnOp};
use resolve::DeclId;

/// A node of a hardware value: an index into the arena of its elaboration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HwId(usize);

/// The core name of the port with the source name `x`. A port keeps its source name.
pub(crate) fn port_name(x: &str) -> Name {
    Name {
        head: x.to_owned(),
        rest: Vec::new(),
    }
}

/// The operation of a node. Section 7.4 lowers each node to core operations.
pub(crate) enum Op {
    Ref(PathId),
    Out(PathId, Name),
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
    /// The condition of an aggregate `if`, which several leaf statements share. The lowering
    /// binds it to one temporary at its first use. `k` numbers the marks of one instantiation.
    /// The mark has no charge and no size.
    Share(u64),
    Resize,
    Reinterpret,
}

impl Op {
    /// The size of a node of the type `ty` without its operands. A name and a child output refer
    /// to a core name, and each has the size of a finite value of its type (section 5.4). A
    /// constant has the size of its value. Each other node has the size 1.
    fn size(&self, ty: &Ty) -> u64 {
        match self {
            Op::Lit(v) => v.size(),
            Op::Count { size, .. } => *size,
            Op::Share(_) => 0,
            Op::Ref(_) | Op::Out(..) => match ty {
                Ty::UInt(w) | Ty::SInt(w) => width_size(*w),
                _ => 1,
            },
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
        let mut size = op.size(&ty);
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
        self.nodes.get(h.0).map_or(Ty::Bool, |n| n.ty.clone())
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Port {
    pub sym: Sym,
    pub input: bool,
    pub ty: Ty,
}

/// A handle. Its number indexes the resources or the instances of its instantiation. An
/// instance also holds the index of its done instantiation, and a child input the number of
/// its instance.
#[derive(Clone)]
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

/// Where a reference starts: the local of the frame at this index of the frame stack, or the
/// constant at this index of the table of constants.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Root {
    Local(usize, DeclId),
    Const(usize),
}

/// A reference to a value that exists: a root, then the numbers of the elements of the
/// containers below it. It copies nothing, so a read that the cost model does not charge does
/// no work in the size of the value.
#[derive(Clone)]
pub(crate) struct Ref {
    pub root: Root,
    pub path: Vec<usize>,
}

/// A part of a literal that waits for its type. It is a value in its normal form as an
/// aggregate part, the literal `[]` at the position, or an array or a tuple literal at the
/// position. Such a literal has at least one part that waits.
#[derive(Clone)]
pub(crate) enum Part {
    Value(Agg),
    Empty(Pos),
    Array(Pos, Vec<Part>),
    Tuple(Pos, Vec<Part>),
}

/// A value of the evaluator: a static value, a hardware value, or a handle. `Pending` is a
/// literal with `[]` before a typed use gives it its type. It holds the position of its first
/// `[]`.
#[derive(Clone)]
pub(crate) enum Val {
    Static(Value),
    Hw(HwId),
    Handle(Handle),
    Pending(Pos, Part),
    /// A hardware aggregate: a tree with at least one hardware leaf.
    Agg(Box<Agg>),
}

/// What a result is, without a copy: a static value, a hardware value, a handle, or a literal
/// that waits for its type.
#[derive(Clone, Copy)]
pub(crate) enum Seen<'a> {
    Static(&'a Value),
    Hw(HwId),
    Handle(&'a Handle),
    Pending(Pos, &'a Part),
    Agg(&'a Agg),
}

impl Val {
    pub(crate) fn seen(&self) -> Seen<'_> {
        match self {
            Val::Static(v) => Seen::Static(v),
            Val::Hw(h) => Seen::Hw(*h),
            Val::Handle(h) => Seen::Handle(h),
            Val::Pending(q, p) => Seen::Pending(*q, p),
            Val::Agg(a) => Seen::Agg(a),
        }
    }

    /// The type. A handle and a literal that waits have none.
    pub(crate) fn ty(&self, g: &Graph, tys: &mut Types) -> Option<TyId> {
        self.seen().ty(g, tys)
    }
}

impl Seen<'_> {
    /// The type. A handle and a literal that waits have none.
    pub(crate) fn ty(&self, g: &Graph, tys: &mut Types) -> Option<TyId> {
        match self {
            Seen::Static(v) => Some(v.ty(tys)),
            Seen::Hw(h) => Some(tys.mk(g.ty(*h))),
            Seen::Agg(a) => Some(a.ty(g, tys)),
            Seen::Handle(_) | Seen::Pending(..) => None,
        }
    }

    /// What the value is, for a message. A literal that waits is `None`: its text needs the
    /// values that it refers to.
    pub(crate) fn text(&self, g: &Graph, tys: &Types) -> Option<String> {
        Some(match self {
            Seen::Static(v) => v.text(tys),
            Seen::Hw(h) => format!("hardware {}", tys.text_of(&g.ty(*h))),
            Seen::Handle(h) => match h {
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
            Seen::Agg(a) => a.stored_ty().map_or_else(
                || "hardware".to_owned(),
                |t| format!("hardware {}", tys.text(t)),
            ),
            Seen::Pending(..) => return None,
        })
    }
}
