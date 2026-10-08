//! The interpreter: it runs a typed design one clock cycle at a time (spec
//! section 5.2).
//!
//! Each module evaluates its nodes in the order of its schedule. An instance
//! output needs only the child inputs in its dependencies, and the schedule
//! of the parent orders only those before it. A child frame thus gets its
//! inputs one by one and computes each node as soon as the node can be
//! computed. Each node is computed once per cycle.

use std::collections::HashMap;
use std::num::NonZeroU32;

use num_bigint::BigUint;

use crate::Bits;
use crate::ast::{BinOp, UnOp};
use crate::diag::{Diagnostic, ErrorCode};
use crate::typed::{Callee, Design, Expr, ModIdx, Module, Node};

/// A simulation of a design that has no extern. The start state is all zero.
pub struct Sim<'d> {
    design: &'d Design,
    frames: Frames,
}

impl<'d> Sim<'d> {
    /// Builds the all-zero start state of `design`.
    ///
    /// # Errors
    /// Returns `E014` at the first `extern` item if the design has an extern:
    /// no environment gives the extern a semantics (spec section 5.4).
    ///
    /// # Panics
    /// `design` must come from [`crate::check::check`]. An instance of an
    /// extern that the design does not declare panics.
    pub fn new(design: &'d Design) -> Result<Sim<'d>, Diagnostic> {
        // Spec section 5.4: each extern gives E014, also an extern that no
        // instance runs, so the first extern item wins. The check comes
        // before any frame: the hierarchy can be exponentially large.
        if let Some(ext) = design.externs.first() {
            return Err(Diagnostic {
                code: ErrorCode::E014,
                span: ext.span,
                message: "no environment for extern".into(),
            });
        }
        Ok(Sim {
            design,
            frames: Frames::new(design),
        })
    }

    /// Runs one cycle: returns the outputs of the top module for the current
    /// state and `inputs`, then updates the state.
    ///
    /// `inputs` must come from [`crate::vectors::parse_input`] with the top
    /// module of this design.
    #[must_use]
    pub fn step(&mut self, inputs: &Inputs) -> Outputs {
        let frames = &mut self.frames;
        frames.begin();
        for (i, value) in inputs.0.iter().enumerate() {
            frames.0[TOP].inputs.set(i, value.clone());
        }
        frames.settle(self.design, TOP);
        let outputs = Outputs(frames.0[TOP].outs.values.clone());
        frames.finish(self.design);
        frames.update(self.design);
        outputs
    }
}

/// The values of the data inputs of a top module for one cycle: one value of
/// the port width for each input, in port order. Only
/// [`crate::vectors::parse_input`] builds them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inputs(pub(crate) Vec<Bits>);

/// The values of the outputs of a top module for one cycle, in port order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outputs(pub(crate) Vec<Bits>);

/// Values of one kind that a cycle computes, with a flag for each value that
/// is known in this cycle.
struct Slots {
    values: Vec<Bits>,
    known: Vec<bool>,
}

impl Slots {
    fn new(widths: impl Iterator<Item = NonZeroU32>) -> Slots {
        let values: Vec<Bits> = widths.map(Bits::zero).collect();
        Slots {
            known: vec![false; values.len()],
            values,
        }
    }

    fn set(&mut self, i: usize, value: Bits) {
        self.values[i] = value;
        self.known[i] = true;
    }
}

/// The state of one module instance and its values in the current cycle.
struct Frame {
    module: ModIdx,
    regs: Vec<Bits>,
    /// The written words of each memory. A word that was never written is 0.
    /// A map keeps a deep memory cheap.
    mems: Vec<HashMap<u32, Bits>>,
    /// The frame of each instance, by [`crate::typed::InstIdx`].
    children: Vec<usize>,
    inputs: Slots,
    lets: Slots,
    outs: Slots,
    /// The frame has not computed its nodes in this cycle yet.
    fresh: bool,
}

impl Frame {
    /// The all-zero frame of `module`, without its children.
    fn new(m: &Module, module: ModIdx) -> Frame {
        Frame {
            module,
            regs: m.regs.iter().map(|r| Bits::zero(r.width)).collect(),
            mems: m.mems.iter().map(|_| HashMap::new()).collect(),
            children: Vec::with_capacity(m.insts.len()),
            inputs: Slots::new(m.inputs.iter().map(|p| p.width)),
            lets: Slots::new(m.lets.iter().map(|l| l.width)),
            outs: Slots::new(m.outputs.iter().map(|p| p.width)),
            fresh: true,
        }
    }
}

/// The position of the frame of the top module.
const TOP: usize = 0;

/// The frames of all module instances in one flat table: the top first, and
/// each child after its parent. Each walk over the hierarchy keeps its own
/// stack, so a deep hierarchy cannot overflow the call stack.
struct Frames(Vec<Frame>);

impl Frames {
    /// The all-zero frames of a design without externs: the top and every
    /// instance below it.
    ///
    /// # Panics
    /// An instance of an extern panics. [`Sim::new`] admits only a design
    /// without externs, and a checked design has no instance of an extern
    /// that it does not declare.
    fn new(design: &Design) -> Frames {
        let top = &design.modules[design.top.index()];
        let mut frames = vec![Frame::new(top, design.top)];
        let mut parent = 0;
        while let Some(frame) = frames.get(parent) {
            let m = &design.modules[frame.module.index()];
            for inst in &m.insts {
                let Callee::Module(child) = inst.callee else {
                    unreachable!("a design without externs runs an extern");
                };
                let index = frames.len();
                frames.push(Frame::new(&design.modules[child.index()], child));
                frames[parent].children.push(index);
            }
            parent += 1;
        }
        Frames(frames)
    }

    /// Forgets the values of the last cycle.
    fn begin(&mut self) {
        for frame in &mut self.0 {
            for slots in [&mut frame.inputs, &mut frame.lets, &mut frame.outs] {
                slots.known.fill(false);
            }
            frame.fresh = true;
        }
    }

    /// Computes each node of the schedule of frame `root` that the known
    /// values allow. A child with new inputs computes what it can before the
    /// parent goes on.
    fn settle(&mut self, design: &Design, root: usize) {
        // Each entry is a frame and the position in its schedule to go on at.
        let mut stack = vec![(root, 0)];
        'frames: while let Some((f, start)) = stack.pop() {
            let m = &design.modules[self.0[f].module.index()];
            if start == 0 {
                self.0[f].fresh = false;
            }
            for (at, node) in m.schedule.iter().enumerate().skip(start) {
                match *node {
                    Node::Let(l) => {
                        let (l, expr) = (l.index(), &m.lets[l.index()].expr);
                        if !self.0[f].lets.known[l] && self.ready(f, expr) {
                            let value = self.eval(m, f, expr);
                            self.0[f].lets.set(l, value);
                        }
                    }
                    Node::Output(o) => {
                        let (o, expr) = (o.index(), &m.assigns[o.index()]);
                        if !self.0[f].outs.known[o] && self.ready(f, expr) {
                            let value = self.eval(m, f, expr);
                            self.0[f].outs.set(o, value);
                        }
                    }
                    Node::InstOut(u, _) => {
                        if let Some(child) = self.feed(m, f, u.index()) {
                            stack.push((f, at + 1));
                            stack.push((child, 0));
                            continue 'frames;
                        }
                    }
                }
            }
        }
    }

    /// Passes each known input of frame `f` to its child `u`. Returns the
    /// frame of the child if it has new inputs or has not computed yet.
    fn feed(&mut self, m: &Module, f: usize, u: usize) -> Option<usize> {
        let child = self.0[f].children[u];
        let mut fed = false;
        for (i, expr) in m.insts[u].inputs.iter().enumerate() {
            if !self.0[child].inputs.known[i] && self.ready(f, expr) {
                let value = self.eval(m, f, expr);
                self.0[child].inputs.set(i, value);
                fed = true;
            }
        }
        (fed || self.0[child].fresh).then_some(child)
    }

    /// Completes the solution below the settled top: each child gets all its
    /// inputs, also the inputs that no output of the child depends on. A
    /// parent is complete before its children.
    fn finish(&mut self, design: &Design) {
        for f in 0..self.0.len() {
            let m = &design.modules[self.0[f].module.index()];
            for u in 0..self.0[f].children.len() {
                if let Some(child) = self.feed(m, f, u) {
                    self.settle(design, child);
                }
            }
        }
    }

    /// Whether each value that `expr` reads in frame `f` is known in this
    /// cycle.
    fn ready(&self, f: usize, expr: &Expr) -> bool {
        let frame = &self.0[f];
        match expr {
            Expr::Input(i) => frame.inputs.known[i.index()],
            Expr::Let(l) => frame.lets.known[l.index()],
            Expr::Output(o) => frame.outs.known[o.index()],
            Expr::InstOut(u, o) => self.0[frame.children[u.index()]].outs.known[o.index()],
            Expr::Reg(_) | Expr::Const(_) => true,
            Expr::Read(_, a) | Expr::Un(_, a) | Expr::Extract(a, ..) | Expr::Replicate(a, _) => {
                self.ready(f, a)
            }
            Expr::Bin(_, a, b) | Expr::Icmp(_, a, b) => self.ready(f, a) && self.ready(f, b),
            Expr::Mux(c, t, e) => self.ready(f, c) && self.ready(f, t) && self.ready(f, e),
        }
    }

    /// The value of `expr` in frame `f` of module `m`. Each value that it
    /// reads must be known.
    fn eval(&self, m: &Module, f: usize, expr: &Expr) -> Bits {
        let frame = &self.0[f];
        match expr {
            Expr::Input(i) => frame.inputs.values[i.index()].clone(),
            Expr::Let(l) => frame.lets.values[l.index()].clone(),
            Expr::Output(o) => frame.outs.values[o.index()].clone(),
            Expr::Reg(r) => frame.regs[r.index()].clone(),
            Expr::InstOut(u, o) => self.0[frame.children[u.index()]].outs.values[o.index()].clone(),
            Expr::Const(value) => value.clone(),
            Expr::Un(UnOp::Not, a) => self.eval(m, f, a).not(),
            Expr::Bin(op, a, b) => {
                let (a, b) = (self.eval(m, f, a), self.eval(m, f, b));
                match op {
                    BinOp::Add => a.add(&b),
                    BinOp::Sub => a.sub(&b),
                    BinOp::Mul => a.mul(&b),
                    BinOp::And => a.and(&b),
                    BinOp::Or => a.or(&b),
                    BinOp::Xor => a.xor(&b),
                    BinOp::Shl => a.shl(&b),
                    BinOp::Shru => a.shru(&b),
                    BinOp::Shrs => a.shrs(&b),
                    BinOp::Concat => a.concat(&b),
                }
            }
            Expr::Icmp(pred, a, b) => self.eval(m, f, a).icmp(*pred, &self.eval(m, f, b)),
            Expr::Mux(cond, then, els) => {
                if is_one(&self.eval(m, f, cond)) {
                    self.eval(m, f, then)
                } else {
                    self.eval(m, f, els)
                }
            }
            Expr::Extract(a, lo, n) => self.eval(m, f, a).extract(*lo, *n),
            Expr::Replicate(a, k) => self.eval(m, f, a).replicate(*k),
            Expr::Read(mem, a) => {
                let mem_def = &m.mems[mem.index()];
                address(&self.eval(m, f, a), mem_def.depth)
                    .and_then(|addr| frame.mems[mem.index()].get(&addr).cloned())
                    .unwrap_or_else(|| Bits::zero(mem_def.width))
            }
        }
    }

    /// Takes the next state of each frame from the complete solution of this
    /// cycle. A frame reads only its own state and the values of the cycle,
    /// so the order of the frames does not matter.
    fn update(&mut self, design: &Design) {
        for f in 0..self.0.len() {
            let m = &design.modules[self.0[f].module.index()];
            let regs: Vec<Bits> = m
                .regs
                .iter()
                .map(|r| match &r.reset {
                    Some((signal, value)) if is_one(&self.eval(m, f, signal)) => {
                        self.eval(m, f, value)
                    }
                    _ => self.eval(m, f, &r.next),
                })
                .collect();
            // All writes read the old state, so they are computed before any applies.
            let writes: Vec<Vec<(u32, Bits)>> = m
                .mems
                .iter()
                .map(|mem| {
                    mem.writes
                        .iter()
                        .filter(|w| is_one(&self.eval(m, f, &w.en)))
                        .filter_map(|w| {
                            address(&self.eval(m, f, &w.addr), mem.depth)
                                .map(|addr| (addr, self.eval(m, f, &w.data)))
                        })
                        .collect()
                })
                .collect();
            let frame = &mut self.0[f];
            frame.regs = regs;
            // In port order: a higher port overwrites a lower port.
            for (words, ports) in frame.mems.iter_mut().zip(writes) {
                words.extend(ports);
            }
        }
    }
}

fn is_one(bit: &Bits) -> bool {
    bit.to_biguint() == BigUint::from(1u8)
}

/// The address as a word index, if it is below `depth`.
fn address(addr: &Bits, depth: u32) -> Option<u32> {
    u32::try_from(addr.to_biguint()).ok().filter(|&a| a < depth)
}
