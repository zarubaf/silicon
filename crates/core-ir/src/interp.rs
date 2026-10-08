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
use crate::diag::{Diagnostic, ErrorCode, Span};
use crate::typed::{Callee, Design, Expr, ModIdx, Module, Node};

/// A simulation of a design that has no extern. The start state is all zero.
pub struct Sim<'d> {
    design: &'d Design,
    top: Frame,
}

impl<'d> Sim<'d> {
    /// Builds the all-zero start state of `design`.
    ///
    /// # Errors
    /// Returns `E014` at the first `extern` item if the design has an extern:
    /// no environment gives the extern a semantics (spec section 5.4).
    pub fn new(design: &'d Design) -> Result<Sim<'d>, Diagnostic> {
        // Spec section 5.4: each extern gives E014, also an extern that no
        // instance runs, so the first extern item wins over the first instance.
        let top = match design.externs.first() {
            Some(ext) => Err(ext.span),
            None => Frame::new(design, design.top),
        };
        let top = top.map_err(|span| Diagnostic {
            code: ErrorCode::E014,
            span,
            message: "no environment for extern".into(),
        })?;
        Ok(Sim { design, top })
    }

    /// Runs one cycle: returns the outputs of the top module for the current
    /// state and `inputs`, then updates the state.
    ///
    /// `inputs` must come from [`crate::vectors::parse_input`] with the top
    /// module of this design.
    #[must_use]
    pub fn step(&mut self, inputs: &Inputs) -> Outputs {
        self.top.begin();
        for (i, value) in inputs.0.iter().enumerate() {
            self.top.inputs.set(i, value.clone());
        }
        self.top.settle(self.design);
        let outputs = Outputs(self.top.outs.values.clone());
        self.top.finish(self.design);
        self.top.update(self.design);
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
    children: Vec<Frame>,
    inputs: Slots,
    lets: Slots,
    outs: Slots,
    /// The frame has not computed its nodes in this cycle yet.
    fresh: bool,
}

impl Frame {
    /// The all-zero frame of `module`, or the position of an extern that an
    /// instance below it runs.
    fn new(design: &Design, module: ModIdx) -> Result<Frame, Span> {
        let m = &design.modules[module.index()];
        let children = m
            .insts
            .iter()
            .map(|inst| match inst.callee {
                Callee::Module(child) => Frame::new(design, child),
                Callee::Extern(ext) => Err(design.externs[ext.index()].span),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Frame {
            module,
            regs: m.regs.iter().map(|r| Bits::zero(r.width)).collect(),
            mems: m.mems.iter().map(|_| HashMap::new()).collect(),
            children,
            inputs: Slots::new(m.inputs.iter().map(|p| p.width)),
            lets: Slots::new(m.lets.iter().map(|l| l.width)),
            outs: Slots::new(m.outputs.iter().map(|p| p.width)),
            fresh: true,
        })
    }

    /// Forgets the values of the last cycle, in this frame and below.
    fn begin(&mut self) {
        for slots in [&mut self.inputs, &mut self.lets, &mut self.outs] {
            slots.known.fill(false);
        }
        self.fresh = true;
        for child in &mut self.children {
            child.begin();
        }
    }

    /// Computes each node of the schedule that the known values allow.
    fn settle(&mut self, design: &Design) {
        self.fresh = false;
        let m = &design.modules[self.module.index()];
        for node in &m.schedule {
            match *node {
                Node::Let(l) => {
                    let (l, expr) = (l.index(), &m.lets[l.index()].expr);
                    if !self.lets.known[l] && self.ready(expr) {
                        let value = self.eval(m, expr);
                        self.lets.set(l, value);
                    }
                }
                Node::Output(o) => {
                    let (o, expr) = (o.index(), &m.assigns[o.index()]);
                    if !self.outs.known[o] && self.ready(expr) {
                        let value = self.eval(m, expr);
                        self.outs.set(o, value);
                    }
                }
                Node::InstOut(u, _) => self.feed(design, m, u.index()),
            }
        }
    }

    /// Passes each known input to child `u`, and lets the child compute what
    /// it can when it has new inputs.
    fn feed(&mut self, design: &Design, m: &Module, u: usize) {
        let mut fed = false;
        for (i, expr) in m.insts[u].inputs.iter().enumerate() {
            if !self.children[u].inputs.known[i] && self.ready(expr) {
                let value = self.eval(m, expr);
                self.children[u].inputs.set(i, value);
                fed = true;
            }
        }
        let child = &mut self.children[u];
        if fed || child.fresh {
            child.settle(design);
        }
    }

    /// Completes the solution below a settled frame: each child gets all its
    /// inputs, also the inputs that no output of the child depends on.
    fn finish(&mut self, design: &Design) {
        let m = &design.modules[self.module.index()];
        for u in 0..self.children.len() {
            self.feed(design, m, u);
            self.children[u].finish(design);
        }
    }

    /// Whether each value that `expr` reads is known in this cycle.
    fn ready(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Input(i) => self.inputs.known[i.index()],
            Expr::Let(l) => self.lets.known[l.index()],
            Expr::InstOut(u, o) => self.children[u.index()].outs.known[o.index()],
            Expr::Reg(_) | Expr::Const(_) => true,
            Expr::Read(_, a) | Expr::Un(_, a) | Expr::Extract(a, ..) | Expr::Replicate(a, _) => {
                self.ready(a)
            }
            Expr::Bin(_, a, b) | Expr::Icmp(_, a, b) => self.ready(a) && self.ready(b),
            Expr::Mux(c, t, e) => self.ready(c) && self.ready(t) && self.ready(e),
        }
    }

    /// The value of `expr`. Each value that it reads must be known.
    fn eval(&self, m: &Module, expr: &Expr) -> Bits {
        match expr {
            Expr::Input(i) => self.inputs.values[i.index()].clone(),
            Expr::Let(l) => self.lets.values[l.index()].clone(),
            Expr::Reg(r) => self.regs[r.index()].clone(),
            Expr::InstOut(u, o) => self.children[u.index()].outs.values[o.index()].clone(),
            Expr::Const(value) => value.clone(),
            Expr::Un(UnOp::Not, a) => self.eval(m, a).not(),
            Expr::Bin(op, a, b) => {
                let (a, b) = (self.eval(m, a), self.eval(m, b));
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
            Expr::Icmp(pred, a, b) => self.eval(m, a).icmp(*pred, &self.eval(m, b)),
            Expr::Mux(c, t, e) => {
                if is_one(&self.eval(m, c)) {
                    self.eval(m, t)
                } else {
                    self.eval(m, e)
                }
            }
            Expr::Extract(a, lo, n) => self.eval(m, a).extract(*lo, *n),
            Expr::Replicate(a, k) => self.eval(m, a).replicate(*k),
            Expr::Read(mem, a) => {
                let mem_def = &m.mems[mem.index()];
                address(&self.eval(m, a), mem_def.depth)
                    .and_then(|addr| self.mems[mem.index()].get(&addr).cloned())
                    .unwrap_or_else(|| Bits::zero(mem_def.width))
            }
        }
    }

    /// Takes the next state from the complete solution of this cycle.
    fn update(&mut self, design: &Design) {
        let m = &design.modules[self.module.index()];
        let regs: Vec<Bits> = m
            .regs
            .iter()
            .map(|r| match &r.reset {
                Some((signal, value)) if is_one(&self.eval(m, signal)) => self.eval(m, value),
                _ => self.eval(m, &r.next),
            })
            .collect();
        // All writes read the old state, so they are computed before any applies.
        let writes: Vec<Vec<(u32, Bits)>> = m
            .mems
            .iter()
            .map(|mem| {
                mem.writes
                    .iter()
                    .filter(|w| is_one(&self.eval(m, &w.en)))
                    .filter_map(|w| {
                        address(&self.eval(m, &w.addr), mem.depth)
                            .map(|addr| (addr, self.eval(m, &w.data)))
                    })
                    .collect()
            })
            .collect();
        self.regs = regs;
        // In port order: a higher port overwrites a lower port.
        for (words, ports) in self.mems.iter_mut().zip(writes) {
            words.extend(ports);
        }
        for child in &mut self.children {
            child.update(design);
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
