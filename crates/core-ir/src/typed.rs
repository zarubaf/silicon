//! The typed core IR that the checker produces and the interpreter runs.
//!
//! Every reference is a typed index into a table of its module. No name is a
//! string after checking, and no expression can read a clock: the clock of a
//! module is its [`ClockPort`], and no [`Expr`] variant mentions it.

use crate::ast::{BinOp, UnOp};
use crate::diag::Span;
use crate::{Bits, Pred};
use std::num::NonZeroU32;

macro_rules! index {
    ($(#[$doc:meta] $name:ident),* $(,)?) => {$(
        #[$doc]
        #[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
        pub struct $name(usize);

        impl $name {
            pub(crate) fn new(index: usize) -> Self {
                Self(index)
            }

            /// The position in the table.
            #[must_use]
            pub fn index(self) -> usize {
                self.0
            }
        }
    )*};
}

index! {
    /// Position of a module in [`Design::modules`].
    ModIdx,
    /// Position of an extern in [`Design::externs`].
    ExternIdx,
    /// Position of a data input port, the clock excluded.
    InputIdx,
    /// Position of an output port.
    OutputIdx,
    /// Position of a `let` in [`Module::lets`].
    LetIdx,
    /// Position of a register in [`Module::regs`].
    RegIdx,
    /// Position of a memory in [`Module::mems`].
    MemIdx,
    /// Position of an instance in [`Module::insts`].
    InstIdx,
}

/// The address width of a memory with `depth` words: `max(1, ceil(log2 depth))`
/// (spec section 4.1).
#[must_use]
pub fn address_width(depth: u32) -> u32 {
    (u32::BITS - depth.saturating_sub(1).leading_zeros()).max(1)
}

/// For each output (by [`OutputIdx`]), the inputs it depends on combinationally,
/// in port order.
pub type Deps = Vec<Vec<InputIdx>>;

/// A data port. Clock ports are not ports of this form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Port {
    /// The port name, kept for printing only.
    pub name: String,
    /// The width in bits.
    pub width: NonZeroU32,
    /// The position of the port among all ports of its unit, the clock
    /// included.
    pub position: usize,
}

/// A combinational expression. No variant refers to a clock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// A data input of the module.
    Input(InputIdx),
    /// A `let` binding.
    Let(LetIdx),
    /// The current value of a register.
    Reg(RegIdx),
    /// An output of the module itself: the value of its `assign`.
    Output(OutputIdx),
    /// An output of an instance.
    InstOut(InstIdx, OutputIdx),
    /// A constant.
    Const(Bits),
    /// A unary operation.
    Un(UnOp, Box<Expr>),
    /// A binary operation.
    Bin(BinOp, Box<Expr>, Box<Expr>),
    /// An integer comparison with a one-bit result.
    Icmp(Pred, Box<Expr>, Box<Expr>),
    /// `Mux(cond, then, else)`.
    Mux(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `Extract(arg, lo, width)`.
    Extract(Box<Expr>, u32, u32),
    /// `Replicate(arg, count)`.
    Replicate(Box<Expr>, u32),
    /// An asynchronous read of a memory at an address.
    Read(MemIdx, Box<Expr>),
}

/// A named `let` binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Let {
    /// The name, kept for printing only.
    pub name: String,
    /// The width in bits.
    pub width: NonZeroU32,
    /// The bound expression.
    pub expr: Expr,
}

/// A register with its next-state expression and optional synchronous reset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reg {
    /// The name, kept for printing only.
    pub name: String,
    /// The width in bits.
    pub width: NonZeroU32,
    /// The value after the next clock edge.
    pub next: Expr,
    /// The reset signal and the reset value.
    pub reset: Option<(Expr, Expr)>,
}

/// One write port of a memory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Write {
    /// The address.
    pub addr: Expr,
    /// The data to store.
    pub data: Expr,
    /// The one-bit write enable.
    pub en: Expr,
}

/// A memory with synchronous write ports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mem {
    /// The name, kept for printing only.
    pub name: String,
    /// The width of one word in bits.
    pub width: NonZeroU32,
    /// The number of words.
    pub depth: u32,
    /// The write ports, by port index.
    pub writes: Vec<Write>,
}

/// What an instance runs.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Callee {
    /// A module of the same design.
    Module(ModIdx),
    /// An extern, which has a dependency declaration and no body.
    Extern(ExternIdx),
}

/// An instance of a module or extern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inst {
    /// The instance name, kept for printing only.
    pub name: String,
    /// The instantiated unit.
    pub callee: Callee,
    /// The arguments, by child [`InputIdx`]. The clock input is omitted.
    pub inputs: Vec<Expr>,
}

/// A step of the combinational schedule.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Node {
    /// Evaluate a `let`.
    Let(LetIdx),
    /// Evaluate an output assignment.
    Output(OutputIdx),
    /// Evaluate one output of an instance.
    InstOut(InstIdx, OutputIdx),
}

/// A checked module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    /// The module name.
    pub name: String,
    /// The data inputs, by [`InputIdx`].
    pub inputs: Vec<Port>,
    /// The outputs, by [`OutputIdx`].
    pub outputs: Vec<Port>,
    /// The clock input, if the module has one.
    pub clock: Option<ClockPort>,
    /// The `let` bindings, by [`LetIdx`].
    pub lets: Vec<Let>,
    /// The registers, by [`RegIdx`].
    pub regs: Vec<Reg>,
    /// The memories, by [`MemIdx`].
    pub mems: Vec<Mem>,
    /// The instances, by [`InstIdx`].
    pub insts: Vec<Inst>,
    /// The output assignments, by [`OutputIdx`].
    pub assigns: Vec<Expr>,
    /// The evaluation order. The dependency analysis fills it.
    pub schedule: Vec<Node>,
    /// The combinational dependencies of the outputs. The analysis fills it.
    pub deps: Deps,
}

/// A clock input port, kept for the signature of a module or an extern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClockPort {
    /// The port name.
    pub name: String,
    /// The position of the port among all ports of its unit.
    pub position: usize,
}

/// An extern unit: ports and a dependency declaration, no body.
///
/// An instance of a clocked extern gets the clock of its parent, as an
/// instance of a clocked module does: a design has at most one clock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extern {
    /// The extern name.
    pub name: String,
    /// The data inputs, by [`InputIdx`].
    pub inputs: Vec<Port>,
    /// The outputs, by [`OutputIdx`].
    pub outputs: Vec<Port>,
    /// The clock input, if the extern has one.
    pub clock: Option<ClockPort>,
    /// The declared combinational dependencies of the outputs.
    pub deps: Deps,
    /// The start of the `extern` item. `run` reports `E014` here.
    pub span: Span,
}

/// A checked design.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Design {
    /// The modules, children first.
    pub modules: Vec<Module>,
    /// The externs, by [`ExternIdx`], in source order.
    pub externs: Vec<Extern>,
    /// The top module.
    pub top: ModIdx,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counter_by_hand() {
        let eight = NonZeroU32::new(8).unwrap();
        let one = Bits::zero(eight);
        let counter = Module {
            name: "counter".into(),
            inputs: vec![],
            outputs: vec![Port {
                name: "q".into(),
                width: eight,
                position: 1,
            }],
            clock: Some(ClockPort {
                name: "clk".into(),
                position: 0,
            }),
            lets: vec![],
            regs: vec![Reg {
                name: "count".into(),
                width: eight,
                next: Expr::Bin(
                    BinOp::Add,
                    Box::new(Expr::Reg(RegIdx::new(0))),
                    Box::new(Expr::Const(one)),
                ),
                reset: None,
            }],
            mems: vec![],
            insts: vec![],
            assigns: vec![Expr::Reg(RegIdx::new(0))],
            schedule: vec![],
            deps: Deps::default(),
        };
        let design = Design {
            modules: vec![counter],
            externs: vec![],
            top: ModIdx::new(0),
        };
        let top = &design.modules[design.top.index()];
        assert_eq!(top.name, "counter");
        assert!(top.clock.is_some());
        assert_eq!(top.assigns, vec![Expr::Reg(RegIdx::new(0))]);
    }
}
