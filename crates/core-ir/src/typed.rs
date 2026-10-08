//! The typed core IR that the checker produces and the interpreter runs.
//!
//! Every reference is a typed index into a table of its module. No name is a
//! string after checking, and no expression can read a clock: the clock of a
//! module is the `has_clock` flag, and no [`Expr`] variant mentions it.

use crate::ast::{BinOp, UnOp};
use crate::{Bits, Pred};

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

/// For each output (by [`OutputIdx`]), the inputs it depends on combinationally,
/// in port order.
pub type Deps = Vec<Vec<InputIdx>>;

/// A data port. Clock ports are not ports of this form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Port {
    /// The port name, kept for printing only.
    pub name: String,
    /// The width in bits.
    pub width: u32,
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
    pub width: u32,
    /// The bound expression.
    pub expr: Expr,
}

/// A register with its next-state expression and optional synchronous reset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reg {
    /// The name, kept for printing only.
    pub name: String,
    /// The width in bits.
    pub width: u32,
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
    pub width: u32,
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
    /// Whether the module has a clock port.
    pub has_clock: bool,
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

/// An extern unit: ports and a dependency declaration, no body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extern {
    /// The extern name.
    pub name: String,
    /// The data inputs, by [`InputIdx`].
    pub inputs: Vec<Port>,
    /// The outputs, by [`OutputIdx`].
    pub outputs: Vec<Port>,
    /// The declared combinational dependencies of the outputs.
    pub deps: Deps,
}

/// A checked design.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Design {
    /// The modules, children first.
    pub modules: Vec<Module>,
    /// The externs, by [`ExternIdx`].
    pub externs: Vec<Extern>,
    /// The top module.
    pub top: ModIdx,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counter_by_hand() {
        let one = Bits::zero(8);
        let counter = Module {
            name: "counter".into(),
            inputs: vec![],
            outputs: vec![Port {
                name: "q".into(),
                width: 8,
            }],
            has_clock: true,
            lets: vec![],
            regs: vec![Reg {
                name: "count".into(),
                width: 8,
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
        assert!(top.has_clock);
        assert_eq!(top.assigns, vec![Expr::Reg(RegIdx::new(0))]);
    }
}
