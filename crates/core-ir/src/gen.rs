//! Random well-formed designs for the property and differential tests.
//!
//! A design comes from a tape of random numbers. Each choice of the builder
//! takes the next number of the tape. An exhausted tape gives 0, and choice 0
//! is always the simplest option. Proptest shrinks a failing tape to fewer
//! and smaller numbers, so a failing design shrinks to a simpler one.
//!
//! Each design passes the checker by construction:
//!
//! - The names are a kind prefix and a number, or `clk`, so they are unique,
//!   never a keyword, and never start with `silicon_`.
//! - Each expression is built for its target width, and each operation gets
//!   operands of the widths that it needs.
//! - The `let` bindings and the instances form a sequence. An expression of
//!   this sequence reads only inputs, registers, memories, and earlier
//!   entries, so the combinational graph has no cycle.
//! - A module instantiates only earlier modules, at most 3 levels deep.

use num_bigint::BigUint;
use proptest::collection::vec;
use proptest::prelude::*;

use crate::Pred;
use crate::ast::{
    BinOp, Conn, Design, Dir, Expr, Item, Module, Name, Num, Port, Reset, Stmt, Ty, UnOp,
};
use crate::diag::Span;
use crate::typed;

/// The most modules in a design. The last module is the top.
const MODULES: u32 = 6;
/// The most levels of instances below a module.
const LEVELS: u32 = 3;
/// The most levels of nested operations in one expression.
const NESTING: u32 = 4;
/// The most data inputs, outputs, `let` bindings, registers, memories,
/// write ports, and instances of a module.
const INPUTS: u32 = 4;
const OUTPUTS: u32 = 4;
const LETS: u32 = 6;
const REGS: u32 = 3;
const MEMS: u32 = 2;
const WRITES: u32 = 2;
const INSTS: u32 = 3;
const DEPTH: u32 = 20;
/// The widths are 1 to `NARROW`, and sometimes up to `WIDE`.
const NARROW: u32 = 64;
const WIDE: u32 = 300;
/// The clock input of each module that has one.
const CLOCK: &str = "clk";

const BINOPS: [BinOp; 9] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::Shru,
    BinOp::Shrs,
];

const PREDS: [Pred; 10] = [
    Pred::Eq,
    Pred::Ne,
    Pred::Ult,
    Pred::Ule,
    Pred::Ugt,
    Pred::Uge,
    Pred::Slt,
    Pred::Sle,
    Pred::Sgt,
    Pred::Sge,
];

/// Random designs without externs that pass [`crate::check::check`].
pub fn design() -> impl Strategy<Value = Design> {
    vec(any::<u32>(), 0..4096).prop_map(|tape| {
        Tape {
            numbers: tape.into_iter(),
        }
        .design()
    })
}

/// Random `in=` lines for the module `top` of a checked design.
pub fn inputs(top: &typed::Module) -> impl Strategy<Value = String> + use<> {
    let ports: Vec<BoxedStrategy<String>> = top
        .inputs
        .iter()
        .map(|port| {
            let (name, width) = (port.name.clone(), port.width);
            vec(any::<u8>(), width.div_ceil(8) as usize)
                .prop_map(move |bytes| {
                    let value = BigUint::from_bytes_le(&bytes) & mask(width);
                    format!("{name} {value}")
                })
                .boxed()
        })
        .collect();
    ports.prop_map(|pairs| format!("in=({})", pairs.join(" ")))
}

/// The value with the low `width` bits set.
fn mask(width: u32) -> BigUint {
    (BigUint::from(1u8) << width) - 1u8
}

/// The address width of a memory with `depth` words (spec section 4.1).
fn address_width(depth: u32) -> u32 {
    (u32::BITS - depth.saturating_sub(1).leading_zeros()).max(1)
}

fn name(text: String) -> Name {
    Name {
        text,
        span: Span::default(),
    }
}

fn num(value: u32) -> Num {
    Num {
        value,
        span: Span::default(),
    }
}

fn reference(text: &str) -> Expr {
    Expr::Ref(name(text.to_owned()))
}

/// A port of a generated module.
enum Pin {
    Clock,
    Input(String, u32),
    Output(String, u32),
}

impl Pin {
    fn port(&self) -> Port {
        let (dir, port, ty) = match self {
            Pin::Clock => (Dir::Input, CLOCK, Ty::Clock),
            Pin::Input(port, width) => (Dir::Input, port.as_str(), Ty::Bits(num(*width))),
            Pin::Output(port, width) => (Dir::Output, port.as_str(), Ty::Bits(num(*width))),
        };
        Port {
            dir,
            name: name(port.to_owned()),
            ty,
            span: Span::default(),
        }
    }
}

/// The interface of a generated module, for its parents.
struct Interface {
    name: String,
    /// The ports in port order.
    pins: Vec<Pin>,
    has_clock: bool,
    /// The levels of instances below the module.
    levels: u32,
}

/// What an expression of a module can read.
#[derive(Default)]
struct Scope {
    /// The values with their widths: inputs, registers, earlier `let`
    /// bindings, and the outputs of earlier instances.
    values: Vec<(Expr, u32)>,
    /// The memories with their names, word widths, and depths.
    mems: Vec<(String, u32, u32)>,
}

struct Tape {
    numbers: std::vec::IntoIter<u32>,
}

impl Tape {
    /// A number below `n`, or 0 if `n` is 0.
    fn below(&mut self, n: u32) -> u32 {
        self.numbers.next().unwrap_or(0).checked_rem(n).unwrap_or(0)
    }

    /// A number from `lo` to `hi`.
    fn between(&mut self, lo: u32, hi: u32) -> u32 {
        lo + self.below(hi - lo + 1)
    }

    /// An index into a list of `len` elements.
    fn index(&mut self, len: usize) -> usize {
        (self.numbers.next().unwrap_or(0) as usize)
            .checked_rem(len)
            .unwrap_or(0)
    }

    fn flag(&mut self) -> bool {
        self.below(2) == 1
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            items.swap(i, self.index(i + 1));
        }
    }

    /// A width, mostly up to 64 bits.
    fn width(&mut self) -> u32 {
        if self.below(16) == 15 {
            self.between(NARROW + 1, WIDE)
        } else {
            self.between(1, NARROW)
        }
    }

    fn design(mut self) -> Design {
        let count = self.between(1, MODULES);
        let mut interfaces: Vec<Interface> = Vec::new();
        let mut items = Vec::new();
        for k in 0..count {
            let (interface, module) = self.module(k, &interfaces);
            interfaces.push(interface);
            items.push(Item::Module(module));
        }
        let top = interfaces
            .last()
            .map_or_else(String::new, |top| top.name.clone());
        self.shuffle(&mut items);
        Design {
            top: name(top),
            items,
            span: Span::default(),
        }
    }

    /// Module number `k`. It can instantiate the modules of `library`.
    fn module(&mut self, k: u32, library: &[Interface]) -> (Interface, Module) {
        let has_clock = self.flag();
        let pins = self.pins(has_clock);
        let mut scope = Scope::default();
        for pin in &pins {
            if let Pin::Input(port, width) = pin {
                scope.values.push((reference(port), *width));
            }
        }
        let regs: Vec<(String, u32)> = (0..if has_clock { self.below(REGS + 1) } else { 0 })
            .map(|r| (format!("r{r}"), self.width()))
            .collect();
        for (reg, width) in &regs {
            scope.values.push((reference(reg), *width));
        }
        let mems: Vec<(String, u32, u32)> = (0..if has_clock { self.below(MEMS + 1) } else { 0 })
            .map(|m| (format!("mem{m}"), self.width(), self.between(1, DEPTH)))
            .collect();
        scope.mems.clone_from(&mems);

        let children: Vec<&Interface> = library
            .iter()
            .filter(|child| child.levels < LEVELS && (has_clock || !child.has_clock))
            .collect();
        let (mut stmts, levels) = self.definitions(&children, &mut scope);
        for (reg, width) in &regs {
            stmts.push(self.reg(reg, *width, &scope));
            stmts.push(Stmt::Next {
                reg: name(reg.clone()),
                expr: self.expr(&scope, *width, NESTING),
                span: Span::default(),
            });
        }
        for (mem, width, depth) in &mems {
            self.mem(mem, *width, *depth, &scope, &mut stmts);
        }
        for pin in &pins {
            if let Pin::Output(port, width) = pin {
                stmts.push(Stmt::Assign {
                    out: name(port.clone()),
                    expr: self.expr(&scope, *width, NESTING),
                    span: Span::default(),
                });
            }
        }
        self.shuffle(&mut stmts);

        let module = Module {
            name: name(format!("m{k}")),
            ports: pins.iter().map(Pin::port).collect(),
            stmts,
            span: Span::default(),
        };
        let interface = Interface {
            name: module.name.text.clone(),
            pins,
            has_clock,
            levels,
        };
        (interface, module)
    }

    /// The ports of a module in a random order.
    fn pins(&mut self, has_clock: bool) -> Vec<Pin> {
        let mut pins = Vec::new();
        if has_clock {
            pins.push(Pin::Clock);
        }
        for i in 0..self.below(INPUTS + 1) {
            pins.push(Pin::Input(format!("i{i}"), self.width()));
        }
        for o in 0..self.below(OUTPUTS + 1) {
            pins.push(Pin::Output(format!("o{o}"), self.width()));
        }
        self.shuffle(&mut pins);
        pins
    }

    /// The `let` bindings and the instances of `children`, in one sequence
    /// in which each entry reads only the earlier ones. Also gives the levels
    /// of instances below the module.
    fn definitions(&mut self, children: &[&Interface], scope: &mut Scope) -> (Vec<Stmt>, u32) {
        let insts = if children.is_empty() {
            0
        } else {
            self.below(INSTS + 1)
        };
        let lets = self.below(LETS + 1);
        let mut stmts = Vec::new();
        let mut levels = 0;
        let (mut l, mut u) = (0, 0);
        while l < lets || u < insts {
            if u < insts && (l == lets || self.flag()) {
                let child = children[self.index(children.len())];
                stmts.push(self.inst(&format!("u{u}"), child, scope));
                levels = levels.max(child.levels + 1);
                u += 1;
            } else {
                let width = self.width();
                let let_name = format!("l{l}");
                stmts.push(Stmt::Let {
                    name: name(let_name.clone()),
                    width: num(width),
                    expr: self.expr(scope, width, NESTING),
                    span: Span::default(),
                });
                scope.values.push((reference(&let_name), width));
                l += 1;
            }
        }
        (stmts, levels)
    }

    /// A memory and its write ports.
    fn mem(&mut self, mem: &str, width: u32, depth: u32, scope: &Scope, stmts: &mut Vec<Stmt>) {
        stmts.push(Stmt::Mem {
            name: name(mem.to_owned()),
            width: num(width),
            depth: num(depth),
            clk: name(CLOCK.to_owned()),
            span: Span::default(),
        });
        for port in 0..self.below(WRITES + 1) {
            stmts.push(Stmt::Write {
                mem: name(mem.to_owned()),
                port,
                addr: self.expr(scope, address_width(depth), NESTING),
                data: self.expr(scope, width, NESTING),
                en: self.expr(scope, 1, NESTING),
                span: Span::default(),
            });
        }
    }

    fn reg(&mut self, reg: &str, width: u32, scope: &Scope) -> Stmt {
        let reset = self.flag().then(|| Reset {
            signal: self.expr(scope, 1, NESTING),
            value: self.expr(scope, width, NESTING),
            span: Span::default(),
        });
        Stmt::Reg {
            name: name(reg.to_owned()),
            width: num(width),
            clk: name(CLOCK.to_owned()),
            reset,
            span: Span::default(),
        }
    }

    /// Instance `inst` of `child`. Its outputs join `scope` after the
    /// connections are built, so no connection reads the instance itself.
    fn inst(&mut self, inst: &str, child: &Interface, scope: &mut Scope) -> Stmt {
        let mut conns = Vec::new();
        for pin in &child.pins {
            let (port, expr) = match pin {
                Pin::Clock => (CLOCK, reference(CLOCK)),
                Pin::Input(port, width) => (port.as_str(), self.expr(scope, *width, NESTING)),
                Pin::Output(..) => continue,
            };
            conns.push(Conn {
                port: name(port.to_owned()),
                expr,
                span: Span::default(),
            });
        }
        for pin in &child.pins {
            if let Pin::Output(port, width) = pin {
                let out = Expr::InstOut {
                    inst: name(inst.to_owned()),
                    port: name(port.clone()),
                    span: Span::default(),
                };
                scope.values.push((out, *width));
            }
        }
        Stmt::Inst {
            name: name(inst.to_owned()),
            module: name(child.name.clone()),
            conns,
            span: Span::default(),
        }
    }

    /// An expression of width `width` with at most `nesting` levels of
    /// operations. An operation that does not fit the width gives a leaf.
    fn expr(&mut self, scope: &Scope, width: u32, nesting: u32) -> Expr {
        if nesting == 0 {
            return self.leaf(scope, width);
        }
        let sub = |tape: &mut Tape, width| Box::new(tape.expr(scope, width, nesting - 1));
        let span = Span::default();
        match self.below(10) {
            1 => Expr::Unary {
                op: UnOp::Not,
                arg: sub(self, width),
                span,
            },
            2 => Expr::Binary {
                op: BINOPS[self.index(BINOPS.len())],
                lhs: sub(self, width),
                rhs: sub(self, width),
                span,
            },
            3 if width > 1 => {
                let high = self.between(1, width - 1);
                Expr::Binary {
                    op: BinOp::Concat,
                    lhs: sub(self, high),
                    rhs: sub(self, width - high),
                    span,
                }
            }
            4 if width == 1 => {
                let operands = self.width();
                Expr::Icmp {
                    pred: PREDS[self.index(PREDS.len())],
                    lhs: sub(self, operands),
                    rhs: sub(self, operands),
                    span,
                }
            }
            5 => Expr::Mux {
                cond: sub(self, 1),
                then: sub(self, width),
                els: sub(self, width),
                span,
            },
            6 => {
                let arg = width + self.below(NARROW);
                Expr::Extract {
                    lo: self.below(arg - width + 1),
                    arg: sub(self, arg),
                    width: num(width),
                    span,
                }
            }
            7 => {
                let counts: Vec<u32> = (1..=width).filter(|k| width.is_multiple_of(*k)).collect();
                let count = counts[self.index(counts.len())];
                Expr::Replicate {
                    arg: sub(self, width / count),
                    count: num(count),
                    span,
                }
            }
            8 => {
                let fits: Vec<&(String, u32, u32)> =
                    scope.mems.iter().filter(|(_, w, _)| *w == width).collect();
                match fits.get(self.index(fits.len())) {
                    Some((mem, _, depth)) => Expr::Read {
                        mem: name(mem.clone()),
                        addr: sub(self, address_width(*depth)),
                        span,
                    },
                    None => self.leaf(scope, width),
                }
            }
            _ => self.leaf(scope, width),
        }
    }

    /// A constant, a value of the scope, or a slice of a wider value.
    fn leaf(&mut self, scope: &Scope, width: u32) -> Expr {
        let span = Span::default();
        let wide: Vec<&(Expr, u32)> = scope.values.iter().filter(|(_, w)| *w >= width).collect();
        match (self.below(3), wide.get(self.index(wide.len()))) {
            (1, Some((value, w))) if *w == width => value.clone(),
            (1 | 2, Some((value, w))) => Expr::Extract {
                arg: Box::new(value.clone()),
                lo: self.below(w - width + 1),
                width: num(width),
                span,
            },
            _ => Expr::Const {
                width: num(width),
                value: self.constant(width),
                value_span: span,
                span,
            },
        }
    }

    /// A value below `2^width`: zero, one, all ones, or random bits.
    fn constant(&mut self, width: u32) -> BigUint {
        match self.below(4) {
            0 => BigUint::ZERO,
            1 => BigUint::from(1u8),
            2 => mask(width),
            _ => {
                let words: Vec<u32> = (0..width.div_ceil(32))
                    .map(|_| self.below(u32::MAX))
                    .collect();
                BigUint::from_slice(&words) & mask(width)
            }
        }
    }
}
