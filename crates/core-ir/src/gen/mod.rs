// SPDX-License-Identifier: Apache-2.0
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
//!   never a keyword, and match the name pattern.
//! - Each expression is built for its target width, and each operation gets
//!   operands of the widths that it needs.
//! - The `let` bindings and the instances form a sequence. An expression of
//!   this sequence reads only inputs, registers, memories, and earlier
//!   entries. A deferred connection of an instance can also read later
//!   entries, but no value that depends on an instance output that the
//!   connection feeds. The outputs follow in port order, and an output can
//!   read the earlier outputs. The registers and the memories read the
//!   complete scope. The combinational graph thus has no cycle.
//! - A module instantiates only earlier modules. The top is the last module.
//!   It instantiates each module that no other module instantiates, so it
//!   reaches all modules, at most 3 levels deep.

mod expr;
mod scope;

use std::collections::BTreeSet;

use num_bigint::BigUint;
use proptest::collection::vec;
use proptest::prelude::*;

use crate::ast::{Conn, Design, Dir, Expr, Item, Module, Name, Num, Port, Reset, Stmt, Ty};
use crate::diag::Span;
use crate::typed::{self, address_width};
use crate::value::mask;
use expr::NESTING;
use scope::{Graph, Mem, Scope, Source, Value};

/// The most modules in a design. The last module is the top.
const MODULES: u32 = 6;
/// The most levels of instances below a module.
const LEVELS: u32 = 3;
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
/// The reset input of each module that has a clock, with `Resets::Module`.
pub const RESET: &str = "rst";

/// How the registers of a design reset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resets {
    /// Any 1-bit expression resets, to any expression, or no reset.
    Random,
    /// Each register resets on the reset input of its module to a constant.
    Module,
}

/// Which memories a design has.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mems {
    /// No memory.
    None,
    /// Memories with any number of write ports and combinational reads.
    Core,
}

/// Which forms of the core IR the generator uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    /// Which memories a design has.
    pub mems: Mems,
    /// Names with a `$` field.
    pub dollar_names: bool,
    /// How registers reset.
    pub resets: Resets,
}

impl Config {
    /// The forms that slice-1 source can express: no memory, no `$` in a
    /// name, and each register resets on the reset of its module.
    #[must_use]
    pub fn source() -> Config {
        Config {
            mems: Mems::None,
            dollar_names: false,
            resets: Resets::Module,
        }
    }
}

impl Default for Config {
    fn default() -> Config {
        Config {
            mems: Mems::Core,
            dollar_names: true,
            resets: Resets::Random,
        }
    }
}

/// Random designs without externs that pass [`crate::check::check`].
pub fn design() -> impl Strategy<Value = Design> {
    design_with(Config::default())
}

/// Random designs of the forms that `config` allows.
pub fn design_with(config: Config) -> impl Strategy<Value = Design> {
    vec(any::<u32>(), 0..4096).prop_map(move |tape| {
        Tape {
            numbers: tape.into_iter(),
            config,
        }
        .design()
    })
}

/// A random value for the input `port`, as the digits of an `in=` entry.
fn port_value(port: &typed::Port) -> BoxedStrategy<String> {
    let width = port.width.get();
    vec(any::<u8>(), width.div_ceil(8) as usize)
        .prop_map(move |bytes| (BigUint::from_bytes_le(&bytes) & mask(width)).to_string())
        .boxed()
}

/// Random `in=` lines for the module `top` of a checked design.
pub fn inputs(top: &typed::Module) -> impl Strategy<Value = String> + use<> {
    let ports: Vec<BoxedStrategy<String>> = top
        .inputs
        .iter()
        .map(|port| {
            let name = port.name.clone();
            port_value(port)
                .prop_map(move |value| format!("{name} {value}"))
                .boxed()
        })
        .collect();
    ports.prop_map(|pairs| format!("in=({})", pairs.join(" ")))
}

/// Whether the reset is active in each of `cycles` input lines. The first
/// line resets with probability 3/4, so that the state starts defined. Each
/// later line resets with probability 1/8, so that the state lives for about
/// eight cycles.
pub fn resets(cycles: usize) -> impl Strategy<Value = Vec<bool>> {
    (
        proptest::bool::weighted(0.75),
        vec(proptest::bool::weighted(0.125), cycles.saturating_sub(1)),
    )
        .prop_map(move |(first, later)| {
            std::iter::once(first)
                .chain(later)
                // The first line exists even for no cycles.
                .take(cycles)
                .collect::<Vec<bool>>()
        })
}

/// `cycles` random `in=` lines for the module `top` of a checked design. The
/// value of the input [`RESET`] comes from [`resets`], the others as in
/// [`inputs`].
pub fn lines(top: &typed::Module, cycles: usize) -> impl Strategy<Value = Vec<String>> + use<> {
    let others: Vec<BoxedStrategy<String>> = top
        .inputs
        .iter()
        .filter(|port| port.name != RESET)
        .map(port_value)
        .collect();
    let names: Vec<String> = top.inputs.iter().map(|port| port.name.clone()).collect();
    (resets(cycles), vec(others, cycles)).prop_map(move |(resets, rows)| {
        resets
            .into_iter()
            .zip(rows)
            .map(|(reset, row)| {
                let mut row = row.into_iter();
                let pairs: Vec<String> = names
                    .iter()
                    // `row` holds one value per non-reset name, so only a
                    // missing row value (never) drops a pair.
                    .filter_map(|name| {
                        let value = if name == RESET {
                            Some(String::from(if reset { "1" } else { "0" }))
                        } else {
                            row.next()
                        };
                        value.map(|value| format!("{name} {value}"))
                    })
                    .collect();
                format!("in=({})", pairs.join(" "))
            })
            .collect()
    })
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
    /// The module reset, with `Resets::Module`. It is no data input.
    Reset,
    Input(String, u32),
    Output(String, u32),
}

impl Pin {
    fn port(&self) -> Port {
        let (dir, port, ty) = match self {
            Pin::Clock => (Dir::Input, CLOCK, Ty::Clock),
            Pin::Reset => (Dir::Input, RESET, Ty::Bits(num(1))),
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
    /// For each output in port order, the positions of the data inputs that
    /// it reads combinationally.
    deps: Vec<BTreeSet<usize>>,
    /// The levels of instances below the module.
    levels: u32,
}

/// An instance with the connections that it has so far.
struct Inst {
    name: String,
    module: String,
    conns: Vec<Conn>,
}

/// A connection that waits for the complete scope of its module.
struct Deferred {
    /// The position of the instance.
    inst: usize,
    port: String,
    width: u32,
    /// The instance outputs, as nodes, that read the connected input.
    feeds: BTreeSet<usize>,
}

/// The `let` bindings and the instances of a module under construction.
#[derive(Default)]
struct Body {
    scope: Scope,
    graph: Graph,
    stmts: Vec<Stmt>,
    insts: Vec<Inst>,
    deferred: Vec<Deferred>,
}

struct Tape {
    numbers: std::vec::IntoIter<u32>,
    config: Config,
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

    /// The name of the `n`th entity of a kind. Choice 0 is the plain name.
    /// The other choices start with `silicon_` or have a `$` field, because
    /// Silicon reserves no name (spec 3.4). The kind and the number keep the
    /// names unique.
    fn label(&mut self, kind: &str, n: impl std::fmt::Display) -> String {
        let choices = if self.config.dollar_names { 4 } else { 2 };
        match self.below(choices) {
            1 => format!("silicon_{kind}{n}"),
            2 => format!("{kind}{n}$f"),
            3 => format!("silicon_{kind}${n}"),
            _ => format!("{kind}{n}"),
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
        let mut library: Vec<Interface> = Vec::new();
        let mut items = Vec::new();
        let mut used = BTreeSet::new();
        for k in 0..count - 1 {
            let (interface, module, children) = self.module(k, &library, &[], LEVELS - 1);
            used.extend(children);
            library.push(interface);
            items.push(Item::Module(module));
        }
        let orphans: Vec<usize> = (0..library.len()).filter(|c| !used.contains(c)).collect();
        let (top, module, _) = self.module(count - 1, &library, &orphans, LEVELS);
        items.push(Item::Module(module));
        self.shuffle(&mut items);
        Design {
            top: name(top.name),
            items,
            span: Span::default(),
        }
    }

    /// Module number `k` and the positions in `library` of the modules that
    /// it instantiates: the modules `required`, and some more with fewer
    /// than `levels` levels below them.
    fn module(
        &mut self,
        k: u32,
        library: &[Interface],
        required: &[usize],
        levels: u32,
    ) -> (Interface, Module, Vec<usize>) {
        let has_clock = self.flag() || required.iter().any(|&c| library[c].has_clock);
        let pins = self.pins(has_clock);
        let mut body = Body::default();
        let inputs = pins.iter().filter_map(|pin| match pin {
            Pin::Input(port, width) => Some((port, *width)),
            Pin::Clock | Pin::Reset | Pin::Output(..) => None,
        });
        for (i, (port, width)) in inputs.enumerate() {
            body.scope.values.push(Value {
                expr: reference(port),
                width,
                source: Source::Input(i),
            });
        }
        let regs: Vec<(String, u32)> = (0..if has_clock { self.below(REGS + 1) } else { 0 })
            .map(|r| (self.label("r", r), self.width()))
            .collect();
        for (reg, width) in &regs {
            body.scope.values.push(Value {
                expr: reference(reg),
                width: *width,
                source: Source::State,
            });
        }
        let mem_count = if has_clock && self.config.mems == Mems::Core {
            self.below(MEMS + 1)
        } else {
            0
        };
        let mems: Vec<Mem> = (0..mem_count)
            .map(|m| Mem {
                name: self.label("mem", m),
                width: self.width(),
                depth: self.between(1, DEPTH),
            })
            .collect();
        body.scope.mems.clone_from(&mems);

        let eligible: Vec<usize> = (0..library.len())
            .filter(|&c| library[c].levels < levels && (has_clock || !library[c].has_clock))
            .collect();
        let mut chosen = required.to_vec();
        if !eligible.is_empty() {
            for _ in 0..self.below(INSTS + 1) {
                chosen.push(eligible[self.index(eligible.len())]);
            }
        }
        let children: Vec<&Interface> = chosen.iter().map(|&c| &library[c]).collect();
        self.definitions(&children, &mut body);
        let (deps, assigns) = self.outputs(&pins, &mut body);

        let scope = &body.scope;
        let mut stmts = std::mem::take(&mut body.stmts);
        stmts.extend(assigns);
        for (reg, width) in &regs {
            stmts.push(self.reg(reg, *width, scope));
            stmts.push(Stmt::Next {
                reg: name(reg.clone()),
                expr: self.expr(scope, *width, NESTING),
                span: Span::default(),
            });
        }
        for mem in &mems {
            self.mem(mem, scope, &mut stmts);
        }
        for mut inst in std::mem::take(&mut body.insts) {
            self.shuffle(&mut inst.conns);
            stmts.push(Stmt::Inst {
                name: name(inst.name),
                module: name(inst.module),
                conns: inst.conns,
                span: Span::default(),
            });
        }
        self.shuffle(&mut stmts);

        let interface = Interface {
            name: format!("m{k}"),
            has_clock,
            deps,
            levels: children.iter().map(|c| c.levels + 1).max().unwrap_or(0),
            pins,
        };
        let module = Module {
            name: name(interface.name.clone()),
            ports: interface.pins.iter().map(Pin::port).collect(),
            stmts,
            span: Span::default(),
        };
        (interface, module, chosen)
    }

    /// The `assign` of each output in port order, and the inputs that each
    /// output reads combinationally. Each output joins the scope after its
    /// `assign`, so a later output, a register, or a memory can read it.
    fn outputs(&mut self, pins: &[Pin], body: &mut Body) -> (Vec<BTreeSet<usize>>, Vec<Stmt>) {
        let mut deps = Vec::new();
        let mut assigns = Vec::new();
        for pin in pins {
            if let Pin::Output(port, width) = pin {
                let expr = self.expr(&body.scope, *width, NESTING);
                let sources = body.scope.sources(&expr);
                let node = body.graph.node();
                body.graph.read(node, &sources);
                deps.push(body.graph.support(&sources).inputs);
                body.scope.values.push(Value {
                    expr: reference(port),
                    width: *width,
                    source: Source::Node(node),
                });
                assigns.push(Stmt::Assign {
                    out: name(port.clone()),
                    expr,
                    span: Span::default(),
                });
            }
        }
        (deps, assigns)
    }

    /// The ports of a module in a random order.
    fn pins(&mut self, has_clock: bool) -> Vec<Pin> {
        let mut pins = Vec::new();
        if has_clock {
            pins.push(Pin::Clock);
            if self.config.resets == Resets::Module {
                pins.push(Pin::Reset);
            }
        }
        for i in 0..self.below(INPUTS + 1) {
            pins.push(Pin::Input(self.label("i", i), self.width()));
        }
        for o in 0..self.below(OUTPUTS + 1) {
            pins.push(Pin::Output(self.label("o", o), self.width()));
        }
        self.shuffle(&mut pins);
        pins
    }

    /// The `let` bindings and the instances of `children` in a random
    /// sequence, then the deferred connections.
    fn definitions(&mut self, children: &[&Interface], body: &mut Body) {
        let lets = self.below(LETS + 1) as usize;
        let mut steps: Vec<Option<&Interface>> = children.iter().copied().map(Some).collect();
        steps.resize(children.len() + lets, None);
        self.shuffle(&mut steps);
        for step in steps {
            match step {
                Some(child) => self.inst(child, body),
                None => self.binding(body),
            }
        }
        for d in std::mem::take(&mut body.deferred) {
            let allowed = body.scope.without(&body.graph, &d.feeds);
            let expr = self.expr(&allowed, d.width, NESTING);
            let sources = body.scope.sources(&expr);
            for &node in &d.feeds {
                body.graph.read(node, &sources);
            }
            body.insts[d.inst].conns.push(Conn {
                port: name(d.port),
                expr,
                span: Span::default(),
            });
        }
    }

    /// The next `let` binding. It reads only the earlier entries.
    fn binding(&mut self, body: &mut Body) {
        let width = self.width();
        let binding = self.label("l", body.stmts.len());
        let expr = self.expr(&body.scope, width, NESTING);
        let node = body.graph.node();
        body.graph.read(node, &body.scope.sources(&expr));
        body.stmts.push(Stmt::Let {
            name: name(binding.clone()),
            width: num(width),
            expr,
            span: Span::default(),
        });
        body.scope.values.push(Value {
            expr: reference(&binding),
            width,
            source: Source::Node(node),
        });
    }

    /// The next instance of `child`. A data connection reads the scope now,
    /// or it waits for the complete scope. The outputs of the instance join
    /// the scope after the connections that read the scope now.
    fn inst(&mut self, child: &Interface, body: &mut Body) {
        let inst = self.label("u", body.insts.len());
        let outputs: Vec<usize> = child.deps.iter().map(|_| body.graph.node()).collect();
        let mut conns = Vec::new();
        let mut position = 0;
        for pin in &child.pins {
            match pin {
                Pin::Clock => conns.push(Conn {
                    port: name(CLOCK.to_owned()),
                    expr: reference(CLOCK),
                    span: Span::default(),
                }),
                Pin::Reset => conns.push(Conn {
                    port: name(RESET.to_owned()),
                    expr: reference(RESET),
                    span: Span::default(),
                }),
                Pin::Input(port, width) => {
                    let feeds: BTreeSet<usize> = child
                        .deps
                        .iter()
                        .zip(&outputs)
                        .filter(|(deps, _)| deps.contains(&position))
                        .map(|(_, &node)| node)
                        .collect();
                    position += 1;
                    if self.flag() {
                        body.deferred.push(Deferred {
                            inst: body.insts.len(),
                            port: port.clone(),
                            width: *width,
                            feeds,
                        });
                        continue;
                    }
                    let expr = self.expr(&body.scope, *width, NESTING);
                    let sources = body.scope.sources(&expr);
                    for &node in &feeds {
                        body.graph.read(node, &sources);
                    }
                    conns.push(Conn {
                        port: name(port.clone()),
                        expr,
                        span: Span::default(),
                    });
                }
                Pin::Output(..) => {}
            }
        }
        let ports = child.pins.iter().filter_map(|pin| match pin {
            Pin::Output(port, width) => Some((port, *width)),
            Pin::Clock | Pin::Reset | Pin::Input(..) => None,
        });
        for ((port, width), node) in ports.zip(outputs) {
            body.scope.values.push(Value {
                expr: Expr::InstOut {
                    inst: name(inst.clone()),
                    port: name(port.clone()),
                    span: Span::default(),
                },
                width,
                source: Source::Node(node),
            });
        }
        body.insts.push(Inst {
            name: inst,
            module: child.name.clone(),
            conns,
        });
    }

    /// A memory and its write ports.
    fn mem(&mut self, mem: &Mem, scope: &Scope, stmts: &mut Vec<Stmt>) {
        stmts.push(Stmt::Mem {
            name: name(mem.name.clone()),
            width: num(mem.width),
            depth: num(mem.depth),
            clk: name(CLOCK.to_owned()),
            span: Span::default(),
        });
        for port in 0..self.below(WRITES + 1) {
            stmts.push(Stmt::Write {
                mem: name(mem.name.clone()),
                port,
                addr: self.expr(scope, address_width(mem.depth), NESTING),
                data: self.expr(scope, mem.width, NESTING),
                en: self.expr(scope, 1, NESTING),
                span: Span::default(),
            });
        }
    }

    fn reg(&mut self, reg: &str, width: u32, scope: &Scope) -> Stmt {
        let reset = match self.config.resets {
            Resets::Random => self.flag().then(|| Reset {
                signal: self.expr(scope, 1, NESTING),
                value: self.expr(scope, width, NESTING),
                span: Span::default(),
            }),
            Resets::Module => Some(Reset {
                signal: reference(RESET),
                value: Expr::Const {
                    width: num(width),
                    value: self.constant(width),
                    value_span: Span::default(),
                    span: Span::default(),
                },
                span: Span::default(),
            }),
        };
        Stmt::Reg {
            name: name(reg.to_owned()),
            width: num(width),
            clk: name(CLOCK.to_owned()),
            reset,
            span: Span::default(),
        }
    }
}
