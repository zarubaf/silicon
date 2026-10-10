//! The lowering of one checked module to an `hw.module`.
//!
//! The body of an `hw.module` is a graph region: an operation can use a value
//! before its definition. The lowering thus visits the statements in the
//! order of the canonical text (spec section 3.3), and each `read` form gets
//! the next read port of its memory in that order (spec section 7.3).
//!
//! The value names cannot collide. A user name has no `.` (rule `E002`), a
//! register name is a backend name (spec section 3.4), and a temporary value
//! has a number as name.

use core_ir::ast::{BinOp, UnOp};
use core_ir::typed::{Callee, ClockPort, Design, Expr, Module, Port, Reg, address_width};
use core_ir::{Bits, Pred};

use crate::MemConfig;
use crate::mlir::{self, Dir, Pin, Ty};
use crate::names;

/// True if each address of a memory of `depth` words is in range: the depth
/// is a power of two, so an access needs no guard.
fn full_range(depth: u32) -> bool {
    u64::from(depth) == 1u64 << address_width(depth)
}

/// A port of a unit. An input keeps its position among the data inputs.
enum UnitPort<'a> {
    Clock(&'a ClockPort),
    Input(usize, &'a Port),
    Output(&'a Port),
}

impl UnitPort<'_> {
    fn pin(&self) -> Pin {
        let (dir, name, ty) = match self {
            UnitPort::Clock(c) => (Dir::In, &c.name, Ty::Clock),
            UnitPort::Input(_, p) => (Dir::In, &p.name, Ty::Int(p.width.get())),
            UnitPort::Output(p) => (Dir::Out, &p.name, Ty::Int(p.width.get())),
        };
        Pin {
            dir,
            name: name.clone(),
            ty,
        }
    }
}

/// The ports of a unit in source order.
fn unit_ports<'a>(
    inputs: &'a [Port],
    outputs: &'a [Port],
    clock: Option<&'a ClockPort>,
) -> Vec<UnitPort<'a>> {
    let mut ports: Vec<(usize, UnitPort<'a>)> = inputs
        .iter()
        .enumerate()
        .map(|(i, p)| (p.position, UnitPort::Input(i, p)))
        .chain(outputs.iter().map(|p| (p.position, UnitPort::Output(p))))
        .chain(clock.map(|c| (c.position, UnitPort::Clock(c))))
        .collect();
    ports.sort_by_key(|(position, _)| *position);
    ports.into_iter().map(|(_, port)| port).collect()
}

fn pins(ports: &[UnitPort<'_>]) -> Vec<Pin> {
    ports.iter().map(UnitPort::pin).collect()
}

/// The ports of the unit that `callee` names, in source order.
fn callee_ports(design: &Design, callee: Callee) -> (&str, Vec<UnitPort<'_>>) {
    match callee {
        Callee::Module(m) => {
            let m = &design.modules[m.index()];
            let ports = unit_ports(&m.inputs, &m.outputs, m.clock.as_ref());
            (&m.name, ports)
        }
        Callee::Extern(e) => {
            let e = &design.externs[e.index()];
            let ports = unit_ports(&e.inputs, &e.outputs, e.clock.as_ref());
            (&e.name, ports)
        }
    }
}

fn callee_outputs(design: &Design, callee: Callee) -> &[Port] {
    match callee {
        Callee::Module(m) => &design.modules[m.index()].outputs,
        Callee::Extern(e) => &design.externs[e.index()].outputs,
    }
}

/// The `hw.module.extern` declarations of the externs of a design.
pub fn externs(design: &Design) -> String {
    design
        .externs
        .iter()
        .map(|e| {
            let ports = unit_ports(&e.inputs, &e.outputs, e.clock.as_ref());
            mlir::extern_module(&e.name, &pins(&ports))
        })
        .collect()
}

/// The indices of `items`, sorted by name in byte order.
fn by_name<T>(items: &[T], name: impl Fn(&T) -> &str) -> Vec<usize> {
    let mut order: Vec<usize> = (0..items.len()).collect();
    order.sort_by(|&a, &b| name(&items[a]).cmp(name(&items[b])));
    order
}

/// True for an expression that names a value and emits no operation.
fn is_name(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Input(_) | Expr::Let(_) | Expr::Reg(_) | Expr::Output(_) | Expr::InstOut(..)
    )
}

fn reg_name(reg: &Reg) -> String {
    format!("%{}", names::register(&reg.name))
}

fn pred(p: Pred) -> &'static str {
    match p {
        Pred::Eq => "eq",
        Pred::Ne => "ne",
        Pred::Ult => "ult",
        Pred::Ule => "ule",
        Pred::Ugt => "ugt",
        Pred::Uge => "uge",
        Pred::Slt => "slt",
        Pred::Sle => "sle",
        Pred::Sgt => "sgt",
        Pred::Sge => "sge",
    }
}

/// The `comb` operation of a binary operation of the same name. CIRCT gives a
/// shift amount of the width or more the meaning of spec section 4.1, so a
/// shift needs no guard.
fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Xor => "xor",
        BinOp::Shl => "shl",
        BinOp::Shru => "shru",
        BinOp::Shrs => "shrs",
        BinOp::Concat => "concat",
    }
}

/// A value: its MLIR name with the `%` and its width.
struct Value {
    name: String,
    width: u32,
}

/// One read port of a memory.
#[derive(Default)]
struct ReadPort {
    addr: String,
    data: String,
}

/// One write port of a memory, with the guarded enable.
struct WritePort {
    addr: Value,
    data: Value,
    en: Value,
}

/// The lowering state of one module.
struct Lowering<'a> {
    design: &'a Design,
    module: &'a Module,
    body: String,
    temps: usize,
    /// The read ports of each memory, by memory and port index.
    reads: Vec<Vec<ReadPort>>,
    /// The write ports of each memory, by memory and port index.
    writes: Vec<Vec<WritePort>>,
}

/// The MLIR text of `module` and the configurations of its memories.
///
/// `design` comes from the checker, and `module` is one of its modules.
pub fn module(design: &Design, module: &Module) -> (String, Vec<MemConfig>) {
    let mut l = Lowering {
        design,
        module,
        body: String::new(),
        temps: 0,
        reads: module.mems.iter().map(|_| Vec::new()).collect(),
        writes: module.mems.iter().map(|_| Vec::new()).collect(),
    };
    l.statements();
    let configs = l.memories();
    let outputs: Vec<(String, Ty)> = module
        .assigns
        .iter()
        .zip(&module.outputs)
        .map(|(assign, port)| {
            let value = l.named(assign, &port.name, port.width.get());
            (value.name, Ty::Int(value.width))
        })
        .collect();
    let ports = unit_ports(&module.inputs, &module.outputs, module.clock.as_ref());
    let text = mlir::module(&module.name, &pins(&ports), &l.body, &outputs);
    (text, configs)
}

impl<'a> Lowering<'a> {
    fn line(&mut self, text: &str) {
        self.body.push_str("  ");
        self.body.push_str(text);
        self.body.push('\n');
    }

    fn temp(&mut self) -> String {
        let name = format!("%{}", self.temps);
        self.temps += 1;
        name
    }

    /// Emits the operation `op` with a result of `width` bits. The result
    /// gets the name `dest`, or a temporary name.
    fn op(&mut self, dest: Option<&str>, op: &str, width: u32) -> Value {
        let name = dest.map_or_else(|| self.temp(), |d| format!("%{d}"));
        self.line(&format!("{name} = {op}"));
        Value { name, width }
    }

    fn constant(&mut self, dest: Option<&str>, value: &str, width: u32) -> Value {
        self.op(dest, &format!("hw.constant {value} : i{width}"), width)
    }

    /// The clock of the module. A checked module with a register, a memory,
    /// or a clocked instance has one.
    fn clock(&self) -> String {
        match &self.module.clock {
            Some(clock) => format!("%{}", clock.name),
            None => unreachable!("a checked module that uses a clock has one"),
        }
    }

    /// The value of a statement that defines `name`: the value that `expr`
    /// names, or the result of its operation with the name `name`.
    fn named(&self, expr: &'a Expr, name: &str, width: u32) -> Value {
        self.alias(expr).unwrap_or_else(|| Value {
            name: format!("%{name}"),
            width,
        })
    }

    /// The value that `expr` names, or `None` if `expr` is an operation.
    fn alias(&self, mut expr: &'a Expr) -> Option<Value> {
        let m = self.module;
        loop {
            let (name, width) = match expr {
                Expr::Input(i) => {
                    let port = &m.inputs[i.index()];
                    (format!("%{}", port.name), port.width)
                }
                Expr::Reg(r) => {
                    let reg = &m.regs[r.index()];
                    (reg_name(reg), reg.width)
                }
                Expr::InstOut(i, o) => {
                    let inst = &m.insts[i.index()];
                    let port = &callee_outputs(self.design, inst.callee)[o.index()];
                    (format!("%{}.{}", inst.name, port.name), port.width)
                }
                Expr::Let(l) => {
                    let decl = &m.lets[l.index()];
                    if is_name(&decl.expr) {
                        expr = &decl.expr;
                        continue;
                    }
                    (format!("%{}", decl.name), decl.width)
                }
                Expr::Output(o) => {
                    let assign = &m.assigns[o.index()];
                    if is_name(assign) {
                        expr = assign;
                        continue;
                    }
                    let port = &m.outputs[o.index()];
                    (format!("%{}", port.name), port.width)
                }
                _ => return None,
            };
            return Some(Value {
                name,
                width: width.get(),
            });
        }
    }

    /// Lowers the expressions of the statements in canonical order, and
    /// emits the instances and the registers.
    fn statements(&mut self) {
        let m = self.module;
        let regs = by_name(&m.regs, |r| r.name.as_str());
        let resets: Vec<Option<(Value, Value)>> = regs
            .iter()
            .map(|&r| {
                m.regs[r]
                    .reset
                    .as_ref()
                    .map(|(signal, value)| (self.expr(signal, None), self.expr(value, None)))
            })
            .collect();
        for i in by_name(&m.insts, |i| i.name.as_str()) {
            self.instance(i);
        }
        for l in by_name(&m.lets, |l| l.name.as_str()) {
            let decl = &m.lets[l];
            if !is_name(&decl.expr) {
                self.expr(&decl.expr, Some(&decl.name));
            }
        }
        let nexts: Vec<Value> = regs
            .iter()
            .map(|&r| self.expr(&m.regs[r].next, None))
            .collect();
        for mem in by_name(&m.mems, |mem| mem.name.as_str()) {
            for write in &m.mems[mem].writes {
                let addr = self.expr(&write.addr, None);
                let data = self.expr(&write.data, None);
                let en = self.expr(&write.en, None);
                let en = match self.in_range(mem, &addr) {
                    Some(ok) => self.op(None, &format!("comb.and {}, {} : i1", en.name, ok), 1),
                    None => en,
                };
                self.writes[mem].push(WritePort { addr, data, en });
            }
        }
        for o in by_name(&m.outputs, |p| p.name.as_str()) {
            if !is_name(&m.assigns[o]) {
                self.expr(&m.assigns[o], Some(&m.outputs[o].name));
            }
        }
        for ((&r, next), reset) in regs.iter().zip(nexts).zip(resets) {
            let reg = &m.regs[r];
            let reset = reset.map_or_else(String::new, |(signal, value)| {
                format!(" reset {}, {}", signal.name, value.name)
            });
            let text = format!(
                "{} = seq.compreg {}, {}{reset} : i{}",
                reg_name(reg),
                next.name,
                self.clock(),
                reg.width
            );
            self.line(&text);
        }
    }

    /// Lowers the connections of instance `i` in the port order of the
    /// child, and emits the instance.
    fn instance(&mut self, i: usize) {
        let inst = &self.module.insts[i];
        let (callee, ports) = callee_ports(self.design, inst.callee);
        let mut args = Vec::new();
        let mut results = Vec::new();
        for port in &ports {
            match port {
                UnitPort::Clock(_) => args.push(self.clock()),
                UnitPort::Input(k, _) => args.push(self.expr(&inst.inputs[*k], None).name),
                UnitPort::Output(p) => results.push(format!("%{}.{}", inst.name, p.name)),
            }
        }
        let text = mlir::instance(&inst.name, callee, &pins(&ports), &args, &results);
        self.line(&text);
    }

    /// The one-bit value `addr < D` of memory `mem`, or `None` if each
    /// address is in range.
    fn in_range(&mut self, mem: usize, addr: &Value) -> Option<String> {
        let depth = self.module.mems[mem].depth;
        if full_range(depth) {
            return None;
        }
        let width = address_width(depth);
        let bound = self.constant(None, &depth.to_string(), width);
        let ok = self.op(
            None,
            &format!("comb.icmp ult {}, {} : i{width}", addr.name, bound.name),
            1,
        );
        Some(ok.name)
    }

    /// Emits one instance of a memory module for each memory.
    fn memories(&mut self) -> Vec<MemConfig> {
        let m = self.module;
        let mut configs = Vec::new();
        for (index, mem) in m.mems.iter().enumerate() {
            let reads = std::mem::take(&mut self.reads[index]);
            let writes = std::mem::take(&mut self.writes[index]);
            let config = MemConfig {
                depth: mem.depth,
                width: mem.width.get(),
                reads: reads.len(),
                writes: writes.len(),
            };
            let mut args = vec![self.clock()];
            args.extend(reads.iter().map(|r| r.addr.clone()));
            for w in writes {
                args.extend([w.addr.name, w.data.name, w.en.name]);
            }
            let results: Vec<String> = reads.into_iter().map(|r| r.data).collect();
            let text = mlir::instance(
                &mem.name,
                &config.module_name(),
                &config.pins(),
                &args,
                &results,
            );
            self.line(&text);
            configs.push(config);
        }
        configs
    }

    /// Lowers `expr`. The result of its last operation gets the name `dest`.
    fn expr(&mut self, expr: &'a Expr, dest: Option<&str>) -> Value {
        if let Some(value) = self.alias(expr) {
            return value;
        }
        match expr {
            Expr::Const(bits) => self.const_bits(dest, bits),
            Expr::Un(UnOp::Not, arg) => {
                let arg = self.expr(arg, None);
                let ones = self.constant(None, "-1", arg.width);
                let op = format!("comb.xor {}, {} : i{}", arg.name, ones.name, arg.width);
                self.op(dest, &op, arg.width)
            }
            Expr::Bin(BinOp::Concat, a, b) => {
                let (a, b) = (self.expr(a, None), self.expr(b, None));
                let op = format!(
                    "comb.concat {}, {} : i{}, i{}",
                    a.name, b.name, a.width, b.width
                );
                self.op(dest, &op, a.width + b.width)
            }
            Expr::Bin(op, a, b) => {
                let (a, b) = (self.expr(a, None), self.expr(b, None));
                let op = format!("comb.{} {}, {} : i{}", bin_op(*op), a.name, b.name, a.width);
                self.op(dest, &op, a.width)
            }
            Expr::Icmp(p, a, b) => {
                let (a, b) = (self.expr(a, None), self.expr(b, None));
                let op = format!(
                    "comb.icmp {} {}, {} : i{}",
                    pred(*p),
                    a.name,
                    b.name,
                    a.width
                );
                self.op(dest, &op, 1)
            }
            Expr::Mux(c, t, e) => {
                let c = self.expr(c, None);
                let t = self.expr(t, None);
                let e = self.expr(e, None);
                let op = format!("comb.mux {}, {}, {} : i{}", c.name, t.name, e.name, t.width);
                self.op(dest, &op, t.width)
            }
            Expr::Extract(arg, lo, n) => {
                let arg = self.expr(arg, None);
                let op = format!(
                    "comb.extract {} from {lo} : (i{}) -> i{n}",
                    arg.name, arg.width
                );
                self.op(dest, &op, *n)
            }
            Expr::Replicate(arg, k) => {
                let arg = self.expr(arg, None);
                let width = arg.width * k;
                let op = format!("comb.replicate {} : (i{}) -> i{width}", arg.name, arg.width);
                self.op(dest, &op, width)
            }
            Expr::Read(mem, addr) => self.read(mem.index(), addr, dest),
            Expr::Input(_) | Expr::Let(_) | Expr::Reg(_) | Expr::Output(_) | Expr::InstOut(..) => {
                unreachable!("`alias` covers each name")
            }
        }
    }

    fn const_bits(&mut self, dest: Option<&str>, bits: &Bits) -> Value {
        self.constant(dest, &bits.to_biguint().to_string(), bits.width())
    }

    /// Lowers a `read` form: the next read port of `mem`, and the guard
    /// that gives 0 out of range.
    fn read(&mut self, mem: usize, addr: &'a Expr, dest: Option<&str>) -> Value {
        // The port number comes before the address, in the order of the text.
        let port = self.reads[mem].len();
        self.reads[mem].push(ReadPort::default());
        let addr = self.expr(addr, None);
        let width = self.module.mems[mem].width.get();
        let (data, value) = if let Some(ok) = self.in_range(mem, &addr) {
            let data = self.temp();
            let zero = self.constant(None, "0", width);
            let op = format!("comb.mux {ok}, {data}, {} : i{width}", zero.name);
            (data, self.op(dest, &op, width))
        } else {
            let data = dest.map_or_else(|| self.temp(), |d| format!("%{d}"));
            let value = Value {
                name: data.clone(),
                width,
            };
            (data, value)
        };
        self.reads[mem][port] = ReadPort {
            addr: addr.name,
            data,
        };
        value
    }
}
