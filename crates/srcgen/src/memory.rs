// SPDX-License-Identifier: Apache-2.0
//! The matcher for the core block of a source memory (frontend spec 7.6)
//! and the lift of a matched block.
//!
//! The block is one core memory with a registered read: a data register
//! and a valid register that both reset to 0 on the module reset, and one
//! write that the module reset disables. Any other shape is
//! `Unsupported::Memory`. This module is the only place that knows the
//! source lowering of a memory, so `core-ir` stays independent of it.

use super::expr::Env;
use super::lift::Unsupported;
use core_ir::Pred;
use core_ir::ast::{BinOp, Expr, Module, Stmt};
use core_ir::r#gen::RESET;
use core_ir::typed::address_width;

/// A matched memory block of a module.
pub(super) struct Memory<'a> {
    name: &'a str,
    width: u32,
    depth: u32,
    data: &'a str,
    valid: &'a str,
    read_en: &'a Expr,
    read_addr: &'a Expr,
    write_addr: &'a Expr,
    write_data: &'a Expr,
    write_en: &'a Expr,
}

/// The source lines of one memory, by section of the module body.
#[derive(Default)]
pub(super) struct Lines {
    pub wires: Vec<String>,
    pub mems: Vec<String>,
    pub assigns: Vec<String>,
}

fn is_const(e: &Expr, width: u32, value: u32) -> bool {
    matches!(e, Expr::Const { width: w, value: v, .. }
        if w.value == width && *v == value.into())
}

fn is_reset_ref(e: &Expr) -> bool {
    matches!(e, Expr::Ref(n) if n.text == RESET)
}

/// Whether the register `reg` of `m` has the width `width` and resets to 0
/// on the module reset.
fn resets_to_zero(m: &Module, reg: &str, width: u32) -> bool {
    m.stmts.iter().any(|s| match s {
        Stmt::Reg {
            name,
            width: w,
            reset: Some(r),
            ..
        } => {
            name.text == reg
                && w.value == width
                && is_reset_ref(&r.signal)
                && is_const(&r.value, width, 0)
        }
        _ => false,
    })
}

/// The memories of `m`, or the first one that is not a registered-read
/// block.
pub(super) fn find<'a>(m: &'a Module, env: &Env<'_>) -> Result<Vec<Memory<'a>>, Unsupported> {
    let mut found: Vec<Memory<'a>> = Vec::new();
    for s in &m.stmts {
        if let Stmt::Mem {
            name, width, depth, ..
        } = s
        {
            let claimed: Vec<&str> = found.iter().map(|f| f.valid).collect();
            found.push(block(
                m,
                env,
                &name.text,
                (width.value, depth.value),
                &claimed,
            )?);
        }
    }
    Ok(found)
}

fn block<'a>(
    m: &'a Module,
    env: &Env<'_>,
    name: &'a str,
    (width, depth): (u32, u32),
    claimed: &[&str],
) -> Result<Memory<'a>, Unsupported> {
    let bad = || Unsupported::Memory(name.to_owned());
    let same = |a: &Expr, b: &Expr| Ok::<_, Unsupported>(env.source(a)? == env.source(b)?);

    let mut writes = m.stmts.iter().filter_map(|s| match s {
        Stmt::Write {
            mem,
            port,
            addr,
            data,
            en,
            ..
        } if mem.text == name => Some((*port, addr, data, en)),
        _ => None,
    });
    let (Some((0, write_addr, write_data, enable)), None) = (writes.next(), writes.next()) else {
        return Err(bad());
    };
    let Expr::Binary {
        op: BinOp::And,
        lhs: write_en,
        rhs: running,
        ..
    } = enable
    else {
        return Err(bad());
    };
    let disabled_by_reset = matches!(&**running, Expr::Binary { op: BinOp::Xor, lhs, rhs, .. }
        if is_reset_ref(lhs) && is_const(rhs, 1, 1));
    if !disabled_by_reset {
        return Err(bad());
    }

    let mut loads = m.stmts.iter().filter_map(|s| match s {
        Stmt::Next {
            reg,
            expr: Expr::Mux {
                cond, then, els, ..
            },
            ..
        } => match (&**then, &**els) {
            (Expr::Read { mem, addr, .. }, Expr::Ref(held))
                if mem.text == name && held.text == reg.text =>
            {
                Some((reg.text.as_str(), &**cond, &**addr))
            }
            _ => None,
        },
        _ => None,
    });
    let (Some((data, read_en, read_addr)), None) = (loads.next(), loads.next()) else {
        return Err(bad());
    };

    let a = address_width(depth);
    let in_range = |c: &Expr| -> Result<bool, Unsupported> {
        Ok(if depth == 1 << a {
            is_const(c, 1, 1)
        } else {
            matches!(c, Expr::Icmp { pred: Pred::Ult, lhs, rhs, .. }
                if is_const(rhs, a, depth) && same(lhs, read_addr).unwrap_or(false))
        })
    };
    let mut valids = Vec::new();
    for s in &m.stmts {
        if let Stmt::Next {
            reg,
            expr:
                Expr::Binary {
                    op: BinOp::And,
                    lhs,
                    rhs,
                    ..
                },
            ..
        } = s
            && reg.text != data
            && !claimed.contains(&reg.text.as_str())
            && resets_to_zero(m, &reg.text, 1)
            && same(lhs, read_en)?
            && in_range(rhs)?
        {
            valids.push(reg.text.as_str());
        }
    }
    // Memories with equal requests have valid registers that no shape tells
    // apart. They hold the same value, so the first free one is correct.
    let Some(&valid) = valids.first() else {
        return Err(bad());
    };
    if !resets_to_zero(m, data, width) {
        return Err(bad());
    }
    Ok(Memory {
        name,
        width,
        depth,
        data,
        valid,
        read_en,
        read_addr,
        write_addr,
        write_data,
        write_en,
    })
}

impl Memory<'_> {
    /// Whether the statement `s` belongs to the block, so that the lift
    /// does not print it as a register or a wire.
    pub(super) fn owns(&self, s: &Stmt) -> bool {
        match s {
            Stmt::Mem { name, .. } | Stmt::Write { mem: name, .. } => name.text == self.name,
            Stmt::Reg { name, .. } => name.text == self.data || name.text == self.valid,
            Stmt::Next { reg, .. } => reg.text == self.data || reg.text == self.valid,
            _ => false,
        }
    }

    /// The source name of the response `let`, and so the source text for
    /// reads of the data and valid registers.
    fn response(&self) -> String {
        format!("{}_r", self.name)
    }

    /// The source text that a read of the register `reg` of this block
    /// becomes, or `None` for another name. A 1-bit core value that source
    /// holds as `Bool` crosses back with the idiom of `Env::source`.
    pub(super) fn alias(&self, reg: &str) -> Option<String> {
        let r = self.response();
        if reg == self.data {
            Some(format!("{r}.data"))
        } else if reg == self.valid {
            Some(format!(
                "(if ({r}.valid) {{ UInt[1](1) }} else {{ UInt[1](0) }})"
            ))
        } else {
            None
        }
    }

    /// The names that the lift declares for this block.
    pub(super) fn names(&self) -> [String; 6] {
        let n = self.name;
        ["ra", "re", "wa", "wd", "we", "r"].map(|suffix| format!("{n}_{suffix}"))
    }

    /// The source lines of the block. The request of each port binds to a
    /// wire, because the read address can depend on the read data.
    pub(super) fn lines(&self, env: &Env<'_>) -> Result<Lines, Unsupported> {
        let n = self.name;
        let names = self.names();
        let [ra, re, wa, wd, we, r] = &names;
        let (a, w, depth) = (address_width(self.depth), self.width, self.depth);
        let flag = |e: &Expr| Ok::<_, Unsupported>(format!("({} == UInt[1](1))", env.source(e)?));
        let mut lines = Lines::default();
        lines.wires.extend([
            format!("    wire {ra}: UInt[{a}];"),
            format!("    wire {re}: Bool;"),
            format!("    wire {wa}: UInt[{a}];"),
            format!("    wire {wd}: UInt[{w}];"),
            format!("    wire {we}: Bool;"),
        ]);
        lines.mems.extend([
            format!("    mem {n}: [UInt[{w}]; {depth}];"),
            format!("    let {r} = read_port({n}, {ra}, {re});"),
            format!("    write_port({n}, {wa}, {wd}, {we});"),
        ]);
        lines.assigns.extend([
            format!("    {ra} := {};", env.source(self.read_addr)?),
            format!("    {re} := {};", flag(self.read_en)?),
            format!("    {wa} := {};", env.source(self.write_addr)?),
            format!("    {wd} := {};", env.source(self.write_data)?),
            format!("    {we} := {};", flag(self.write_en)?),
        ]);
        Ok(lines)
    }
}

#[cfg(test)]
mod tests {
    use super::super::lift::{Unsupported, lift};
    use core_ir::text::parse;

    fn lifted(core: &str) -> Result<String, Unsupported> {
        lift(&parse(core).unwrap(), &[]).map(|l| l.text)
    }

    /// A clocked module `m0` with the inputs `ra`, `re`, `wa`, `wd`, `we`
    /// and the memory block of `depth` words of `width` bits.
    fn module(width: u32, depth: u32, ra: &str, extra: &str) -> String {
        let a = core_ir::typed::address_width(depth);
        let in_range = if depth == 1 << a {
            "(const 1 1)".to_owned()
        } else {
            format!("(icmp ult {ra} (const {a} {depth}))")
        };
        format!(
            "(design m0 (module m0 (input clk clock) (input rst (bits 1)) \
             (input ra (bits {a})) (input re (bits 1)) (input wa (bits {a})) \
             (input wd (bits {width})) (input we (bits 1)) \
             (output od (bits {width})) (output ov (bits 1)) \
             (mem mem0 (bits {width}) {depth} clk) \
             (reg d0 (bits {width}) clk (reset sync rst (const {width} 0))) \
             (reg v0 (bits 1) clk (reset sync rst (const 1 0))) \
             (next d0 (mux re (read mem0 {ra}) d0)) \
             (next v0 (and re {in_range})) \
             (write mem0 0 wa wd (and we (xor rst (const 1 1)))) \
             (assign od d0) (assign ov v0){extra}))"
        )
    }

    /// The source of the block of 7.6 for `a`-bit addresses, `w`-bit words,
    /// `depth` words, and the request wire `ra` of the read address.
    fn expected(a: u32, w: u32, depth: u32, ra: &str) -> String {
        let flag = |s: &str| format!("({s} == UInt[1](1))");
        format!(
            "module m0() {{\n\
             \x20   input ra: UInt[{a}];\n    input re: UInt[1];\n    input wa: UInt[{a}];\n\
             \x20   input wd: UInt[{w}];\n    input we: UInt[1];\n\
             \x20   output od: UInt[{w}];\n    output ov: UInt[1];\n\
             \x20   wire mem0_ra: UInt[{a}];\n    wire mem0_re: Bool;\n\
             \x20   wire mem0_wa: UInt[{a}];\n    wire mem0_wd: UInt[{w}];\n    wire mem0_we: Bool;\n\
             \x20   mem mem0: [UInt[{w}]; {depth}];\n\
             \x20   let mem0_r = read_port(mem0, mem0_ra, mem0_re);\n\
             \x20   write_port(mem0, mem0_wa, mem0_wd, mem0_we);\n\
             \x20   mem0_ra := {ra};\n    mem0_re := {};\n    mem0_wa := wa;\n\
             \x20   mem0_wd := wd;\n    mem0_we := {};\n\
             \x20   od := mem0_r.data;\n\
             \x20   ov := (if (mem0_r.valid) {{ UInt[1](1) }} else {{ UInt[1](0) }});\n}}\n",
            flag("re"),
            flag("we")
        )
    }

    #[test]
    fn a_power_of_two_depth_lifts_to_the_memory_block() {
        assert_eq!(
            lifted(&module(8, 4, "ra", "")).unwrap(),
            expected(2, 8, 4, "ra")
        );
    }

    #[test]
    fn depth_five_has_a_range_check_and_lifts_the_same_way() {
        assert_eq!(
            lifted(&module(8, 5, "ra", "")).unwrap(),
            expected(3, 8, 5, "ra")
        );
    }

    #[test]
    fn depth_one_and_word_width_one_lift() {
        assert_eq!(
            lifted(&module(1, 1, "ra", "")).unwrap(),
            expected(1, 1, 1, "ra")
        );
    }

    #[test]
    fn the_read_address_can_read_the_data_register() {
        let core = module(2, 3, "d0", "");
        let want = expected(2, 2, 3, "d0");
        assert_eq!(
            lifted(&core).unwrap(),
            want.replace("mem0_ra := d0;", "mem0_ra := mem0_r.data;")
        );
    }

    #[test]
    fn two_memories_with_equal_requests_lift() {
        let two = module(
            8,
            4,
            "ra",
            "(mem mem1 (bits 8) 4 clk) \
             (reg d1 (bits 8) clk (reset sync rst (const 8 0))) \
             (reg v1 (bits 1) clk (reset sync rst (const 1 0))) \
             (next d1 (mux re (read mem1 ra) d1)) \
             (next v1 (and re (const 1 1))) \
             (write mem1 0 wa wd (and we (xor rst (const 1 1))))",
        );
        let text = lifted(&two).unwrap();
        assert!(text.contains("mem mem1: [UInt[8]; 4];"), "{text}");
        assert!(!text.contains("reg "), "{text}");
    }

    #[test]
    fn an_unrelated_register_with_the_same_next_is_not_the_valid_register() {
        let decoy =
            "(reg x (bits 1) clk (reset sync rst (const 1 1))) (next x (and re (const 1 1)))";
        let ok = module(8, 4, "ra", "");
        // Before the real valid register.
        let before = ok.replace("(reg d0 ", &format!("{decoy} (reg d0 "));
        // After the real valid register.
        let after = ok.replace("(assign od d0)", &format!("{decoy} (assign od d0)"));
        for core in [before, after] {
            let text = lifted(&core).unwrap();
            assert!(text.contains("mem mem0:"), "{text}");
            assert!(text.contains("reg x"), "{text}");
        }
    }

    #[test]
    fn a_wire_of_the_block_with_a_taken_name_is_an_error() {
        let extra = "(inst mem0_ra m1)";
        let core = module(8, 4, "ra", "").replace("(design m0 ", "(design m0 (module m1) ");
        let taken = core.replace("(assign ov v0)", &format!("(assign ov v0){extra}"));
        assert_eq!(lifted(&taken), Err(Unsupported::Name("mem0_ra".into())));
    }

    #[test]
    fn another_shape_stays_unsupported() {
        let ok = module(8, 4, "ra", "");
        let memory = Err(Unsupported::Memory("mem0".into()));
        // A write that the reset does not disable.
        let free = ok.replace("(and we (xor rst (const 1 1)))", "we");
        assert_eq!(lifted(&free), memory);
        // A second write port.
        let two = ok.replace("(assign od", "(write mem0 1 wa wd we) (assign od");
        assert_eq!(lifted(&two), memory);
        // A combinational read.
        let comb = ok.replace("(assign od d0)", "(assign od (read mem0 ra))");
        assert_eq!(lifted(&comb), memory);
        // A valid register that ignores the range of the address.
        let range = module(8, 5, "ra", "").replace("(icmp ult ra (const 3 5))", "(const 1 1)");
        assert_eq!(lifted(&range), memory);
        // A data register without the reset.
        let noreset = ok.replace(
            "(reg d0 (bits 8) clk (reset sync rst (const 8 0)))",
            "(reg d0 (bits 8) clk)",
        );
        assert_eq!(lifted(&noreset), memory);
        // A valid register that resets to 1.
        let one = ok.replace(
            "(reset sync rst (const 1 0))",
            "(reset sync rst (const 1 1))",
        );
        assert_eq!(lifted(&one), memory);
    }
}
