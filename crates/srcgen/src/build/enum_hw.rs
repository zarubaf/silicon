// SPDX-License-Identifier: Apache-2.0
//! Hardware enums: the ports of a module, and the registers, wires,
//! and `let`s of an enum type.
//!
//! An enum value has the two leaves `tag` and `payload`. The builder makes
//! one from a name of the same enum, from a constructor with hardware
//! payload values, from `reinterpret` of hardware bits, and sometimes from
//! a static value. A `reinterpret` of an input can give a tag that no
//! variant declares. The bits of an enum enter the scalar names of a
//! frame through `reinterpret(UInt[data_bits(E)], e)`, because an enum has
//! no fields (front-end spec 5.1).

use super::hw::{Want, reads_name};
use super::stat;
use super::{Builder, Ctx, HwEnum, Names};
use crate::program::{EnumDef, HExpr, Place, SExpr, Scalar, Stmt, Ty};

/// The enum inputs and the enum outputs of a module.
type EnumPorts = (Vec<(String, EnumDef)>, Vec<(String, EnumDef)>);

/// The most enum ports of a module, for each direction.
const PORTS: u32 = 2;

/// Whether the enum value `e` is hardware: it reads a port, a register,
/// or a wire. A `let` of a static value is a static binding, and a
/// `match` over it selects one arm at elaboration time.
pub(super) fn is_hardware(ctx: &Ctx, e: &HExpr) -> bool {
    match e {
        HExpr::Name(_) | HExpr::Field(..) => ctx
            .enums
            .iter()
            .find(|x| x.expr == *e)
            .map_or_else(|| reads_name(e), |x| x.hardware),
        HExpr::Ctor(_, _, args) => args.iter().any(|a| is_hardware(ctx, a)),
        HExpr::Reinterpret(_, a) => is_hardware(ctx, a),
        _ => reads_name(e),
    }
}

/// The type `UInt[data_bits(E)]` of the bits of an enum.
fn bits_ty(def: &EnumDef) -> Ty {
    Ty::UInt(SExpr::DataBits(def.name.clone(), Vec::new()))
}

impl Builder {
    /// The enum ports of a module: inputs `ei<k>` and outputs `eo<k>`.
    pub(super) fn enum_ports(&mut self) -> EnumPorts {
        if self.enums.is_empty() {
            return (Vec::new(), Vec::new());
        }
        let ports = |b: &mut Builder, prefix: &'static str| {
            let mut names = Names::default();
            (0..b.side_below(PORTS + 1))
                .filter_map(|_| b.any_enum().map(|d| (names.fresh(prefix), d)))
                .collect::<Vec<_>>()
        };
        let inputs = ports(self, "ei");
        let outputs = ports(self, "eo");
        (inputs, outputs)
    }

    /// The type of the bits of `def` as a wanted type.
    fn bits_want(def: &EnumDef, envs: usize) -> Want {
        Want {
            types: vec![Scalar::UInt(def.data_bits()); envs],
            ty: Some(bits_ty(def)),
        }
    }

    /// A value of type `UInt[data_bits(E)]`: a hardware expression, or the
    /// constant of that type. A static integer would not convert at
    /// `reinterpret`.
    fn bits_value(&mut self, ctx: &Ctx, def: &EnumDef, depth: u32) -> HExpr {
        let want = Builder::bits_want(def, ctx.envs.len());
        let bits = self
            .hw(ctx, &want, depth)
            .unwrap_or(HExpr::Static(stat::int(0)));
        self.typed_bits(ctx, def, bits)
    }

    /// `bits`, or the constant `UInt[data_bits(E)](k)` if `bits` is a
    /// static integer.
    fn typed_bits(&mut self, ctx: &Ctx, def: &EnumDef, bits: HExpr) -> HExpr {
        if !matches!(bits, HExpr::Static(_)) {
            return bits;
        }
        let want = Builder::bits_want(def, ctx.envs.len());
        let k = self.fit(&want.types, self.reach(ctx), &ctx.envs);
        HExpr::Make(bits_ty(def), k)
    }

    /// A hardware name of the enum `def` in scope, if there is one.
    fn enum_name(&mut self, ctx: &Ctx, def: &EnumDef) -> Option<HExpr> {
        let names: Vec<&HwEnum> = ctx.enums.iter().filter(|e| e.def == *def).collect();
        let e = names.get(self.tape.index(names.len()))?;
        Some(e.expr.clone())
    }

    /// A hardware value of the enum `def`, with draws from the side tape.
    pub(super) fn enum_expr(&mut self, ctx: &Ctx, def: &EnumDef, depth: u32) -> HExpr {
        let envs = ctx.envs.len();
        match self.tape.below(8) {
            0..=2 => {
                if let Some(name) = self.enum_name(ctx, def) {
                    return name;
                }
            }
            3 | 4 => {
                let at = self.tape.index(def.variants.len());
                if let Some(v) = def.variants.get(at) {
                    note!(self, hw_ctors);
                    let args = v
                        .payload
                        .iter()
                        .map(|t| self.value(ctx, &Want::uniform(*t, envs), depth))
                        .collect();
                    return HExpr::Ctor(def.name.clone(), v.name.clone(), args);
                }
            }
            5 => {
                let r = self.reach(ctx);
                return HExpr::Static(self.enum_value(def, r));
            }
            _ => {}
        }
        // Any bits, also a tag that no variant declares.
        let bits = self.bits_value(ctx, def, depth);
        note!(self, hw_unpacks);
        HExpr::Reinterpret(Ty::Enum(def.name.clone()), Box::new(bits))
    }

    /// The value of an enum output or register: it reads a name, so that
    /// the state and the outputs depend on the inputs.
    pub(super) fn enum_driver(&mut self, ctx: &Ctx, def: &EnumDef) -> HExpr {
        self.on_side(|b| {
            let e = b.enum_expr(ctx, def, 2);
            if reads_name(&e) {
                return e;
            }
            let want = Builder::bits_want(def, ctx.envs.len());
            let bits = b.driver(ctx, &want);
            let bits = b.typed_bits(ctx, def, bits);
            HExpr::Reinterpret(Ty::Enum(def.name.clone()), Box::new(bits))
        })
    }

    /// One hardware enum statement of a frame: a `let`, a `wire`, a `reg`, or
    /// a `let` of the bits of an enum name. The caller is on the side tape.
    /// A register joins `regs`, which close at the end of the frame.
    pub(super) fn enum_hw_stmt(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        clocked: bool,
        out: &mut Vec<Stmt>,
        regs: &mut Vec<(String, EnumDef)>,
    ) {
        let Some(def) = self.pick_enum() else {
            return;
        };
        match self.tape.below(8) {
            2 | 3 => self.enum_wire(ctx, names, &def, out),
            4..=6 if clocked => self.enum_reg(ctx, names, &def, out, regs),
            7 => self.bits_let(ctx, names, out),
            _ => self.enum_let(ctx, names, &def, out),
        }
    }

    /// `let l: E = e;`
    fn enum_let(&mut self, ctx: &mut Ctx, names: &mut Names, def: &EnumDef, out: &mut Vec<Stmt>) {
        let value = self.enum_expr(ctx, def, stat::DEPTH);
        let hardware = is_hardware(ctx, &value);
        let name = names.fresh("l");
        out.push(Stmt::Let {
            name: name.clone(),
            mutable: false,
            ty: Some(Ty::Enum(def.name.clone())),
            value,
        });
        note!(self, hw_lets);
        ctx.enums.push(HwEnum {
            expr: HExpr::Name(name),
            def: def.clone(),
            hardware,
        });
    }

    /// `wire w: E; w := e;`
    fn enum_wire(&mut self, ctx: &mut Ctx, names: &mut Names, def: &EnumDef, out: &mut Vec<Stmt>) {
        let name = names.fresh("w");
        out.push(Stmt::Wire(name.clone(), Ty::Enum(def.name.clone())));
        let value = self.enum_expr(ctx, def, stat::DEPTH);
        out.push(Stmt::Connect(Place::Name(name.clone()), value));
        note!(self, hw_wires);
        ctx.enums.push(HwEnum {
            expr: HExpr::Name(name),
            def: def.clone(),
            hardware: true,
        });
    }

    /// `reg r: E = reset;`, driven at the end of the frame.
    fn enum_reg(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        def: &EnumDef,
        out: &mut Vec<Stmt>,
        regs: &mut Vec<(String, EnumDef)>,
    ) {
        let reset = self.enum_value(def, self.reach(ctx));
        let name = names.fresh("r");
        out.push(Stmt::Reg(name.clone(), Ty::Enum(def.name.clone()), reset));
        note!(self, hw_regs);
        regs.push((name.clone(), def.clone()));
        ctx.enums.push(HwEnum {
            expr: HExpr::Name(name),
            def: def.clone(),
            hardware: true,
        });
    }

    /// `let l: UInt[data_bits(E)] = reinterpret(UInt[data_bits(E)], e);`
    /// for a name `e` of an enum, so that the scalar forms can read the
    /// tag and the payload.
    fn bits_let(&mut self, ctx: &mut Ctx, names: &mut Names, out: &mut Vec<Stmt>) {
        let hardware: Vec<&HwEnum> = ctx.enums.iter().filter(|e| e.hardware).collect();
        let Some(e) = hardware
            .get(self.tape.index(hardware.len()))
            .copied()
            .cloned()
        else {
            return;
        };
        let ty = bits_ty(&e.def);
        let name = names.fresh("l");
        out.push(Stmt::Let {
            name: name.clone(),
            mutable: false,
            ty: None,
            value: HExpr::Reinterpret(ty.clone(), Box::new(e.expr)),
        });
        note!(self, hw_bits);
        ctx.hw.push(super::Hw {
            expr: HExpr::Name(name),
            ty: Some(ty),
            types: vec![Scalar::UInt(e.def.data_bits()); ctx.envs.len()],
            mutable: false,
        });
    }

    /// The `:=` of each enum register.
    pub(super) fn close_enum_regs(
        &mut self,
        ctx: &Ctx,
        regs: Vec<(String, EnumDef)>,
        out: &mut Vec<Stmt>,
    ) {
        for (name, def) in regs {
            let value = self.enum_driver(ctx, &def);
            out.push(Stmt::Connect(Place::Name(name), value));
        }
    }
}
