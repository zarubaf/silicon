// SPDX-License-Identifier: Apache-2.0
//! Enums: the `enum` items, and the static values of an enum.
//!
//! An enum has a tag type `UInt[W]` with `W` in `1..=3`, up to four
//! variants with distinct tags, and up to two payload leaves for each
//! variant. Its tags are in shuffled order, and in most enums some tags of
//! `0..2^W` belong to no variant. A value can still have such a tag, from
//! `E()`, from `reinterpret`, or from an input line. In one enum of four,
//! all tags of a two-bit tag type belong to a variant, so a `match` over
//! all variants needs no `_`.
//!
//! Every draw of an enum form comes from the side tape (`on_side`). A form
//! adds a statement or replaces a subexpression, so the main tape of a
//! program keeps the statements that it would draw without enums.

use super::stat::{self, Reach};
use super::{Builder, Built, Ctx, Names};
use crate::eval::Env;
use crate::program::{EnumDef, Item, SExpr, STy, Scalar, Stmt, Variant};
use num_bigint::BigUint;

/// The most enums, variants of an enum, and payload leaves of a variant.
const ENUMS: u32 = 2;
const VARIANTS: u32 = 4;
const PAYLOADS: u32 = 2;
/// The widths of a payload leaf. The last one is drawn rarely: the
/// payload of the enum then passes 256 bits.
const WIDTHS: [u32; 7] = [1, 2, 3, 4, 8, 16, 64];
const WIDE: u32 = 257;
/// The most enum statements that a frame adds, and the most enum consts.
const EXTRA_STMTS: u32 = 3;
const EXTRA_CONSTS: u32 = 2;

impl Builder {
    /// Runs `f` with the side tape as the tape. A form of enums draws from
    /// it, also when it calls the code of the other forms. A call inside
    /// `f` stays on the side tape.
    pub(super) fn on_side<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        if self.swapped {
            return f(self);
        }
        self.swapped = true;
        std::mem::swap(&mut self.tape, &mut self.side);
        let out = f(self);
        std::mem::swap(&mut self.tape, &mut self.side);
        self.swapped = false;
        out
    }

    /// A number below `n` from the side tape, also while `on_side` has
    /// swapped the tapes.
    pub(super) fn side_below(&mut self, n: u32) -> u32 {
        if self.swapped {
            self.tape.below(n)
        } else {
            self.side.below(n)
        }
    }

    /// Whether a draw of the side tape with the odds `1 / odds` takes an
    /// enum form, if the file has an enum.
    pub(super) fn aside(&mut self, odds: u32) -> bool {
        !self.enums.is_empty() && self.side_below(odds) == 0
    }

    /// The `enum` items `E<k>`. They come first, so everything can use them.
    pub(super) fn enums(&mut self) -> Built {
        self.on_side(|b| {
            for k in 0..b.tape.below(ENUMS + 1) {
                let def = b.enum_def(k);
                b.enums.push(def);
                b.refresh()?;
            }
            Ok(())
        })
    }

    fn enum_def(&mut self, k: u32) -> EnumDef {
        let tag_width = self.tape.between(1, 3);
        let space = 1u32 << tag_width;
        // One draw in four declares each tag, when the cap on the variants
        // allows it.
        let full = space <= VARIANTS && self.tape.below(4) == 0;
        let count = if full {
            space
        } else {
            self.tape.between(1, VARIANTS.min(space - 1))
        };
        let mut tags: Vec<u32> = (0..space).collect();
        for i in (1..tags.len()).rev() {
            let j = self.tape.index(i + 1);
            tags.swap(i, j);
        }
        let variants = tags
            .into_iter()
            .take(count as usize)
            .enumerate()
            .map(|(i, tag)| Variant {
                name: format!("V{i}"),
                tag: BigUint::from(tag),
                payload: (0..self.tape.below(PAYLOADS + 1))
                    .map(|_| self.payload_ty())
                    .collect(),
            })
            .collect();
        EnumDef {
            name: format!("E{k}"),
            tag_width,
            variants,
        }
    }

    fn payload_ty(&mut self) -> Scalar {
        let shape = self.tape.below(3);
        let w = if self.tape.below(16) == 15 {
            WIDE
        } else {
            self.pick(&WIDTHS)
        };
        match shape {
            0 => Scalar::Bool,
            1 => Scalar::UInt(w),
            _ => Scalar::SInt(w),
        }
    }

    /// The enum items, for the file scope.
    pub(super) fn enum_items(&self) -> impl Iterator<Item = Item> + '_ {
        self.enums.iter().cloned().map(Item::Enum)
    }

    /// A random enum of the file. The file has one.
    pub(super) fn pick_enum(&mut self) -> Option<EnumDef> {
        self.enums.get(self.tape.index(self.enums.len())).cloned()
    }

    /// A random enum of the file and a static value of it, from the side
    /// tape.
    pub(super) fn any_enum_value(&mut self, r: Reach<'_>) -> Option<(EnumDef, SExpr)> {
        self.on_side(|b| {
            let def = b.pick_enum()?;
            let value = b.enum_value(&def, stat::DEPTH, r);
            Some((def, value))
        })
    }

    /// A random enum of the file, from the side tape.
    pub(super) fn any_enum(&mut self) -> Option<EnumDef> {
        self.on_side(Builder::pick_enum)
    }

    /// The `const`s of an enum type, after the other consts.
    pub(super) fn enum_consts(&mut self) -> Built {
        self.on_side(|b| {
            if b.enums.is_empty() {
                return Ok(());
            }
            let envs = [Env::default()];
            for _ in 0..b.tape.below(EXTRA_CONSTS + 1) {
                let Some(def) = b.pick_enum() else { break };
                let names = b.const_names();
                let r = Reach {
                    names: &names,
                    fns: 0,
                    envs: Some(&envs),
                };
                let value = b.enum_value(&def, stat::DEPTH, r);
                note!(b, enum_consts);
                let k = b.consts.len();
                b.consts
                    .push((format!("C{k}"), STy::Enum(Box::new(def)), value));
                b.refresh()?;
            }
            Ok(())
        })
    }

    /// The number of enum statements that a frame adds to its own.
    pub(super) fn enum_stmts(&mut self) -> u32 {
        if self.enums.is_empty() {
            0
        } else {
            self.side_below(EXTRA_STMTS + 1)
        }
    }

    /// One enum statement of a frame: a static `let`, or a hardware form.
    /// A register joins `regs`.
    pub(super) fn enum_stmt(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        clocked: bool,
        out: &mut Vec<Stmt>,
        regs: &mut Vec<(String, EnumDef)>,
    ) -> Built {
        self.on_side(|b| {
            if b.tape.below(6) == 0 {
                b.enum_static_let(ctx, names, out)
            } else {
                b.enum_hw_stmt(ctx, names, clocked, out, regs);
                Ok(())
            }
        })
    }

    /// `let s: E = value;` of a static enum value.
    fn enum_static_let(&mut self, ctx: &mut Ctx, names: &mut Names, out: &mut Vec<Stmt>) -> Built {
        let Some(def) = self.pick_enum() else {
            return Ok(());
        };
        let value = self.enum_value(&def, stat::DEPTH, self.reach(ctx));
        let (value, vs) = if let Some(vs) = self.values(&value, &ctx.envs) {
            (value, vs)
        } else {
            let zero = SExpr::Zero(def.name.clone(), Vec::new());
            let vs = self
                .values(&zero, &ctx.envs)
                .ok_or(crate::eval::Fault::Type)?;
            (zero, vs)
        };
        let ty = STy::Enum(Box::new(def));
        let name = names.fresh("s");
        for (env, v) in ctx.envs.iter_mut().zip(vs) {
            env.statics.insert(name.clone(), v);
        }
        ctx.statics.push((name.clone(), ty.clone()));
        note!(self, enum_lets);
        out.push(Stmt::StaticLet(name, ty, value));
        Ok(())
    }

    /// A static value of the enum `def`: a constructor, the zero `E()`, or
    /// the bits of any tag through `reinterpret`. The caller is on the side
    /// tape.
    pub(super) fn enum_value(&mut self, def: &EnumDef, depth: u32, r: Reach<'_>) -> SExpr {
        match self.tape.below(8) {
            5 => {
                note!(self, enum_zeros);
                SExpr::Zero(def.name.clone(), Vec::new())
            }
            6 | 7 => {
                note!(self, enum_unpacks);
                let n = self.finite_value(&STy::UInt(def.data_bits()), 3);
                let bits = self.finite_literal(n);
                SExpr::Unpack(
                    def.name.clone(),
                    Box::new(SExpr::BitsConv(def.name.clone(), Box::new(bits))),
                )
            }
            _ => self.constructor(def, depth, r),
        }
    }

    /// `E::V` or `E::V(a, b)` of a random variant, with arguments that
    /// fit their payload types in each env.
    fn constructor(&mut self, def: &EnumDef, depth: u32, r: Reach<'_>) -> SExpr {
        let at = self.tape.index(def.variants.len());
        let Some(v) = def.variants.get(at) else {
            return SExpr::Zero(def.name.clone(), Vec::new());
        };
        note!(self, enum_ctors);
        let args = v
            .payload
            .iter()
            .map(|t| self.payload_arg(*t, depth, r))
            .collect();
        SExpr::Ctor(def.name.clone(), v.name.clone(), args)
    }

    /// An argument for a payload leaf of type `t`.
    fn payload_arg(&mut self, t: Scalar, _depth: u32, r: Reach<'_>) -> SExpr {
        match r.envs {
            Some(envs) => self.fit(&vec![t; envs.len()], r, envs),
            None => match t {
                Scalar::Bool => SExpr::Bool(false),
                _ => stat::int(0),
            },
        }
    }
}
