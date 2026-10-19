// SPDX-License-Identifier: Apache-2.0
//! Helpers that take resources (front-end spec 5.6, "Resource-typed formals
//! and results"), and the statements of a module frame that call them.
//!
//! A resource helper `H<k>` is never called in an expression, so it has its
//! own list. It binds the resource of its `Reg` or `Wire` formal with `:=`
//! and returns `()`. Its name starts with `H`, which the twin inlines.
//!
//! Every draw comes from the side tape (`on_side`), so a program without a
//! resource helper is the program of the main tape alone, and choice 0 is no
//! helper.
//!
//! Rules by construction:
//!
//! - A call stands only at a statement of a module frame (`S016`): the
//!   builder makes it in `frame`, never in an arm or a type.
//! - A `reg` stands only in a clocked module (`S017`).
//! - The ledger of a frame holds each resource that waits for its binding
//!   (`S018`). A declaration adds one, and a binding call or a `:=` removes
//!   it. The frame that declares a resource binds it, at its end, so a
//!   branch or a loop body never binds a resource of its parent. A wire
//!   binds at once and joins the readable names after its binding, so no
//!   combinational cycle occurs (`S020`).

use super::hw::Want;
use super::{Builder, Built, Ctx, Hw, Module, Names};
use crate::eval::Env;
use crate::program::{FTy, HExpr, Place, Stmt};

/// The most resource helpers, and the most handle statements of a frame.
const RES_HELPERS: u32 = 3;
const HANDLE_STMTS: u32 = 3;
/// The depth of the hardware expressions that the helpers and their calls
/// hold: small, so that the mean text of a program stays near its bound.
const HANDLE_DEPTH: u32 = 2;

/// A helper that takes resources. Its formals are handles first, then data.
#[derive(Clone)]
pub(super) struct ResHelper {
    pub(super) name: String,
    pub(super) params: Vec<(String, FTy)>,
    pub(super) body: Vec<Stmt>,
}

/// A resource of a frame that waits for its binding.
#[derive(Clone, Debug)]
pub(super) struct Pending {
    pub(super) name: String,
    /// The helper that binds it.
    pub(super) helper: usize,
}

impl Builder {
    /// The helpers `H<k>`, from the side tape.
    pub(super) fn res_helpers(&mut self) -> Built {
        self.on_side(|b| {
            for k in 0..b.tape.below(RES_HELPERS + 1) {
                let h = b.bind_helper(k as usize);
                b.res_helpers.push(h);
                note!(b, res_helpers);
            }
            Ok(())
        })
    }

    /// `fn H<k>(a0: Reg[T], x1: U) -> () { a0 := e; return (); }`, or the
    /// same with `Wire[T]`. A register is readable in `e`, for a hold.
    fn bind_helper(&mut self, k: usize) -> ResHelper {
        let wire = self.tape.flag();
        let (ty, scalar) = self.data_ty();
        let handle = if wire {
            FTy::Wire(ty.clone())
        } else {
            FTy::Reg(ty.clone())
        };
        let mut names = Names::default();
        let mut params = vec![("a0".to_owned(), handle)];
        let mut hw = Vec::new();
        for _ in 0..self.tape.between(1, 2) {
            let (t, s) = self.data_ty();
            let name = names.fresh("x");
            params.push((name.clone(), FTy::Data(t.clone())));
            hw.push(Hw {
                expr: HExpr::Name(name),
                ty: Some(t),
                types: vec![s],
                mutable: false,
            });
        }
        if !wire {
            hw.push(Hw {
                expr: HExpr::Name("a0".to_owned()),
                ty: Some(ty.clone()),
                types: vec![scalar],
                mutable: false,
            });
        }
        let ctx = Ctx {
            envs: vec![Env::default()],
            statics: self.const_names(),
            hw,
            helpers: self.helpers.len(),
            ..Ctx::default()
        };
        let want = Want {
            types: vec![scalar],
            ty: Some(ty),
        };
        let value = self.driver_at(&ctx, &want, HANDLE_DEPTH);
        ResHelper {
            name: format!("H{k}"),
            params,
            body: vec![Stmt::Connect(Place::Name("a0".to_owned()), value)],
        }
    }

    /// The number of handle statements that a frame adds to its own.
    pub(super) fn handle_stmts(&mut self) -> u32 {
        if self.res_helpers.is_empty() {
            0
        } else {
            self.side_below(HANDLE_STMTS + 1)
        }
    }

    /// One handle statement of a frame: a call of a helper that binds a
    /// fresh wire or register.
    pub(super) fn handle_stmt(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built {
        self.on_side(|b| b.bind_call(ctx, m, out))
    }

    /// A fresh resource of the type of the first formal of a helper, and
    /// the call that binds it. A wire binds at once and then reads. A
    /// register binds at the end of the frame.
    fn bind_call(&mut self, ctx: &mut Ctx, m: &mut Module, out: &mut Vec<Stmt>) -> Built {
        let usable: Vec<usize> = self
            .res_helpers
            .iter()
            .enumerate()
            .filter(|(_, h)| m.clocked || !matches!(h.params.first(), Some((_, FTy::Reg(_)))))
            .map(|(i, _)| i)
            .collect();
        let Some(&i) = usable.get(self.tape.index(usable.len())) else {
            return Ok(());
        };
        let Some((_, handle)) = self.res_helpers.get(i).and_then(|h| h.params.first()) else {
            return Ok(());
        };
        let (ty, wire) = match handle {
            FTy::Wire(t) => (t.clone(), true),
            FTy::Reg(t) => (t.clone(), false),
            _ => return Ok(()),
        };
        let types = self.types(&ty, &ctx.envs)?;
        let readable = Hw {
            expr: HExpr::Name(String::new()),
            ty: Some(ty.clone()),
            types: types.clone(),
            mutable: false,
        };
        if wire {
            let name = m.names.fresh("w");
            out.push(Stmt::Wire(name.clone(), ty));
            let call = self.binder_call(ctx, i, &name)?;
            out.push(call);
            note!(self, bind_wire_calls);
            ctx.hw.push(Hw {
                expr: HExpr::Name(name),
                ..readable
            });
        } else {
            let name = m.names.fresh("r");
            let reset = self.fit(&types, self.reach(ctx), &ctx.envs);
            out.push(Stmt::Reg(name.clone(), ty, reset));
            ctx.hw.push(Hw {
                expr: HExpr::Name(name.clone()),
                ..readable
            });
            ctx.pending.push(Pending { name, helper: i });
        }
        Ok(())
    }

    /// `H<i>(name, e, ...)` with a value for each data formal.
    fn binder_call(&mut self, ctx: &Ctx, i: usize, name: &str) -> Built<Stmt> {
        let h = self
            .res_helpers
            .get(i)
            .cloned()
            .ok_or(crate::eval::Fault::Type)?;
        let mut args = vec![HExpr::Name(name.to_owned())];
        for (_, t) in h.params.iter().skip(1) {
            let FTy::Data(t) = t else {
                return Err(crate::eval::Fault::Type);
            };
            let scalar = self.types(t, &[Env::default()])?;
            let [scalar] = scalar[..] else {
                return Err(crate::eval::Fault::Type);
            };
            args.push(self.value(ctx, &Want::uniform(scalar, ctx.envs.len()), HANDLE_DEPTH));
        }
        Ok(Stmt::Call(h.name, args))
    }

    /// The binding calls of the registers that this frame declared.
    pub(super) fn close_pending(&mut self, ctx: &mut Ctx, out: &mut Vec<Stmt>) -> Built {
        let pending = std::mem::take(&mut ctx.pending);
        self.on_side(|b| {
            for p in pending {
                let call = b.binder_call(ctx, p.helper, &p.name)?;
                out.push(call);
                note!(b, bind_reg_calls);
            }
            Ok(())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::tapes;
    use super::super::*;

    /// A helper that binds a register and a helper that binds a wire each
    /// occur in at least 10% of 256 programs.
    #[test]
    fn programs_bind_registers_and_wires_through_helpers() {
        const TAPES: usize = 256;
        let (mut regs, mut wires) = (0, 0);
        for tape in tapes(TAPES) {
            let mut b = Builder::new(tape);
            let p = b.program();
            assert!(p.is_ok(), "a program faults: {p:?}");
            regs += usize::from(b.stats.bind_reg_calls > 0);
            wires += usize::from(b.stats.bind_wire_calls > 0);
        }
        assert!(regs * 10 >= TAPES, "registers: {regs} of {TAPES}");
        assert!(wires * 10 >= TAPES, "wires: {wires} of {TAPES}");
    }

    /// A call of a helper that takes resources is a statement of a module
    /// frame (`S016`), never in a helper, and the helper binds each handle
    /// formal.
    #[test]
    fn a_resource_call_stands_in_a_module_frame_only() {
        fn calls(body: &[Stmt], out: &mut Vec<String>) {
            for s in body {
                match s {
                    Stmt::Call(f, _) => out.push(f.clone()),
                    Stmt::If(_, t, e) => {
                        calls(t, out);
                        calls(e.as_deref().unwrap_or_default(), out);
                    }
                    Stmt::For(_, _, _, b) | Stmt::Block(b) => calls(b, out),
                    _ => {}
                }
            }
        }
        for tape in tapes(256) {
            let Ok(p) = build(tape) else { continue };
            for item in &p.items {
                let mut found = Vec::new();
                match item {
                    Item::Module { body, .. } => calls(body, &mut found),
                    Item::Helper {
                        name, body, params, ..
                    } if name.starts_with('H') => {
                        calls(body, &mut found);
                        assert!(
                            params
                                .iter()
                                .any(|(_, t)| *t != FTy::Data(Ty::Bool)
                                    && !matches!(t, FTy::Data(_))),
                            "{name} takes no handle"
                        );
                    }
                    _ => {}
                }
                assert!(found.iter().all(|f| f.starts_with('H')), "{found:?}");
                if matches!(item, Item::Helper { .. }) {
                    assert!(found.is_empty(), "a helper calls a helper: {found:?}");
                }
            }
        }
    }
}
