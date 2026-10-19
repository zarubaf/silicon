// SPDX-License-Identifier: Apache-2.0
//! Helpers that take resources (front-end spec 5.6, "Resource-typed formals
//! and results"), and the statements of a module frame that call them.
//!
//! A resource helper `H<k>` is never called in an expression, so it has its
//! own list. It binds the resource of its first formal, a `Reg`, a `Wire`,
//! or an `Input`, with `:=` and returns `()`. A helper with a `Mem` formal
//! makes the two port calls on the memory and returns the data of the
//! response. Its name starts with `H`, which the twin inlines.
//!
//! Every draw comes from the side tape (`on_side`), so a program without a
//! resource helper is the program of the main tape alone, and choice 0 is no
//! helper.
//!
//! Rules by construction:
//!
//! - A call stands only at a statement of a module frame (`S016`): the
//!   builder makes it in `frame`, never in an arm or a type.
//! - A `reg` and a `mem` stand only in a clocked module (`S017`).
//! - The ledger of a frame holds each resource that waits for its binding
//!   (`S018`). A declaration adds one, and a binding call or a `:=` removes
//!   it. The frame that declares a resource binds it, at its end, so a
//!   branch or a loop body never binds a resource of its parent. A wire
//!   binds at once and joins the readable names after its binding, so no
//!   combinational cycle occurs (`S020`). A child output joins them after
//!   all inputs of the child have a binding.
//! - A memory has one `write_port` and one `read_port`, together in one
//!   place, the module or one helper.
//! - A helper that binds a child input takes the type of an input of a
//!   later module, and a type that reads no parameter of that module
//!   (`S010`, `S005`).

use super::hw::Want;
use super::{Builder, Built, Ctx, Hw, Module, Names, Sig};
use crate::eval::{Env, Fault};
use crate::program::{FTy, HExpr, Place, Radix, SExpr, Scalar, Stmt, Ty};
use num_bigint::BigInt;

/// The most resource helpers, and the most handle statements of a frame.
const RES_HELPERS: u32 = 3;
const HANDLE_STMTS: u32 = 3;
/// The depth of the hardware expressions that the helpers and their calls
/// hold: small, so that the mean text of a program stays near its bound.
const HANDLE_DEPTH: u32 = 1;
/// The depths of a memory.
const DEPTHS: [u32; 2] = [2, 4];

/// What a helper does with its first formal.
#[derive(Clone)]
pub(super) enum Role {
    Reg,
    Wire,
    /// Binds the input `port` of a child of module `module`.
    Input {
        module: usize,
        port: String,
    },
    /// Writes the memory and reads it: the word and the depth.
    Mem {
        word: Ty,
        depth: u32,
    },
}

/// A helper that takes resources. Its formals are handles first, then data.
#[derive(Clone)]
pub(super) struct ResHelper {
    pub(super) name: String,
    pub(super) params: Vec<(String, FTy)>,
    pub(super) ret: FTy,
    pub(super) body: Vec<Stmt>,
    pub(super) result: HExpr,
    pub(super) role: Role,
}

/// A resource of a frame that waits for its binding.
#[derive(Clone, Debug)]
pub(super) struct Pending {
    pub(super) name: String,
    /// The helper that binds it.
    pub(super) helper: usize,
}

/// The number of address bits of a memory with `depth` words (spec 7.6).
fn address_bits(depth: u32) -> u32 {
    depth.next_power_of_two().trailing_zeros().max(1)
}

fn literal(n: u32) -> SExpr {
    SExpr::Int(BigInt::from(n), Radix::Dec)
}

impl Builder {
    /// The helpers `H<k>`, from the side tape.
    pub(super) fn res_helpers(&mut self) -> Built {
        self.on_side(|b| {
            for k in 0..b.tape.below(RES_HELPERS + 1) {
                let h = b.res_helper(k as usize)?;
                b.res_helpers.push(h);
                note!(b, res_helpers);
            }
            Ok(())
        })
    }

    /// A helper of a random role.
    fn res_helper(&mut self, k: usize) -> Built<ResHelper> {
        let name = format!("H{k}");
        match self.tape.below(4) {
            0 => Ok(self.bind_helper(name, false)),
            1 => Ok(self.bind_helper(name, true)),
            2 => self.input_helper(name),
            _ => Ok(self.mem_helper(name)),
        }
    }

    /// The scope of a helper body: its data formals as readable names.
    fn helper_ctx(&self, hw: Vec<Hw>) -> Ctx {
        Ctx {
            envs: vec![Env::default()],
            statics: self.const_names(),
            hw,
            helpers: self.helpers.len(),
            ..Ctx::default()
        }
    }

    /// The data formals `x<n>` of a helper: one or two of a random type,
    /// and the names that they make readable.
    fn data_formals(&mut self, names: &mut Names) -> (Vec<(String, FTy)>, Vec<Hw>) {
        let mut params = Vec::new();
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
        (params, hw)
    }

    /// `fn H<k>(a0: Reg[T], x1: U) -> () { a0 := e; return (); }`, or the
    /// same with `Wire[T]`. A register is readable in `e`, for a hold.
    fn bind_helper(&mut self, name: String, wire: bool) -> ResHelper {
        let (ty, scalar) = self.data_ty();
        let handle = if wire {
            FTy::Wire(ty.clone())
        } else {
            FTy::Reg(ty.clone())
        };
        let mut names = Names::default();
        let (data, mut hw) = self.data_formals(&mut names);
        if !wire {
            hw.push(Hw {
                expr: HExpr::Name("a0".to_owned()),
                ty: Some(ty.clone()),
                types: vec![scalar],
                mutable: false,
            });
        }
        let ctx = self.helper_ctx(hw);
        let want = Want {
            types: vec![scalar],
            ty: Some(ty),
        };
        let value = self.driver_at(&ctx, &want, HANDLE_DEPTH);
        ResHelper {
            name,
            params: [("a0".to_owned(), handle)]
                .into_iter()
                .chain(data)
                .collect(),
            ret: FTy::Unit,
            body: vec![Stmt::Connect(Place::Name("a0".to_owned()), value)],
            result: HExpr::Unit,
            role: if wire { Role::Wire } else { Role::Reg },
        }
    }

    /// `fn H<k>(a0: Input[T], x1: U) -> () { a0 := e; return (); }` for the
    /// type `T` of an input of a later module. Without a later module that
    /// has such an input, a wire helper.
    fn input_helper(&mut self, name: String) -> Built<ResHelper> {
        let inputs: Vec<(usize, String, Ty)> = self
            .sigs
            .iter()
            .enumerate()
            .skip(1)
            .flat_map(|(j, sig)| {
                sig.inputs
                    .iter()
                    .filter(|(_, t)| closed(sig, t))
                    .map(move |(p, t)| (j, p.clone(), t.clone()))
            })
            .collect();
        let Some((module, port, ty)) = inputs.get(self.tape.index(inputs.len())).cloned() else {
            return Ok(self.bind_helper(name, true));
        };
        let scalar = self.scalar(&ty)?;
        let mut names = Names::default();
        let (data, hw) = self.data_formals(&mut names);
        let ctx = self.helper_ctx(hw);
        let want = Want {
            types: vec![scalar],
            ty: Some(ty.clone()),
        };
        let value = self.driver_at(&ctx, &want, HANDLE_DEPTH);
        Ok(ResHelper {
            name,
            params: [("a0".to_owned(), FTy::Input(ty))]
                .into_iter()
                .chain(data)
                .collect(),
            ret: FTy::Unit,
            body: vec![Stmt::Connect(Place::Name("a0".to_owned()), value)],
            result: HExpr::Unit,
            role: Role::Input { module, port },
        })
    }

    /// `fn H<k>(a0: Mem[T, N], x1: UInt[A], x2: T, x3: Bool, x4: Bool) -> T`
    /// with `write_port(a0, x1, x2, x3)`, `let l0 = a0.read_port(x1, x4)`,
    /// and `return l0.data`.
    fn mem_helper(&mut self, name: String) -> ResHelper {
        let (word, _) = self.data_ty();
        let depth = self.pick(&DEPTHS);
        let addr = Ty::UInt(literal(address_bits(depth)));
        let formal = |n: &str, t: &Ty| (n.to_owned(), FTy::Data(t.clone()));
        let params = vec![
            ("a0".to_owned(), FTy::Mem(word.clone(), literal(depth))),
            formal("x1", &addr),
            formal("x2", &word),
            formal("x3", &Ty::Bool),
            formal("x4", &Ty::Bool),
        ];
        let hname = |n: &str| HExpr::Name(n.to_owned());
        let write = Stmt::WritePort {
            mem: "a0".to_owned(),
            addr: Box::new(hname("x1")),
            data: Box::new(hname("x2")),
            en: Box::new(hname("x3")),
            receiver: self.tape.flag(),
        };
        let read = Stmt::Let {
            name: "l0".to_owned(),
            mutable: false,
            ty: None,
            value: HExpr::ReadPort {
                mem: "a0".to_owned(),
                addr: Box::new(hname("x1")),
                en: Box::new(hname("x4")),
                receiver: self.tape.flag(),
            },
        };
        ResHelper {
            name,
            params,
            ret: FTy::Data(word.clone()),
            body: vec![write, read],
            result: HExpr::Field("l0".to_owned(), "data".to_owned()),
            role: Role::Mem { word, depth },
        }
    }

    /// The concrete type of a type that reads only consts.
    fn scalar(&self, t: &Ty) -> Built<Scalar> {
        match self.types(t, &[Env::default()])?[..] {
            [s] => Ok(s),
            _ => Err(Fault::Type),
        }
    }

    /// The number of handle statements that a frame adds to its own.
    pub(super) fn handle_stmts(&mut self) -> u32 {
        self.side_below(HANDLE_STMTS + 1)
    }

    /// One handle statement of a frame: a call of a helper that takes a
    /// fresh resource, or a memory with its two port calls.
    pub(super) fn handle_stmt(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built {
        self.on_side(|b| {
            if m.clocked && (b.res_helpers.is_empty() || b.tape.below(3) == 0) {
                return b.direct_mem(ctx, m, out);
            }
            b.bind_call(ctx, m, out)
        })
    }

    /// The helpers that a module can call: a register and a memory need a
    /// clocked module, and a child needs a module after it.
    fn usable(&self, m: &Module) -> Vec<usize> {
        self.res_helpers
            .iter()
            .enumerate()
            .filter(|(_, h)| match &h.role {
                Role::Reg | Role::Mem { .. } => m.clocked,
                Role::Wire => true,
                Role::Input { module, .. } => self.reachable(m, *module),
            })
            .map(|(i, _)| i)
            .collect()
    }

    /// A fresh resource of the type of the first formal of a helper, and
    /// the call that binds it. A wire binds at once and then reads. A
    /// register binds at the end of the frame.
    fn bind_call(&mut self, ctx: &mut Ctx, m: &mut Module, out: &mut Vec<Stmt>) -> Built {
        let usable = self.usable(m);
        let Some(&i) = usable.get(self.tape.index(usable.len())) else {
            return Ok(());
        };
        let h = self.res_helpers.get(i).cloned().ok_or(Fault::Type)?;
        match h.role {
            Role::Wire | Role::Reg => {
                let (Some((_, FTy::Wire(ty) | FTy::Reg(ty))), wire) =
                    (h.params.first(), matches!(h.role, Role::Wire))
                else {
                    return Err(Fault::Type);
                };
                let types = self.types(ty, &ctx.envs)?;
                let name = m.names.fresh(if wire { "w" } else { "r" });
                if wire {
                    out.push(Stmt::Wire(name.clone(), ty.clone()));
                    let call = self.binder_call(ctx, i, HExpr::Name(name.clone()))?;
                    out.push(call);
                    note!(self, bind_wire_calls);
                } else {
                    let reset = self.fit(&types, self.reach(ctx), &ctx.envs);
                    out.push(Stmt::Reg(name.clone(), ty.clone(), reset));
                    ctx.pending.push(Pending {
                        name: name.clone(),
                        helper: i,
                    });
                }
                ctx.hw.push(Hw {
                    expr: HExpr::Name(name),
                    ty: Some(ty.clone()),
                    types,
                    mutable: false,
                });
            }
            Role::Input { module, port } => {
                let child = self.declare_child(ctx, m, module, out)?;
                self.bind_child_inputs(ctx, &child, Some(&port), out)?;
                let first = HExpr::Field(child.name.clone(), port);
                let call = self.binder_call(ctx, i, first)?;
                out.push(call);
                note!(self, bind_input_calls);
                self.expose_child_outputs(ctx, &child)?;
            }
            Role::Mem { word, depth } => {
                let name = m.names.fresh("n");
                out.push(Stmt::Mem(name.clone(), word.clone(), literal(depth)));
                let (callee, args) = self.binder_args(ctx, i, HExpr::Name(name))?;
                let read = m.names.fresh("l");
                out.push(Stmt::Let {
                    name: read.clone(),
                    mutable: false,
                    ty: None,
                    value: HExpr::Call(callee, args),
                });
                note!(self, bind_mem_calls);
                self.push_read(ctx, HExpr::Name(read), &word)?;
            }
        }
        Ok(())
    }

    /// `mem n: [T; N];`, `write_port`, and `let l = read_port`, in the
    /// module. The data of the response is readable.
    fn direct_mem(&mut self, ctx: &mut Ctx, m: &mut Module, out: &mut Vec<Stmt>) -> Built {
        let (word, scalar) = self.data_ty();
        let depth = self.pick(&DEPTHS);
        let addr = Scalar::UInt(address_bits(depth));
        let name = m.names.fresh("n");
        out.push(Stmt::Mem(name.clone(), word.clone(), literal(depth)));
        let write = Stmt::WritePort {
            mem: name.clone(),
            addr: Box::new(self.actual(ctx, addr)),
            data: Box::new(self.actual(ctx, scalar)),
            en: Box::new(self.actual(ctx, Scalar::Bool)),
            receiver: self.tape.flag(),
        };
        out.push(write);
        let read = m.names.fresh("l");
        let value = HExpr::ReadPort {
            mem: name,
            addr: Box::new(self.actual(ctx, addr)),
            en: Box::new(self.actual(ctx, Scalar::Bool)),
            receiver: self.tape.flag(),
        };
        out.push(Stmt::Let {
            name: read.clone(),
            mutable: false,
            ty: None,
            value,
        });
        note!(self, direct_mems);
        self.push_read(ctx, HExpr::Field(read, "data".to_owned()), &word)
    }

    /// Makes the data `expr` of type `ty` a readable name.
    fn push_read(&mut self, ctx: &mut Ctx, expr: HExpr, ty: &Ty) -> Built {
        let types = self.types(ty, &ctx.envs)?;
        ctx.hw.push(Hw {
            expr,
            ty: Some(ty.clone()),
            types,
            mutable: false,
        });
        Ok(())
    }

    /// A short value of type `scalar`: a readable name of that type, or a
    /// static value that converts. A deeper expression only makes the
    /// text of the program longer.
    fn actual(&mut self, ctx: &Ctx, scalar: Scalar) -> HExpr {
        let types = vec![scalar; ctx.envs.len()];
        let names: Vec<&Hw> = ctx.hw.iter().filter(|h| h.types == types).collect();
        match names.get(self.tape.index(names.len())) {
            Some(h) if self.tape.below(4) != 0 => h.expr.clone(),
            _ => HExpr::Static(self.fit(&types, self.reach(ctx), &ctx.envs)),
        }
    }

    /// The name of helper `i` and its actuals: `first` for the first
    /// formal, and a value for each data formal.
    fn binder_args(&mut self, ctx: &Ctx, i: usize, first: HExpr) -> Built<(String, Vec<HExpr>)> {
        let h = self.res_helpers.get(i).cloned().ok_or(Fault::Type)?;
        let mut args = vec![first];
        for (_, t) in h.params.iter().skip(1) {
            let FTy::Data(t) = t else {
                return Err(Fault::Type);
            };
            let scalar = self.scalar(t)?;
            args.push(self.value(ctx, &Want::uniform(scalar, ctx.envs.len()), HANDLE_DEPTH));
        }
        Ok((h.name, args))
    }

    /// `H<i>(first, e, ...);`
    fn binder_call(&mut self, ctx: &Ctx, i: usize, first: HExpr) -> Built<Stmt> {
        let (name, args) = self.binder_args(ctx, i, first)?;
        Ok(Stmt::Call(name, args))
    }

    /// The binding calls of the registers that this frame declared.
    pub(super) fn close_pending(&mut self, ctx: &mut Ctx, out: &mut Vec<Stmt>) -> Built {
        let pending = std::mem::take(&mut ctx.pending);
        self.on_side(|b| {
            for p in pending {
                let call = b.binder_call(ctx, p.helper, HExpr::Name(p.name))?;
                out.push(call);
                note!(b, bind_reg_calls);
            }
            Ok(())
        })
    }
}

/// Whether the type `t` of a port of `sig` reads no parameter of it, so
/// that a caller can write the type.
fn closed(sig: &Sig, t: &Ty) -> bool {
    let (Ty::UInt(w) | Ty::SInt(w)) = t else {
        return matches!(t, Ty::Bool);
    };
    let text = crate::program::sexpr(w);
    !text
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|token| sig.params.iter().any(|(p, _)| p == token))
}

#[cfg(test)]
mod tests {
    use super::super::tests::tapes;
    use super::super::*;

    /// Each kind of binder call occurs in at least 10% of 256 programs.
    #[test]
    fn programs_call_each_kind_of_binder() {
        const TAPES: usize = 256;
        let mut with = [0usize; 5];
        for tape in tapes(TAPES) {
            let mut b = Builder::new(tape);
            let p = b.program();
            assert!(p.is_ok(), "a program faults: {p:?}");
            let s = &b.stats;
            for (n, seen) in with.iter_mut().zip([
                s.bind_reg_calls,
                s.bind_wire_calls,
                s.bind_input_calls,
                s.bind_mem_calls,
                s.direct_mems,
            ]) {
                *n += usize::from(seen > 0);
            }
        }
        for n in with {
            assert!(n * 10 >= TAPES, "{with:?} of {TAPES}");
        }
    }

    /// A call of a helper that takes resources is a statement of a module
    /// frame (`S016`) or the root of a `let`, never in a helper.
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
                    Item::Module { body, .. } | Item::Helper { body, .. } => {
                        calls(body, &mut found);
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
