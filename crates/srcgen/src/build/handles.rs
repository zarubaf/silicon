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
//! Every draw comes from the hand tape (`on_hand`), so a program without a
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

use super::hw::{Want, adapt};
use super::inst::Child;
use super::{Builder, Built, Ctx, Hw, Module, Names, Sig};
use crate::eval::{Env, Fault, Value};
use crate::program::{FTy, HBin, HExpr, Place, Radix, SExpr, Scalar, Stmt, Ty};
use num_bigint::BigInt;

/// The most resource helpers, and the most handle statements of a frame.
const RES_HELPERS: u32 = 6;
const HANDLE_STMTS: u32 = 1;
/// The depth of the hardware expressions that the helpers and their calls
/// hold: small, so that the mean text of a program stays near its bound.
pub(super) const HANDLE_DEPTH: u32 = 1;
/// The most resources that handle forms declare in a program, counted once
/// for each env that runs the declaration, and the most that one statement
/// of a frame declares. A statement waits when the rest of the budget does
/// not cover it.
const MAX_DECLS: usize = 24;
const UNIT_DECLS: usize = 6;

/// The roles of the draw of a helper, the first role that declares, and the
/// first role of a list.
const ROLES: u32 = 24;
const DECLARE: u32 = 9;
const LISTS: u32 = 19;
/// The depths of a memory.
pub(super) const DEPTHS: [u32; 2] = [2, 4];

/// What a helper does.
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
    /// Declares resources, and returns some of them.
    Declare,
    /// Binds each element of a list of handles in a loop.
    List(ListOf),
}

/// The elements of the list that a list helper binds.
#[derive(Clone)]
pub(super) enum ListOf {
    Reg(Ty),
    Wire(Ty),
    /// The input `port` of a child of module `module`, of the type `ty`.
    Input {
        module: usize,
        port: String,
        ty: Ty,
    },
}

/// A step from a container of handles to an element.
#[derive(Clone, Debug)]
pub(super) enum Step {
    Index(u32),
    Select(u32),
    Field(String),
}

/// A resource that a helper declares.
#[derive(Clone)]
pub(super) enum Leaf {
    Reg(Ty),
    Wire(Ty),
    Mem { word: Ty, depth: u32 },
    Instance { module: usize, tuple: Vec<Value> },
}

/// A resource in the result of a helper: where it stands in the result, and
/// whether the helper binds it. The caller binds each other one.
#[derive(Clone)]
pub(super) struct Part {
    pub(super) path: Vec<Step>,
    pub(super) leaf: Leaf,
    pub(super) bound: bool,
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
    /// The resources in the result, in the order of the type.
    pub(super) parts: Vec<Part>,
    /// Whether the helper declares a register, a memory, or a clocked
    /// child, so that only a clocked module calls it.
    pub(super) clocked: bool,
    /// The children that the helper instantiates, with their argument
    /// tuples. A module before them calls the helper.
    pub(super) children: Vec<(usize, Vec<Value>)>,
}

impl ResHelper {
    /// A helper that binds the resources of its formals.
    pub(super) fn binder(
        name: String,
        params: Vec<(String, FTy)>,
        ret: FTy,
        body: Vec<Stmt>,
        result: HExpr,
        role: Role,
    ) -> ResHelper {
        ResHelper {
            name,
            params,
            ret,
            body,
            result,
            role,
            parts: Vec::new(),
            clocked: false,
            children: Vec::new(),
        }
    }
}

/// A resource of a frame that waits for its binding.
#[derive(Clone, Debug)]
pub(super) struct Pending {
    /// The handle: a name, or a selection from a container.
    pub(super) first: HExpr,
    /// The helper that binds it, or `:=` in the frame.
    pub(super) via: Option<usize>,
    /// Its data type.
    pub(super) ty: Ty,
}

/// The `:=` target of a handle.
pub(super) fn place_of(e: &HExpr) -> Place {
    match e {
        HExpr::Name(n) => Place::Name(n.clone()),
        HExpr::Field(a, b) => Place::Field(a.clone(), b.clone()),
        _ => Place::Path(e.clone()),
    }
}

/// The handle at the end of `steps` from the name `root`.
pub(super) fn at(root: &str, steps: &[Step]) -> HExpr {
    steps
        .iter()
        .fold(HExpr::Name(root.to_owned()), |base, step| {
            match (step, base) {
                (Step::Field(f), HExpr::Name(n)) => HExpr::Field(n, f.clone()),
                (Step::Field(_), base) => base,
                (Step::Index(i), base) => HExpr::Index(Box::new(base), literal(*i)),
                (Step::Select(k), base) => HExpr::Select(Box::new(base), *k),
            }
        })
}

/// A kind of handle statement of a frame.
enum Class {
    /// A memory of the module with its two port calls.
    Direct,
    /// A call of one of the helpers of one role that bind a fresh resource.
    Binder(Vec<usize>),
    /// A call of one of the helpers that declare resources.
    Declare(Vec<usize>),
    /// A group: a list, a loop that fills it, and the call that binds it.
    List,
}

/// The number of address bits of a memory with `depth` words (spec 7.6).
fn address_bits(depth: u32) -> u32 {
    depth.next_power_of_two().trailing_zeros().max(1)
}

pub(super) fn literal(n: u32) -> SExpr {
    SExpr::Int(BigInt::from(n), Radix::Dec)
}

impl Builder {
    /// Runs `f` with the hand tape as the tape, as `on_side` does with the
    /// side tape. A call inside `f` stays on the hand tape.
    pub(super) fn on_hand<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        if self.swapped {
            return f(self);
        }
        self.swapped = true;
        std::mem::swap(&mut self.tape, &mut self.hand);
        let out = f(self);
        std::mem::swap(&mut self.tape, &mut self.hand);
        self.swapped = false;
        out
    }

    /// A number below `n` from the hand tape, also while `on_hand` has
    /// swapped the tapes.
    pub(super) fn hand_below(&mut self, n: u32) -> u32 {
        if self.swapped {
            self.tape.below(n)
        } else {
            self.hand.below(n)
        }
    }

    /// The helpers `H<k>`, from the hand tape. The draws pick the roles
    /// first, and the helpers that declare come last, so that they can call
    /// the others.
    pub(super) fn res_helpers(&mut self) -> Built {
        self.on_hand(|b| {
            let mut roles: Vec<u32> = (0..b.tape.below(RES_HELPERS + 1))
                .map(|_| b.tape.below(ROLES))
                .collect();
            roles.sort_by_key(|&n| match n {
                ..DECLARE => 0,
                LISTS.. => 1,
                _ => 2,
            });
            for role in roles {
                let h = b.res_helper(format!("H{}", b.res_helpers.len()), role)?;
                let of = match &h.role {
                    Role::List(ListOf::Reg(t)) => Some((true, t.clone())),
                    Role::List(ListOf::Wire(t)) => Some((false, t.clone())),
                    _ => None,
                };
                b.res_helpers.push(h);
                note!(b, res_helpers);
                // A group can push the result of a helper that declares one
                // element, so a list helper often comes with such a helper.
                if let Some((reg, ty)) = of
                    && b.tape.flag()
                {
                    let name = format!("H{}", b.res_helpers.len());
                    let factory = b.factory_helper(name, reg, &ty)?;
                    b.res_helpers.push(factory);
                }
            }
            Ok(())
        })
    }

    /// A helper of the role `role`: of the draws `0..ROLES`, a register, a
    /// wire, three inputs, two memories, and the declaring helpers (`DECLARE`
    /// and above), and the lists last.
    fn res_helper(&mut self, name: String, role: u32) -> Built<ResHelper> {
        match role {
            0 | 1 => Ok(self.bind_helper(name, false)),
            2 | 3 => Ok(self.bind_helper(name, true)),
            4 | 5 => self.input_helper(name),
            6..=8 => Ok(self.mem_helper(name)),
            n if n < LISTS => self.declare_helper(name),
            n => Ok(self.list_helper(name, n - LISTS)),
        }
    }

    /// The scope of a helper body: its data formals as readable names.
    pub(super) fn helper_ctx(&self, hw: Vec<Hw>) -> Ctx {
        Ctx {
            envs: vec![Env::default()],
            statics: self.const_names(),
            hw,
            helpers: self.helpers.len(),
            local: true,
            ..Ctx::default()
        }
    }

    /// The data formals `x<n>` of a helper: one or two, and the names that
    /// they make readable. The first one has the type `first` if there is
    /// one, so that the value of a binding is short.
    pub(super) fn data_formals(
        &mut self,
        names: &mut Names,
        first: Option<(Ty, Scalar)>,
    ) -> (Vec<(String, FTy)>, Vec<Hw>) {
        let mut params = Vec::new();
        let mut hw = Vec::new();
        let mut first = first;
        for _ in 0..self.tape.between(1, 2) {
            let (t, s) = first.take().unwrap_or_else(|| self.data_ty());
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
        let (data, mut hw) = self.data_formals(&mut names, Some((ty.clone(), scalar)));
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
        ResHelper::binder(
            name,
            [("a0".to_owned(), handle)]
                .into_iter()
                .chain(data)
                .collect(),
            FTy::Unit,
            vec![Stmt::Connect(Place::Name("a0".to_owned()), value)],
            HExpr::Unit,
            if wire { Role::Wire } else { Role::Reg },
        )
    }

    /// `fn H<k>(a0: Input[T], x1: U) -> () { a0 := e; return (); }` for the
    /// type `T` of an input of a later module. Without a later module that
    /// has such an input, a wire helper.
    fn input_helper(&mut self, name: String) -> Built<ResHelper> {
        let Some((module, port, ty)) = self.input_candidate() else {
            return Ok(self.bind_helper(name, true));
        };
        let scalar = self.scalar(&ty)?;
        let mut names = Names::default();
        let (data, hw) = self.data_formals(&mut names, Some((ty.clone(), scalar)));
        let ctx = self.helper_ctx(hw);
        let want = Want {
            types: vec![scalar],
            ty: Some(ty.clone()),
        };
        let value = self.driver_at(&ctx, &want, HANDLE_DEPTH);
        Ok(ResHelper::binder(
            name,
            [("a0".to_owned(), FTy::Input(ty))]
                .into_iter()
                .chain(data)
                .collect(),
            FTy::Unit,
            vec![Stmt::Connect(Place::Name("a0".to_owned()), value)],
            HExpr::Unit,
            Role::Input { module, port },
        ))
    }

    /// An input of a later module whose type reads no parameter of that
    /// module: the module, the port, and the type.
    pub(super) fn input_candidate(&mut self) -> Option<(usize, String, Ty)> {
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
        inputs.get(self.tape.index(inputs.len())).cloned()
    }

    /// `fn H<k>(a0: Mem[T, N], x1: UInt[A], x2: T, x3: Bool, x4: Bool) -> T`
    /// with `write_port(a0, x1, x2, x3)`, `let l0 = a0.read_port(x1, x4)`,
    /// and `return l0.data`.
    fn mem_helper(&mut self, name: String) -> ResHelper {
        let (word, _) = self.word_ty();
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
        ResHelper::binder(
            name,
            params,
            FTy::Data(word.clone()),
            vec![write, read],
            HExpr::Field("l0".to_owned(), "data".to_owned()),
            Role::Mem { word, depth },
        )
    }

    /// The type of a memory word: a data type of at most 16 bits.
    pub(super) fn word_ty(&mut self) -> (Ty, Scalar) {
        let (t, s) = self.data_ty();
        if s.bits() > 16 {
            (Ty::UInt(literal(8)), Scalar::UInt(8))
        } else {
            (t, s)
        }
    }

    /// The concrete type of a type that reads only consts.
    pub(super) fn scalar(&self, t: &Ty) -> Built<Scalar> {
        match self.types(t, &[Env::default()])?[..] {
            [s] => Ok(s),
            _ => Err(Fault::Type),
        }
    }

    /// The number of handle statements that a frame adds to its own.
    pub(super) fn handle_stmts(&mut self) -> u32 {
        self.hand_below(HANDLE_STMTS + 1)
    }

    /// One handle statement of a frame. The draw picks a kind of statement
    /// first, so that a kind with few helpers still occurs: the memory of
    /// the module, a call of a helper of each role that binds a fresh
    /// resource, a call of a helper that declares resources, or a group.
    pub(super) fn handle_stmt(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built {
        self.on_hand(|b| {
            if !b.within_budget(ctx) {
                return Ok(());
            }
            let mut classes: Vec<Class> = Vec::new();
            if m.clocked {
                classes.push(Class::Direct);
            }
            let usable = b.usable(m);
            for same in [
                |r: &Role| matches!(r, Role::Reg),
                |r: &Role| matches!(r, Role::Wire),
                |r: &Role| matches!(r, Role::Input { .. }),
                |r: &Role| matches!(r, Role::Mem { .. }),
            ] {
                let found: Vec<usize> = usable
                    .iter()
                    .copied()
                    .filter(|&i| b.res_helpers.get(i).is_some_and(|h| same(&h.role)))
                    .collect();
                if !found.is_empty() {
                    classes.push(Class::Binder(found));
                }
            }
            let declarers = b.usable_declarers(m);
            if !declarers.is_empty() {
                classes.push(Class::Declare(declarers));
            }
            if b.has_list_helper() {
                classes.push(Class::List);
            }
            let Some(class) = classes.get(b.tape.index(classes.len())) else {
                return Ok(());
            };
            match class {
                Class::Direct => b.direct_mem(ctx, m, out),
                Class::Binder(found) => {
                    let i = found.get(b.tape.index(found.len())).copied();
                    i.map_or(Ok(()), |i| b.bind_call(ctx, m, i, out))
                }
                Class::Declare(declarers) => b.declare_call(ctx, m, declarers, out),
                Class::List => b.list_group(ctx, m, out),
            }
        })
    }

    /// A call of each helper that no call names yet and that the module can
    /// call, at the end of its top frame. A helper that no module calls only
    /// makes the program longer, and the calls give the outputs of the
    /// module resources to read.
    pub(super) fn call_unused(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built {
        self.on_hand(|b| {
            for i in 0..b.res_helpers.len() {
                if b.called.contains(&i) || !b.within_budget(ctx) {
                    continue;
                }
                let Some(role) = b.res_helpers.get(i).map(|h| h.role.clone()) else {
                    continue;
                };
                match role {
                    Role::Declare => {
                        if b.usable_declarers(m).contains(&i) {
                            b.declare_call(ctx, m, &[i], out)?;
                        }
                    }
                    Role::List(_) => b.list_group_of(ctx, m, i, out)?,
                    role => {
                        if b.usable(m).contains(&i) {
                            b.bind_call(ctx, m, i, out)?;
                            // A second call of a helper that binds a wire
                            // makes a second wire under another path.
                            if matches!(role, Role::Wire) && b.tape.flag() && b.within_budget(ctx) {
                                b.bind_call(ctx, m, i, out)?;
                            }
                        }
                    }
                }
            }
            Ok(())
        })
    }

    /// Whether the budget of declarations covers one more statement in the
    /// frame of `ctx`.
    fn within_budget(&self, ctx: &Ctx) -> bool {
        self.decls + UNIT_DECLS * ctx.envs.len() <= MAX_DECLS
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
                Role::Declare | Role::List(_) => false,
            })
            .map(|(i, _)| i)
            .collect()
    }

    /// A fresh resource of the type of the first formal of a helper, and
    /// the call that binds it. A wire binds at once and then reads. A
    /// register binds at the end of the frame.
    fn bind_call(&mut self, ctx: &mut Ctx, m: &mut Module, i: usize, out: &mut Vec<Stmt>) -> Built {
        let h = self.res_helpers.get(i).cloned().ok_or(Fault::Type)?;
        called!(self, ctx, i);
        match h.role {
            Role::Wire | Role::Reg => {
                let (Some((_, FTy::Wire(ty) | FTy::Reg(ty))), wire) =
                    (h.params.first(), matches!(h.role, Role::Wire))
                else {
                    return Err(Fault::Type);
                };
                let types = self.types(ty, &ctx.envs)?;
                let name = m.names.fresh(if wire { "w" } else { "r" });
                self.decls += ctx.envs.len();
                if wire {
                    out.push(Stmt::Wire(name.clone(), ty.clone()));
                    let call = self.binder_call(ctx, i, HExpr::Name(name.clone()))?;
                    out.push(call);
                    note!(self, bind_wire_calls);
                } else {
                    let reset = self.short(types.first().copied().ok_or(Fault::Type)?);
                    out.push(Stmt::Reg(name.clone(), ty.clone(), reset));
                    ctx.pending.push(Pending {
                        first: HExpr::Name(name.clone()),
                        via: Some(i),
                        ty: ty.clone(),
                    });
                }
                ctx.publish(Hw {
                    expr: HExpr::Name(name),
                    ty: Some(ty.clone()),
                    types,
                    mutable: false,
                });
            }
            Role::Input { module, port } => {
                self.decls += ctx.envs.len();
                let child = self.declare_child(ctx, m, module, out)?;
                self.bind_child_inputs(ctx, &child, Some(&port), out)?;
                let first = HExpr::Field(child.name.clone(), port);
                let call = self.binder_call(ctx, i, first)?;
                out.push(call);
                note!(self, bind_input_calls);
                self.expose_child_handles(ctx, &child)?;
            }
            Role::Mem { word, depth } => {
                self.decls += ctx.envs.len();
                let name = m.names.fresh("n");
                out.push(Stmt::Mem(name.clone(), word.clone(), literal(depth)));
                self.mem_ports(ctx, &mut m.names, (&name, &word, depth), Some(i), out)?;
            }
            Role::Declare | Role::List(_) => {}
        }
        Ok(())
    }

    /// The two port calls on the memory `mem` of the word `word` and the
    /// depth `depth`, through the helper `via` or in the frame. The data
    /// of the response is readable.
    pub(super) fn mem_ports(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        (mem, word, depth): (&str, &Ty, u32),
        via: Option<usize>,
        out: &mut Vec<Stmt>,
    ) -> Built<HExpr> {
        let read = names.fresh("l");
        if let Some(i) = via {
            let (callee, args) = self.binder_args(ctx, i, HExpr::Name(mem.to_owned()))?;
            out.push(Stmt::Let {
                name: read.clone(),
                mutable: false,
                ty: None,
                value: HExpr::Call(callee, args),
            });
            note!(self, bind_mem_calls);
            let data = HExpr::Name(read);
            self.push_read(ctx, data.clone(), word)?;
            return Ok(data);
        }
        let scalar = self.scalar(word)?;
        let addr = Scalar::UInt(address_bits(depth));
        let write = Stmt::WritePort {
            mem: mem.to_owned(),
            addr: Box::new(self.actual(ctx, addr)),
            data: Box::new(self.actual(ctx, scalar)),
            en: Box::new(self.actual(ctx, Scalar::Bool)),
            receiver: self.tape.flag(),
        };
        out.push(write);
        let value = HExpr::ReadPort {
            mem: mem.to_owned(),
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
        let data = HExpr::Field(read, "data".to_owned());
        self.push_read(ctx, data.clone(), word)?;
        Ok(data)
    }

    /// `mem n: [T; N];`, `write_port`, and `let l = read_port`, in the
    /// module. The data of the response is readable.
    fn direct_mem(&mut self, ctx: &mut Ctx, m: &mut Module, out: &mut Vec<Stmt>) -> Built {
        let (word, _) = self.word_ty();
        let depth = self.pick(&DEPTHS);
        let name = m.names.fresh("n");
        self.decls += ctx.envs.len();
        out.push(Stmt::Mem(name.clone(), word.clone(), literal(depth)));
        self.mem_ports(ctx, &mut m.names, (&name, &word, depth), None, out)?;
        Ok(())
    }

    /// Makes the data `expr` of type `ty` a readable name.
    pub(super) fn push_read(&mut self, ctx: &mut Ctx, expr: HExpr, ty: &Ty) -> Built {
        let types = self.types(ty, &ctx.envs)?;
        ctx.publish(Hw {
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
    pub(super) fn actual(&mut self, ctx: &Ctx, scalar: Scalar) -> HExpr {
        let types = vec![scalar; ctx.envs.len()];
        let names: Vec<&Hw> = ctx
            .hw
            .iter()
            .chain(&ctx.hand)
            .filter(|h| h.types == types)
            .collect();
        match names.get(self.tape.index(names.len())) {
            Some(h) if self.tape.below(4) != 0 => h.expr.clone(),
            _ => HExpr::Static(self.short(scalar)),
        }
    }

    /// The outputs of a child that a helper or a group declared, as names
    /// of the hand tape only: the main tape does not see them.
    pub(super) fn expose_child_handles(&mut self, ctx: &mut Ctx, child: &Child) -> Built {
        let (hw, enums) = (ctx.hw.len(), ctx.enums.len());
        self.expose_child_outputs(ctx, child)?;
        if !ctx.local {
            let outputs = ctx.hw.split_off(hw);
            ctx.hand.extend(outputs);
            ctx.enums.truncate(enums);
        }
        Ok(())
    }

    /// The value `e` of an output of the wanted type, with a name of the
    /// hand tape mixed in: `read ^ e`, or `read != e` for a `Bool`. The
    /// outputs of a module thus depend on the resources of its helpers.
    pub(super) fn mix_hand(&mut self, ctx: &Ctx, want: &Want, e: HExpr) -> HExpr {
        self.on_hand(|b| {
            if ctx.hand.is_empty() || b.tape.below(4) == 0 {
                return e;
            }
            let Some(h) = ctx.hand.get(b.tape.index(ctx.hand.len())) else {
                return e;
            };
            let Some(read) = adapt(h.expr.clone(), &Want::of(h), want) else {
                return e;
            };
            note!(b, mixed_outputs);
            #[cfg(test)]
            match &h.expr {
                HExpr::Read(_) => b.stats.mixed_explicit_reads += 1,
                HExpr::Index(..) | HExpr::Select(..) => b.stats.mixed_container_reads += 1,
                HExpr::Field(_, f) if f.starts_with('m') => b.stats.mixed_container_reads += 1,
                _ => {}
            }
            let op = if want.types.first() == Some(&Scalar::Bool) {
                HBin::Ne
            } else {
                HBin::Xor
            };
            HExpr::Binary(op, Box::new(read), Box::new(e))
        })
    }

    /// A short literal of type `scalar`: below 8 in magnitude.
    pub(super) fn short(&mut self, scalar: Scalar) -> SExpr {
        match scalar {
            Scalar::Bool => SExpr::Bool(self.tape.flag()),
            Scalar::UInt(w) => literal(self.tape.below(1 << w.min(3))),
            Scalar::SInt(w) => literal(self.tape.below(1 << (w - 1).min(2))),
        }
    }

    /// The name of helper `i` and its actuals: `first` for the first
    /// formal, and a value for each data formal.
    fn binder_args(&mut self, ctx: &Ctx, i: usize, first: HExpr) -> Built<(String, Vec<HExpr>)> {
        let (name, rest) = self.data_args(ctx, i, 1)?;
        Ok((name, std::iter::once(first).chain(rest).collect()))
    }

    /// The name of helper `i` and a value for each formal of a helper that
    /// declares resources: all its formals are data.
    pub(super) fn binder_args_of(&mut self, ctx: &Ctx, i: usize) -> Built<(String, Vec<HExpr>)> {
        self.data_args(ctx, i, 0)
    }

    /// The name of helper `i` and a value for each formal after the first
    /// `skip`, which must be data formals.
    fn data_args(&mut self, ctx: &Ctx, i: usize, skip: usize) -> Built<(String, Vec<HExpr>)> {
        let h = self.res_helpers.get(i).cloned().ok_or(Fault::Type)?;
        self.called.insert(i);
        let mut args = Vec::new();
        for (_, t) in h.params.iter().skip(skip) {
            let FTy::Data(t) = t else {
                return Err(Fault::Type);
            };
            let scalar = self.scalar(t)?;
            args.push(self.actual(ctx, scalar));
        }
        Ok((h.name, args))
    }

    /// `H<i>(first, e, ...);`
    pub(super) fn binder_call(&mut self, ctx: &Ctx, i: usize, first: HExpr) -> Built<Stmt> {
        let (name, args) = self.binder_args(ctx, i, first)?;
        Ok(Stmt::Call(name, args))
    }

    /// The binding of each register that this frame declared: a call of a
    /// helper, or `:=`.
    pub(super) fn close_pending(&mut self, ctx: &mut Ctx, out: &mut Vec<Stmt>) -> Built {
        let pending = std::mem::take(&mut ctx.pending);
        self.on_hand(|b| {
            for p in pending {
                let Pending { first, via, ty } = p;
                out.push(b.bind_handle(ctx, &first, via, &ty)?);
                note!(b, bind_reg_calls);
            }
            Ok(())
        })
    }

    /// The binding of the handle `first` of a register or a wire of the type
    /// `ty`: a call of the helper `via`, or `first := e;`.
    pub(super) fn bind_handle(
        &mut self,
        ctx: &Ctx,
        first: &HExpr,
        via: Option<usize>,
        ty: &Ty,
    ) -> Built<Stmt> {
        if let Some(i) = via {
            return self.binder_call(ctx, i, first.clone());
        }
        let want = Want {
            types: self.types(ty, &ctx.envs)?,
            ty: Some(ty.clone()),
        };
        let value = self.driver_at(&ctx.view(), &want, HANDLE_DEPTH);
        Ok(Stmt::Connect(place_of(first), value))
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
    use super::super::handle_lists::HANDLE_LEN;
    use super::super::tests::tapes;
    use super::super::*;
    use super::{MAX_DECLS, RES_HELPERS};
    use std::collections::BTreeMap;

    /// The forms of handles that a program holds, by name, from the counts
    /// of its executed calls.
    fn forms(s: &Stats) -> [(&'static str, bool); 23] {
        [
            ("Reg formal", s.bind_reg_calls > 0),
            ("Wire formal", s.bind_wire_calls > 0),
            ("Input formal", s.bind_input_calls > 0),
            ("Mem formal", s.bind_mem_calls > 0),
            ("memory of the module", s.direct_mems > 0),
            ("declared reg", s.decl_regs > 0),
            ("declared wire", s.decl_wires > 0),
            ("declared mem", s.decl_mems > 0),
            ("declared instance", s.decl_instances > 0),
            ("result ()", s.unit_results > 0),
            ("result handle", s.handle_results > 0),
            ("result tuple", s.tuple_results > 0),
            ("result array", s.array_results > 0),
            ("result record", s.record_results > 0),
            ("result data (let v = h())", s.scratch_calls > 0),
            ("list of handles", s.list_groups > 0),
            ("list of inputs", s.list_input_groups > 0),
            (":= through a container", s.container_binds > 0),
            ("caller binds a child input", s.caller_child_inputs > 0),
            ("nested call", s.nested_calls > 0),
            ("repeated call", s.repeat_calls > 0),
            ("read(h)", s.mixed_explicit_reads > 0),
            ("read through a container", s.mixed_container_reads > 0),
        ]
    }

    /// Each form of handles occurs in at least 10% of 256 programs, and a
    /// call of a helper that takes resources in at least 40%.
    #[test]
    fn programs_cover_handles() {
        const TAPES: usize = 256;
        let mut with = BTreeMap::<&str, usize>::new();
        let mut calls = 0;
        for tape in tapes(TAPES) {
            let mut b = Builder::new(tape);
            let p = b.program();
            assert!(p.is_ok(), "a program faults: {p:?}");
            let s = &b.stats;
            for (form, seen) in forms(s) {
                *with.entry(form).or_default() += usize::from(seen);
            }
            let any = s.bind_reg_calls
                + s.bind_wire_calls
                + s.bind_input_calls
                + s.bind_mem_calls
                + s.declare_calls
                + s.list_groups;
            calls += usize::from(any > 0);
        }
        eprintln!("COVER {with:?} calls {calls}");
        for (form, n) in &with {
            assert!(
                n * 10 >= TAPES,
                "{form} occurs in {n} of {TAPES} programs: {with:?}"
            );
        }
        assert!(calls * 5 >= TAPES * 2, "calls: {calls} of {TAPES}");
    }

    /// A call of a helper that takes resources is a statement of a module
    /// frame (`S016`) or the root of a `let`, or a statement of a helper.
    /// It is never inside an expression, so no hardware arm and no static
    /// position holds one (`S016`, `S011`).
    #[test]
    fn no_resource_call_in_an_arm_or_a_static_position() {
        fn nested(e: &HExpr, root: bool) -> bool {
            let any = |xs: &[HExpr]| xs.iter().any(|x| nested(x, false));
            match e {
                HExpr::Call(f, xs) => (!root && f.starts_with('H')) || any(xs),
                HExpr::Unary(_, a)
                | HExpr::Resize(_, a)
                | HExpr::Reinterpret(_, a)
                | HExpr::Index(a, _)
                | HExpr::Select(a, _)
                | HExpr::Read(a) => nested(a, false),
                HExpr::Binary(_, a, b) => nested(a, false) || nested(b, false),
                HExpr::If(c, a, b) => [c, a, b].iter().any(|x| nested(x, false)),
                HExpr::Match(m) => {
                    nested(&m.scrutinee, false) || m.arms.iter().any(|(_, a)| nested(a, false))
                }
                HExpr::Ctor(_, _, xs)
                | HExpr::Tuple(xs)
                | HExpr::Array(xs)
                | HExpr::Record(_, xs) => any(xs),
                HExpr::Receiver(r, _, xs) => nested(r, false) || any(xs),
                HExpr::ReadPort { addr, en, .. } => nested(addr, false) || nested(en, false),
                _ => false,
            }
        }
        fn walk(body: &[Stmt]) -> bool {
            body.iter().any(|s| match s {
                Stmt::Call(f, xs) => f.starts_with('H') && xs.iter().any(|x| nested(x, false)),
                Stmt::Let { value, .. } => nested(value, true),
                Stmt::Connect(_, v) | Stmt::Assign(_, v) | Stmt::HPush(_, v) => nested(v, false),
                Stmt::WritePort { addr, data, en, .. } => {
                    [addr, data, en].iter().any(|x| nested(x, false))
                }
                Stmt::If(_, t, e) => walk(t) || walk(e.as_deref().unwrap_or_default()),
                Stmt::For(_, _, _, b) | Stmt::Block(b) => walk(b),
                _ => false,
            })
        }
        for tape in tapes(256) {
            let Ok(p) = build(tape) else { continue };
            for item in &p.items {
                let bad = match item {
                    Item::Module { body, .. } => walk(body),
                    Item::Helper { body, result, .. } => walk(body) || nested(result, true),
                    _ => false,
                };
                assert!(!bad, "a call of a helper in an expression\n{}", p.text());
            }
        }
    }

    /// The caps of the forms of handles hold on 256 programs: the
    /// declarations that they make, the helpers, the length of a list, the
    /// depth of a memory, and its word.
    #[test]
    fn handle_forms_stay_in_caps() {
        let mut most = 0;
        for tape in tapes(256) {
            let mut b = Builder::new(tape);
            let Ok(p) = b.program() else { continue };
            most = most.max(b.decls);
            assert!(b.res_helpers.len() <= 2 * RES_HELPERS as usize);
            let mut stmts = Vec::new();
            for item in &p.items {
                if let Item::Module { body, .. } | Item::Helper { body, .. } = item {
                    stmts.extend(super::super::tests::stmts_of_body(body));
                }
            }
            for s in stmts {
                match s {
                    Stmt::Mem(_, word, SExpr::Int(depth, _)) => {
                        assert!(*depth == 2.into() || *depth == 4.into(), "{depth}");
                        let bits = b.scalar(word).map(Scalar::bits);
                        assert!(bits.is_ok_and(|w| w <= 16), "{word:?}");
                    }
                    Stmt::For(_, _, SExpr::Int(len, _), body)
                        if body.iter().any(|s| matches!(s, Stmt::HPush(..))) =>
                    {
                        assert!(*len <= HANDLE_LEN.into(), "{len}");
                    }
                    _ => {}
                }
            }
        }
        assert!(most <= MAX_DECLS, "{most} declarations in one program");
    }
}
