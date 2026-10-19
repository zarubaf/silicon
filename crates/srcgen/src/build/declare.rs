// SPDX-License-Identifier: Apache-2.0
//! Helpers that declare resources (front-end spec 5.6, "Helpers that
//! declare resources"), and the calls of them.
//!
//! A helper `H<k>` declares one or two resources: a `reg`, a `wire`, a
//! `mem`, or an `instance`. It returns `()`, one handle, a tuple, an array,
//! or a struct of handles. The helper binds each resource that it keeps
//! (with `:=`, through a call of an earlier helper, or with two port calls
//! on a memory), or it returns the resource unbound for its caller.
//!
//! Rules by construction:
//!
//! - A helper declares only at its top frame (`S016`), and it runs in the
//!   owner of its caller, so its children belong to the caller.
//! - A container of handles is a tuple, an array, or a struct. An array has
//!   one handle type (`S010`). A tuple, an array, and a struct hold
//!   registers and wires only, so a `data` context reads each element
//!   (`S010`). A memory and an instance stand alone.
//! - The caller binds each unbound resource once (`S018`): a wire at once,
//!   a register at the end of its frame, a memory with both ports, and an
//!   instance with all its inputs.
//! - A helper that instantiates module `j` has one child, and a module
//!   before `j` calls it. The call adds the context of `j`, so a child that
//!   no call reaches stays dropped. The `instance` statement and the type
//!   `Instance[M, args]` share their arguments (`S019`).

use super::handles::{DEPTHS, Leaf, Part, Pending, ResHelper, Role, Step, at, literal};
use super::inst::Child;
use super::stat::Reach;
use super::{Builder, Built, CONTEXTS, Ctx, Hw, Module, Names};
use crate::eval::{Env, Fault, Value, convert};
use crate::program::{FTy, FieldTy, HExpr, Item, SExpr, Stmt, StructDef, Ty};

/// The body of a helper under construction.
struct Hb {
    names: Names,
    ctx: Ctx,
    body: Vec<Stmt>,
    clocked: bool,
    children: Vec<(usize, Vec<Value>)>,
}

/// The kinds of resource that a helper declares.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Reg,
    Wire,
    Mem,
    Instance,
}

/// The result of a helper: its type, its expression, and its resources.
type Shaped = (FTy, HExpr, Vec<Part>);

impl Builder {
    /// A helper that declares resources.
    pub(super) fn declare_helper(&mut self, name: String) -> Built<ResHelper> {
        let mut names = Names::default();
        let (data, hw) = self.data_formals(&mut names);
        let mut hb = Hb {
            names,
            ctx: self.helper_ctx(hw),
            body: Vec::new(),
            clocked: false,
            children: Vec::new(),
        };
        let (ret, result, parts) = match self.tape.below(8) {
            0 | 1 => self.unit_shape(&mut hb)?,
            2..=4 => self.one_shape(&mut hb)?,
            5 => self.tuple_shape(&mut hb)?,
            6 => self.array_shape(&mut hb)?,
            _ => self.record_shape(&mut hb)?,
        };
        Ok(ResHelper {
            name,
            params: data,
            ret,
            body: hb.body,
            result,
            role: Role::Declare,
            parts,
            clocked: hb.clocked,
            children: hb.children,
        })
    }

    /// One or two resources, all bound: `()`.
    fn unit_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        for _ in 0..self.tape.between(1, 2) {
            let kind = self.pick(&[Kind::Reg, Kind::Wire, Kind::Mem, Kind::Instance]);
            self.declare_leaf(hb, kind, None, true)?;
        }
        Ok((FTy::Unit, HExpr::Unit, Vec::new()))
    }

    /// One resource, returned. A memory returns unbound, and an instance
    /// may return with its inputs bound.
    fn one_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let kind = self.pick(&[
            Kind::Reg,
            Kind::Reg,
            Kind::Wire,
            Kind::Wire,
            Kind::Mem,
            Kind::Instance,
        ]);
        let bound = kind != Kind::Mem && self.tape.flag();
        let (name, fty, leaf) = self.declare_leaf(hb, kind, None, bound)?;
        let part = Part {
            path: Vec::new(),
            leaf,
            bound,
        };
        Ok((fty, HExpr::Name(name), vec![part]))
    }

    /// Two registers or wires in a tuple.
    fn tuple_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let mut types = Vec::new();
        let mut parts = Vec::new();
        let mut items = Vec::new();
        for k in 0..2 {
            let kind = self.pick(&[Kind::Reg, Kind::Wire]);
            let bound = self.tape.flag();
            let (name, fty, leaf) = self.declare_leaf(hb, kind, None, bound)?;
            types.push(fty);
            items.push(HExpr::Name(name));
            parts.push(Part {
                path: vec![Step::Select(k)],
                leaf,
                bound,
            });
        }
        Ok((FTy::Tuple(types), HExpr::Tuple(items), parts))
    }

    /// Two or three registers, or wires, of one type in an array.
    fn array_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let kind = self.pick(&[Kind::Reg, Kind::Wire]);
        let n = self.tape.between(2, 3);
        let mut elem = None;
        let mut parts = Vec::new();
        let mut items = Vec::new();
        for i in 0..n {
            let bound = self.tape.flag();
            let hint = elem.as_ref().map(|(_, ty): &(FTy, Ty)| ty);
            let (name, fty, leaf) = self.declare_leaf(hb, kind, hint, bound)?;
            let (Leaf::Reg(ty) | Leaf::Wire(ty)) = &leaf else {
                return Err(Fault::Type);
            };
            elem.get_or_insert((fty, ty.clone()));
            items.push(HExpr::Name(name));
            parts.push(Part {
                path: vec![Step::Index(i)],
                leaf,
                bound,
            });
        }
        let (fty, _) = elem.ok_or(Fault::Type)?;
        Ok((FTy::Array(Box::new(fty), n), HExpr::Array(items), parts))
    }

    /// Two or three registers or wires in a struct `T<n>`.
    fn record_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let name = format!("T{}", self.hstructs.len());
        let mut fields = Vec::new();
        let mut parts = Vec::new();
        let mut items = Vec::new();
        for i in 0..self.tape.between(2, 3) {
            let kind = self.pick(&[Kind::Reg, Kind::Wire]);
            let bound = self.tape.flag();
            let (var, fty, leaf) = self.declare_leaf(hb, kind, None, bound)?;
            let field = format!("m{i}");
            fields.push((field.clone(), FieldTy::Handle(fty)));
            items.push(HExpr::Name(var));
            parts.push(Part {
                path: vec![Step::Field(field)],
                leaf,
                bound,
            });
        }
        self.hstructs.push(StructDef {
            name: name.clone(),
            params: Vec::new(),
            fields,
        });
        Ok((FTy::Struct(name.clone()), HExpr::Record(name, items), parts))
    }

    /// Declares a resource of `kind` in the helper. `hint` is the type of
    /// the elements of an array. `bound` says whether the helper binds it.
    /// Gives the name, the handle type, and the leaf. A kind that the
    /// program cannot have gives a wire.
    fn declare_leaf(
        &mut self,
        hb: &mut Hb,
        kind: Kind,
        hint: Option<&Ty>,
        bound: bool,
    ) -> Built<(String, FTy, Leaf)> {
        match kind {
            Kind::Reg | Kind::Wire => self.register_or_wire(hb, kind == Kind::Reg, hint, bound),
            Kind::Mem => self.helper_mem(hb, bound),
            Kind::Instance => match self.helper_child(hb, bound)? {
                Some(leaf) => Ok(leaf),
                None => self.register_or_wire(hb, false, hint, bound),
            },
        }
    }

    /// `reg r: T = k;` or `wire w: T;`, and its binding if `bound`.
    fn register_or_wire(
        &mut self,
        hb: &mut Hb,
        reg: bool,
        hint: Option<&Ty>,
        bound: bool,
    ) -> Built<(String, FTy, Leaf)> {
        let ty = match hint {
            Some(t) => t.clone(),
            None => self.leaf_ty(reg),
        };
        let scalar = self.scalar(&ty)?;
        let name = hb.names.fresh(if reg { "r" } else { "w" });
        let first = HExpr::Name(name.clone());
        let readable = Hw {
            expr: first.clone(),
            ty: Some(ty.clone()),
            types: vec![scalar],
            mutable: false,
        };
        if reg {
            let reset = self.short(scalar);
            hb.body.push(Stmt::Reg(name.clone(), ty.clone(), reset));
            hb.clocked = true;
            hb.ctx.hw.push(readable.clone());
        } else {
            hb.body.push(Stmt::Wire(name.clone(), ty.clone()));
        }
        if bound {
            let via = self.binder_for(reg, &ty);
            let stmt = self.bind_handle(&hb.ctx, &first, via, &ty)?;
            hb.body.push(stmt);
            if !reg {
                hb.ctx.hw.push(readable);
            }
        }
        let (fty, leaf) = if reg {
            (FTy::Reg(ty.clone()), Leaf::Reg(ty))
        } else {
            (FTy::Wire(ty.clone()), Leaf::Wire(ty))
        };
        Ok((name, fty, leaf))
    }

    /// The type of a register or a wire: the type of an earlier binder in
    /// one draw in two, so that a nested call can bind it.
    fn leaf_ty(&mut self, reg: bool) -> Ty {
        let binders: Vec<Ty> = self
            .res_helpers
            .iter()
            .filter_map(|h| match (&h.role, h.params.first()) {
                (Role::Reg, Some((_, FTy::Reg(t)))) if reg => Some(t.clone()),
                (Role::Wire, Some((_, FTy::Wire(t)))) if !reg => Some(t.clone()),
                _ => None,
            })
            .collect();
        if self.tape.flag()
            && let Some(t) = binders.get(self.tape.index(binders.len()))
        {
            return t.clone();
        }
        self.data_ty().0
    }

    /// An earlier helper that binds a register or a wire of the type `ty`,
    /// in one draw in two.
    pub(super) fn binder_for(&mut self, reg: bool, ty: &Ty) -> Option<usize> {
        let found: Vec<usize> = self
            .res_helpers
            .iter()
            .enumerate()
            .filter(|(_, h)| match (&h.role, h.params.first()) {
                (Role::Reg, Some((_, FTy::Reg(t)))) => reg && t == ty,
                (Role::Wire, Some((_, FTy::Wire(t)))) => !reg && t == ty,
                _ => false,
            })
            .map(|(i, _)| i)
            .collect();
        let pick = self.tape.index(found.len());
        found.get(pick).copied().filter(|_| self.tape.flag())
    }

    /// An earlier helper that makes the port calls on a memory of this
    /// word and depth, in one draw in two.
    fn mem_binder_for(&mut self, word: &Ty, depth: u32) -> Option<usize> {
        let found: Vec<usize> = self
            .res_helpers
            .iter()
            .enumerate()
            .filter(|(_, h)| {
                matches!(&h.role, Role::Mem { word: w, depth: d } if w == word && *d == depth)
            })
            .map(|(i, _)| i)
            .collect();
        let pick = self.tape.index(found.len());
        found.get(pick).copied().filter(|_| self.tape.flag())
    }

    /// `mem n: [T; N];`, and the two port calls if `bound`.
    fn helper_mem(&mut self, hb: &mut Hb, bound: bool) -> Built<(String, FTy, Leaf)> {
        let (word, _) = self.data_ty();
        let depth = self.pick(&DEPTHS);
        let name = hb.names.fresh("n");
        hb.body
            .push(Stmt::Mem(name.clone(), word.clone(), literal(depth)));
        hb.clocked = true;
        if bound {
            let via = self.mem_binder_for(&word, depth);
            self.mem_ports(
                &mut hb.ctx,
                &mut hb.names,
                (&name, &word, depth),
                via,
                &mut hb.body,
            )?;
        }
        let fty = FTy::Mem(word.clone(), literal(depth));
        Ok((name, fty, Leaf::Mem { word, depth }))
    }

    /// `instance u = M<j>(args);` of a later module, and the binding of its
    /// inputs if `bound`. A helper has one child; without a later module,
    /// or with a child already, there is none.
    fn helper_child(&mut self, hb: &mut Hb, bound: bool) -> Built<Option<(String, FTy, Leaf)>> {
        if !hb.children.is_empty() || self.sigs.len() < 2 {
            return Ok(None);
        }
        let later = u32::try_from(self.sigs.len() - 1).map_err(|_| Fault::Type)?;
        let j = self.tape.between(1, later) as usize;
        let sig = self.sigs.get(j).cloned().ok_or(Fault::Type)?;
        let envs = [Env::default()];
        let consts = self.const_names();
        let r = Reach {
            names: &consts,
            fns: 0,
            envs: Some(&envs),
        };
        let args: Vec<SExpr> = sig
            .params
            .iter()
            .map(|(_, t)| self.argument(t, r, &envs))
            .collect();
        let tuple = self.converted_tuple(j, &args)?;
        let name = hb.names.fresh("u");
        hb.body
            .push(Stmt::Instance(name.clone(), sig.name.clone(), args.clone()));
        hb.clocked |= sig.clocked;
        hb.children.push((j, tuple.clone()));
        if bound {
            let child = Child {
                name: name.clone(),
                envs: vec![Env::of(&sig.params, &tuple)],
                sig: sig.clone(),
            };
            self.bind_child_inputs(&mut hb.ctx, &child, None, &mut hb.body)?;
        }
        let fty = FTy::Instance(sig.name, args);
        Ok(Some((name, fty, Leaf::Instance { module: j, tuple })))
    }

    /// The identity of module `j` at the arguments `args`: each argument
    /// converted to its parameter type (#188).
    fn converted_tuple(&self, j: usize, args: &[SExpr]) -> Built<Vec<Value>> {
        let sig = self.sigs.get(j).ok_or(Fault::Type)?;
        args.iter()
            .zip(&sig.params)
            .map(|(a, (_, t))| {
                let v = crate::eval::eval(a, &Env::default(), &self.scope)?;
                convert(t, v)
            })
            .collect()
    }

    /// The helpers that declare resources and that a call in `m` can use:
    /// a clocked helper needs a clocked module, the module comes before the
    /// child, and the child has room for the context.
    pub(super) fn usable_declarers(&self, m: &Module) -> Vec<usize> {
        self.res_helpers
            .iter()
            .enumerate()
            .filter(|(_, h)| {
                matches!(h.role, Role::Declare)
                    && (!h.clocked || m.clocked)
                    && h.children.iter().all(|(j, tuple)| {
                        self.reachable(m, *j)
                            && self.contexts.get(*j).is_some_and(|known| {
                                known.contains(tuple) || known.len() < CONTEXTS
                            })
                    })
            })
            .map(|(i, _)| i)
            .collect()
    }

    /// A call of one of the helpers `declarers`: `h(args);` for `()`, else
    /// `let t = h(args);`. Then the caller takes each resource of the
    /// result: it binds the unbound ones, and the registers and wires
    /// become readable.
    pub(super) fn declare_call(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        declarers: &[usize],
        out: &mut Vec<Stmt>,
    ) -> Built {
        let Some(&i) = declarers.get(self.tape.index(declarers.len())) else {
            return Ok(());
        };
        let h = self.res_helpers.get(i).cloned().ok_or(Fault::Type)?;
        let (callee, args) = self.binder_args_of(ctx, i)?;
        for (j, tuple) in &h.children {
            let known = self.contexts.get_mut(*j).ok_or(Fault::Type)?;
            if !known.contains(tuple) {
                known.push(tuple.clone());
            }
        }
        note!(self, declare_calls);
        if matches!(h.ret, FTy::Unit) {
            out.push(Stmt::Call(callee, args));
            return Ok(());
        }
        let root = m.names.fresh("t");
        out.push(Stmt::Let {
            name: root.clone(),
            mutable: false,
            ty: None,
            value: HExpr::Call(callee, args),
        });
        for part in &h.parts {
            self.take_part(ctx, m, out, &root, part)?;
        }
        Ok(())
    }

    /// The caller's side of one resource of a result `root`.
    fn take_part(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
        root: &str,
        part: &Part,
    ) -> Built {
        let first = at(root, &part.path);
        match &part.leaf {
            Leaf::Reg(ty) => {
                self.read_handle(ctx, &first, ty)?;
                if !part.bound {
                    let via = self.binder_for(true, ty);
                    ctx.pending.push(Pending {
                        first,
                        via,
                        ty: ty.clone(),
                    });
                }
            }
            Leaf::Wire(ty) => {
                if !part.bound {
                    let via = self.binder_for(false, ty);
                    out.push(self.bind_handle(ctx, &first, via, ty)?);
                }
                self.read_handle(ctx, &first, ty)?;
            }
            Leaf::Mem { word, depth } => {
                if !part.bound {
                    let via = self.mem_binder_for(word, *depth);
                    self.mem_ports(ctx, &mut m.names, (root, word, *depth), via, out)?;
                }
            }
            Leaf::Instance { module, tuple } => {
                let sig = self.sigs.get(*module).cloned().ok_or(Fault::Type)?;
                let env = Env::of(&sig.params, tuple);
                let child = Child {
                    name: root.to_owned(),
                    envs: vec![env; ctx.envs.len()],
                    sig,
                };
                if !part.bound {
                    self.bind_child_inputs(ctx, &child, None, out)?;
                }
                self.expose_child_outputs(ctx, &child)?;
            }
        }
        Ok(())
    }

    /// Makes the register or wire `first` readable: in a `data` context it
    /// reads as data, or `read(first)` reads it.
    fn read_handle(&mut self, ctx: &mut Ctx, first: &HExpr, ty: &Ty) -> Built {
        let expr = if self.tape.below(3) == 0 {
            note!(self, explicit_reads);
            HExpr::Read(Box::new(first.clone()))
        } else {
            first.clone()
        };
        if !matches!(first, HExpr::Name(_)) {
            note!(self, container_reads);
        }
        let types = self.types(ty, &ctx.envs)?;
        ctx.hw.push(Hw {
            expr,
            ty: Some(ty.clone()),
            types,
            mutable: false,
        });
        Ok(())
    }

    /// The structs of handles, as items.
    pub(super) fn handle_struct_items(&self) -> impl Iterator<Item = Item> + '_ {
        self.hstructs.iter().cloned().map(Item::Struct)
    }
}
