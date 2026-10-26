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

use super::handles::{
    DEPTHS, HANDLE_DEPTH, Leaf, ListOf, Part, Pending, ResHelper, Role, Step, at, literal,
};
use super::inst::Child;
use super::reflect::RTy;
use super::stat::{Reach, value_expr};
use super::{Builder, Built, CONTEXTS, Ctx, Hw, Module, Names};
use crate::eval::{Env, Fault, Value, convert};
use crate::program::{FTy, FieldTy, HExpr, SExpr, Stmt, StructDef, Ty};

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
        let (data, hw) = self.data_formals(&mut names, None);
        let mut hb = Hb {
            names,
            ctx: self.helper_ctx(hw),
            body: Vec::new(),
            clocked: false,
            children: Vec::new(),
        };
        // A register or wire that an earlier helper binds.
        if self.tape.flag() {
            self.nested_extra(&mut hb)?;
        }
        let (ret, result, parts) = match self.fresh_shape() {
            0 => self.unit_shape(&mut hb)?,
            1 => self.one_shape(&mut hb, &[Kind::Reg, Kind::Wire])?,
            2 => self.one_shape(&mut hb, &[Kind::Mem])?,
            3 => self.one_shape(&mut hb, &[Kind::Instance])?,
            4 => self.tuple_shape(&mut hb)?,
            5 => self.array_shape(&mut hb)?,
            6 => self.record_shape(&mut hb)?,
            _ => self.scratch_shape(&mut hb)?,
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

    /// The shape of the result of the next helper that declares: a shape
    /// that no earlier helper has, if one is left, by the weights.
    fn fresh_shape(&mut self) -> usize {
        const WEIGHTS: [u32; 8] = [3, 1, 1, 5, 4, 1, 3, 4];
        let open: Vec<usize> = (0..WEIGHTS.len())
            .filter(|s| !self.shapes.contains(s))
            .collect();
        let pool: Vec<usize> = if open.is_empty() {
            (0..WEIGHTS.len()).collect()
        } else {
            open
        };
        let total: u32 = pool.iter().filter_map(|&s| WEIGHTS.get(s)).sum();
        let mut n = self.tape.below(total);
        for &s in &pool {
            let w = WEIGHTS.get(s).copied().unwrap_or(0);
            if n < w {
                self.shapes.insert(s);
                return s;
            }
            n -= w;
        }
        0
    }

    /// `fn H<k>(x0: U) -> Reg[T] { reg r0: T = k; return r0; }`, or the
    /// same with a wire: a helper that declares one element for a list.
    pub(super) fn factory_helper(&mut self, name: String, reg: bool, ty: &Ty) -> Built<ResHelper> {
        let mut names = Names::default();
        let (data, hw) = self.data_formals(&mut names, None);
        let mut hb = Hb {
            names,
            ctx: self.helper_ctx(hw),
            body: Vec::new(),
            clocked: false,
            children: Vec::new(),
        };
        let (var, fty, leaf) = self.declare_resource(&mut hb, reg, ty, None, false)?;
        let part = Part {
            path: Vec::new(),
            leaf,
            bound: false,
        };
        Ok(ResHelper {
            name,
            params: data,
            ret: fty,
            body: hb.body,
            result: HExpr::Name(var),
            role: Role::Declare,
            parts: vec![part],
            clocked: hb.clocked,
            children: hb.children,
        })
    }

    /// A memory with both port calls, and the data of the response as the
    /// result: the result holds no handle.
    fn scratch_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let (word, depth) = {
            let (word, _) = self.word_ty();
            (word, self.pick(&DEPTHS))
        };
        let name = hb.names.fresh("n");
        hb.body
            .push(Stmt::Mem(name.clone(), word.clone(), literal(depth)));
        hb.clocked = true;
        let via = self.mem_binder_for(&word, depth);
        let data = self.mem_ports(
            &mut hb.ctx,
            &mut hb.names,
            (&name, &word, depth),
            via,
            &mut hb.body,
        )?;
        Ok((FTy::Data(word), data, Vec::new()))
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
    fn one_shape(&mut self, hb: &mut Hb, kinds: &[Kind]) -> Built<Shaped> {
        let kind = kinds
            .get(self.tape.index(kinds.len()))
            .copied()
            .unwrap_or(Kind::Wire);
        let bound = match kind {
            Kind::Mem => false,
            Kind::Instance => self.tape.below(8) == 0,
            _ => self.tape.flag(),
        };
        let (name, fty, leaf) = self.declare_leaf(hb, kind, None, bound)?;
        let part = Part {
            path: Vec::new(),
            leaf,
            bound,
        };
        Ok((fty, HExpr::Name(name), vec![part]))
    }

    /// A register or a wire at `path` in a container, or, in one draw in
    /// three, an array of two or three of one type there. Gives the handle
    /// type, the expression, and the resources.
    fn member(&mut self, hb: &mut Hb, path: &[Step]) -> Built<Shaped> {
        if self.tape.below(3) == 0 {
            let (fty, items, parts) = self.array_of(hb, path)?;
            let n = u32::try_from(items.len()).map_err(|_| Fault::Type)?;
            return Ok((FTy::Array(Box::new(fty), n), HExpr::Array(items), parts));
        }
        let kind = self.pick(&[Kind::Reg, Kind::Wire]);
        let bound = self.tape.flag();
        let (name, fty, leaf) = self.declare_leaf(hb, kind, None, bound)?;
        let part = Part {
            path: path.to_vec(),
            leaf,
            bound,
        };
        Ok((fty, HExpr::Name(name), vec![part]))
    }

    /// Two registers or wires in a tuple, and in one draw in three an array
    /// of them in place of one.
    fn tuple_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let mut types = Vec::new();
        let mut parts = Vec::new();
        let mut items = Vec::new();
        for k in 0..2 {
            let (fty, item, mut found) = self.member(hb, &[Step::Select(k)])?;
            types.push(fty);
            items.push(item);
            parts.append(&mut found);
        }
        Ok((FTy::Tuple(types), HExpr::Tuple(items), parts))
    }

    /// Two or three registers, or wires, of one type in an array.
    fn array_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let (fty, items, parts) = self.array_of(hb, &[])?;
        let n = u32::try_from(items.len()).map_err(|_| Fault::Type)?;
        Ok((FTy::Array(Box::new(fty), n), HExpr::Array(items), parts))
    }

    /// Two or three registers or wires of one type, at `path`, then the
    /// index.
    fn array_of(&mut self, hb: &mut Hb, path: &[Step]) -> Built<(FTy, Vec<HExpr>, Vec<Part>)> {
        let kind = self.pick(&[Kind::Reg, Kind::Wire]);
        let n = self.tape.between(2, 3);
        let mut elem: Option<(FTy, Ty)> = None;
        let mut parts = Vec::new();
        let mut items = Vec::new();
        for i in 0..n {
            let bound = self.tape.flag();
            let hint = elem.as_ref().map(|(_, ty)| ty);
            let (name, fty, leaf) = self.declare_leaf(hb, kind, hint, bound)?;
            let (Leaf::Reg(ty) | Leaf::Wire(ty)) = &leaf else {
                return Err(Fault::Type);
            };
            elem.get_or_insert((fty, ty.clone()));
            items.push(HExpr::Name(name));
            let mut steps = path.to_vec();
            steps.push(Step::Index(i));
            parts.push(Part {
                path: steps,
                leaf,
                bound,
            });
        }
        let (fty, _) = elem.ok_or(Fault::Type)?;
        Ok((fty, items, parts))
    }

    /// Two or three registers or wires in a struct `T<n>`, and in one draw
    /// in three an array of them in place of one.
    fn record_shape(&mut self, hb: &mut Hb) -> Built<Shaped> {
        let name = format!("T{}", self.hstructs.len());
        let mut fields = Vec::new();
        let mut parts = Vec::new();
        let mut items = Vec::new();
        for i in 0..self.tape.between(2, 3) {
            let field = format!("m{i}");
            let (fty, item, mut found) = self.member(hb, &[Step::Field(field.clone())])?;
            fields.push((field, FieldTy::Handle(fty)));
            items.push(item);
            parts.append(&mut found);
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
        if kind == Kind::Mem {
            return self.helper_mem(hb, bound);
        }
        if kind == Kind::Instance
            && let Some(leaf) = self.helper_child(hb, bound)?
        {
            return Ok(leaf);
        }
        let reg = kind == Kind::Reg;
        let ty = hint.cloned().unwrap_or_else(|| self.leaf_ty(reg));
        self.declare_resource(hb, reg, &ty, None, bound)
    }

    /// A register or a wire of the type of an earlier binder, bound by a
    /// call of that binder: a call frame of depth 2. Without a binder, none.
    fn nested_extra(&mut self, hb: &mut Hb) -> Built {
        let binders: Vec<(usize, bool, Ty)> = self
            .res_helpers
            .iter()
            .enumerate()
            .filter_map(|(i, h)| match (&h.role, h.params.first()) {
                (Role::Reg, Some((_, FTy::Reg(t)))) => Some((i, true, t.clone())),
                (Role::Wire, Some((_, FTy::Wire(t)))) => Some((i, false, t.clone())),
                _ => None,
            })
            .collect();
        let Some((i, reg, ty)) = binders.get(self.tape.index(binders.len())).cloned() else {
            return Ok(());
        };
        self.declare_resource(hb, reg, &ty, Some(i), true)?;
        Ok(())
    }

    /// The declaration of a register or a wire of the type `ty`. `forced`
    /// is the helper that binds it; else the draw picks.
    fn declare_resource(
        &mut self,
        hb: &mut Hb,
        reg: bool,
        ty: &Ty,
        forced: Option<usize>,
        bound: bool,
    ) -> Built<(String, FTy, Leaf)> {
        let ty = ty.clone();
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
            let via = match forced {
                Some(i) => Some(i),
                None => self.binder_for(reg, &ty),
            };
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
            .filter_map(|h| match &h.role {
                Role::Reg | Role::List(ListOf::Reg(_)) if reg => element(h),
                Role::Wire | Role::List(ListOf::Wire(_)) if !reg => element(h),
                _ => None,
            })
            .collect();
        if self.tape.below(4) != 0
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
        found.get(pick).copied().filter(|_| self.tape.below(4) != 0)
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
        let (word, _) = self.word_ty();
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
        if !hb.children.is_empty() || self.modules() < 2 {
            return Ok(None);
        }
        let later = u32::try_from(self.modules() - 1).map_err(|_| Fault::Type)?;
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
                args: args.clone(),
                sig: sig.clone(),
                via: None,
            };
            self.bind_child_inputs(&mut hb.ctx, &child, None, HANDLE_DEPTH, &mut hb.body)?;
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

    /// Whether the helper `d` declares one register (or wire) of the type
    /// `ty`, returns it unbound, and has no child.
    pub(super) fn returns_unbound(&self, d: usize, ty: &Ty, reg: bool) -> bool {
        let Some(h) = self.res_helpers.get(d) else {
            return false;
        };
        let want = if reg {
            FTy::Reg(ty.clone())
        } else {
            FTy::Wire(ty.clone())
        };
        h.children.is_empty() && h.ret == want && matches!(h.parts.as_slice(), [p] if !p.bound)
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
        if !self.afford(ctx, Self::declarations_of(&h)) {
            return Ok(());
        }
        called!(self, ctx, i);
        #[cfg(test)]
        self.note_declarations(&h);
        let (callee, args) = self.data_args(ctx, i, 0)?;
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
        if let FTy::Data(ty) = &h.ret {
            self.push_read(ctx, HExpr::Name(root.clone()), ty)?;
        }
        for part in &h.parts {
            self.take_part(ctx, m, out, &root, part)?;
        }
        Ok(())
    }

    /// Counts what an executed call of the helper `h` declares and returns.
    #[cfg(test)]
    fn note_declarations(&mut self, h: &ResHelper) {
        for s in &h.body {
            match s {
                Stmt::Reg(..) => self.stats.decl_regs += 1,
                Stmt::Wire(..) => self.stats.decl_wires += 1,
                Stmt::Mem(..) => self.stats.decl_mems += 1,
                Stmt::Instance(..) => self.stats.decl_instances += 1,
                _ => {}
            }
        }
        self.stats.array_results += u32::from(has_array(&h.ret, &self.hstructs));
        match &h.ret {
            FTy::Unit => self.stats.unit_results += 1,
            FTy::Tuple(_) => self.stats.tuple_results += 1,
            FTy::Struct(_) => self.stats.record_results += 1,
            FTy::Data(_) => self.stats.scratch_calls += 1,
            FTy::Array(..) => {}
            _ => self.stats.handle_results += 1,
        }
        let nested = h.body.iter().any(|s| {
            matches!(
                s,
                Stmt::Call(..)
                    | Stmt::Let {
                        value: HExpr::Call(..),
                        ..
                    }
            )
        });
        self.stats.nested_calls += u32::from(nested);
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
        let first = at(root, &part.path)?;
        // `@TypeOf(t.0)` of a handle in a container gives its handle type.
        if !ctx.local {
            let handle = match &part.leaf {
                Leaf::Reg(ty) => RTy::of(ty).map(|t| RTy::Reg(Box::new(t))),
                Leaf::Wire(ty) => RTy::of(ty).map(|t| RTy::Wire(Box::new(t))),
                Leaf::Mem { word, depth } => RTy::of(word).map(|t| RTy::Mem(Box::new(t), *depth)),
                Leaf::Instance { .. } => Some(RTy::Instance),
            };
            self.add_root(&crate::program::hexpr(&first), handle);
        }
        match &part.leaf {
            Leaf::Reg(ty) => {
                self.read_handle(ctx, &first, ty)?;
                if !part.bound {
                    let via = self.binder_for(true, ty);
                    note!(
                        self,
                        container_binds,
                        !part.path.is_empty() && via.is_none()
                    );
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
                    note!(
                        self,
                        container_binds,
                        !part.path.is_empty() && via.is_none()
                    );
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
                    args: tuple.iter().map(value_expr).collect(),
                    sig,
                    via: None,
                };
                if !part.bound {
                    note!(self, caller_child_inputs);
                    self.bind_child_inputs(ctx, &child, None, HANDLE_DEPTH, out)?;
                }
                self.expose_child_handles(ctx, &child)?;
            }
        }
        Ok(())
    }

    /// Makes the register or wire `first` readable: in a `data` context it
    /// reads as data, or `read(first)` reads it.
    pub(super) fn read_handle(&mut self, ctx: &mut Ctx, first: &HExpr, ty: &Ty) -> Built {
        let expr = if self.tape.flag() {
            HExpr::Read(Box::new(first.clone()))
        } else {
            first.clone()
        };
        let types = self.types(ty, &ctx.envs)?;
        ctx.publish(Hw {
            expr,
            ty: Some(ty.clone()),
            types,
            mutable: false,
        });
        Ok(())
    }
}

/// The type of the resource that a binder or a list helper takes: the type
/// of its first formal, or of the elements of its list.
fn element(h: &ResHelper) -> Option<Ty> {
    match h.params.first() {
        Some((_, FTy::Reg(t) | FTy::Wire(t))) => Some(t.clone()),
        Some((_, FTy::List(l))) => match &**l {
            FTy::Reg(t) | FTy::Wire(t) => Some(t.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Whether the type holds an array: a result array, an element of a tuple,
/// or a field of a struct.
#[cfg(test)]
fn has_array(t: &FTy, structs: &[StructDef]) -> bool {
    match t {
        FTy::Array(..) => true,
        FTy::Tuple(ts) => ts.iter().any(|t| has_array(t, structs)),
        FTy::Struct(name) => structs
            .iter()
            .filter(|d| d.name == *name)
            .flat_map(|d| &d.fields)
            .any(|(_, f)| matches!(f, FieldTy::Handle(t) if has_array(t, structs))),
        _ => false,
    }
}
