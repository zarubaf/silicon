// SPDX-License-Identifier: Apache-2.0
//! Lists of handles (front-end spec 5.6, "Resource-typed formals and
//! results"), and the helpers that bind their elements.
//!
//! A group is four statements of a module frame, made together:
//!
//! ```text
//! let mut G0 = list(Reg[UInt[8]]);
//! comptime for j0 in 0..3 { reg r0: UInt[8] = 0; G0.push(r0); }
//! H1(G0, x);
//! ```
//!
//! `H1` binds each element `a0[j]` in a loop over `0..len(a0)`. The group
//! is atomic: its loop declares each resource and gives it to the list, and
//! the call binds it, so no resource waits and no frame binds an element
//! (`S018`). An element is a `reg`, a `wire`, the result of a helper that
//! returns one such resource unbound, or the input of a child. A list holds
//! one handle type (`S010`), and the loop bounds are literals, so every
//! module context builds a list of one length (`S011`). The elements read
//! as data after the call.

use super::handles::{ListOf, ResHelper, Role, literal};
use super::{Builder, Built, Ctx, Module};
use crate::eval::Fault;
use crate::program::{FTy, HBin, HExpr, Place, Radix, SExpr, Stmt, Ty};
use num_bigint::BigInt;

/// The most elements of a list.
pub(super) const HANDLE_LEN: u32 = 4;

impl Builder {
    /// A helper that binds the elements of a list: `kind` 0 for registers,
    /// 1 for wires, and 2 or 3 for child inputs. Without a later module
    /// that has an input of a closed type, it takes registers.
    pub(super) fn list_helper(&mut self, name: String, kind: u32) -> ResHelper {
        let input = if kind >= 2 {
            self.input_candidate()
        } else {
            None
        };
        let (of, elem) = if let Some((module, port, ty)) = input {
            let of = ListOf::Input {
                module,
                port,
                ty: ty.clone(),
            };
            (of, FTy::Input(ty))
        } else {
            let w = self.pick(&[4, 8]);
            let ty = Ty::UInt(literal(w));
            if kind == 1 {
                (ListOf::Wire(ty.clone()), FTy::Wire(ty))
            } else {
                (ListOf::Reg(ty.clone()), FTy::Reg(ty))
            }
        };
        let ty = match &of {
            ListOf::Reg(t) | ListOf::Wire(t) | ListOf::Input { ty: t, .. } => t.clone(),
        };
        // `a0[j0] := x1 ^ T(j0)` for a type that holds the index.
        let held = HExpr::Name("x1".to_owned());
        let value = match &ty {
            Ty::UInt(SExpr::Int(w, _)) if *w >= BigInt::from(4) => HExpr::Binary(
                HBin::Xor,
                Box::new(held),
                Box::new(HExpr::Make(ty.clone(), SExpr::Name("j0".to_owned()))),
            ),
            _ => held,
        };
        let element = HExpr::Index(
            Box::new(HExpr::Name("a0".to_owned())),
            SExpr::Name("j0".to_owned()),
        );
        let len = SExpr::Len(Box::new(SExpr::Name("a0".to_owned())));
        let bind = Stmt::For(
            "j0".to_owned(),
            SExpr::Int(BigInt::ZERO, Radix::Dec),
            len,
            vec![Stmt::Connect(Place::Path(element), value)],
        );
        ResHelper::binder(
            name,
            vec![
                ("a0".to_owned(), FTy::List(Box::new(elem))),
                ("x1".to_owned(), FTy::Data(ty)),
            ],
            FTy::Unit,
            vec![bind],
            HExpr::Unit,
            Role::List(of),
        )
    }

    /// Whether the program has a helper that binds a list.
    pub(super) fn has_list_helper(&self) -> bool {
        self.res_helpers
            .iter()
            .any(|h| matches!(h.role, Role::List(_)))
    }

    /// A group of one of the helpers that fit the module. A module that no
    /// helper of lists fits makes nothing.
    pub(super) fn list_group(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let usable: Vec<usize> = (0..self.res_helpers.len())
            .filter(|&i| self.list_fits(m, i))
            .collect();
        let Some(&i) = usable.get(self.tape.index(usable.len())) else {
            return Ok(());
        };
        self.list_group_of(ctx, m, i, out)
    }

    /// Whether the helper `i` binds a list that the module can make: a
    /// register needs a clocked module, and a child needs a later module.
    fn list_fits(&self, m: &Module, i: usize) -> bool {
        match self.res_helpers.get(i).map(|h| &h.role) {
            Some(Role::List(ListOf::Reg(_))) => m.clocked,
            Some(Role::List(ListOf::Wire(_))) => true,
            Some(Role::List(ListOf::Input { module, .. })) => self.reachable(m, *module),
            _ => false,
        }
    }

    /// A group: the list, the loop that fills it, and the call of the helper
    /// `i` that binds it. A module that the helper does not fit makes
    /// nothing.
    pub(super) fn list_group_of(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        i: usize,
        out: &mut Vec<Stmt>,
    ) -> Built {
        if !self.list_fits(m, i) {
            return Ok(());
        }
        let h = self.res_helpers.get(i).cloned().ok_or(Fault::Type)?;
        called!(self, ctx, i);
        let Role::List(of) = h.role else {
            return Err(Fault::Type);
        };
        let len = self.tape.between(1, HANDLE_LEN);
        let list = m.names.fresh("G");
        let binder = m.names.fresh("j");
        let (lo, hi) = (literal(0), literal(len));
        let Some(mut inner) = self.iterations(ctx, &binder, &lo, &hi)? else {
            return Ok(());
        };
        self.decls += inner.envs.len();
        let mut body = Vec::new();
        let (elem, readable) = match &of {
            ListOf::Reg(ty) => {
                self.list_resource(&mut inner, m, (&list, ty, true), &mut body)?;
                (FTy::Reg(ty.clone()), Some(ty.clone()))
            }
            ListOf::Wire(ty) => {
                self.list_resource(&mut inner, m, (&list, ty, false), &mut body)?;
                (FTy::Wire(ty.clone()), Some(ty.clone()))
            }
            ListOf::Input { module, port, ty } => {
                let child = self.declare_child(&mut inner, m, *module, &mut body)?;
                self.bind_child_inputs(&mut inner, &child, Some(port), &mut body)?;
                let first = HExpr::Field(child.name, port.clone());
                body.push(Stmt::HPush(list.clone(), first));
                (FTy::Input(ty.clone()), None)
            }
        };
        out.push(Stmt::HList(list.clone(), elem));
        out.push(Stmt::For(binder, lo, hi, body));
        let call = self.binder_call(ctx, i, HExpr::Name(list.clone()))?;
        out.push(call);
        note!(self, list_groups);
        note!(self, list_input_groups, matches!(of, ListOf::Input { .. }));
        if let Some(ty) = readable {
            for k in 0..len {
                let element = HExpr::Index(Box::new(HExpr::Name(list.clone())), literal(k));
                self.read_handle(ctx, &element, &ty)?;
            }
        }
        Ok(())
    }

    /// One iteration of a group of registers or wires: a `reg` or `wire`,
    /// or a call of a helper that returns one unbound, and its push.
    fn list_resource(
        &mut self,
        inner: &mut Ctx,
        m: &mut Module,
        (list, ty, reg): (&str, &Ty, bool),
        body: &mut Vec<Stmt>,
    ) -> Built {
        let declarers: Vec<usize> = self
            .usable_declarers(m)
            .into_iter()
            .filter(|&d| self.returns_unbound(d, ty, reg))
            .collect();
        let name = if self.tape.flag() && !declarers.is_empty() {
            let d = declarers[self.tape.index(declarers.len())];
            called!(self, inner, d);
            let (callee, args) = self.data_args(inner, d, 0)?;
            let name = m.names.fresh("t");
            body.push(Stmt::Let {
                name: name.clone(),
                mutable: false,
                ty: None,
                value: HExpr::Call(callee, args),
            });
            name
        } else {
            let scalar = self.scalar(ty)?;
            if reg {
                let name = m.names.fresh("r");
                let reset = self.short(scalar);
                body.push(Stmt::Reg(name.clone(), ty.clone(), reset));
                name
            } else {
                let name = m.names.fresh("w");
                body.push(Stmt::Wire(name.clone(), ty.clone()));
                name
            }
        };
        body.push(Stmt::HPush(list.to_owned(), HExpr::Name(name)));
        Ok(())
    }
}
