// SPDX-License-Identifier: Apache-2.0
//! The statements of a module body (Lean `hwStmt`): `reg`, `wire`, `mem`, `instance`, and `:=`,
//! with the checks that a statement in a `fn` runs before it.

use super::bind::Target;
use super::design::{ChildDecl, Mem, RegDecl};
use crate::Code;
use crate::agg::Agg;
use crate::eval::typed::Whole;
use crate::eval::{Evaluator, Mode, Res, Slot, fail, need};
use crate::hw::{Handle, Kind, Seen, Val};
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Expr, Ident, Item, PortForm, Pos, Stmt, TypeExpr};
use resolve::Target as Ref;

impl Evaluator<'_> {
    /// The two checks of a declaration or a `:=` statement before its module steps, with no
    /// charge (section 6.2). Under a guard it is `S016`, and the text names the function of the
    /// outermost call under the guard. In the static mode it is `S011`. A module body has
    /// neither.
    pub(in crate::eval) fn hardware_checks(&self, pos: Pos, s: &Stmt) -> Res<()> {
        let here = self.item_name(self.item);
        if let Some(guard) = self.guard {
            let callee = self.item_name(guard.callee.unwrap_or(self.item));
            return fail(Code::S016, pos, guard.effect(callee));
        }
        let kind = match s {
            Stmt::Reg { .. } => "register",
            Stmt::Wire { .. } => "wire",
            Stmt::Mem { .. } => "memory",
            Stmt::Inst { .. } => "instance",
            Stmt::Input { .. } => "input",
            Stmt::Output { .. } => "output",
            _ => "`:=`",
        };
        match self.mode {
            Some(Mode::Static(m)) => fail(
                Code::S011,
                pos,
                format!(
                    "the `comptime fn` `{}` makes no hardware, but its call reaches this {kind} \
                     in `{here}`; call `{here}` from a `fn` or a module body",
                    self.item_name(m)
                ),
            ),
            Some(Mode::Eval) => fail(
                Code::S011,
                pos,
                format!(
                    "the `eval` command makes no hardware, but its expression reaches this \
                     {kind} in `{here}`; evaluate an expression that makes no hardware, or \
                     elaborate a module that calls `{here}`"
                ),
            ),
            None => Ok(()),
        }
    }

    /// A statement of a module body that makes hardware. Its statement charge is paid.
    pub(in crate::eval) fn module_stmt(&mut self, s: &Stmt) -> Res<()> {
        match s {
            Stmt::Input {
                pos,
                name,
                form,
                ty,
            }
            | Stmt::Output {
                pos,
                name,
                form,
                ty,
            } => {
                let input = matches!(s, Stmt::Input { .. });
                if let PortForm::Indexed(k) = form {
                    return self.entry_decl(*pos, input, name, k, ty);
                }
                let tid = self.type_expr(ty)?;
                let t = self.data_type(*pos, tid)?;
                let id = self.decl(name)?;
                let v = match form {
                    PortForm::Keyed(k) => self.keyed_port(*pos, input, id, (t, tid), k)?,
                    _ => self.port(*pos, input, self.sym(id), (t, tid), None)?,
                };
                self.bind(
                    id,
                    Slot {
                        ty: Some(tid),
                        mutable: false,
                        value: v,
                    },
                );
            }
            Stmt::Reg {
                pos,
                name,
                ty,
                init,
            } => self.reg_stmt(*pos, name, ty, init)?,
            Stmt::Mem {
                pos,
                name,
                word,
                depth,
            } => self.mem_stmt(*pos, name, word, depth)?,
            Stmt::Wire { pos, name, ty } => {
                let tid = self.type_expr(ty)?;
                self.data_type(*pos, tid)?;
                let id = self.decl(name)?;
                let path = self.fresh(id);
                #[cfg(test)]
                self.elab.work.body.wires.push(path);
                let w = self.resource(Kind::Wire, path, tid, *pos, (self.sym(id), None), None);
                self.bind(
                    id,
                    Slot {
                        ty: Some(tid),
                        mutable: false,
                        value: w,
                    },
                );
            }
            Stmt::Connect { pos, target, value } => {
                let t = self.connect_target(target)?;
                let o = self.eval(value)?;
                let o = need(value, o)?;
                let ty = match &t {
                    Target::Own { ty, .. } => *ty,
                    Target::Child { port, .. } => port.ty,
                };
                let copies = o.is_ref();
                let v = self.typed_use(*pos, ty, copies, o, Whole)?;
                let v = self.sink_value(*pos, ty, v)?;
                self.bind_target(*pos, t, v);
            }
            Stmt::Inst {
                pos,
                name,
                module,
                args,
            } => self.inst_stmt(*pos, name, module, args)?,
            _ => {}
        }
        Ok(())
    }

    /// The value of a `:=` binding of the type `t` at `pos`, after its typed use. A static
    /// scalar becomes a hardware constant. A static value of another type is empty or has only
    /// static leaves, so it stays static. A hardware value and a hardware aggregate stay.
    pub(super) fn sink_value(&mut self, pos: Pos, t: TyId, v: Val) -> Res<Agg> {
        match v {
            Val::Static(x) if matches!(self.tys.get(t), Ty::Bool | Ty::UInt(_) | Ty::SInt(_)) => {
                Ok(Agg::Hw(self.lit(pos, x)?))
            }
            Val::Static(x) => Ok(Agg::Static(x)),
            Val::Hw(h) => Ok(Agg::Hw(h)),
            Val::Agg(a) => Ok(*a),
            v @ (Val::Handle(_) | Val::Pending(..)) => fail(
                Code::S010,
                pos,
                format!("{} is not data", self.text(v.seen())),
            ),
        }
    }

    /// A `reg` statement. A register in a combinational module is `S017` before its type.
    pub(super) fn reg_stmt(
        &mut self,
        pos: Pos,
        name: &Ident,
        ty: &TypeExpr,
        init: &Expr,
    ) -> Res<()> {
        if self.elab.work.body.domain.is_none() {
            return fail(
                Code::S017,
                pos,
                "a combinational module has no register; remove `domains()` from the module, or \
                 move the register to a clocked module"
                    .to_owned(),
            );
        }
        let tid = self.type_expr(ty)?;
        let ty = self.data_type(pos, tid)?;
        let out = self.eval(init)?;
        let out = need(init, out)?;
        self.copy(pos, &out)?;
        let out = self.settle(pos, tid, out)?;
        let init = self.conform(pos, tid, out)?;
        let id = self.decl(name)?;
        let path = self.fresh(id);
        self.elab.work.body.regs.push(RegDecl {
            path,
            ty: ty.clone(),
            init,
            pos,
        });
        let reg = self.resource(Kind::Reg, path, tid, pos, (self.sym(id), None), None);
        self.bind(
            id,
            Slot {
                ty: Some(tid),
                mutable: false,
                value: reg,
            },
        );
        Ok(())
    }

    /// A `mem` statement. Each error is at the statement: a combinational module (`S017`), the
    /// word type, then the depth. No `[T; N]` type is made, so the depth adds no metadata
    /// charge. The name binds a memory handle, which is never data.
    pub(super) fn mem_stmt(
        &mut self,
        pos: Pos,
        name: &Ident,
        word: &TypeExpr,
        depth: &Expr,
    ) -> Res<()> {
        if self.elab.work.body.domain.is_none() {
            return fail(
                Code::S017,
                pos,
                "a combinational module has no memory; remove `domains()` from the module, or \
                 move the memory to a clocked module"
                    .to_owned(),
            );
        }
        let tid = self.type_expr(word)?;
        self.mem_word(pos, tid)?;
        let out = self.structural(|ev| {
            let out = ev.eval(depth)?;
            need(depth, out)
        })?;
        let depth = self.mem_depth(pos, &out)?;
        let id = self.decl(name)?;
        let path = self.fresh(id);
        let sym = self.sym(id);
        let number = self.elab.work.body.mems.len();
        self.elab.work.body.mems.push(Mem {
            name: sym,
            path,
            word: tid,
            depth,
            pos,
            read: None,
            write: None,
            read_at: None,
            write_at: None,
        });
        self.bind(
            id,
            Slot {
                ty: None,
                mutable: false,
                value: Val::Handle(Handle::Mem(number)),
            },
        );
        Ok(())
    }

    /// An `instance` statement.
    pub(super) fn inst_stmt(
        &mut self,
        pos: Pos,
        name: &Ident,
        module: &Ident,
        args: &[Expr],
    ) -> Res<()> {
        let i = match self.file.target(module.id) {
            Some(Ref::Decl(id)) => self.items.get(&id).copied(),
            _ => None,
        }
        .unwrap_or(usize::MAX);
        let args = self.arguments(pos, i, args)?;
        let Some(Item::Module {
            name: m, domains, ..
        }) = self.file.ast().get(i)
        else {
            return fail(Code::S010, pos, "an instance needs a module".to_owned());
        };
        let clocked = domains.as_ref().is_none_or(|d| !d.is_empty());
        if self.elab.work.body.domain.is_none() && clocked {
            return fail(
                Code::S017,
                pos,
                format!(
                    "a combinational module has no clocked child `{}`; remove `domains()` from \
                     the module, or move the instance to a clocked module",
                    m.name
                ),
            );
        }
        // The converted arguments paid for their sizes, so the type adds no charge.
        let values: Vec<Value> = args.iter().map(|(_, v)| v.clone()).collect();
        let done = self.instantiate(pos, i, args)?;
        let ty = self.tys.instance(i, &m.name, values);
        let id = self.decl(name)?;
        let path = self.fresh(id);
        let k = self.elab.work.body.children.len();
        self.elab.work.body.children.push(ChildDecl {
            path,
            inst: done,
            pos,
            name: name.name.clone(),
        });
        self.elab.work.bound.push(0);
        self.bind(
            id,
            Slot {
                ty: None,
                mutable: false,
                value: Val::Handle(Handle::Inst {
                    id: k,
                    path,
                    inst: done,
                    ty,
                }),
            },
        );
        Ok(())
    }

    /// The target of a `:=` binding: a register, a wire, an own output, or a child input. A handle
    /// alias and the steps of `target_part` can select it. Each other part is `S017` at the start
    /// of the target. `S018` counts the target by its resource.
    pub(super) fn connect_target(&mut self, e: &Expr) -> Res<Target> {
        let part = self.target_part(e)?;
        match self.store.seen(&part) {
            Seen::Handle(Handle::Res { kind, id, ty, path }) => Ok(Target::Own {
                kind: *kind,
                id: *id,
                ty: *ty,
                path: *path,
            }),
            Seen::Handle(Handle::Input { inst, path, port }) => Ok(Target::Child {
                inst: *inst,
                path: *path,
                port: port.clone(),
            }),
            seen => fail(Code::S017, e.pos(), Self::kind_text(&self.about(seen))),
        }
    }

    /// A port, a register, and a wire have a hardware data type (section 5.1), also an
    /// aggregate and an empty one. The metadata tells, so a function type at any depth is
    /// `S010` with no walk.
    pub(super) fn data_type(&self, pos: Pos, t: TyId) -> Res<Ty> {
        self.not_handle(pos, t)?;
        if self.tys.meta(t).data {
            Ok(self.tys.get(t).clone())
        } else {
            fail(
                Code::S010,
                pos,
                format!(
                    "a port, a register, and a wire need a hardware data type, not `{}`; use a \
                     fixed-width type, for example `UInt[8]`",
                    self.tys.text(t)
                ),
            )
        }
    }
}
