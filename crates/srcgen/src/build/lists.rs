// SPDX-License-Identifier: Apache-2.0
//! Static lists: the `comptime fn` that builds a list in a `comptime for`
//! with a receiver `push`, the `let` of a list, and the `push` and `pop`
//! statements of a frame.
//!
//! A list changes only in the frame that declares it: a nested frame has
//! its own env copies, so a change there would not reach the frame after
//! it. So `Ctx::lists` names the mutable lists of the current frame only.
//! A `pop` takes only a list that is not empty in each env, and a `push`
//! only a list below `MAX_LIST`, so no statement faults.

use super::stat::{Kind, Reach, int, param_kind};
use super::{Builder, Built, COUNT, Ctx, LIST_FNS, Names};
use crate::eval::{Env, exec_static};
use crate::program::{Item, ListFn, SExpr, STy, Stmt};

impl Builder {
    /// The list builders `b<k>`, each checked on the sample.
    pub(super) fn list_fns(&mut self) -> Built {
        for k in 0..self.tape.below(LIST_FNS + 1) {
            let f = self.list_fn(k as usize);
            self.list_fns.push(f);
            self.refresh()?;
        }
        Ok(())
    }

    /// `b<k>(x0: Nat, ...) -> List[T]`. The element is a static expression
    /// of the formals and the binder `j0`; one that faults on the sample,
    /// or that is negative for a `Nat` list, takes the binder `j0`.
    fn list_fn(&mut self, k: usize) -> ListFn {
        let mut params = vec![("x0".to_owned(), STy::Nat)];
        for i in 1..=self.tape.below(3) {
            let t = if self.tape.flag() {
                STy::Bool
            } else {
                STy::Int
            };
            params.push((format!("x{i}"), t));
        }
        let elem = if self.tape.below(3) == 2 {
            STy::Nat
        } else {
            STy::Int
        };
        let names: Vec<(String, STy)> = params
            .iter()
            .cloned()
            .chain(std::iter::once(("j0".to_owned(), STy::Int)))
            .collect();
        let r = Reach {
            names: &names,
            fns: self.fns.len(),
            envs: None,
        };
        let element = self.sexpr(Kind::Int, super::stat::DEPTH, r);
        let mut f = ListFn {
            name: format!("b{k}"),
            params,
            elem,
            element,
        };
        if !self.list_sample(&f) {
            f.element = SExpr::Name("j0".to_owned());
        }
        f
    }

    /// Whether `f` builds a list on each call of the sample.
    fn list_sample(&self, f: &ListFn) -> bool {
        let mut items = self.file_items();
        items.push(Item::ListFn(f.clone()));
        Builder::sample_calls(&items, &f.name, &f.params).is_some()
    }

    /// A call of a list builder, or `list(T)`, as a list of the type
    /// `List[T]`. A call that faults in an env takes `list(T)`.
    fn list_value(&mut self, r: Reach<'_>) -> (SExpr, STy) {
        let Some(envs) = r.envs else {
            return (SExpr::NewList(STy::Int), STy::Int);
        };
        if let Some(f) = self
            .list_fns
            .get(self.tape.index(self.list_fns.len()))
            .filter(|_| self.tape.below(4) != 0)
        {
            let (name, params, elem) = (f.name.clone(), f.params.clone(), f.elem.clone());
            let count = self.number(0, COUNT);
            let rest: Vec<SExpr> = params
                .iter()
                .skip(1)
                .map(|(_, t)| self.sexpr(param_kind(t), 1, r))
                .collect();
            let call = SExpr::Call(name, std::iter::once(count).chain(rest).collect());
            note!(self, list_calls);
            if self.holds(&call, envs, |_| true) {
                return (call, elem);
            }
            note!(self, list_call_fallbacks);
            return (SExpr::NewList(elem.clone()), elem);
        }
        let elem = if self.tape.below(3) == 2 {
            STy::Nat
        } else {
            STy::Int
        };
        (SExpr::NewList(elem.clone()), elem)
    }

    /// `let xs: List[T] = ...;` or `let mut xs: List[T] = ...;`. A mutable
    /// list is open to `push` and `pop` in this frame.
    pub(super) fn list_let(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let (value, elem) = self.list_value(self.reach(ctx));
        let ty = STy::List(Box::new(elem));
        let name = names.fresh("s");
        let mutable = self.tape.flag();
        let stmt = if mutable {
            Stmt::MutLet(name.clone(), ty.clone(), value)
        } else {
            Stmt::StaticLet(name.clone(), ty.clone(), value)
        };
        self.run(ctx, &stmt)?;
        ctx.statics.push((name.clone(), ty.clone()));
        out.push(stmt);
        if self.tape.flag() {
            self.list_exit_let(ctx, names, out, &name, &ty);
        }
        if mutable {
            ctx.lists.push(name);
            // A fresh mutable list gets a few changes at once, so that
            // most of them are not empty at the `pop`.
            for _ in 0..self.tape.below(3) {
                self.push_stmt(ctx, out);
            }
            if self.tape.flag() {
                self.pop_stmt(ctx, names, out);
            }
        }
        Ok(())
    }

    /// `let s: Int = xs[i];` or `let s: Int = len(xs);`: an exit from the
    /// list that the frame just declared, so that its length and its elements
    /// reach a static position.
    fn list_exit_let(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
        list: &str,
        ty: &STy,
    ) {
        let reach = self.reach(ctx);
        let base = SExpr::Name(list.to_owned());
        let Some(value) = self.descend(base, ty, Kind::Int, super::stat::DEPTH, reach) else {
            return;
        };
        let name = names.fresh("s");
        let stmt = Stmt::StaticLet(name.clone(), STy::Int, value);
        if self.try_run(ctx, &stmt) {
            ctx.statics.push((name, STy::Int));
            out.push(stmt);
        }
    }

    /// `xs.push(e);` on a mutable list of the frame with room for one more
    /// element in each env.
    pub(super) fn push_stmt(&mut self, ctx: &mut Ctx, out: &mut Vec<Stmt>) {
        let Some(list) = ctx.lists.get(self.tape.index(ctx.lists.len())).cloned() else {
            return;
        };
        let e = self.sexpr(Kind::Int, super::stat::DEPTH, self.reach(ctx));
        let stmt = Stmt::Push(list.clone(), e);
        if self.try_run(ctx, &stmt) {
            note!(self, pushes);
            ctx.forget(&list);
            out.push(stmt);
            return;
        }
        note!(self, push_fallbacks);
        let stmt = Stmt::Push(list.clone(), int(0));
        if self.try_run(ctx, &stmt) {
            note!(self, pushes);
            ctx.forget(&list);
            out.push(stmt);
        }
    }

    /// `let s: Int = xs.pop();` on a mutable list of the frame that is not
    /// empty in any env. The scan starts at a random list and takes the
    /// first list that has an element.
    pub(super) fn pop_stmt(&mut self, ctx: &mut Ctx, names: &mut Names, out: &mut Vec<Stmt>) {
        let start = self.tape.index(ctx.lists.len());
        let name = names.fresh("s");
        for k in 0..ctx.lists.len() {
            let Some(list) = ctx.lists.get((start + k) % ctx.lists.len()).cloned() else {
                return;
            };
            let stmt = Stmt::PopLet(name.clone(), list.clone());
            if self.try_run(ctx, &stmt) {
                note!(self, pops);
                ctx.forget(&list);
                ctx.statics.push((name, STy::Int));
                out.push(stmt);
                return;
            }
        }
        if !ctx.lists.is_empty() {
            note!(self, pop_fallbacks);
        }
    }

    /// The static statement `s` on each env of `ctx`; a fault is a bug.
    pub(super) fn run(&self, ctx: &mut Ctx, s: &Stmt) -> Built {
        for env in &mut ctx.envs {
            exec_static(s, env, &self.scope)?;
        }
        Ok(())
    }

    /// `s` on each env of `ctx`, which stay unchanged if one faults.
    pub(super) fn try_run(&self, ctx: &mut Ctx, s: &Stmt) -> bool {
        let mut envs: Vec<Env> = ctx.envs.clone();
        let ok = envs
            .iter_mut()
            .all(|env| exec_static(s, env, &self.scope).is_ok());
        if ok {
            ctx.envs = envs;
        }
        ok
    }

    /// A list as the `eval` probe: a call of a list builder.
    pub(super) fn list_probe(&mut self) -> Option<SExpr> {
        let envs = [Env::default()];
        let names: Vec<(String, STy)> = Vec::new();
        let r = Reach {
            names: &names,
            fns: 0,
            envs: Some(&envs),
        };
        let f = self.list_fns.get(self.tape.index(self.list_fns.len()))?;
        let (name, params) = (f.name.clone(), f.params.clone());
        let count = self.number(0, COUNT);
        let rest: Vec<SExpr> = params
            .iter()
            .skip(1)
            .map(|(_, t)| self.sexpr(param_kind(t), 1, r))
            .collect();
        Some(SExpr::Call(
            name,
            std::iter::once(count).chain(rest).collect(),
        ))
    }
}
