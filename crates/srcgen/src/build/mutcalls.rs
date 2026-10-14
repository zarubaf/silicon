// SPDX-License-Identifier: Apache-2.0
//! Functions with a `mut` formal, and the calls that write back to a root.
//!
//! A `comptime fn` has a `mut a0: Int` or `mut a0: List[Int]` formal; a
//! helper `fn` has one `mut` hardware formal. A call is a statement
//! `let r = f(root, e);` or `let r = root.f(e);`, and `root` is a `let mut`
//! of exactly the type of the formal. The explicit arguments are static or
//! hardware expressions that name no call with a `mut` formal, so no
//! mutation of `root` is in the window of `root` (`S008`). A call stands
//! at a statement of a frame, never in a hardware arm or a type (`S016`).

use super::hw::Want;
use super::stat::{Kind, Reach, int};
use super::{Builder, Built, Ctx, Helper, Hw, MUT_FNS, MUT_HELPERS, Module, Names};
use crate::eval::{Env, Value};
use crate::program::{HExpr, Item, MutFn, SExpr, STy, Stmt};

/// The values of the root `a0` that the sample of a function takes.
fn sample_roots(root: &STy) -> Vec<Value> {
    match root {
        STy::List(_) => vec![
            Value::List(STy::Int, Vec::new()),
            Value::List(STy::Int, (1..=3).map(|n| Value::Int(n.into())).collect()),
        ],
        _ => super::SAMPLE_INTS
            .iter()
            .map(|n| Value::Int((*n).into()))
            .collect(),
    }
}

impl Builder {
    /// The functions `k<n>`, each checked on the sample.
    pub(super) fn mut_fns(&mut self) -> Built {
        for k in 0..self.tape.below(MUT_FNS + 1) {
            let f = self.mut_fn(k as usize);
            self.mut_fns.push(f);
            self.refresh()?;
        }
        Ok(())
    }

    /// `k<n>(mut a0, x1: Int) -> Int`. An update or a result that faults on
    /// the sample takes `x1`.
    fn mut_fn(&mut self, k: usize) -> MutFn {
        let root = if self.tape.flag() {
            STy::List(Box::new(STy::Int))
        } else {
            STy::Int
        };
        let mut names = vec![("x1".to_owned(), STy::Int)];
        let mut result_names = names.clone();
        if root == STy::Int {
            names.push(("a0".to_owned(), STy::Int));
            result_names.push(("a0".to_owned(), STy::Int));
        }
        names.extend(self.const_names());
        result_names.extend(self.const_names());
        let fns = self.fns.len();
        let reach = |names| Reach {
            names,
            fns,
            envs: None,
        };
        let update = self.sexpr(Kind::Int, super::stat::DEPTH, reach(&names));
        let over_result = |b: &mut Builder| {
            let e = b.sexpr(Kind::Int, super::stat::DEPTH, reach(&result_names));
            if root == STy::Int {
                e
            } else {
                // The length of the list after the push.
                let len = SExpr::Len(Box::new(SExpr::Name("a0".to_owned())));
                super::stat::bin(crate::program::SBin::Add, e, len)
            }
        };
        let ret = over_result(self);
        // One function in two is effectful: it runs a `diagnostic`.
        let diag = (self.tape.below(2) == 0).then(|| (self.next_message(), over_result(self)));
        let mut f = MutFn {
            name: format!("k{k}"),
            root,
            update,
            ret,
            diag,
        };
        if !self.mut_sample(&f) {
            f.update = SExpr::Name("x1".to_owned());
            f.ret = SExpr::Name("x1".to_owned());
            if let Some((_, value)) = &mut f.diag {
                *value = SExpr::Name("x1".to_owned());
            }
        }
        if f.diag.is_some() {
            note!(self, effectful_fns);
        }
        f
    }

    /// Whether `f` runs on each root and argument of the sample.
    fn mut_sample(&self, f: &MutFn) -> bool {
        let mut items = self.file_items();
        items.push(Item::MutFn(f.clone()));
        let Ok(scope) = crate::eval::Scope::new(&items) else {
            return false;
        };
        for root in sample_roots(&f.root) {
            for x in super::SAMPLE_INTS {
                let mut env = Env::default();
                env.statics.insert("r".to_owned(), root.clone());
                let call = Stmt::MutCall {
                    name: "t".to_owned(),
                    root: "r".to_owned(),
                    f: f.name.clone(),
                    args: vec![int(x)],
                    receiver: false,
                };
                if crate::eval::exec_static(&call, &mut env, &scope).is_err() {
                    return false;
                }
            }
        }
        true
    }

    /// A call of a `comptime fn` with a `mut` formal on a root of this
    /// frame, or on a fresh `let mut`.
    pub(super) fn static_mut_call(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let Some(f) = self
            .mut_fns
            .get(self.tape.index(self.mut_fns.len()))
            .cloned()
        else {
            return Ok(());
        };
        let root = self.static_root(ctx, names, out, &f.root)?;
        let result = names.fresh("s");
        // A call through a function value is a plain call.
        let (callee, receiver) = self.mut_callee(&f.name);
        for arg in [self.sexpr(Kind::Int, 1, self.reach(ctx)), int(0)] {
            let stmt = Stmt::MutCall {
                name: result.clone(),
                root: root.clone(),
                f: callee.clone(),
                args: vec![arg],
                receiver,
            };
            if self.try_run(ctx, &stmt) {
                note!(self, mut_calls);
                ctx.forget(&root);
                if f.diag.is_some() {
                    note!(self, effectful_calls);
                }
                ctx.statics.push((result, STy::Int));
                out.push(stmt);
                return Ok(());
            }
            note!(self, mut_call_fallbacks);
        }
        Ok(())
    }

    /// A mutable root of the type `ty` in this frame, or a new one.
    fn static_root(
        &mut self,
        ctx: &mut Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
        ty: &STy,
    ) -> Built<String> {
        let roots = if *ty == STy::Int {
            &ctx.counters
        } else {
            &ctx.lists
        };
        let have: Vec<&String> = roots
            .iter()
            .filter(|n| ctx.statics.iter().any(|(m, t)| m == *n && t == ty))
            .collect();
        if let Some(n) = have
            .get(self.tape.index(have.len()))
            .filter(|_| self.tape.below(4) != 0)
        {
            return Ok((*n).clone());
        }
        let name = names.fresh("s");
        let value = if *ty == STy::Int {
            self.evaluated(Kind::Int, self.reach(ctx), &ctx.envs).0
        } else {
            SExpr::NewList(STy::Int)
        };
        let stmt = Stmt::MutLet(name.clone(), ty.clone(), value);
        self.run(ctx, &stmt)?;
        ctx.statics.push((name.clone(), ty.clone()));
        if *ty == STy::Int {
            ctx.counters.push(name.clone());
        } else {
            ctx.lists.push(name.clone());
        }
        out.push(stmt);
        Ok(name)
    }

    /// The helpers `g<n>(mut a0: T, x1: U) -> V`.
    pub(super) fn mut_helpers(&mut self) -> Built {
        for k in 0..self.tape.below(MUT_HELPERS + 1) {
            let h = self.mut_helper(k as usize)?;
            self.mut_helpers.push(h);
        }
        Ok(())
    }

    /// `a0 = ...;` in the body, then a result over `a0` and `x1`. It calls
    /// only helpers without a `mut` formal.
    fn mut_helper(&mut self, k: usize) -> Built<Helper> {
        let mut names = Names::default();
        let root = self.data_ty();
        let extra = self.data_ty();
        let ret = self.data_ty();
        let params = vec![
            ("a0".to_owned(), root.0.clone(), root.1),
            ("x1".to_owned(), extra.0.clone(), extra.1),
        ];
        let mut ctx = Ctx {
            envs: vec![Env::default()],
            statics: self.const_names(),
            hw: vec![
                Hw {
                    expr: HExpr::Name("a0".to_owned()),
                    ty: Some(root.0.clone()),
                    types: vec![root.1],
                    mutable: true,
                },
                Hw {
                    expr: HExpr::Name("x1".to_owned()),
                    ty: Some(extra.0.clone()),
                    types: vec![extra.1],
                    mutable: false,
                },
            ],
            helpers: self.helpers.len(),
            lists: Vec::new(),
            counters: Vec::new(),
        };
        let mut body = Vec::new();
        for _ in 0..self.tape.below(2) {
            self.binding(&mut ctx, &mut names, &mut body, false)?;
        }
        let want = Want {
            types: vec![root.1],
            ty: Some(root.0),
        };
        body.push(Stmt::Assign(
            "a0".to_owned(),
            self.value(&ctx, &want, super::hw::DEPTH),
        ));
        let want = Want {
            types: vec![ret.1],
            ty: Some(ret.0.clone()),
        };
        let result = self.value(&ctx, &want, super::hw::DEPTH);
        Ok(Helper {
            name: format!("g{k}"),
            params,
            mut_first: true,
            ret,
            body,
            result,
        })
    }

    /// `let l = g(v, e);` or `let l = v.g(e);` on a mutable hardware name
    /// `v` of the type of the first formal, or on a fresh `let mut`.
    pub(super) fn hw_mut_call(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let Some(h) = self
            .mut_helpers
            .get(self.tape.index(self.mut_helpers.len()))
            .cloned()
        else {
            return Ok(());
        };
        let envs = ctx.envs.len();
        let (root_ty, root_scalar) = h
            .params
            .first()
            .map(|(_, t, s)| (t.clone(), *s))
            .ok_or(crate::eval::Fault::Type)?;
        let (extra_ty, extra_scalar) = h
            .params
            .get(1)
            .map(|(_, t, s)| (t.clone(), *s))
            .ok_or(crate::eval::Fault::Type)?;
        let root_want = Want {
            types: vec![root_scalar; envs],
            ty: Some(root_ty.clone()),
        };
        let have: Vec<&Hw> = ctx
            .hw
            .iter()
            .filter(|x| x.mutable && x.types == root_want.types)
            .collect();
        let existing = have
            .get(self.tape.index(have.len()))
            .filter(|_| self.tape.below(4) != 0)
            .and_then(|x| match &x.expr {
                HExpr::Name(n) => Some(n.clone()),
                _ => None,
            });
        let root = if let Some(n) = existing {
            n
        } else {
            let name = m.names.fresh("v");
            let value = self.value(ctx, &root_want, super::hw::DEPTH);
            out.push(Stmt::Let {
                name: name.clone(),
                mutable: true,
                ty: Some(root_ty.clone()),
                value,
            });
            ctx.hw.push(Hw {
                expr: HExpr::Name(name.clone()),
                ty: Some(root_ty),
                types: root_want.types.clone(),
                mutable: true,
            });
            name
        };
        let extra = Want {
            types: vec![extra_scalar; envs],
            ty: Some(extra_ty),
        };
        let arg = self.value(ctx, &extra, super::hw::DEPTH);
        let value = if self.tape.flag() {
            note!(self, hw_mut_receivers);
            HExpr::Receiver(Box::new(HExpr::Name(root)), h.name.clone(), vec![arg])
        } else {
            HExpr::Call(h.name.clone(), vec![HExpr::Name(root), arg])
        };
        note!(self, hw_mut_calls);
        let name = m.names.fresh("l");
        out.push(Stmt::Let {
            name: name.clone(),
            mutable: false,
            ty: None,
            value,
        });
        ctx.hw.push(Hw {
            expr: HExpr::Name(name),
            ty: Some(h.ret.0),
            types: vec![h.ret.1; envs],
            mutable: false,
        });
        Ok(())
    }
}
