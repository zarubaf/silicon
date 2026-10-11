// SPDX-License-Identifier: Apache-2.0
//! Instances: the choice of a child, its arguments, and the argument
//! tuples that become the contexts of the child.

use super::hw::Want;
use super::stat::value_expr;
use super::{Builder, Built, CONTEXTS, Ctx, Hw, Module};
use crate::r#gen::eval::{Env, Fault, Value};
use crate::r#gen::program::{HExpr, Place, SExpr, Stmt};

impl Builder {
    /// Whether module `m` can instantiate module `j`: a later module, and a
    /// combinational parent takes only combinational children.
    pub(super) fn reachable(&self, m: &Module, j: usize) -> bool {
        j > m.index && (m.clocked || self.sigs.get(j).is_some_and(|s| !s.clocked))
    }

    /// An instance of a random child, if one is reachable.
    pub(super) fn instance(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        out: &mut Vec<Stmt>,
    ) -> Built<bool> {
        let children: Vec<usize> = (m.index + 1..self.sigs.len())
            .filter(|&j| self.reachable(m, j))
            .collect();
        let Some(&j) = children.get(self.tape.index(children.len())) else {
            return Ok(false);
        };
        self.instantiate(ctx, m, j, out)?;
        Ok(true)
    }

    /// `instance u = M<j>(args);` and the `:=` of each child input.
    pub(super) fn instantiate(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        j: usize,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let sig = self.sigs.get(j).cloned().ok_or(Fault::Type)?;
        let mut args = Vec::new();
        for (_, t) in &sig.params {
            args.push(self.argument(*t, self.reach(ctx), &ctx.envs));
        }
        let tuples = self.tuples(j, &mut args, &ctx.envs)?;
        let name = m.names.fresh("u");
        out.push(Stmt::Instance(name.clone(), sig.name.clone(), args));
        let envs: Vec<Env> = tuples.iter().map(|a| Env::of(&sig.params, a)).collect();
        for (p, t) in &sig.inputs {
            let types = self.types(t, &envs)?;
            let value = self.driver(ctx, &Want { types, ty: None });
            let place = Place::Field(name.clone(), p.clone());
            out.push(Stmt::Connect(place, value));
        }
        for (q, t) in &sig.outputs {
            let types = self.types(t, &envs)?;
            ctx.hw.push(Hw {
                expr: HExpr::Field(name.clone(), q.clone()),
                ty: None,
                types,
                mutable: false,
            });
        }
        Ok(())
    }

    /// The argument tuple of each env, recorded as contexts of module `j`.
    /// When `j` would pass `CONTEXTS` tuples, the arguments become the
    /// literals of a tuple that it has.
    fn tuples(&mut self, j: usize, args: &mut Vec<SExpr>, envs: &[Env]) -> Built<Vec<Vec<Value>>> {
        let columns: Vec<Vec<Value>> = args
            .iter()
            .map(|a| self.values(a, envs))
            .collect::<Option<_>>()
            .ok_or(Fault::Type)?;
        let mut tuples: Vec<Vec<Value>> = (0..envs.len())
            .map(|i| columns.iter().filter_map(|c| c.get(i).cloned()).collect())
            .collect();
        let known = self.contexts.get(j).ok_or(Fault::Type)?.clone();
        let mut all = known.clone();
        for t in &tuples {
            if !all.contains(t) {
                all.push(t.clone());
            }
        }
        if all.len() > CONTEXTS {
            let pick = known.first().or(tuples.first()).ok_or(Fault::Type)?.clone();
            *args = pick.iter().map(value_expr).collect();
            tuples = vec![pick.clone(); envs.len()];
            all = known;
            if !all.contains(&pick) {
                all.push(pick);
            }
        }
        *self.contexts.get_mut(j).ok_or(Fault::Type)? = all;
        Ok(tuples)
    }
}
