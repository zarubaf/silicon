// SPDX-License-Identifier: Apache-2.0
//! Instances: the choice of a child, its arguments, and the argument
//! tuples that become the contexts of the child.

use super::hw::{DEPTH, Want};
use super::stat::value_expr;
use super::{Builder, Built, CONTEXTS, Ctx, Hw, HwEnum, Module, Sig};
use crate::eval::{Env, Fault, Value, convert};
use crate::program::{HExpr, Place, SExpr, STy, Stmt};

/// An instance that the builder declared: its name, the signature of its
/// module, and the env of its arguments for each env of the caller.
pub(super) struct Child {
    pub(super) name: String,
    pub(super) sig: Sig,
    pub(super) envs: Vec<Env>,
}

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
        // A child that already has a context and a finite parameter is
        // instantiated again more often: its identity then occurs under
        // two spellings (#188).
        let again: Vec<usize> = children
            .iter()
            .copied()
            .filter(|&j| {
                self.contexts.get(j).is_some_and(|c| !c.is_empty())
                    && self.sigs.get(j).is_some_and(|s| {
                        s.params
                            .iter()
                            .any(|(_, t)| matches!(t, STy::UInt(_) | STy::SInt(_)))
                    })
            })
            .collect();
        let pool = if self.tape.below(2) == 0 && !again.is_empty() {
            &again
        } else {
            &children
        };
        let Some(&j) = pool.get(self.tape.index(pool.len())) else {
            return Ok(false);
        };
        self.instantiate(ctx, m, j, out)?;
        // A second `instance` of a child with a finite parameter reaches
        // its context again, often under another spelling (#188).
        if again.contains(&j) && self.tape.flag() {
            self.instantiate(ctx, m, j, out)?;
        }
        Ok(true)
    }

    /// `instance u = M<j>(args);`, the `:=` of each child input, and the
    /// outputs of the child as readable names.
    pub(super) fn instantiate(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        j: usize,
        out: &mut Vec<Stmt>,
    ) -> Built {
        let child = self.declare_child(ctx, m, j, out)?;
        self.bind_child_inputs(ctx, &child, None, DEPTH, out)?;
        self.expose_child_outputs(ctx, &child)
    }

    /// `instance u = M<j>(args);`
    pub(super) fn declare_child(
        &mut self,
        ctx: &mut Ctx,
        m: &mut Module,
        j: usize,
        out: &mut Vec<Stmt>,
    ) -> Built<Child> {
        let sig = self.sigs.get(j).cloned().ok_or(Fault::Type)?;
        let mut args = Vec::new();
        let again = self.known_tuple(j);
        for (i, (_, t)) in sig.params.iter().enumerate() {
            args.push(match again.as_ref().and_then(|a| a.get(i)) {
                Some(v) => self.respelled(t, v),
                None => self.argument(t, self.reach(ctx), &ctx.envs),
            });
        }
        let tuples = self.tuples(j, &mut args, &ctx.envs)?;
        let name = m.names.fresh("u");
        out.push(Stmt::Instance(name.clone(), sig.name.clone(), args));
        let envs: Vec<Env> = tuples.iter().map(|a| Env::of(&sig.params, a)).collect();
        Ok(Child { name, sig, envs })
    }

    /// The `:=` of each input of the child, but the input `skip`, which
    /// the caller binds.
    pub(super) fn bind_child_inputs(
        &mut self,
        ctx: &mut Ctx,
        child: &Child,
        skip: Option<&str>,
        depth: u32,
        out: &mut Vec<Stmt>,
    ) -> Built {
        for (p, t) in &child.sig.inputs {
            if skip == Some(p.as_str()) {
                continue;
            }
            let types = self.types(t, &child.envs)?;
            let value = self.driver_at(ctx, &Want { types, ty: None }, depth);
            let place = Place::Field(child.name.clone(), p.clone());
            out.push(Stmt::Connect(place, value));
        }
        for (p, def) in &child.sig.enum_inputs {
            let value = self.enum_driver(ctx, def);
            out.push(Stmt::Connect(
                Place::Field(child.name.clone(), p.clone()),
                value,
            ));
        }
        Ok(())
    }

    /// The outputs of the child, as names that later values read.
    pub(super) fn expose_child_outputs(&mut self, ctx: &mut Ctx, child: &Child) -> Built {
        for (q, def) in &child.sig.enum_outputs {
            ctx.enums.push(HwEnum {
                expr: HExpr::Field(child.name.clone(), q.clone()),
                def: def.clone(),
                hardware: true,
            });
        }
        for (q, t) in &child.sig.outputs {
            let types = self.types(t, &child.envs)?;
            ctx.hw.push(Hw {
                expr: HExpr::Field(child.name.clone(), q.clone()),
                ty: None,
                types,
                mutable: false,
            });
        }
        Ok(())
    }

    /// An argument tuple that a context of module `j` already holds, in
    /// three of four calls, if `j` has a finite parameter: the arguments
    /// then reach that context again, and the spelling of a finite one may
    /// differ.
    fn known_tuple(&mut self, j: usize) -> Option<Vec<Value>> {
        let finite = self
            .sigs
            .get(j)?
            .params
            .iter()
            .any(|(_, t)| matches!(t, STy::UInt(_) | STy::SInt(_)));
        if !finite || self.tape.below(4) == 0 {
            return None;
        }
        let known = self.contexts.get(j)?;
        known.get(self.tape.index(known.len())).cloned()
    }

    /// The argument tuple of each env, recorded as contexts of module `j`.
    /// When `j` would pass `CONTEXTS` tuples, the arguments become the
    /// literals of a tuple that it has.
    fn tuples(&mut self, j: usize, args: &mut Vec<SExpr>, envs: &[Env]) -> Built<Vec<Vec<Value>>> {
        let params = self.sigs.get(j).ok_or(Fault::Type)?.params.clone();
        // The identity is that of the converted arguments (#188).
        let columns: Vec<Vec<Value>> = args
            .iter()
            .zip(&params)
            .map(|(a, (_, t))| {
                self.values(a, envs)?
                    .into_iter()
                    .map(|v| convert(t, v).ok())
                    .collect()
            })
            .collect::<Option<_>>()
            .ok_or(Fault::Type)?;
        let mut tuples: Vec<Vec<Value>> = (0..envs.len())
            .map(|i| columns.iter().filter_map(|c| c.get(i).cloned()).collect())
            .collect();
        #[cfg(test)]
        self.note_spellings(j, args, &tuples);
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

    /// Counts the identities of a finite argument that two spellings reach.
    #[cfg(test)]
    fn note_spellings(&mut self, j: usize, args: &[SExpr], tuples: &[Vec<Value>]) {
        use crate::program::sexpr;
        let finite = tuples
            .iter()
            .flatten()
            .any(|v| matches!(v, Value::UInt(..) | Value::SInt(..)));
        if !finite {
            return;
        }
        let text = args.iter().map(sexpr).collect::<Vec<_>>().join(", ");
        for t in tuples {
            let key = t.iter().map(Value::serialize).collect::<Vec<_>>().join(" ");
            let seen = self.spellings.entry((j, key)).or_default();
            if seen.insert(text.clone()) && seen.len() == 2 {
                note!(self, aliased_args);
            }
        }
    }
}
