// SPDX-License-Identifier: Apache-2.0
//! Function values: a `const` that holds a function item, a call through
//! it, and a function as the argument of a module parameter of a function
//! type.
//!
//! A function type needs the exact signature of the item, with the `mut`
//! marks. The evaluator holds the item name and calls the item, so a call
//! through a value costs the generator no more than a call of the item.

use super::stat::{Kind, Reach, kind};
use super::{Builder, Built};
use crate::eval::Value;
use crate::program::{FnTy, Item, SExpr, STy, Ty};

/// A helper `fn` as a function value: a `const` with the helper's types.
#[derive(Clone, Debug)]
pub(super) struct HwValue {
    pub(super) name: String,
    pub(super) target: String,
    pub(super) params: Vec<Ty>,
    pub(super) ret: Ty,
}

impl Builder {
    /// The consts `F<n>` of function type, for the `comptime fn`s and the
    /// functions with a `mut` formal, and those of the helpers. A function
    /// does not read them, so they come after all the functions.
    pub(super) fn fn_values(&mut self) -> Built {
        let mut targets: Vec<String> = self.fns.iter().map(|f| f.name.clone()).collect();
        targets.extend(self.mut_fns.iter().map(|f| f.name.clone()));
        let mut next = 0;
        for target in targets {
            if self.tape.below(4) == 0 {
                continue;
            }
            self.fn_value(&target, &mut next)?;
        }
        for h in self.helpers.clone() {
            if self.tape.below(2) == 0 {
                continue;
            }
            let name = format!("F{next}");
            next += 1;
            self.hw_values.push(HwValue {
                name,
                target: h.name.clone(),
                params: h.params.iter().map(|(_, t, _)| t.clone()).collect(),
                ret: h.ret.0.clone(),
            });
            note!(self, hw_values);
        }
        Ok(())
    }

    /// The number of function values so far; the next `F<n>` takes it.
    pub(super) fn fn_value_count(&self) -> u32 {
        let consts = self
            .consts
            .iter()
            .filter(|(n, t, _)| n.starts_with('F') && matches!(t, STy::Fn(_)))
            .count();
        u32::try_from(consts + self.hw_values.len()).unwrap_or(u32::MAX)
    }

    /// The const `F<next>` that holds the function item `target`.
    pub(super) fn fn_value(&mut self, target: &str, next: &mut u32) -> Built {
        let Some(ty) = self.scope.fn_ty(target) else {
            return Ok(());
        };
        let mutable = ty.params.iter().any(|(m, _)| *m);
        let name = format!("F{next}");
        *next += 1;
        self.consts
            .push((name, STy::Fn(Box::new(ty)), SExpr::Name(target.to_owned())));
        self.refresh()?;
        note!(self, fn_values);
        if mutable {
            note!(self, mut_values);
        }
        Ok(())
    }

    /// The items for the helper values.
    pub(super) fn hw_value_items(&self) -> impl Iterator<Item = Item> + '_ {
        self.hw_values.iter().map(|v| Item::HwFnValue {
            name: v.name.clone(),
            target: v.target.clone(),
            params: v.params.clone(),
            ret: v.ret.clone(),
        })
    }

    /// The names that hold the function type `ty` at the file scope: the
    /// items with that signature and the consts of that type.
    pub(super) fn fn_candidates(&self, ty: &FnTy) -> Vec<String> {
        let items = self
            .fns
            .iter()
            .map(|f| f.name.as_str())
            .chain(self.list_fns.iter().map(|f| f.name.as_str()))
            .chain(self.mut_fns.iter().map(|f| f.name.as_str()));
        let consts = self
            .consts
            .iter()
            .filter(|(_, t, _)| matches!(t, STy::Fn(f) if **f == *ty))
            .map(|(n, _, _)| n.as_str());
        items
            .filter(|n| self.scope.fn_ty(n).is_some_and(|t| t == *ty))
            .chain(consts)
            .map(str::to_owned)
            .collect()
    }

    /// The type of a module parameter that takes a function: the signature
    /// of a `comptime fn`.
    pub(super) fn fn_param_ty(&mut self) -> Option<STy> {
        let f = self.fns.get(self.tape.index(self.fns.len()))?;
        let ty = self.scope.fn_ty(&f.name)?;
        Some(STy::Fn(Box::new(ty)))
    }

    /// The value that a module argument of the function type `ty` can be:
    /// one of the candidates.
    pub(super) fn fn_argument(&mut self, ty: &FnTy) -> SExpr {
        let names = self.fn_candidates(ty);
        match names.get(self.tape.index(names.len())) {
            Some(n) => SExpr::Name(n.clone()),
            None => SExpr::Name(String::new()),
        }
    }

    /// A call through a name of function type in scope, with a result of
    /// `kind` and no `mut` formal. The arguments hold in each env of `r`,
    /// else the call takes the arguments of the base case. A position with
    /// no envs has no such call.
    pub(super) fn value_call(&mut self, want: Kind, depth: u32, r: Reach<'_>) -> Option<SExpr> {
        let envs = r.envs?;
        let callable: Vec<(&String, &FnTy)> = r
            .names
            .iter()
            .filter_map(|(n, t)| match t {
                STy::Fn(f)
                    if kind(&f.ret) == Some(want)
                        && f.params.iter().all(|(m, t)| !m && kind(t).is_some()) =>
                {
                    Some((n, &**f))
                }
                _ => None,
            })
            .collect();
        let (name, ty) = *callable.get(self.tape.index(callable.len()))?;
        let (name, ty) = (name.clone(), ty.clone());
        let d = depth.saturating_sub(1);
        // The count of a recursion stays small, as in a call by name.
        let args: Vec<SExpr> = ty
            .params
            .iter()
            .enumerate()
            .map(|(i, (_, t))| match (i, t) {
                (0, STy::Nat | STy::Int) => self.number(0, super::COUNT),
                (_, t) => self.sexpr(super::stat::param_kind(t), d, r),
            })
            .collect();
        let call = SExpr::Call(name.clone(), args);
        note!(self, value_calls);
        if self.holds(&call, envs, |_| true) {
            return Some(call);
        }
        note!(self, value_call_fallbacks);
        let base = ty
            .params
            .iter()
            .map(|(_, t)| match super::stat::param_kind(t) {
                Kind::Int => super::stat::int(0),
                Kind::Bool => SExpr::Bool(false),
                Kind::Str => SExpr::Str(String::new()),
            })
            .collect();
        Some(SExpr::Call(name, base))
    }

    /// The callee for a mut function `f`: its own name, or a const that
    /// holds it, with the receiver form only for the name.
    pub(super) fn mut_callee(&mut self, f: &str) -> (String, bool) {
        let Some(ty) = self.scope.fn_ty(f) else {
            return (f.to_owned(), self.tape.flag());
        };
        let values: Vec<String> = self
            .consts
            .iter()
            .filter(|(_, t, v)| {
                matches!(t, STy::Fn(g) if **g == ty) && *v == SExpr::Name(f.to_owned())
            })
            .map(|(n, _, _)| n.clone())
            .collect();
        if !values.is_empty()
            && self.tape.below(4) != 0
            && let Some(v) = values.get(self.tape.index(values.len()))
        {
            note!(self, mut_value_calls);
            return (v.clone(), false);
        }
        (f.to_owned(), self.tape.flag())
    }

    /// The value of a call through a function value: the name of the
    /// helper that a helper value holds, if the callee is one.
    pub(super) fn hw_value_of(&self, target: &str) -> Option<String> {
        self.hw_values
            .iter()
            .find(|v| v.target == target)
            .map(|v| v.name.clone())
    }

    /// The function values that a module with the parameter `ty` accepts,
    /// as values.
    pub(super) fn fn_domain(&self, ty: &FnTy) -> Vec<Value> {
        self.fn_candidates(ty)
            .into_iter()
            .map(|n| Value::Function(n, ty.clone()))
            .collect()
    }
}
