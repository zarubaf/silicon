// SPDX-License-Identifier: Apache-2.0
//! Held keys and early keys of a chain (#237, #367, #378).
//!
//! A statement group reads a small container through a chain whose later
//! key calls a function with a `mut` formal on the local that the earlier
//! key read:
//!
//! ```text
//! let s0: [[Int; 2]; 2] = [[1, 2], [3, 4]];
//! let mut s1: Int = 1;
//! let s2: Int = @field(s0, s1)[k0(s1, 3)];
//! diagnostic("d0", (s2, s1));
//! ```
//!
//! The earlier key keeps its old value, so a front end that reads `s1`
//! again after the call selects another row or fails the range check. The
//! group is the *held key*. When the function runs a `diagnostic`, the group
//! is the *early key*: its record comes when the key evaluates, and the
//! front ends order it with the checks of the earlier steps (#378, #387).
//! The record of the group shows the value and the new local.
//!
//! A group declares only names of its own, keeps no name in the scope of the
//! frame, and draws from the field tape alone, so a program without a group
//! is the program of the other tapes alone.

use super::stat::int;
use super::{Builder, Built, Ctx, Names};
use crate::eval::{Env, exec_static};
use crate::program::{MutFn, SBin, SExpr, STy, Stmt};
use num_bigint::BigInt;

/// One statement of a frame in this many is followed by a group, and the
/// most groups of one program.
const GROUP_ODDS: u32 = 6;
const MAX_GROUPS: u32 = 4;

impl Builder {
    /// A group of statements after a statement of the frame, if the field
    /// tape says so.
    pub(super) fn key_group(&mut self, ctx: &Ctx, names: &mut Names, out: &mut Vec<Stmt>) -> Built {
        if self.key_groups >= MAX_GROUPS || ctx.envs.is_empty() {
            return Ok(());
        }
        self.on_field(|b| {
            if b.tape.below(GROUP_ODDS) != GROUP_ODDS - 1 {
                return Ok(());
            }
            let stmts = b.held_read(names)?;
            // Each env runs the group, so a fault keeps it out.
            let ok = ctx.envs.iter().all(|env| {
                let mut env: Env = env.clone();
                stmts
                    .iter()
                    .all(|s| exec_static(s, &mut env, &b.scope).is_ok())
            });
            if ok {
                b.key_groups += 1;
                out.extend(stmts);
            }
            Ok(())
        })
    }

    /// The function `k<n>(mut a0: Int, x1: Int) -> Int` that adds to the
    /// root and gives an index of `0..2`, with a `diagnostic` or without.
    fn key_fn(&mut self, effectful: bool) -> Built<String> {
        let slot = usize::from(effectful);
        if let Some(name) = self.key_fns.get(slot).cloned().flatten() {
            return Ok(name);
        }
        let name = format!("k{}", self.mut_fns.len());
        let var = |n: &str| SExpr::Name(n.to_owned());
        let sum = SExpr::Binary(SBin::Add, Box::new(var("a0")), Box::new(var("x1")));
        let diag = effectful.then(|| {
            let value = SExpr::Tuple(vec![var("x1"), var("a0")]);
            (self.next_message(), value)
        });
        let delta = self.tape.between(1, 3);
        self.mut_fns.push(MutFn {
            name: name.clone(),
            root: STy::Int,
            pre: Vec::new(),
            update: SExpr::Binary(
                SBin::Add,
                Box::new(var("a0")),
                Box::new(int(i64::from(delta))),
            ),
            ret: SExpr::Binary(SBin::And, Box::new(sum), Box::new(int(1))),
            diag,
        });
        self.refresh()?;
        if let Some(entry) = self.key_fns.get_mut(slot) {
            *entry = Some(name.clone());
        }
        Ok(name)
    }

    /// The statements of one group: the container, the local key, the read,
    /// and the record.
    fn held_read(&mut self, names: &mut Names) -> Built<Vec<Stmt>> {
        let early = self.tape.flag();
        let f = self.key_fn(early)?;
        let (c, k, v) = (names.fresh("s"), names.fresh("s"), names.fresh("s"));
        let name = |n: &String| SExpr::Name(n.clone());
        let row = STy::Array(Box::new(STy::Int), 2);
        let tuple = self.tape.flag();
        let ty = if tuple {
            STy::Tuple(vec![row.clone(), row])
        } else {
            STy::Array(Box::new(row), 2)
        };
        let mut rows = Vec::new();
        for _ in 0..2 {
            let cells = (0..2).map(|_| self.small_int()).collect();
            rows.push(SExpr::Array(cells));
        }
        let value = if tuple {
            SExpr::Tuple(rows)
        } else {
            SExpr::Array(rows)
        };
        let start = self.tape.between(0, 1);
        let arg = self.tape.between(0, 5);
        // A tuple takes no `[k]`, so its first step is `@field`. One step
        // of the chain at least reads as `@field`.
        let plain_first = !tuple && self.tape.flag();
        let first = if plain_first {
            SExpr::Index(Box::new(name(&c)), Box::new(name(&k)))
        } else {
            SExpr::At(Box::new(name(&c)), Box::new(name(&k)))
        };
        let call = SExpr::KeyCall(f, k.clone(), Box::new(int(i64::from(arg))));
        let read = if plain_first || self.tape.flag() {
            SExpr::At(Box::new(first), Box::new(call))
        } else {
            SExpr::Index(Box::new(first), Box::new(call))
        };
        note!(self, held_groups);
        note!(self, early_groups, early);
        let shown = SExpr::Tuple(vec![name(&v), name(&k)]);
        Ok(vec![
            Stmt::StaticLet(c, ty, value),
            Stmt::MutLet(k, STy::Int, int(i64::from(start))),
            Stmt::StaticLet(v, STy::Int, read),
            Stmt::Diagnostic(self.next_message(), shown),
        ])
    }

    fn small_int(&mut self) -> SExpr {
        let n = i64::from(self.tape.below(10));
        let sign = if self.tape.below(4) == 3 { -1 } else { 1 };
        SExpr::Int(BigInt::from(n * sign), crate::program::Radix::Dec)
    }
}
