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
//! The same chain is a place: the group `let s3: Int = k2(@field(s0, s1)[k0(s1,
//! 3)], 2);` passes the part of a `let mut` container as the `mut` actual of
//! a function, and the keys of the place hold the call. A literal chain
//! (`@field(@field(t, 1), 0)`) passes the part with no held key.
//!
//! A group declares only names of its own, keeps no name in the scope of the
//! frame, and draws from the field tape alone, so a program without a group
//! is the program of the other tapes alone.

use super::stat::int;
use super::{Builder, Built, Ctx, Names};
use crate::program::{MutFn, SBin, SExpr, STy, Stmt};
use num_bigint::BigInt;

/// One statement of a frame in this many is followed by a group, and the
/// most groups of one program.
const GROUP_ODDS: u32 = 14;
const MAX_GROUPS: u32 = 4;
/// The slots of `key_fns`: the key function, the key function with a
/// `diagnostic`, and the function that a place passes its part to.
const PLAIN: usize = 0;
pub(super) const EFFECT: usize = 1;
const PLACE: usize = 2;

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
            let stmts = if b.tape.flag() {
                b.held_read(names)?
            } else {
                b.held_place(names)?
            };
            b.key_groups += 1;
            out.extend(stmts);
            Ok(())
        })
    }

    /// The function `k<n>(mut a0: Int, x1: Int) -> Int` that adds to the
    /// root and gives an index of `0..2`, with a `diagnostic` or without.
    pub(super) fn key_fn(&mut self, slot: usize) -> Built<String> {
        let effectful = slot == EFFECT;
        if let Some(name) = self.key_fns.get(slot).cloned().flatten() {
            return Ok(name);
        }
        let name = format!("k{}", self.mut_fns.len() + self.key_mut_fns.len());
        let var = |n: &str| SExpr::Name(n.to_owned());
        let sum = SExpr::Binary(SBin::Add, Box::new(var("a0")), Box::new(var("x1")));
        let diag = effectful.then(|| {
            let value = SExpr::Tuple(vec![var("x1"), var("a0")]);
            (self.next_message(), value)
        });
        let delta = self.tape.between(1, 3);
        let (update, ret) = if slot == PLACE {
            (sum, var("a0"))
        } else {
            let delta = SExpr::Binary(
                SBin::Add,
                Box::new(var("a0")),
                Box::new(int(i64::from(delta))),
            );
            (
                delta,
                SExpr::Binary(SBin::And, Box::new(sum), Box::new(int(1))),
            )
        };
        self.key_mut_fns.push(MutFn {
            name: name.clone(),
            root: STy::Int,
            pre: Vec::new(),
            update,
            ret,
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
        let func = self.key_fn(if early { EFFECT } else { PLAIN })?;
        let (cont, key, got) = (names.fresh("s"), names.fresh("s"), names.fresh("s"));
        let name = |n: &String| SExpr::Name(n.clone());
        let (ty, value, tuple) = self.small_container();
        let start = self.tape.between(0, 1);
        let arg = self.tape.between(0, 5);
        // A tuple takes no `[key]`, so its first step is `@field`. One step
        // of the chain at least reads as `@field`.
        let plain_first = !tuple && self.tape.flag();
        let first = if plain_first {
            SExpr::Index(Box::new(name(&cont)), Box::new(name(&key)))
        } else {
            SExpr::At(Box::new(name(&cont)), Box::new(name(&key)))
        };
        let call = SExpr::KeyCall(func, key.clone(), Box::new(int(i64::from(arg))));
        let read = if plain_first || self.tape.flag() {
            SExpr::At(Box::new(first), Box::new(call))
        } else {
            SExpr::Index(Box::new(first), Box::new(call))
        };
        note!(self, held_groups);
        note!(self, field_name_keys);
        note!(self, early_groups, early);
        let shown = SExpr::Tuple(vec![name(&got), name(&key)]);
        Ok(vec![
            Stmt::StaticLet(cont, ty, value),
            Stmt::MutLet(key, STy::Int, int(i64::from(start))),
            Stmt::StaticLet(got, STy::Int, read),
            Stmt::Diagnostic(self.next_message(), shown),
        ])
    }

    /// The statements of one place group: a `let mut` container, the call
    /// of a function on a part of it, and the record of the result and of
    /// the container. A held place reads a local `k` in the first key and
    /// calls a function on `k` in the second.
    fn held_place(&mut self, names: &mut Names) -> Built<Vec<Stmt>> {
        let held = self.tape.flag();
        let early = self.tape.flag();
        let outer = self.key_fn(PLACE)?;
        let (cont, key, got) = (names.fresh("s"), names.fresh("s"), names.fresh("s"));
        let name = |n: &String| SExpr::Name(n.clone());
        let (ty, value, tuple) = self.small_container();
        let lit = |sel: &mut Builder| int(i64::from(sel.tape.between(0, 1)));
        let (first_key, second_key) = if held {
            let func = self.key_fn(if early { EFFECT } else { PLAIN })?;
            let arg = int(i64::from(self.tape.between(0, 5)));
            (name(&key), SExpr::KeyCall(func, key.clone(), Box::new(arg)))
        } else {
            (lit(self), lit(self))
        };
        let (base, sel) = (Box::new(name(&cont)), Box::new(first_key));
        // A tuple takes `.N` or `@field`, an array `[i]` or `@field`; one
        // step reads as `@field` at least.
        let plain_first = !held && self.tape.flag();
        let first = match (&*sel, tuple, plain_first) {
            (SExpr::Int(n, radix), true, true) => {
                let key = u32::try_from(n).unwrap_or(0);
                SExpr::Select(base, key, *radix)
            }
            (_, false, true) => SExpr::Index(base, sel),
            _ => SExpr::At(base, sel),
        };
        let place = if plain_first || self.tape.flag() {
            SExpr::At(Box::new(first), Box::new(second_key))
        } else {
            SExpr::Index(Box::new(first), Box::new(second_key))
        };
        note!(self, place_groups);
        note!(self, held_place_groups, held);
        note!(self, field_name_keys, held);
        note!(self, early_groups, held && early);
        let arg = int(i64::from(self.tape.between(0, 6)));
        let shown = SExpr::Tuple(vec![name(&got), name(&cont), name(&key)]);
        let mut stmts = vec![Stmt::MutLet(cont.clone(), ty, value)];
        stmts.push(Stmt::MutLet(key.clone(), STy::Int, int(0)));
        stmts.push(Stmt::PlaceCall {
            name: got,
            place,
            f: outer,
            arg,
        });
        stmts.push(Stmt::Diagnostic(self.next_message(), shown));
        Ok(stmts)
    }

    /// A container of two rows of two integers: a tuple or an array of
    /// arrays.
    pub(super) fn small_container(&mut self) -> (STy, SExpr, bool) {
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
        (ty, value, tuple)
    }

    fn small_int(&mut self) -> SExpr {
        let n = i64::from(self.tape.below(10));
        let sign = if self.tape.below(4) == 3 { -1 } else { 1 };
        SExpr::Int(BigInt::from(n * sign), crate::program::Radix::Dec)
    }
}
