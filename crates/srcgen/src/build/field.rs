// SPDX-License-Identifier: Apache-2.0
//! `@field` reads of static containers (front-end spec 9.3). A step of a
//! chain that `descend` draws, `.f`, `.N`, or `[i]`, can read as
//! `@field(base, key)` instead: after the base and the key it is the
//! ordinary selection, so the value stays the same.
//!
//! Each draw comes from the field tape (`on_field`), which no other form
//! reads, and choice 0 is the ordinary step. A program with no spelled
//! step is thus the program of the other tapes alone. The key of a record
//! is a `String`: a literal, `"m" + str(k)`, or a static `String` name. The
//! key of a tuple, an array, and a list is a `Nat`: the literal or the
//! index of the ordinary step, a static name of the same value, or a call
//! plus an offset (`one() + 1`).

use super::stat::{Reach, bin, int};
use super::{Builder, Lane};
use crate::eval::Value;
use crate::program::{Radix, SBin, SExpr, STy};
use num_bigint::BigInt;

/// One eligible step in this many reads as `@field`: a record or a list is
/// rare, so it gets better odds than a tuple or an array.
const RECORD_ODDS: u32 = 2;
pub(super) const LIST_ODDS: u32 = 1;
pub(super) const ARRAY_ODDS: u32 = 8;
const TUPLE_ODDS: u32 = 12;
/// The most steps of one program that read as `@field`.
pub(super) const MAX_FIELDS: u32 = 16;

impl Builder {
    /// Runs `f` on the field tape, isolated from the other tapes.
    pub(super) fn on_field<T>(&mut self, f: impl FnOnce(&mut Builder) -> T) -> T {
        self.isolated(Lane::Field, f)
    }

    /// `@field(base, key)` for the step `.f` of a record, if the tape says
    /// so.
    pub(super) fn field_record(
        &mut self,
        base: &SExpr,
        field: &str,
        r: Reach<'_>,
    ) -> Option<SExpr> {
        self.on_field(|b| {
            if !b.field_site(RECORD_ODDS) {
                return None;
            }
            note!(b, field_records);
            let key = b.record_key(field, r);
            Some(at(base, key))
        })
    }

    /// `@field(base, key)` for the step `.N` of a tuple.
    pub(super) fn field_select(&mut self, base: &SExpr, k: u32, r: Reach<'_>) -> Option<SExpr> {
        self.on_field(|b| {
            if !b.field_site(TUPLE_ODDS) {
                return None;
            }
            note!(b, field_tuples);
            let literal = SExpr::Int(BigInt::from(k), b.radix());
            let key = b.nat_key(&literal, k, r);
            Some(at(base, key))
        })
    }

    /// `@field(base, key)` for the step `[at]` of an array or a list. The
    /// key has the value of `index` in each env.
    pub(super) fn field_index(
        &mut self,
        base: &SExpr,
        index: &SExpr,
        odds: u32,
        r: Reach<'_>,
    ) -> Option<SExpr> {
        self.on_field(|b| {
            if !b.field_site(odds) {
                return None;
            }
            let key = match b.constant(index, r) {
                Some(k) => b.nat_key(index, k, r),
                None => index.clone(),
            };
            Some(at(base, key))
        })
    }

    /// Whether the eligible step takes the spelling, and counts it.
    fn field_site(&mut self, odds: u32) -> bool {
        if self.fields >= self.max_fields || self.tape.below(odds) != odds - 1 {
            return false;
        }
        self.fields += 1;
        note!(self, field_steps);
        true
    }

    fn radix(&mut self) -> Radix {
        match self.tape.below(4) {
            2 => Radix::Hex,
            3 => Radix::Bin,
            _ => Radix::Dec,
        }
    }

    /// The key of a record field: the literal, `"m" + str(k)` for the field
    /// `m<k>`, or a static `String` name that has the field name in each
    /// env.
    fn record_key(&mut self, field: &str, r: Reach<'_>) -> SExpr {
        let literal = SExpr::Str(field.to_owned());
        match self.tape.below(3) {
            1 => {
                let digits = field.strip_prefix('m').and_then(|d| d.parse::<u32>().ok());
                let Some(k) = digits else { return literal };
                note!(self, field_joined_keys);
                let n = SExpr::Int(BigInt::from(k), Radix::Dec);
                bin(
                    SBin::Add,
                    SExpr::Str("m".to_owned()),
                    SExpr::StrOf(Box::new(n)),
                )
            }
            2 => match self.string_name(field, r) {
                Some(name) => {
                    note!(self, field_name_keys);
                    name
                }
                None => literal,
            },
            _ => literal,
        }
    }

    /// A static `String` name whose value is `text` in each env.
    fn string_name(&self, text: &str, r: Reach<'_>) -> Option<SExpr> {
        let envs = r.envs?;
        r.names
            .iter()
            .filter(|(_, t)| *t == STy::Str)
            .map(|(n, _)| SExpr::Name(n.clone()))
            .find(|n| {
                self.values(n, envs)
                    .is_some_and(|vs| vs.iter().all(|v| *v == Value::Str(text.to_owned())))
            })
    }

    /// The key of a tuple, an array, or a list element `k`: `plain`, a
    /// static name with the value `k`, or a call plus an offset.
    fn nat_key(&mut self, plain: &SExpr, k: u32, r: Reach<'_>) -> SExpr {
        match self.tape.below(4) {
            1 => match self.int_name(k, r) {
                Some(name) => {
                    note!(self, field_name_keys);
                    name
                }
                None => plain.clone(),
            },
            2 | 3 => match self.call_key(k, r) {
                Some(key) => {
                    note!(self, field_call_keys);
                    key
                }
                None => plain.clone(),
            },
            _ => plain.clone(),
        }
    }

    /// The value of `e` if it is one natural number in each env.
    fn constant(&self, e: &SExpr, r: Reach<'_>) -> Option<u32> {
        let envs = r.envs?;
        let values = self.values(e, envs)?;
        let mut found: Option<u32> = None;
        for v in &values {
            let Value::Int(n) = v else { return None };
            let n = u32::try_from(n).ok()?;
            if found.is_some_and(|f| f != n) {
                return None;
            }
            found = Some(n);
        }
        found
    }

    /// A static `Int` name whose value is `k` in each env.
    fn int_name(&self, k: u32, r: Reach<'_>) -> Option<SExpr> {
        r.names
            .iter()
            .filter(|(_, t)| matches!(t, STy::Int | STy::Nat))
            .map(|(n, _)| SExpr::Name(n.clone()))
            .find(|n| self.constant(n, r) == Some(k))
    }

    /// `call + (k - value)` for a call of a `comptime fn` whose value is
    /// one number in each env, so that the key is `k` and reads a call.
    fn call_key(&mut self, k: u32, r: Reach<'_>) -> Option<SExpr> {
        if r.fns == 0 {
            return None;
        }
        r.envs?;
        let call = self.fn_call(1, r);
        let value = i64::from(self.constant(&call, r)?);
        let offset = i64::from(k) - value;
        Some(bin(SBin::Add, call, int(offset)))
    }
}

fn at(base: &SExpr, key: SExpr) -> SExpr {
    SExpr::At(Box::new(base.clone()), Box::new(key))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tape of zeros takes no spelling: choice 0 is the ordinary step.
    #[test]
    fn choice_zero_is_the_ordinary_step() {
        let mut b = Builder::new(vec![]);
        let r = Reach {
            names: &[],
            fns: 0,
            envs: None,
        };
        let base = SExpr::Name("s0".to_owned());
        assert_eq!(b.field_select(&base, 1, r), None);
        assert_eq!(b.field_record(&base, "m0", r), None);
        assert_eq!(b.field_index(&base, &int(0), ARRAY_ODDS, r), None);
        assert_eq!(b.fields, 0);
    }

    /// A tape that takes every spelling stops at the cap.
    #[test]
    fn the_cap_stops_the_spellings() {
        let mut b = Builder::new(vec![]);
        b.field.numbers = vec![TUPLE_ODDS - 1; 16].into_iter();
        b.max_fields = 2;
        let r = Reach {
            names: &[],
            fns: 0,
            envs: None,
        };
        let base = SExpr::Name("s0".to_owned());
        let spelled = (0..4)
            .filter(|_| b.field_select(&base, 1, r).is_some())
            .count();
        assert_eq!(spelled, 2);
    }
}
