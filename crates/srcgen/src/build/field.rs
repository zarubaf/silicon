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
use crate::program::{FTy, FieldTy, HExpr, Item, Place, Radix, SBin, SExpr, STy, Stmt};
use num_bigint::BigInt;
use std::collections::BTreeSet;

/// `Odds(n, d)`: `n` eligible steps in `d` read as `@field`. A record or a
/// list is rare, so it gets better odds than a tuple or an array. A list
/// keeps a plain `l[i]` in 8 steps of 15, so each spelling occurs in 10%
/// of the programs.
#[derive(Clone, Copy)]
pub(super) struct Odds(u32, u32);

const RECORD_ODDS: Odds = Odds(1, 2);
pub(super) const LIST_ODDS: Odds = Odds(7, 15);
pub(super) const ARRAY_ODDS: Odds = Odds(1, 8);
const TUPLE_ODDS: Odds = Odds(1, 12);
/// The most steps of one program that read as `@field`.
pub(super) const MAX_FIELDS: u32 = 16;
/// One eligible read or target of hardware in this many takes the spelling,
/// and the most in one program.
const HW_ODDS: u32 = 5;
const MAX_HW_FIELDS: u32 = 24;

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
        odds: Odds,
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
    fn field_site(&mut self, Odds(n, d): Odds) -> bool {
        if self.fields >= self.max_fields || self.tape.below(d) < d - n {
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

/// What the spelling pass knows about the item under it: the instances,
/// which take a `PortKey`, and the names of the fields of structs of
/// handles, which take only a `String`.
struct Cx<'a> {
    instances: BTreeSet<String>,
    records: &'a BTreeSet<String>,
}

impl Builder {
    /// Rewrites reads and `:=` targets of children and containers of handles
    /// in `items` to `@field`, in place. The value of each stays the same.
    pub(super) fn spell_hardware(&mut self, items: &mut [Item]) {
        let records: BTreeSet<String> = items
            .iter()
            .filter_map(|item| match item {
                Item::Struct(def) => Some(def),
                _ => None,
            })
            .flat_map(|def| def.fields.iter())
            .filter(|(_, t)| matches!(t, FieldTy::Handle(_)))
            .map(|(f, _)| f.clone())
            .collect();
        self.on_field(|b| {
            // Three programs in five spell hardware.
            if b.tape.below(5) < 2 {
                return;
            }
            let mut spelled = 0;
            for item in items.iter_mut() {
                match item {
                    Item::Module { body, .. } => {
                        let mut cx = Cx {
                            instances: instances(body, &[]),
                            records: &records,
                        };
                        b.spell_stmts(body, &mut cx, &mut spelled);
                    }
                    Item::Helper {
                        params,
                        body,
                        result,
                        ..
                    } => {
                        let mut cx = Cx {
                            instances: instances(body, params),
                            records: &records,
                        };
                        b.spell_stmts(body, &mut cx, &mut spelled);
                        b.spell_expr(result, &mut cx, &mut spelled);
                    }
                    _ => {}
                }
            }
        });
    }

    fn spell_stmts(&mut self, body: &mut [Stmt], cx: &mut Cx<'_>, spelled: &mut u32) {
        for s in body {
            match s {
                Stmt::Let { value, .. } | Stmt::Assign(_, value) => {
                    self.spell_expr(value, cx, spelled);
                }
                Stmt::Connect(place, value) => {
                    self.spell_place(place, cx, spelled);
                    self.spell_expr(value, cx, spelled);
                }
                Stmt::If(_, then, els) => {
                    self.spell_stmts(then, cx, spelled);
                    if let Some(els) = els {
                        self.spell_stmts(els, cx, spelled);
                    }
                }
                Stmt::For(_, _, _, body) | Stmt::Block(body) => self.spell_stmts(body, cx, spelled),
                _ => {}
            }
        }
    }

    /// Whether the next eligible node takes the spelling.
    fn spell_site(&mut self, spelled: &mut u32) -> bool {
        if *spelled >= MAX_HW_FIELDS || self.tape.below(HW_ODDS) != HW_ODDS - 1 {
            return false;
        }
        *spelled += 1;
        true
    }

    fn spell_place(&mut self, place: &mut Place, cx: &mut Cx<'_>, spelled: &mut u32) {
        match place {
            Place::Field(u, p) => {
                if self.spell_site(spelled) {
                    let key = self.port_key(p, cx.instances.contains(u));
                    *place = Place::Path(HExpr::FieldOf(Box::new(HExpr::Name(u.clone())), key));
                }
            }
            Place::ChildEntry(u, fam, k) => {
                if self.spell_site(spelled) {
                    let key = self.entry_key(fam, k.clone());
                    *place = Place::Path(HExpr::FieldOf(Box::new(HExpr::Name(u.clone())), key));
                }
            }
            Place::Path(e) => self.spell_expr(e, cx, spelled),
            Place::Name(_) | Place::Entry(..) => {}
        }
    }

    /// Rewrites the selections of `e`, the base first. A call keeps its
    /// actuals as they are: a handle formal takes the handle itself.
    fn spell_expr(&mut self, e: &mut HExpr, cx: &mut Cx<'_>, spelled: &mut u32) {
        match e {
            HExpr::Unary(_, a) | HExpr::Resize(_, a) | HExpr::Reinterpret(_, a) => {
                self.spell_expr(a, cx, spelled);
            }
            HExpr::Binary(_, a, b) => {
                self.spell_expr(a, cx, spelled);
                self.spell_expr(b, cx, spelled);
            }
            HExpr::If(c, t, f) => {
                for x in [c, t, f] {
                    self.spell_expr(x, cx, spelled);
                }
            }
            HExpr::Index(b, i) => {
                self.spell_expr(b, cx, spelled);
                if self.spell_site(spelled) {
                    let (base, key) = (std::mem::replace(&mut **b, HExpr::Unit), i.clone());
                    *e = HExpr::FieldOf(Box::new(base), key);
                }
            }
            HExpr::Select(b, k) => {
                self.spell_expr(b, cx, spelled);
                if self.spell_site(spelled) {
                    let key = SExpr::Int(BigInt::from(*k), self.radix());
                    let base = std::mem::replace(&mut **b, HExpr::Unit);
                    *e = HExpr::FieldOf(Box::new(base), key);
                }
            }
            HExpr::Member(b, f) => {
                self.spell_expr(b, cx, spelled);
                if self.spell_site(spelled) {
                    let child = !cx.records.contains(f.as_str());
                    let key = self.port_key(f, child);
                    let base = std::mem::replace(&mut **b, HExpr::Unit);
                    *e = HExpr::FieldOf(Box::new(base), key);
                }
            }
            HExpr::ChildEntry(b, fam, k) => {
                self.spell_expr(b, cx, spelled);
                if self.spell_site(spelled) {
                    let key = self.entry_key(fam, k.clone());
                    let base = std::mem::replace(&mut **b, HExpr::Unit);
                    *e = HExpr::FieldOf(Box::new(base), key);
                }
            }
            HExpr::Field(u, q) => {
                if self.spell_site(spelled) {
                    let key = self.port_key(q, cx.instances.contains(u.as_str()));
                    *e = HExpr::FieldOf(Box::new(HExpr::Name(u.clone())), key);
                }
            }
            HExpr::Match(m) => {
                self.spell_expr(&mut m.scrutinee, cx, spelled);
                for (_, arm) in &mut m.arms {
                    self.spell_expr(arm, cx, spelled);
                }
            }
            _ => {}
        }
    }

    /// The key of a port or of a field: a `String`, and for a child also a
    /// scalar `PortKey`.
    fn port_key(&mut self, name: &str, child: bool) -> SExpr {
        let text = self.name_key(name);
        if child && self.tape.flag() {
            note!(self, field_scalar_keys);
            return SExpr::PortKey(Box::new(text), false, Box::new(int(0)));
        }
        text
    }

    /// The key of the entry `fam[k]`: an indexed `PortKey`.
    fn entry_key(&mut self, fam: &str, k: SExpr) -> SExpr {
        let name = self.name_key(fam);
        note!(self, field_entry_keys);
        SExpr::PortKey(Box::new(name), true, Box::new(k))
    }

    /// The literal of a name, or a join of its letters and its number.
    fn name_key(&mut self, name: &str) -> SExpr {
        let split = name.find(|c: char| c.is_ascii_digit());
        let joined = split.filter(|&at| at > 0 && name[at..].chars().all(|c| c.is_ascii_digit()));
        match joined {
            Some(at) if self.tape.below(3) == 0 => {
                note!(self, field_joined_keys);
                let n: u32 = name[at..].parse().unwrap_or(0);
                let n = SExpr::Int(BigInt::from(n), Radix::Dec);
                bin(
                    SBin::Add,
                    SExpr::Str(name[..at].to_owned()),
                    SExpr::StrOf(Box::new(n)),
                )
            }
            _ => SExpr::Str(name.to_owned()),
        }
    }
}

/// The names of the instances of a body, and of the formals of an instance
/// type.
fn instances(body: &[Stmt], params: &[(String, FTy)]) -> BTreeSet<String> {
    fn walk(body: &[Stmt], out: &mut BTreeSet<String>) {
        for s in body {
            match s {
                Stmt::Instance(n, ..) => {
                    out.insert(n.clone());
                }
                Stmt::If(_, then, els) => {
                    walk(then, out);
                    walk(els.as_deref().unwrap_or_default(), out);
                }
                Stmt::For(_, _, _, body) | Stmt::Block(body) => walk(body, out),
                _ => {}
            }
        }
    }
    let mut out: BTreeSet<String> = params
        .iter()
        .filter(|(_, t)| matches!(t, FTy::Instance(..)))
        .map(|(n, _)| n.clone())
        .collect();
    walk(body, &mut out);
    out
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
        b.field.numbers = vec![TUPLE_ODDS.1 - 1; 16].into_iter();
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
