// SPDX-License-Identifier: Apache-2.0
//! The string operations of Lean `Source.Eval`: `s[i]`, `len(s)`, and `str(n)`. A UTF-8 string
//! needs a scan to find its scalars, so each operation charges the size of the string before
//! it scans (section 5.4). A string that is too long for the fuel fails from its byte length,
//! without a scan.

use super::place::Index;
use super::{Evaluator, Opnd, Out, Res, fail};
use crate::Code;
use crate::hw::Val;
use crate::int::Int;
use crate::value::{Value, int_size};
use parse::ast::Pos;

impl Evaluator<'_> {
    /// Charges the size of the string `o` at `pos`: 1 plus its scalars. A scalar is at most
    /// 4 bytes, so a string with more bytes than 4 times the fuel cannot pay, and the charge
    /// of its lower bound fails before any scan. Another value charges nothing.
    pub(super) fn charge_scan(&mut self, pos: Pos, o: &Out) -> Res<()> {
        let Value::Str(s) = self.store.value(o) else {
            return Ok(());
        };
        let lower = 1 + (s.len() as u64).div_ceil(4);
        if lower > self.fuel.left() {
            return self.charge(pos, u128::from(lower));
        }
        let chars = s.chars().count() as u64;
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Scanned, chars);
        self.charge(pos, 1 + u128::from(chars))
    }

    /// The string with the scalar `i` of the string `base` at the index node `pos`, whose
    /// index expression is at `xp`. The type of the index comes first, then the charge of the
    /// scan, then the range.
    pub(super) fn str_at(&mut self, pos: Pos, xp: Pos, base: &Out, i: &Index) -> Res<Out> {
        if let Index::Bad(m) = i {
            return fail(Code::S010, xp, m.clone());
        }
        self.charge_scan(pos, base)?;
        let Value::Str(s) = self.store.value(base) else {
            return fail(Code::S010, pos, "an index needs a string".to_owned());
        };
        match i {
            Index::Number(k) => {
                if let Some(c) = s.chars().nth(*k) {
                    return Ok(Out::Made(Val::Static(Value::Str(c.to_string()))));
                }
                range(xp, &k.to_string(), s.chars().count())
            }
            Index::Wide(k) => range(xp, k, s.chars().count()),
            Index::Bad(_) => Ok(Out::Made(Val::Static(Value::Unit))),
        }
    }

    /// `len` of the string `o` at the call `pos`: the number of its scalars.
    pub(super) fn str_len(&mut self, pos: Pos, o: &Out) -> Res<Value> {
        self.charge_scan(pos, o)?;
        let Value::Str(s) = self.store.value(o) else {
            return fail(Code::S010, pos, "`len` takes a string".to_owned());
        };
        Ok(Value::Int(Int::from_u64(s.chars().count() as u64)))
    }

    /// `str(n)` at the call `pos`: the decimal form of an `Int`. It charges the square of the
    /// size of `n` before the conversion, and then the size of the result.
    pub(super) fn str_of(&mut self, pos: Pos, g: &str, v: Opnd) -> Res<Option<Out>> {
        let Opnd::Static(o) = v else {
            return fail(Code::S010, pos, format!("`{g}` needs an Int, not hardware"));
        };
        let size = match self.store.value(&o) {
            Value::Int(n) => u128::from(int_size(n)),
            v => {
                return fail(
                    Code::S010,
                    pos,
                    format!("`{g}` needs an Int, not {}", v.text(&self.tys)),
                );
            }
        };
        self.charge(pos, size * size)?;
        let digits = match self.store.value(&o) {
            Value::Int(n) => n.to_string(),
            _ => String::new(),
        };
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Converted, digits.len() as u64);
        let s = Value::Str(digits);
        self.charge(pos, u128::from(s.size()))?;
        Ok(Some(Out::Made(Val::Static(s))))
    }
}

/// `S013` at `xp`: the index `k` is out of range for a string of `chars` scalars.
fn range(xp: Pos, k: &str, chars: usize) -> Res<Out> {
    fail(
        Code::S013,
        xp,
        format!("the index {k} is out of range for {chars} scalar(s)"),
    )
}
