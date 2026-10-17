// SPDX-License-Identifier: Apache-2.0
//! The coverage map of a `match` (design section 5.6). It holds the first arm of each key in
//! the order of the scrutinee type, and it checks the coverage with no walk over the values of
//! the type: it compares the count of the keys with `2^W` by `W` and the bit length of the count,
//! and it finds the smallest uncovered key in one pass over the ordered keys.

use crate::int::Int;
use crate::types::{Ty, TyId, Types};
use parse::ast::Pos;
use std::collections::BTreeMap;

/// The ordered map of a `match`: each key to its first arm and the position of its pattern.
/// `wild` is the first arm `_` and its position. `arms` holds the key of each arm in arm order,
/// none for `_`, for the selects of a hardware scrutinee.
#[derive(Default)]
pub(crate) struct Cover {
    pub keys: BTreeMap<Int, (usize, Pos)>,
    pub wild: Option<(usize, Pos)>,
    pub arms: Vec<Option<Int>>,
}

impl Cover {
    /// The first arm of the key `key`, else the arm `_`.
    pub(crate) fn arm_of(&self, key: Option<&Int>) -> Option<usize> {
        key.and_then(|k| self.keys.get(k))
            .map(|(j, _)| *j)
            .or(self.wild.map(|(j, _)| j))
    }

    /// The smallest key from `lo` that no arm has, in one pass over the ordered keys.
    pub(crate) fn smallest_uncovered(&self, lo: Int) -> Int {
        let one = Int::from_u64(1);
        self.keys.keys().fold(lo, |e, k| {
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Covered, 1);
            if *k == e { e.add(&one) } else { e }
        })
    }
}

/// Whether `n` distinct keys of a type with `2^w` keys are all its keys. The test reads `w` and
/// the bit length of `n`, so it makes no number `2^w`.
pub(crate) fn all_keys(n: usize, w: u64) -> bool {
    n != 0 && w <= u64::from(n.ilog2())
}

/// The number `W` of the `2^W` keys of the scrutinee type `t`: `Bool` has 1 bit, `UInt[W]` and
/// `SInt[W]` have `W`, and an enum has its tag width. `Int` and `Nat` have no finite set.
pub(crate) fn key_bits(tys: &Types, t: TyId) -> Option<u64> {
    match tys.get(t) {
        Ty::Bool => Some(1),
        Ty::UInt(w) | Ty::SInt(w) => Some(u64::from(*w)),
        Ty::Enum(_) => tys.widths(t).map(|w| u64::from(w.tag)),
        _ => None,
    }
}

/// The smallest key of the scrutinee type `t` with `w` bits of keys: `SInt[W]` starts at
/// `-2^(W-1)`, and each other type at 0.
pub(crate) fn key_lo(tys: &Types, t: TyId, w: u64) -> Int {
    match tys.get(t) {
        Ty::SInt(_) => Int::from_u64(1).shl(w.saturating_sub(1)).neg(),
        _ => Int::zero(),
    }
}
