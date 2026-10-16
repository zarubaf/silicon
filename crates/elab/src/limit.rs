// SPDX-License-Identifier: Apache-2.0
//! The size limit of design section 5.4 (issue #255), as Lean `Eval.Basic` and `Eval.Types`
//! define it. A fuel near 2^64 pays for a value that no machine can hold, so each operation that
//! can make a large static value checks a bound before its charge. The bound comes from bit
//! lengths, byte lengths, and list lengths, so the check costs constant work and runs before any
//! big-number arithmetic. A value above the limit is `S015`. The texts are normative
//! (section 6.2).

use crate::Code;
use crate::int::Int;
use crate::ops::Fault;
use crate::types::Meta;
use parse::ast::BinOp;

/// The most bits of a static integer, bytes of a string, and elements of a list. The most bits
/// of each number of the type metadata, and the largest size of a value that a type makes.
pub(crate) const LIMIT: u128 = 1 << 32;

/// Whether `n` is above the limit.
pub(crate) fn over(n: u128) -> bool {
    n > LIMIT
}

const INT_TEXT: &str =
    "the result can have more than 2^32 bits, the limit of a static Int; use smaller operands";
const META_TEXT: &str = "the metadata of the type can have more than 2^32 bits, the limit of a \
    static Int; use a smaller type";
const STR_TEXT: &str =
    "the string has more than 2^32 bytes, the limit of a string; use shorter strings";
const LIST_TEXT: &str =
    "the list has more than 2^32 elements, the limit of a list; use a shorter list";
const ZERO_TEXT: &str = "the value of the type has a size above 2^32, the limit of a value from \
    a type; use a smaller type or keep it a reference";
const RECORD_TEXT: &str = "the recorded value has a size above 2^32, the limit of a record; \
    record a smaller part";

fn fault(text: &str) -> Fault {
    (Code::S015, text.to_owned())
}

/// `S015` unless the bit length bound `bound` of a static integer is in the limit.
pub(crate) fn capped(bound: u128) -> Result<(), Fault> {
    if over(bound) {
        Err(fault(INT_TEXT))
    } else {
        Ok(())
    }
}

/// `S015` unless the byte length `bytes` of a string is in the limit.
pub(crate) fn string(bytes: u128) -> Result<(), Fault> {
    if over(bytes) {
        Err(fault(STR_TEXT))
    } else {
        Ok(())
    }
}

/// `S015` unless the length `len` of a list is in the limit.
pub(crate) fn list(len: u128) -> Result<(), Fault> {
    if over(len) {
        Err(fault(LIST_TEXT))
    } else {
        Ok(())
    }
}

/// `S015` unless the metadata bound `bound` is in the limit.
pub(crate) fn metadata(bound: u128) -> Result<(), Fault> {
    if over(bound) {
        Err(fault(META_TEXT))
    } else {
        Ok(())
    }
}

/// `S015` unless the zero size `size` of a type is in the limit, for a value that the type makes.
pub(crate) fn zero(size: &Int) -> Result<(), Fault> {
    if exceeds(size) {
        Err(fault(ZERO_TEXT))
    } else {
        Ok(())
    }
}

/// `S015` unless the size `size` of a recorded value is in the limit.
pub(crate) fn record(size: u128) -> Result<(), Fault> {
    if over(size) {
        Err(fault(RECORD_TEXT))
    } else {
        Ok(())
    }
}

/// Whether the number `n` is above the limit, with no conversion of a large `n`.
fn exceeds(n: &Int) -> bool {
    n.to_u64().is_none_or(|n| over(u128::from(n)))
}

/// The bound on the bit length of the result of a static integer operator, from the bit lengths
/// `a` and `b` of its operands. `<<` has its own bound (`shl_bits`). The other operators make no
/// result longer than an operand, so their bound is in the limit.
pub(crate) fn int_bound(op: BinOp, a: u64, b: u64) -> u128 {
    let (a, b) = (u128::from(a), u128::from(b));
    match op {
        BinOp::Mul => a + b,
        BinOp::Add | BinOp::Sub | BinOp::And | BinOp::Or | BinOp::Xor => a.max(b) + 1,
        _ => a.max(b),
    }
}

/// The bit length of `x << k` for a count `k` that is not negative. It is exact and needs no
/// shift. A count above the limit is above the limit with no addition.
pub(crate) fn shl_bits(x: &Int, k: &Int) -> u128 {
    if x.is_zero() {
        0
    } else if exceeds(k) {
        LIMIT + 1
    } else {
        u128::from(x.bit_length()) + u128::from(k.to_u64().unwrap_or(0))
    }
}

/// The bit length of the number of parts `n`.
fn count_bits(n: usize) -> u128 {
    u128::from(usize::BITS - n.leading_zeros())
}

/// The largest bit length of the width, the leaf count, and the zero size plus 1 of `m`.
fn meta_bits(m: &Meta) -> u128 {
    let bits = |n: &Int| u128::from(n.bit_length());
    bits(&m.width)
        .max(bits(&m.leaves))
        .max(bits(&m.zero_size) + 1)
}

/// The bound on the bit lengths of the metadata sums of the parts `parts`, before the sums run.
/// A sum of `n` numbers below `2^b` is below `2^(b + bit length of n)`. The zero size gets 1
/// more, by `meta_bits`.
pub(crate) fn sum_bits<'a>(parts: impl ExactSizeIterator<Item = &'a Meta>) -> u128 {
    let count = count_bits(parts.len());
    parts.map(meta_bits).max().unwrap_or(0) + count
}

/// The bound on the bit lengths of the metadata of `[T; N]`, from the metadata `m` of `T`. Each
/// product gets the bound of `*`. The zero size `1 + N * z` gets 1 more.
pub(crate) fn array_bits(m: &Meta, n: &Int) -> u128 {
    u128::from(n.bit_length()) + meta_bits(m)
}

#[cfg(test)]
mod tests {
    use super::*;

    const L: u64 = 1 << 32;

    fn meta(width: u64, leaves: u64, zero_size: u64) -> Meta {
        Meta {
            width: Int::from_u64(width),
            leaves: Int::from_u64(leaves),
            zero_size: Int::from_u64(zero_size),
            data: true,
        }
    }

    fn big(bits: u32) -> Int {
        Int::from_u64(1).shl(u64::from(bits))
    }

    #[test]
    fn a_count_is_in_the_limit_up_to_2_pow_32() {
        assert!(!over(LIMIT) && over(LIMIT + 1));
        assert!(string(LIMIT).is_ok() && string(LIMIT + 1).is_err());
        assert!(list(LIMIT).is_ok() && list(LIMIT + 1).is_err());
        assert!(record(LIMIT).is_ok() && record(LIMIT + 1).is_err());
        assert!(capped(LIMIT).is_ok() && capped(LIMIT + 1).is_err());
        assert!(zero(&Int::from_u64(L)).is_ok());
        assert!(zero(&Int::from_u64(L + 1)).is_err());
        assert!(zero(&big(64)).is_err());
    }

    #[test]
    fn the_bound_of_an_integer_operator_comes_from_the_bit_lengths() {
        assert_eq!(int_bound(BinOp::Add, L - 1, 7), u128::from(L));
        assert_eq!(int_bound(BinOp::Sub, L, 0), u128::from(L) + 1);
        assert_eq!(int_bound(BinOp::Mul, 1 << 31, 1 << 31), u128::from(L));
        assert_eq!(
            int_bound(BinOp::Mul, 1 << 31, (1 << 31) + 1),
            u128::from(L) + 1
        );
        assert_eq!(int_bound(BinOp::And, L, 1), u128::from(L) + 1);
        assert_eq!(int_bound(BinOp::Or, L - 1, 1), u128::from(L));
        assert_eq!(int_bound(BinOp::Xor, 3, L), u128::from(L) + 1);
        assert_eq!(int_bound(BinOp::Div, L, L), u128::from(L));
        assert_eq!(int_bound(BinOp::Rem, L, L), u128::from(L));
    }

    #[test]
    fn a_shift_bound_needs_no_shift_and_no_addition_for_a_huge_count() {
        let one = Int::from_u64(1);
        assert_eq!(shl_bits(&one, &Int::from_u64(L - 1)), u128::from(L));
        assert_eq!(shl_bits(&one, &Int::from_u64(L)), u128::from(L) + 1);
        assert_eq!(shl_bits(&one, &big(100)), u128::from(L) + 1);
        assert_eq!(shl_bits(&one.neg(), &Int::from_u64(7)), 8);
        assert_eq!(shl_bits(&Int::zero(), &big(100)), 0);
    }

    #[test]
    fn the_metadata_bounds_add_one_bit_for_the_zero_size() {
        let bool_meta = meta(1, 1, 1);
        assert_eq!(array_bits(&bool_meta, &Int::from_u64(L - 1)), 32 + 2);
        assert_eq!(array_bits(&meta(8, 1, 4), &Int::from_u64(4)), 3 + 4);
        let wide = Meta {
            width: big(70),
            ..meta(0, 1, 1)
        };
        assert_eq!(array_bits(&wide, &Int::from_u64(1)), 71 + 1);
        assert_eq!(sum_bits([meta(8, 1, 4), meta(8, 1, 4)].iter()), 4 + 2);
        assert_eq!(sum_bits([].iter()), 0);
        assert_eq!(sum_bits([wide].iter()), 71 + 1);
        assert!(metadata(u128::from(L)).is_ok() && metadata(u128::from(L) + 1).is_err());
    }
}
