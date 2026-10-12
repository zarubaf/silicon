// SPDX-License-Identifier: Apache-2.0
//! The static integer of any size. This module is the small interface of design section 4.5:
//! only it uses `num-bigint`, so a proof can take a Lean model of it as an assumption. It also
//! holds each conversion between an integer and the bit vector of a finite value.

use core_ir::Bits;
use num_bigint::{BigInt, BigUint, Sign};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

/// An integer of any size, as Lean `Int`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Int(BigInt);

impl Int {
    #[must_use]
    pub fn zero() -> Int {
        Int(BigInt::ZERO)
    }

    #[must_use]
    pub fn from_u64(n: u64) -> Int {
        Int(BigInt::from(n))
    }

    /// The value of canonical decimal digits, such as those of a source number.
    #[must_use]
    pub fn from_decimal(digits: &str) -> Option<Int> {
        BigInt::parse_bytes(digits.as_bytes(), 10).map(Int)
    }

    /// The unsigned value of a finite value.
    #[must_use]
    pub fn from_unsigned(x: &Bits) -> Int {
        Int(BigInt::from_biguint(Sign::Plus, x.to_biguint()))
    }

    /// The two's complement value of the bits of a finite value, read at the width `width`.
    #[must_use]
    pub fn from_signed(x: &Bits, width: u32) -> Int {
        let unsigned = BigInt::from_biguint(Sign::Plus, x.to_biguint());
        if width > 0 && bit(x, width - 1) {
            Int(unsigned - (BigInt::from(1u8) << width))
        } else {
            Int(unsigned)
        }
    }

    /// Feeds the value to `h`.
    pub fn hash_into(&self, h: &mut impl Hasher) {
        self.0.hash(h);
    }

    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.sign() == Sign::NoSign
    }

    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.0.sign() == Sign::Minus
    }

    /// `natAbs.log2` of Lean: the floor of the binary logarithm of the magnitude, and 0 for 0.
    #[must_use]
    pub fn log2(&self) -> u64 {
        self.0.bits().saturating_sub(1)
    }

    /// The value, if it is from 0 to `u64::MAX`.
    #[must_use]
    pub fn to_u64(&self) -> Option<u64> {
        u64::try_from(&self.0).ok()
    }

    /// Whether `0 <= self < 2^width`.
    #[must_use]
    pub fn fits_unsigned(&self, width: u64) -> bool {
        !self.is_negative() && self.0.bits() <= width
    }

    /// Whether `-2^(width - 1) <= self < 2^(width - 1)`, for `width >= 1`.
    #[must_use]
    pub fn fits_signed(&self, width: u64) -> bool {
        let limit = width.saturating_sub(1);
        let magnitude = self.0.magnitude();
        if self.is_negative() {
            // The magnitude is at most `2^limit`.
            magnitude.bits() <= limit
                || (magnitude.bits() == limit + 1 && magnitude.trailing_zeros() == Some(limit))
        } else {
            magnitude.bits() <= limit
        }
    }

    /// `BitVec.ofInt width self`: the value modulo `2^width`, or `None` for the width 0.
    #[must_use]
    pub fn to_finite(&self, width: u32) -> Option<Bits> {
        let modulus = BigInt::from(1u8) << width;
        let rem = ((&self.0 % &modulus) + &modulus) % &modulus;
        Bits::new(width, rem.magnitude().clone())
    }

    #[must_use]
    pub fn add(&self, other: &Int) -> Int {
        Int(&self.0 + &other.0)
    }

    #[must_use]
    pub fn sub(&self, other: &Int) -> Int {
        Int(&self.0 - &other.0)
    }

    #[must_use]
    pub fn mul(&self, other: &Int) -> Int {
        Int(&self.0 * &other.0)
    }

    /// The quotient rounded toward zero, `Int.tdiv`. The divisor is not 0.
    #[must_use]
    pub fn tdiv(&self, other: &Int) -> Int {
        Int(&self.0 / &other.0)
    }

    /// The remainder with the sign of the dividend, `Int.tmod`. The divisor is not 0.
    #[must_use]
    pub fn tmod(&self, other: &Int) -> Int {
        Int(&self.0 % &other.0)
    }

    #[must_use]
    pub fn neg(&self) -> Int {
        Int(-&self.0)
    }

    /// `-self - 1`, the complement in infinite two's complement.
    #[must_use]
    pub fn not(&self) -> Int {
        Int(!&self.0)
    }

    #[must_use]
    pub fn and(&self, other: &Int) -> Int {
        Int(&self.0 & &other.0)
    }

    #[must_use]
    pub fn or(&self, other: &Int) -> Int {
        Int(&self.0 | &other.0)
    }

    #[must_use]
    pub fn xor(&self, other: &Int) -> Int {
        Int(&self.0 ^ &other.0)
    }

    /// `self * 2^k`.
    #[must_use]
    pub fn shl(&self, k: u64) -> Int {
        Int(&self.0 << k)
    }

    /// `floor (self / 2^k)`.
    #[must_use]
    pub fn shr(&self, k: u64) -> Int {
        Int(&self.0 >> k)
    }

    /// The order of `self` and a small number.
    #[must_use]
    pub fn cmp_u64(&self, n: u64) -> Ordering {
        self.0.cmp(&BigInt::from(n))
    }
}

/// The finite value of the width `width` with the unsigned value `n`, or `None` if `n` does not
/// fit the width or the width is 0.
#[must_use]
pub fn finite(width: u32, n: u64) -> Option<Bits> {
    Bits::new(width, BigUint::from(n))
}

/// The bit at the index `i` of a finite value, read without a copy.
#[must_use]
pub fn bit(x: &Bits, i: u32) -> bool {
    x.value().bit(u64::from(i))
}

/// The natural number `n` as the value of a core constant.
#[must_use]
pub fn nat(n: u64) -> Nat {
    BigUint::from(n)
}

/// The value of a core constant of a finite value.
#[must_use]
pub fn constant(x: &Bits) -> Nat {
    x.to_biguint()
}

/// The value of a core constant, a natural number. It is an alias and not a wrapper, because
/// `Expr::Const` of `core-ir` takes a `BigUint`.
pub type Nat = BigUint;

/// `min(x, limit)` for the unsigned value of a finite value, read without a copy.
#[must_use]
pub fn min_unsigned(x: &Bits, limit: u32) -> u32 {
    let bits = x.value();
    if *bits < BigUint::from(limit) {
        bits.iter_u32_digits().next().unwrap_or(0)
    } else {
        limit
    }
}

/// The size of the unsigned value of a finite value, as `intSize` of Lean: 1 for each 64-bit
/// word, and at least 1.
#[must_use]
pub fn unsigned_size(x: &Bits) -> u64 {
    x.value().bits().saturating_sub(1) / 64 + 1
}

impl fmt::Debug for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The decimal form, with `-` before a negative value.
impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
