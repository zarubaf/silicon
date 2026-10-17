// SPDX-License-Identifier: Apache-2.0
//! The static integer of any size. This module is the small interface of design section 4.5:
//! only it uses `num-bigint`, so a proof can take a Lean model of it as an assumption. It also
//! holds each conversion between an integer and the bit vector of a finite value.

use core_ir::Bits;
use num_bigint::{BigInt, BigUint, Sign};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};

/// An integer of any size, as Lean `Int`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Int(BigInt);

impl Int {
    /// The one place that makes an integer from a result: every operation ends here, so the
    /// test counters see the 64-bit words of a wide result, which no charge site sees.
    fn make(x: BigInt) -> Int {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Words, x.bits().div_ceil(64).max(1));
        Int(x)
    }

    /// The integer 0, for a constant.
    pub const ZERO: Int = Int(BigInt::ZERO);

    #[must_use]
    pub fn zero() -> Int {
        Int::ZERO
    }

    #[must_use]
    pub fn from_u64(n: u64) -> Int {
        Int::make(BigInt::from(n))
    }

    /// The value of canonical decimal digits, such as those of a source number.
    #[must_use]
    pub fn from_decimal(digits: &str) -> Option<Int> {
        BigInt::parse_bytes(digits.as_bytes(), 10).map(Int::make)
    }

    /// The unsigned value of a finite value.
    #[must_use]
    pub fn from_unsigned(x: &Bits) -> Int {
        Int::make(BigInt::from_biguint(Sign::Plus, x.to_biguint()))
    }

    /// The two's complement value of the bits of a finite value, read at the width `width`.
    #[must_use]
    pub fn from_signed(x: &Bits, width: u32) -> Int {
        let unsigned = BigInt::from_biguint(Sign::Plus, x.to_biguint());
        if width > 0 && bit(x, width - 1) {
            Int::make(unsigned - (BigInt::from(1u8) << width))
        } else {
            Int::make(unsigned)
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

    /// The bit length of the magnitude: 0 for 0.
    #[must_use]
    pub fn bit_length(&self) -> u64 {
        self.0.bits()
    }

    /// The length in bytes of the decimal form, with the `-` of a negative value, computed
    /// without the form. The digits come from the bit length and the top 64 bits, which a
    /// float estimates. A value too near a power of ten for the estimate takes one exact
    /// comparison with that power. Thus a large value costs no conversion to decimal.
    #[must_use]
    pub fn decimal_len(&self) -> u64 {
        self.decimal_len_with(&mut Pow10::new())
    }

    /// `decimal_len` with the powers of ten of `pow`: a value near a power of ten builds that
    /// power once, and a later value with the same digit count finds it.
    #[must_use]
    pub(crate) fn decimal_len_with(&self, pow: &mut Pow10) -> u64 {
        u64::from(self.is_negative()) + digits(self.0.magnitude(), pow)
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
        // The modulus `2^width` takes one word for each 64 bits of the width, whatever the value.
        #[cfg(test)]
        crate::counters::add(
            crate::counters::Count::Words,
            u64::from(width).div_ceil(64) + 1,
        );
        let modulus = BigInt::from(1u8) << width;
        let rem = ((&self.0 % &modulus) + &modulus) % &modulus;
        Bits::new(width, rem.magnitude().clone())
    }

    #[must_use]
    pub fn add(&self, other: &Int) -> Int {
        Int::make(&self.0 + &other.0)
    }

    /// Adds `other` in place: the work is in the words of `other` and its carry, not in the
    /// words of `self`.
    pub fn add_assign(&mut self, other: &Int) {
        #[cfg(test)]
        crate::counters::add(
            crate::counters::Count::Words,
            other.0.bits().div_ceil(64).max(1),
        );
        self.0 += &other.0;
    }

    /// The 64-bit words of the magnitude, for the tests of the work of an addition.
    #[cfg(test)]
    pub(crate) fn words(&self) -> Vec<u64> {
        self.0.magnitude().to_u64_digits()
    }

    #[must_use]
    pub fn sub(&self, other: &Int) -> Int {
        Int::make(&self.0 - &other.0)
    }

    #[must_use]
    pub fn mul(&self, other: &Int) -> Int {
        Int::make(&self.0 * &other.0)
    }

    /// The quotient rounded toward zero, `Int.tdiv`. The divisor is not 0.
    #[must_use]
    pub fn tdiv(&self, other: &Int) -> Int {
        Int::make(&self.0 / &other.0)
    }

    /// The remainder with the sign of the dividend, `Int.tmod`. The divisor is not 0.
    #[must_use]
    pub fn tmod(&self, other: &Int) -> Int {
        Int::make(&self.0 % &other.0)
    }

    #[must_use]
    pub fn neg(&self) -> Int {
        Int::make(-&self.0)
    }

    /// `-self - 1`, the complement in infinite two's complement.
    #[must_use]
    pub fn not(&self) -> Int {
        Int::make(!&self.0)
    }

    #[must_use]
    pub fn and(&self, other: &Int) -> Int {
        Int::make(&self.0 & &other.0)
    }

    #[must_use]
    pub fn or(&self, other: &Int) -> Int {
        Int::make(&self.0 | &other.0)
    }

    #[must_use]
    pub fn xor(&self, other: &Int) -> Int {
        Int::make(&self.0 ^ &other.0)
    }

    /// `self * 2^k`.
    #[must_use]
    pub fn shl(&self, k: u64) -> Int {
        Int::make(&self.0 << k)
    }

    /// `floor (self / 2^k)`.
    #[must_use]
    pub fn shr(&self, k: u64) -> Int {
        Int::make(&self.0 >> k)
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

/// The low 32 bits of a word.
fn low_half(word: u64) -> u32 {
    u32::try_from(word & u64::from(u32::MAX)).unwrap_or(0)
}

/// The bit buffer of a static pack (section 5.1): the words of 64 bits, the least significant
/// word first, and the next free bit. A pack allocates one buffer for its width and writes each
/// leaf at its offset, so a leaf of `w` bits takes `w / 64 + 1` word steps at most, and no step
/// reads an earlier leaf.
pub(crate) struct BitBuf {
    words: Vec<u64>,
    next: u64,
}

impl BitBuf {
    /// An empty buffer of `width` bits.
    #[must_use]
    pub(crate) fn new(width: u32) -> BitBuf {
        BitBuf {
            words: vec![0; usize::try_from(u64::from(width).div_ceil(64)).unwrap_or(0)],
            next: 0,
        }
    }

    /// Writes one word `word` of `bits` bits at the next free bit.
    fn put_word(&mut self, word: u64, offset: u64) {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Packed, 1);
        let (index, shift) = (
            usize::try_from(offset / 64).unwrap_or(usize::MAX),
            offset % 64,
        );
        if let Some(low) = self.words.get_mut(index) {
            *low |= word << shift;
        }
        if shift != 0
            && let Some(high) = self.words.get_mut(index.saturating_add(1))
        {
            *high |= word >> (64 - shift);
        }
    }

    /// Writes the bits of the finite value `x` at the next free bit, one word of `x` for each
    /// step. The bits of `x` above its width are zero, so a word adds no bit after the leaf.
    pub(crate) fn put(&mut self, x: &Bits) {
        for (k, word) in x.value().iter_u64_digits().enumerate() {
            self.put_word(word, self.next + 64 * k as u64);
        }
        self.next += u64::from(x.width());
    }

    /// Writes the bit `b` at the next free bit.
    pub(crate) fn put_bit(&mut self, b: bool) {
        self.put_word(u64::from(b), self.next);
        self.next += 1;
    }

    /// The finite value of `width` bits that the buffer holds, or `None` for the width 0.
    #[must_use]
    pub(crate) fn finish(self, width: u32) -> Option<Bits> {
        let halves: Vec<u32> = self
            .words
            .iter()
            .flat_map(|w| [low_half(*w), low_half(*w >> 32)])
            .collect();
        Bits::new(width, BigUint::from_slice(&halves))
    }
}

/// The number of 64-bit words that the value of `x` takes, at least 1. A constant of a wide type
/// with a small value takes one word: the width is a number beside it.
#[cfg(test)]
pub(crate) fn word_count(x: &Bits) -> u64 {
    x.value().bits().div_ceil(64).max(1)
}

/// The 64-bit words of a finite value, the least significant word first. A value of at most
/// 65536 bits has at most 1024 words.
#[must_use]
pub(crate) fn words(x: &Bits) -> Vec<u64> {
    x.value().to_u64_digits()
}

/// The 32 bits of the little-endian words `words` from the bit `at`. A bit above the words is 0.
fn half(words: &[u64], at: u64) -> u32 {
    let (index, shift) = (usize::try_from(at / 64).unwrap_or(usize::MAX), at % 64);
    let low = words.get(index).copied().unwrap_or(0) >> shift;
    let high = if shift == 0 {
        0
    } else {
        words.get(index.saturating_add(1)).copied().unwrap_or(0) << (64 - shift)
    };
    low_half(low | high)
}

/// The bit at the index `at` of the little-endian words. A bit above the words is 0.
#[must_use]
pub(crate) fn word_bit(words: &[u64], at: u64) -> bool {
    let index = usize::try_from(at / 64).unwrap_or(usize::MAX);
    words.get(index).is_some_and(|w| (w >> (at % 64)) & 1 == 1)
}

/// The finite value of `width` bits that the little-endian words hold from the bit `off`, or
/// `None` for the width 0. A bit above the words is 0. It takes one step for each 32 bits of
/// the width, so a read costs `width / 32 + 1` steps whatever the offset and the length of the
/// words are.
#[must_use]
pub(crate) fn read_bits(words: &[u64], off: u64, width: u32) -> Option<Bits> {
    let mut halves: Vec<u32> = (0..u64::from(width).div_ceil(32))
        .map(|k| half(words, off.saturating_add(32 * k)))
        .collect();
    if !width.is_multiple_of(32)
        && let Some(last) = halves.last_mut()
    {
        *last &= (1u32 << (width % 32)) - 1;
    }
    Bits::new(width, BigUint::from_slice(&halves))
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

/// `log10(2)`.
const LOG10_2: f64 = std::f64::consts::LOG10_2;

/// The powers of ten that the exact check of a digit count built, by exponent.
pub(crate) type Pow10 = BTreeMap<u64, BigUint>;

/// `10^e`, built once for each exponent by squaring.
fn pow10(e: u64, pow: &mut Pow10) -> &BigUint {
    pow.entry(e).or_insert_with(|| {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Powered, 1);
        let (mut result, mut base, mut rest) = (BigUint::from(1u32), BigUint::from(10u32), e);
        while rest > 0 {
            if rest & 1 == 1 {
                result *= &base;
            }
            rest >>= 1;
            if rest > 0 {
                base = &base * &base;
            }
        }
        result
    })
}

/// The number of decimal digits of `m`, and 1 for 0.
#[allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)]
fn digits(m: &BigUint, pow: &mut Pow10) -> u64 {
    let bits = m.bits();
    if bits <= 64 {
        let v = u64::try_from(m).unwrap_or(0);
        return v.checked_ilog10().map_or(1, |d| u64::from(d) + 1);
    }
    let limbs = m.to_u64_digits();
    let [.., second, first] = limbs.as_slice() else {
        return 1;
    };
    let two = (u128::from(*first) << 64) | u128::from(*second);
    let top = (two << first.leading_zeros()) >> 64;
    let estimate = (top as f64).log10() + (bits - 64) as f64 * LOG10_2;
    let fraction = estimate.fract();
    let slack = 1e-9 + bits as f64 * 1e-15;
    if fraction > slack && fraction < 1.0 - slack {
        return estimate as u64 + 1;
    }
    // Too near a power of ten for the estimate. The exponent `e` with `10^e <= m < 10^(e + 1)`
    // takes comparisons with exact powers, for any exponent: the estimate only starts the search.
    // One power of ten serves both bounds, so a run of values near one boundary builds one.
    let mut e = estimate as u64;
    while e > 0 && *m < *pow10(e, pow) {
        e -= 1;
    }
    while *m >= pow10(e, pow) * 10u32 {
        e += 1;
    }
    e + 1
}

impl fmt::Debug for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The decimal form, with `-` before a negative value.
impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Formatted, self.decimal_len());
        write!(f, "{}", self.0)
    }
}
