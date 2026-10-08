//! Fixed-width bit-vector values and the combinational operations of the core IR.

use num_bigint::BigUint;

/// Comparison predicate of `icmp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pred {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

/// A bit-vector of width at least 1. The value always fits the width.
///
/// Binary operations assume equal operand widths. The checker guarantees this.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bits {
    width: u32,
    value: BigUint,
}

fn mask(width: u32) -> BigUint {
    (BigUint::from(1u8) << width) - 1u8
}

impl Bits {
    /// Returns `None` if `width` is 0 or `value` does not fit in `width` bits.
    #[must_use]
    pub fn new(width: u32, value: BigUint) -> Option<Bits> {
        (width >= 1 && value.bits() <= u64::from(width)).then_some(Bits { width, value })
    }

    /// The all-zero value. A width of 0 is clamped to 1 so the value stays valid.
    #[must_use]
    pub fn zero(width: u32) -> Bits {
        Bits {
            width: width.max(1),
            value: BigUint::ZERO,
        }
    }

    #[must_use]
    pub fn width(&self) -> u32 {
        self.width
    }

    #[must_use]
    pub fn to_biguint(&self) -> BigUint {
        self.value.clone()
    }

    /// Wraps `value` modulo `2^width`.
    fn wrap(width: u32, value: BigUint) -> Bits {
        Bits {
            width,
            value: value & mask(width),
        }
    }

    fn same_width(&self, other: &Bits) {
        debug_assert_eq!(self.width, other.width, "operand widths differ");
    }

    fn sign(&self) -> bool {
        self.value.bit(u64::from(self.width - 1))
    }

    #[must_use]
    pub fn add(&self, other: &Bits) -> Bits {
        self.same_width(other);
        Bits::wrap(self.width, &self.value + &other.value)
    }

    #[must_use]
    pub fn sub(&self, other: &Bits) -> Bits {
        self.same_width(other);
        let modulus = BigUint::from(1u8) << self.width;
        Bits::wrap(self.width, &self.value + modulus - &other.value)
    }

    #[must_use]
    pub fn mul(&self, other: &Bits) -> Bits {
        self.same_width(other);
        Bits::wrap(self.width, &self.value * &other.value)
    }

    #[must_use]
    pub fn and(&self, other: &Bits) -> Bits {
        self.same_width(other);
        Bits {
            width: self.width,
            value: &self.value & &other.value,
        }
    }

    #[must_use]
    pub fn or(&self, other: &Bits) -> Bits {
        self.same_width(other);
        Bits {
            width: self.width,
            value: &self.value | &other.value,
        }
    }

    #[must_use]
    pub fn xor(&self, other: &Bits) -> Bits {
        self.same_width(other);
        Bits {
            width: self.width,
            value: &self.value ^ &other.value,
        }
    }

    #[must_use]
    pub fn not(&self) -> Bits {
        Bits {
            width: self.width,
            value: mask(self.width) ^ &self.value,
        }
    }

    /// The shift amount if it is below the width, else `None`.
    fn amount(&self, other: &Bits) -> Option<u32> {
        self.same_width(other);
        (other.value < BigUint::from(self.width))
            .then(|| other.value.iter_u32_digits().next().unwrap_or(0))
    }

    #[must_use]
    pub fn shl(&self, other: &Bits) -> Bits {
        match self.amount(other) {
            Some(s) => Bits::wrap(self.width, &self.value << s),
            None => Bits::zero(self.width),
        }
    }

    #[must_use]
    pub fn shru(&self, other: &Bits) -> Bits {
        match self.amount(other) {
            Some(s) => Bits {
                width: self.width,
                value: &self.value >> s,
            },
            None => Bits::zero(self.width),
        }
    }

    #[must_use]
    pub fn shrs(&self, other: &Bits) -> Bits {
        let shifted = match self.amount(other) {
            Some(s) => &self.value >> s,
            None => BigUint::ZERO,
        };
        if !self.sign() {
            return Bits {
                width: self.width,
                value: shifted,
            };
        }
        // The vacated high bits take the sign: all bits that `shifted` cannot reach.
        let reach = match self.amount(other) {
            Some(s) => mask(self.width) >> s,
            None => BigUint::ZERO,
        };
        Bits {
            width: self.width,
            value: shifted | (mask(self.width) ^ reach),
        }
    }

    #[must_use]
    pub fn icmp(&self, pred: Pred, other: &Bits) -> Bits {
        self.same_width(other);
        // Flipping the sign bit maps signed order onto unsigned order.
        let flip = BigUint::from(1u8) << (self.width - 1);
        let (ua, ub) = (&self.value, &other.value);
        let (sa, sb) = (ua ^ &flip, ub ^ &flip);
        let holds = match pred {
            Pred::Eq => ua == ub,
            Pred::Ne => ua != ub,
            Pred::Ult => ua < ub,
            Pred::Ule => ua <= ub,
            Pred::Ugt => ua > ub,
            Pred::Uge => ua >= ub,
            Pred::Slt => sa < sb,
            Pred::Sle => sa <= sb,
            Pred::Sgt => sa > sb,
            Pred::Sge => sa >= sb,
        };
        Bits {
            width: 1,
            value: BigUint::from(u8::from(holds)),
        }
    }

    /// `self` gives the high bits.
    #[must_use]
    pub fn concat(&self, other: &Bits) -> Bits {
        Bits {
            width: self.width + other.width,
            value: (&self.value << other.width) | &other.value,
        }
    }

    /// The `n` bits from `lo` upward. Requires `n >= 1` and `lo + n <= width`.
    #[must_use]
    pub fn extract(&self, lo: u32, n: u32) -> Bits {
        debug_assert!(n >= 1 && lo + n <= self.width, "extract out of range");
        Bits::wrap(n, &self.value >> lo)
    }

    /// `k` copies of `self`. Requires `k >= 1`.
    #[must_use]
    pub fn replicate(&self, k: u32) -> Bits {
        debug_assert!(k >= 1, "replicate count is 0");
        let value = (0..k).fold(BigUint::ZERO, |acc, _| (acc << self.width) | &self.value);
        Bits {
            width: self.width * k,
            value,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn b(w: u32, v: u64) -> Bits {
        Bits::new(w, BigUint::from(v)).unwrap()
    }

    #[test]
    fn wide_add_carries() {
        let a = Bits::new(1000, (BigUint::from(1u8) << 64) - 1u8).unwrap();
        let r = a.add(&Bits::new(1000, BigUint::from(1u8)).unwrap());
        assert_eq!(r.to_biguint(), BigUint::from(1u8) << 64);
    }
    #[test]
    fn add_wraps() {
        assert_eq!(b(8, 255).add(&b(8, 1)), b(8, 0));
    }
    #[test]
    fn shift_by_width() {
        assert_eq!(b(4, 0b1001).shl(&b(4, 4)), b(4, 0));
        assert_eq!(b(4, 0b1001).shru(&b(4, 4)), b(4, 0));
        assert_eq!(b(4, 0b1001).shrs(&b(4, 4)), b(4, 0b1111));
    }
    #[test]
    fn shift_by_max() {
        assert_eq!(b(4, 0b0110).shrs(&b(4, 15)), b(4, 0));
    }
    #[test]
    fn signed_compare() {
        assert_eq!(b(2, 0b10).icmp(Pred::Slt, &b(2, 0b01)), b(1, 1));
    }
    #[test]
    fn concat_puts_first_high() {
        assert_eq!(b(2, 0b10).concat(&b(2, 0b01)), b(4, 0b1001));
    }
    #[test]
    fn rejects_zero_width_and_overflow() {
        assert!(Bits::new(0, BigUint::ZERO).is_none());
        assert!(Bits::new(2, BigUint::from(4u8)).is_none());
    }
}
