//! The bound of a number literal. The lexer applies it, so a literal that is not below
//! 2^65536 is an error token, as in the Lean lexer.

/// Whether the text of a number literal, with its `0x` or `0b` prefix, has a value below
/// 2^65536. No width is larger, so a larger literal has no use. The check reads each digit
/// once, except at the boundary of a decimal literal, where it converts at most 19729
/// digits.
pub fn literal_in_bounds(text: &str) -> bool {
    // Digit counts for 2^65536 - 1: 16384 hex digits, 65536 binary digits, and in
    // decimal every count up to 19728 is below, and 19729 needs the exact check.
    let (digits, hex, bin) = match (text.strip_prefix("0x"), text.strip_prefix("0b")) {
        (Some(d), _) => (d, 16384, 0),
        (_, Some(d)) => (d, 0, 65536),
        _ => (text, 0, 0),
    };
    let digits = digits.trim_start_matches('0');
    match (hex, bin) {
        (16384, _) => digits.len() <= 16384,
        (_, 65536) => digits.len() <= 65536,
        _ => match digits.len() {
            0..=19728 => true,
            19729 => decimal_below_2_pow_65536(digits),
            _ => false,
        },
    }
}

/// Whether decimal digits are below 2^65536: the value has at most 2048 limbs of 32 bits.
fn decimal_below_2_pow_65536(digits: &str) -> bool {
    let mut limbs: Vec<u32> = Vec::new();
    for chunk in digits.as_bytes().chunks(9) {
        let mut scale = 1u64;
        let mut carry = 0u64;
        for digit in chunk {
            scale *= 10;
            carry = carry * 10 + u64::from(digit - b'0');
        }
        for limb in &mut limbs {
            let value = u64::from(*limb) * scale + carry;
            *limb = u32::try_from(value & 0xFFFF_FFFF).unwrap_or(0);
            carry = value >> 32;
        }
        while carry > 0 {
            limbs.push(u32::try_from(carry & 0xFFFF_FFFF).unwrap_or(0));
            carry >>= 32;
        }
    }
    limbs.len() <= 2048
}
