// SPDX-License-Identifier: Apache-2.0
//! The emitted module name of an instantiation (front-end spec 7.1).
//!
//! The generator writes the rule itself, so the names of the predicted
//! records do not come from the front ends. An argument of the builder is
//! an integer, a Boolean, or a function value. Only the first two are
//! readable, so a function gives the digest form.

use super::eval::Value;
use num_bigint::Sign;

/// The longest readable name, in bytes.
const READABLE: usize = 64;

/// The emitted name of module `module` for the argument tuple `args`: the
/// readable form, or the digest form if an argument is not readable or the
/// name is too long.
pub(crate) fn emitted(module: &str, args: &[Value]) -> String {
    let tokens: Option<Vec<String>> = args.iter().map(token).collect();
    if let Some(tokens) = tokens {
        let name = tokens.iter().fold(module.to_owned(), |n, t| n + "$" + t);
        if name.len() <= READABLE {
            return name;
        }
    }
    let serial: Vec<String> = args.iter().map(Value::serialize).collect();
    let text = format!("(instantiation root {module} ({}))", serial.join(" "));
    let [a, b, ..] = sha256(text.as_bytes());
    format!("{module}$0h{a:08x}{b:08x}")
}

/// The readable token of an integer below `2^256` or of a Boolean.
fn token(v: &Value) -> Option<String> {
    match v {
        Value::Int(n) if n.bits() >= 256 => None,
        Value::Int(n) if n.sign() == Sign::Minus => Some(format!("{}n", n.magnitude())),
        Value::Int(n) => Some(n.to_string()),
        Value::Bool(b) => Some(if *b { "1b" } else { "0b" }.to_owned()),
        _ => None,
    }
}

const K: [u32; 64] = [
    0x428a_2f98,
    0x7137_4491,
    0xb5c0_fbcf,
    0xe9b5_dba5,
    0x3956_c25b,
    0x59f1_11f1,
    0x923f_82a4,
    0xab1c_5ed5,
    0xd807_aa98,
    0x1283_5b01,
    0x2431_85be,
    0x550c_7dc3,
    0x72be_5d74,
    0x80de_b1fe,
    0x9bdc_06a7,
    0xc19b_f174,
    0xe49b_69c1,
    0xefbe_4786,
    0x0fc1_9dc6,
    0x240c_a1cc,
    0x2de9_2c6f,
    0x4a74_84aa,
    0x5cb0_a9dc,
    0x76f9_88da,
    0x983e_5152,
    0xa831_c66d,
    0xb003_27c8,
    0xbf59_7fc7,
    0xc6e0_0bf3,
    0xd5a7_9147,
    0x06ca_6351,
    0x1429_2967,
    0x27b7_0a85,
    0x2e1b_2138,
    0x4d2c_6dfc,
    0x5338_0d13,
    0x650a_7354,
    0x766a_0abb,
    0x81c2_c92e,
    0x9272_2c85,
    0xa2bf_e8a1,
    0xa81a_664b,
    0xc24b_8b70,
    0xc76c_51a3,
    0xd192_e819,
    0xd699_0624,
    0xf40e_3585,
    0x106a_a070,
    0x19a4_c116,
    0x1e37_6c08,
    0x2748_774c,
    0x34b0_bcb5,
    0x391c_0cb3,
    0x4ed8_aa4a,
    0x5b9c_ca4f,
    0x682e_6ff3,
    0x748f_82ee,
    0x78a5_636f,
    0x84c8_7814,
    0x8cc7_0208,
    0x90be_fffa,
    0xa450_6ceb,
    0xbef9_a3f7,
    0xc671_78f2,
];

/// SHA-256 of `data`. The digest form of a name needs it, and `srcgen`
/// may not use the code of `elab`.
fn sha256(data: &[u8]) -> [u32; 8] {
    let mut h: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];
    let mut padded = data.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&(data.len() as u64 * 8).to_be_bytes());
    for block in padded.as_chunks::<64>().0 {
        let mut w = [0u32; 64];
        for (slot, word) in w.iter_mut().zip(block.as_chunks::<4>().0) {
            *slot = u32::from_be_bytes(*word);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let mut v = h;
        for i in 0..64 {
            let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
            let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7]
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
            let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(maj);
            v = [
                t1.wrapping_add(t2),
                v[0],
                v[1],
                v[2],
                v[3].wrapping_add(t1),
                v[4],
                v[5],
                v[6],
            ];
        }
        for (a, b) in h.iter_mut().zip(v) {
            *a = a.wrapping_add(b);
        }
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{FnTy, STy};
    use num_bigint::BigInt;

    fn hex(data: &[u8]) -> String {
        sha256(data)
            .iter()
            .fold(String::new(), |hex, w| hex + &format!("{w:08x}"))
    }

    #[test]
    fn sha256_matches_the_standard_vectors() {
        assert_eq!(
            hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    #[test]
    fn integers_and_booleans_name_a_module_readably() {
        let args = [
            Value::Int(BigInt::from(-5)),
            Value::Bool(true),
            Value::Int(BigInt::from(16)),
        ];
        assert_eq!(emitted("M1", &args), "M1$5n$1b$16");
        assert_eq!(emitted("M0", &[]), "M0");
    }

    #[test]
    fn a_function_or_a_long_name_takes_the_digest_form() {
        let f = Value::Function(
            "h0".to_owned(),
            FnTy {
                params: vec![(false, STy::Int)],
                ret: STy::Int,
            },
        );
        let name = emitted("M1", &[f]);
        assert!(
            name.starts_with("M1$0h") && name.len() == "M1$0h".len() + 16,
            "{name}"
        );
        let wide = Value::Int(BigInt::from(1) << 200);
        let long = emitted("M1", &[wide.clone(), wide]);
        assert!(long.starts_with("M1$0h"), "{long}");
    }
}
