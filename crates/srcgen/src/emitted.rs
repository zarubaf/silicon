// SPDX-License-Identifier: Apache-2.0
//! The emitted module name of an instantiation (front-end spec 7.1).
//!
//! The generator writes the rule itself, so the names of the predicted
//! records do not come from the front ends. An argument of the builder is
//! an integer, a Boolean, or a function value. Only the first two are
//! readable, so a function gives the digest form.

use super::eval::Value;
use num_bigint::Sign;
use sha2::{Digest, Sha256};

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
    let digest = Sha256::digest(text.as_bytes());
    let head = digest.first_chunk::<8>().copied().unwrap_or_default();
    format!("{module}$0h{:016x}", u64::from_be_bytes(head))
}

/// The readable token of an integer of magnitude below `2^256` (at most
/// 256 bits, as `intToken` of the Lean spec), or of a Boolean.
fn token(v: &Value) -> Option<String> {
    match v {
        Value::Int(n) if n.bits() > 256 => None,
        Value::Int(n) if n.sign() == Sign::Minus => Some(format!("{}n", n.magnitude())),
        Value::Int(n) => Some(n.to_string()),
        Value::Bool(b) => Some(if *b { "1b" } else { "0b" }.to_owned()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{FnTy, STy};
    use num_bigint::BigInt;

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
    fn an_integer_below_2_pow_256_has_a_token() {
        let top = (BigInt::from(1) << 256) - 1;
        assert!(token(&Value::Int(top)).is_some());
        assert!(token(&Value::Int(BigInt::from(1) << 256)).is_none());
        assert!(token(&Value::Int(BigInt::from(-1) * (BigInt::from(1) << 256))).is_none());
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
