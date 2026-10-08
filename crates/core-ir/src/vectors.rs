//! The `in=` and `out=` vector lines of `run` (spec section 6.4.3).

use std::fmt;

use num_bigint::BigUint;

use crate::Bits;
use crate::typed::Module;

/// A fault in an input line. `run` reports it as a usage error, not as a
/// design error, so it has no error code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VectorError {
    /// The line does not match the tokenization of an input line.
    Syntax,
    /// The line lacks this input.
    Missing(String),
    /// The line lists this name after the last input.
    Extra(String),
    /// The top module has no data input with this name.
    Unknown(String),
    /// This input is not at its place in the port order.
    OutOfOrder(String),
    /// The value of this input does not fit its width.
    TooWide(String),
}

impl fmt::Display for VectorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VectorError::Syntax => write!(f, "the input line is not `in=(NAME VALUE ...)`"),
            VectorError::Missing(name) => write!(f, "the input `{name}` is missing"),
            VectorError::Extra(name) => write!(f, "`{name}` follows the last input"),
            VectorError::Unknown(name) => write!(f, "the top module has no input `{name}`"),
            VectorError::OutOfOrder(name) => write!(f, "the input `{name}` is out of port order"),
            VectorError::TooWide(name) => write!(f, "the value of `{name}` does not fit its width"),
        }
    }
}

impl std::error::Error for VectorError {}

fn is_blank(c: char) -> bool {
    c == ' ' || c == '\t'
}

/// Reads one input line, without its LF, into the values of the data inputs
/// of `top`, in port order.
///
/// # Errors
/// Returns the first fault of the line.
pub fn parse_input(line: &str, top: &Module) -> Result<Vec<Bits>, VectorError> {
    let body = line
        .trim_matches(is_blank)
        .strip_prefix("in=(")
        .and_then(|rest| rest.strip_suffix(')'))
        .ok_or(VectorError::Syntax)?;
    let tokens: Vec<&str> = body.split(is_blank).filter(|t| !t.is_empty()).collect();
    let valid = |t: &str| {
        t.chars()
            .all(|c| c.is_ascii_alphanumeric() || "_$".contains(c))
    };
    let (pairs, odd) = tokens.as_chunks::<2>();
    if !odd.is_empty() || !tokens.iter().all(|t| valid(t)) {
        return Err(VectorError::Syntax);
    }
    let mut values = Vec::with_capacity(top.inputs.len());
    for (k, &[name, digits]) in pairs.iter().enumerate() {
        let Some(port) = top.inputs.get(k) else {
            return Err(VectorError::Extra(name.into()));
        };
        if name != port.name {
            return Err(if top.inputs.iter().any(|p| p.name == name) {
                VectorError::OutOfOrder(name.into())
            } else {
                VectorError::Unknown(name.into())
            });
        }
        if !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(VectorError::Syntax);
        }
        let value = BigUint::parse_bytes(digits.as_bytes(), 10).ok_or(VectorError::Syntax)?;
        values.push(Bits::new(port.width, value).ok_or(VectorError::TooWide(name.into()))?);
    }
    if let Some(port) = top.inputs.get(values.len()) {
        return Err(VectorError::Missing(port.name.clone()));
    }
    Ok(values)
}

/// Prints the `out=` line of the outputs `values` of `top`, with its LF.
#[must_use]
pub fn print_output(top: &Module, values: &[Bits]) -> String {
    let pairs: Vec<String> = top
        .outputs
        .iter()
        .zip(values)
        .map(|(port, value)| format!("{} {}", port.name, value.to_biguint()))
        .collect();
    format!("out=({})\n", pairs.join(" "))
}
