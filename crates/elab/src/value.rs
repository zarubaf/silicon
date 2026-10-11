// SPDX-License-Identifier: Apache-2.0
//! The static values of slice 1, their canonical serialization, and their recursive size, as
//! Lean `Source.Value` defines them. Section 7.1 of the front-end spec uses the serialization
//! in an `InstantiationId`, and section 5.4 uses the size in the cost model.

use crate::int::Int;
use core_ir::Bits;

/// A type as a static value: the scalar types of slice 1. A width is from 1 to 65536.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Nat,
    Int,
    UInt(u32),
    SInt(u32),
}

/// A static value of slice 1. A finite value holds the bit vector of the core semantics with
/// the width of its type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(Int),
    Bool(bool),
    Str(String),
    UInt(Bits),
    SInt(Bits),
    Type(Ty),
}

/// The size of an integer: 1 for each 64-bit word of its magnitude, and at least 1.
#[must_use]
pub fn int_size(n: &Int) -> u64 {
    n.log2() / 64 + 1
}

/// The size of a finite value: 1 for each 64-bit word of its width, and at least 1.
#[must_use]
pub fn width_size(width: u32) -> u64 {
    u64::from(width).div_ceil(64).max(1)
}

impl Ty {
    /// `UInt[W]` or `SInt[W]`.
    #[must_use]
    pub fn is_finite(self) -> bool {
        matches!(self, Ty::UInt(_) | Ty::SInt(_))
    }

    #[must_use]
    pub fn serialize(self) -> String {
        match self {
            Ty::Bool => "bool".to_owned(),
            Ty::Nat => "nat".to_owned(),
            Ty::Int => "int".to_owned(),
            Ty::UInt(w) => format!("(uint {w})"),
            Ty::SInt(w) => format!("(sint {w})"),
        }
    }

    /// The number of nodes of the type term. A width counts as an integer payload.
    #[must_use]
    pub fn size(self) -> u64 {
        match self {
            Ty::Bool | Ty::Nat | Ty::Int => 1,
            Ty::UInt(w) | Ty::SInt(w) => 1 + int_size(&Int::from_u64(u64::from(w))),
        }
    }

    /// The source form, for a message.
    #[must_use]
    pub fn text(self) -> String {
        match self {
            Ty::Bool => "Bool".to_owned(),
            Ty::Nat => "Nat".to_owned(),
            Ty::Int => "Int".to_owned(),
            Ty::UInt(w) => format!("UInt[{w}]"),
            Ty::SInt(w) => format!("SInt[{w}]"),
        }
    }
}

impl Value {
    /// The type of a value. A string and a type have no `Ty` in slice 1.
    #[must_use]
    pub fn ty(&self) -> Option<Ty> {
        match self {
            Value::Int(_) => Some(Ty::Int),
            Value::Bool(_) => Some(Ty::Bool),
            Value::UInt(x) => Some(Ty::UInt(x.width())),
            Value::SInt(x) => Some(Ty::SInt(x.width())),
            Value::Str(_) | Value::Type(_) => None,
        }
    }

    /// The type of a finite value.
    #[must_use]
    pub fn finite_ty(&self) -> Option<Ty> {
        match self {
            Value::UInt(_) | Value::SInt(_) => self.ty(),
            _ => None,
        }
    }

    /// What the value is, for a message.
    #[must_use]
    pub fn text(&self) -> String {
        match self {
            Value::Str(_) => "a string".to_owned(),
            Value::Type(_) => "a type".to_owned(),
            v => v.ty().map(Ty::text).unwrap_or_default(),
        }
    }

    /// The canonical serialization of section 7.1.
    #[must_use]
    pub fn serialize(&self) -> String {
        match self {
            Value::Int(n) => format!("(int {n})"),
            Value::Bool(b) => format!("(bool {b})"),
            Value::Str(s) => {
                let mut out = "(string ".to_owned();
                parse::quote(s, &mut out);
                out.push(')');
                out
            }
            Value::UInt(x) => format!("(uint {} {})", x.width(), Int::from_unsigned(x)),
            Value::SInt(x) => format!("(sint {} {})", x.width(), Int::from_signed(x, x.width())),
            Value::Type(t) => format!("(type {})", t.serialize()),
        }
    }

    /// The recursive size of section 5.4. A string counts characters, not bytes.
    #[must_use]
    pub fn size(&self) -> u64 {
        match self {
            Value::Int(n) => int_size(n),
            Value::Bool(_) => 1,
            Value::Str(s) => 1 + s.chars().count() as u64,
            Value::UInt(x) | Value::SInt(x) => width_size(x.width()),
            Value::Type(t) => t.size(),
        }
    }

    /// The charge of the decimal forms in the serialization: the square of the size for an
    /// integer and a finite value. A naive decimal conversion takes this time.
    #[must_use]
    pub fn decimal_charge(&self) -> u64 {
        match self {
            Value::Int(_) | Value::UInt(_) | Value::SInt(_) => {
                self.size().saturating_mul(self.size())
            }
            _ => 0,
        }
    }
}

/// An `InstantiationId`: a module and its static arguments in order. Up to slice 5, the
/// package of each module is the root package `root`.
pub struct InstantiationId {
    pub module: String,
    pub args: Vec<Value>,
}

impl InstantiationId {
    /// The serialization from the serializations of the arguments.
    #[must_use]
    pub fn render(module: &str, args: &[String]) -> String {
        format!("(instantiation root {module} ({}))", args.join(" "))
    }

    /// The byte length of `render(module, args)`, known before the text exists.
    #[must_use]
    pub fn render_size(module: &str, args: &[String]) -> u64 {
        let mut bytes = 24 + module.len() as u64;
        for arg in args {
            bytes += arg.len() as u64;
        }
        bytes + (args.len() as u64).saturating_sub(1)
    }

    #[must_use]
    pub fn serialize(&self) -> String {
        let args: Vec<String> = self.args.iter().map(Value::serialize).collect();
        InstantiationId::render(&self.module, &args)
    }
}

#[cfg(test)]
mod tests {
    //! The cases of `Silicon.Source.Test.Value` in Lean.

    use super::*;

    fn int(digits: &str) -> Value {
        let (neg, digits) = match digits.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, digits),
        };
        let n = Int::from_decimal(digits).unwrap();
        Value::Int(if neg { n.neg() } else { n })
    }

    fn uint(w: u32, v: u64) -> Value {
        Value::UInt(crate::int::finite(w, v).unwrap())
    }

    fn sint(w: u32, v: u64) -> Value {
        Value::SInt(crate::int::finite(w, v).unwrap())
    }

    fn id(module: &str, args: Vec<Value>) -> InstantiationId {
        InstantiationId {
            module: module.to_owned(),
            args,
        }
    }

    #[test]
    fn serialization() {
        assert_eq!(int("-5").serialize(), "(int -5)");
        assert_eq!(int("0").serialize(), "(int 0)");
        assert_eq!(
            int("18446744073709551616").serialize(),
            "(int 18446744073709551616)"
        );
        assert_eq!(Value::Bool(true).serialize(), "(bool true)");
        assert_eq!(Value::Bool(false).serialize(), "(bool false)");
        assert_eq!(
            Value::Str("a\"b".to_owned()).serialize(),
            "(string \"a\\\"b\")"
        );
        assert_eq!(
            Value::Str("\\\n\r\t".to_owned()).serialize(),
            "(string \"\\\\\\n\\r\\t\")"
        );
        assert_eq!(Value::Str(String::new()).serialize(), "(string \"\")");
        assert_eq!(
            id("Counter", vec![int("8")]).serialize(),
            "(instantiation root Counter ((int 8)))"
        );
        assert_eq!(
            id("Fifo", vec![int("16"), Value::Bool(true)]).serialize(),
            "(instantiation root Fifo ((int 16) (bool true)))"
        );
        assert_eq!(id("Top", vec![]).serialize(), "(instantiation root Top ())");
        for (module, args) in [
            ("Top", vec![]),
            ("Fifo", vec![int("16"), Value::Bool(true)]),
        ] {
            let parts: Vec<String> = args.iter().map(Value::serialize).collect();
            let text = InstantiationId::render(module, &parts);
            assert_eq!(
                InstantiationId::render_size(module, &parts),
                text.len() as u64
            );
        }
    }

    #[test]
    fn finite_values_and_types() {
        assert_eq!(uint(8, 255).serialize(), "(uint 8 255)");
        assert_eq!(sint(8, 255).serialize(), "(sint 8 -1)");
        assert_eq!(sint(8, 127).serialize(), "(sint 8 127)");
        assert_eq!(Value::Type(Ty::Bool).serialize(), "(type bool)");
        assert_eq!(Value::Type(Ty::Nat).serialize(), "(type nat)");
        assert_eq!(Value::Type(Ty::Int).serialize(), "(type int)");
        assert_eq!(Value::Type(Ty::UInt(8)).serialize(), "(type (uint 8))");
        assert_eq!(Value::Type(Ty::SInt(16)).serialize(), "(type (sint 16))");
    }

    #[test]
    fn sizes_at_the_word_limits() {
        assert_eq!(int("0").size(), 1);
        assert_eq!(int("1").size(), 1);
        assert_eq!(int("18446744073709551615").size(), 1);
        assert_eq!(int("18446744073709551616").size(), 2);
        assert_eq!(int("-18446744073709551615").size(), 1);
        assert_eq!(int("-18446744073709551616").size(), 2);
        assert_eq!(int("340282366920938463463374607431768211455").size(), 2);
        assert_eq!(int("340282366920938463463374607431768211456").size(), 3);
        assert_eq!(Value::Bool(true).size(), 1);
        assert_eq!(Value::Str(String::new()).size(), 1);
        assert_eq!(Value::Str("abc".to_owned()).size(), 4);
        assert_eq!(Value::Str("ä".to_owned()).size(), 2);
        assert_eq!(uint(64, 0).size(), 1);
        assert_eq!(sint(65, 0).size(), 2);
        assert_eq!(Value::Type(Ty::Bool).size(), 1);
        assert_eq!(Value::Type(Ty::UInt(8)).size(), 2);
        assert_eq!(int("18446744073709551616").decimal_charge(), 4);
        assert_eq!(Value::Str("abc".to_owned()).decimal_charge(), 0);
    }
}
