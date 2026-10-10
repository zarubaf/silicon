//! The prelude of slice 1. A later slice adds its own names, so a use of one of them is
//! `S003` until then.

/// A name of the slice 1 prelude.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prelude {
    Bool,
    Nat,
    Int,
    UInt,
    SInt,
    Resize,
    Reinterpret,
    StaticAssert,
    Error,
}

/// What a name is, for the position that needs it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Class {
    Value,
    Function,
    Type,
    Module,
    Domain,
}

impl Class {
    pub(crate) fn describe(self) -> &'static str {
        match self {
            Class::Value => "a value",
            Class::Function => "a function",
            Class::Type => "a type",
            Class::Module => "a module",
            Class::Domain => "a domain",
        }
    }
}

impl Prelude {
    pub(crate) fn of(name: &str) -> Option<Prelude> {
        Some(match name {
            "Bool" => Prelude::Bool,
            "Nat" => Prelude::Nat,
            "Int" => Prelude::Int,
            "UInt" => Prelude::UInt,
            "SInt" => Prelude::SInt,
            "resize" => Prelude::Resize,
            "reinterpret" => Prelude::Reinterpret,
            "static_assert" => Prelude::StaticAssert,
            "error" => Prelude::Error,
            _ => return None,
        })
    }

    pub(crate) fn class(self) -> Class {
        match self {
            Prelude::Bool | Prelude::Nat | Prelude::Int | Prelude::UInt | Prelude::SInt => {
                Class::Type
            }
            Prelude::Resize | Prelude::Reinterpret | Prelude::StaticAssert | Prelude::Error => {
                Class::Function
            }
        }
    }
}
