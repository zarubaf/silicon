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

    /// Whether the name is a scalar type of the prelude.
    #[must_use]
    pub fn is_type(self) -> bool {
        matches!(
            self,
            Prelude::Bool | Prelude::Nat | Prelude::Int | Prelude::UInt | Prelude::SInt
        )
    }
}

/// The slice of a prelude name that a later slice adds, for the message of `S003`.
pub(crate) fn later_slice(name: &str) -> Option<u8> {
    Some(match name {
        "String" | "Type" | "Unit" | "List" | "list" | "push" | "pop" | "len" | "str"
        | "data_bits" | "diagnostic" => 2,
        "Reg" | "Wire" | "Mem" | "Input" | "Instance" | "Domain" | "read" => 3,
        "FieldInfo" | "TypeInfo" | "PortKey" | "PortInfo" => 4,
        _ => return None,
    })
}
