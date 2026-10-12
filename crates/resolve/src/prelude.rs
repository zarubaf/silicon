// SPDX-License-Identifier: Apache-2.0
//! The prelude of slices 1 and 2. A later slice adds its own names, so a use of one of them is
//! `S003` until then.

/// A name of the prelude: the scalar types and functions of slice 1, `Unit` and `len` of the
/// containers of slice 2, and `Type` and `data_bits` of the types as values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prelude {
    Bool,
    Nat,
    Int,
    Unit,
    Type,
    UInt,
    SInt,
    Resize,
    Reinterpret,
    StaticAssert,
    Error,
    Len,
    DataBits,
}

impl Prelude {
    pub(crate) fn of(name: &str) -> Option<Prelude> {
        Some(match name {
            "Bool" => Prelude::Bool,
            "Nat" => Prelude::Nat,
            "Int" => Prelude::Int,
            "Unit" => Prelude::Unit,
            "Type" => Prelude::Type,
            "UInt" => Prelude::UInt,
            "SInt" => Prelude::SInt,
            "resize" => Prelude::Resize,
            "reinterpret" => Prelude::Reinterpret,
            "static_assert" => Prelude::StaticAssert,
            "error" => Prelude::Error,
            "len" => Prelude::Len,
            "data_bits" => Prelude::DataBits,
            _ => return None,
        })
    }

    /// Whether the name is a scalar type of the prelude.
    #[must_use]
    pub fn is_type(self) -> bool {
        matches!(
            self,
            Prelude::Bool
                | Prelude::Nat
                | Prelude::Int
                | Prelude::Unit
                | Prelude::Type
                | Prelude::UInt
                | Prelude::SInt
        )
    }
}

/// The slice of a prelude name that a later slice adds, for the message of `S003`.
pub(crate) fn later_slice(name: &str) -> Option<u8> {
    Some(match name {
        "String" | "List" | "list" | "push" | "pop" | "str" | "diagnostic" => 2,
        "Reg" | "Wire" | "Mem" | "Input" | "Instance" | "Domain" | "read" => 3,
        "FieldInfo" | "TypeInfo" | "PortKey" | "PortInfo" => 4,
        _ => return None,
    })
}
