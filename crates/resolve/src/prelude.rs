// SPDX-License-Identifier: Apache-2.0
//! The prelude of slices 1 and 2. A later slice adds its own names, so a use of one of them is
//! `S003` until then.

use parse::ast::ParamMode;

/// A name of the prelude: the scalar types and functions of slice 1, `Unit` and `len` of the
/// containers of slice 2, `Type` and `data_bits` of the types as values, and `String`, `List`,
/// `list`, `push`, `pop`, and `str` of the strings and the lists.
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
    String,
    List,
    ListFn,
    Push,
    Pop,
    Str,
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
            "String" => Prelude::String,
            "List" => Prelude::List,
            "list" => Prelude::ListFn,
            "push" => Prelude::Push,
            "pop" => Prelude::Pop,
            "str" => Prelude::Str,
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
                | Prelude::String
                | Prelude::List
        )
    }

    /// The parameter modes of a prelude function (design section 5.6). A name that is not a
    /// function has one parameter without a mark, as `error`, `len`, and `str` have.
    #[must_use]
    pub fn modes(self) -> &'static [ParamMode] {
        match self {
            Prelude::Resize | Prelude::Reinterpret => &[ParamMode::Comptime, ParamMode::None],
            Prelude::ListFn | Prelude::DataBits => &[ParamMode::Comptime],
            Prelude::Push => &[ParamMode::Mut, ParamMode::None],
            Prelude::Pop => &[ParamMode::Mut],
            Prelude::StaticAssert => &[ParamMode::None, ParamMode::None],
            _ => &[ParamMode::None],
        }
    }

    /// Whether the name is a function of the prelude.
    #[must_use]
    pub fn is_fn(self) -> bool {
        matches!(
            self,
            Prelude::Resize
                | Prelude::Reinterpret
                | Prelude::StaticAssert
                | Prelude::Error
                | Prelude::Len
                | Prelude::DataBits
                | Prelude::ListFn
                | Prelude::Push
                | Prelude::Pop
                | Prelude::Str
        )
    }
}

/// The slice of a prelude name that a later slice adds, for the message of `S003`.
pub(crate) fn later_slice(name: &str) -> Option<u8> {
    Some(match name {
        "diagnostic" => 2,
        "Reg" | "Wire" | "Mem" | "Input" | "Instance" | "Domain" | "read" => 3,
        "FieldInfo" | "TypeInfo" | "PortKey" | "PortInfo" => 4,
        _ => return None,
    })
}
