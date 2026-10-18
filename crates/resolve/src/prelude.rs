// SPDX-License-Identifier: Apache-2.0
//! The prelude of slices 1 to 3. A later slice adds its own names, so a use of one of them is
//! `S003` until then. The prelude struct `ReadResponse` is an item, built here already resolved.

use parse::ast::{Ident, Item, NodeId, Param, ParamMode, Pos, StructField, TypeExpr};

/// A name of the prelude: the scalar types and functions of slice 1, `Unit` and `len` of the
/// containers of slice 2, `Type` and `data_bits` of the types as values, and `String`, `List`,
/// `list`, `push`, `pop`, and `str` of the strings and the lists, and `read_port` and
/// `write_port` of the memories, `diagnostic` of the records, and `Reg`, `Wire`, `Input`, `Mem`,
/// `Instance`, and `read` of the handles.
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
    ReadPort,
    WritePort,
    Diagnostic,
    Reg,
    Wire,
    Input,
    Mem,
    Instance,
    Read,
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
            "read_port" => Prelude::ReadPort,
            "write_port" => Prelude::WritePort,
            "diagnostic" => Prelude::Diagnostic,
            "Reg" => Prelude::Reg,
            "Wire" => Prelude::Wire,
            "Input" => Prelude::Input,
            "Mem" => Prelude::Mem,
            "Instance" => Prelude::Instance,
            "read" => Prelude::Read,
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
                | Prelude::Reg
                | Prelude::Wire
                | Prelude::Input
                | Prelude::Mem
                | Prelude::Instance
        )
    }

    /// The parameter modes of a prelude function (design section 5.6). A name that is not a
    /// function has one parameter without a mark, as `error`, `len`, and `str` have.
    #[must_use]
    pub fn modes(self) -> &'static [ParamMode] {
        match self {
            Prelude::Resize | Prelude::Reinterpret => &[ParamMode::Comptime, ParamMode::None],
            Prelude::ListFn => &[ParamMode::Comptime],
            Prelude::Push => &[ParamMode::Mut, ParamMode::None],
            Prelude::Pop => &[ParamMode::Mut],
            Prelude::StaticAssert => &[ParamMode::None, ParamMode::None],
            Prelude::ReadPort => &[ParamMode::None; 3],
            Prelude::WritePort => &[ParamMode::None; 4],
            Prelude::Diagnostic => &[ParamMode::None; 2],
            _ => &[ParamMode::None],
        }
    }

    /// The parameter that a receiver binds to: the first without a written `comptime` mark.
    #[must_use]
    pub fn receiver(self) -> Option<usize> {
        self.modes().iter().position(|&m| m != ParamMode::Comptime)
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
                | Prelude::ReadPort
                | Prelude::WritePort
                | Prelude::Diagnostic
                | Prelude::Read
        )
    }
}

/// The name of the prelude struct.
pub(crate) const RESPONSE: &str = "ReadResponse";

/// The nodes of the prelude struct, by their number for `NodeId::prelude`.
pub(crate) mod node {
    pub(crate) const NAME: usize = 0;
    pub(crate) const PARAM: usize = 1;
    pub(crate) const PARAM_TYPE: usize = 2;
    pub(crate) const DATA: usize = 3;
    pub(crate) const DATA_TYPE: usize = 4;
    pub(crate) const VALID: usize = 5;
    pub(crate) const VALID_TYPE: usize = 6;
}

/// The prelude struct `struct ReadResponse(comptime T: Type) { data: T, valid: Bool }`. The
/// resolver gives its names their targets itself and never looks them up, so a user item
/// `Bool` or `Type` cannot change it. It has no source position: each position is `0:0`.
pub(crate) fn response_item() -> Item {
    let pos = Pos { line: 0, col: 0 };
    let ident = |k: usize, name: &str| Ident {
        pos,
        id: NodeId::prelude(k),
        name: name.to_owned(),
    };
    let named = |k: usize, name: &str| TypeExpr::Name {
        pos,
        id: NodeId::prelude(k),
        name: name.to_owned(),
    };
    Item::Struct {
        pos,
        name: ident(node::NAME, RESPONSE),
        params: vec![Param {
            pos,
            mode: ParamMode::Comptime,
            name: ident(node::PARAM, "T"),
            ty: named(node::PARAM_TYPE, "Type"),
        }],
        fields: vec![
            StructField {
                name: ident(node::DATA, "data"),
                ty: named(node::DATA_TYPE, "T"),
            },
            StructField {
                name: ident(node::VALID, "valid"),
                ty: named(node::VALID_TYPE, "Bool"),
            },
        ],
    }
}

/// The slice of a prelude name that a later slice adds, for the message of `S003`.
pub(crate) fn later_slice(name: &str) -> Option<u8> {
    Some(match name {
        "FieldInfo" | "TypeInfo" | "PortKey" | "PortInfo" => 4,
        _ => return None,
    })
}

/// The text of `S003` at `Domain`, which waits for more domains (#11).
pub(crate) const DOMAIN_TEXT: &str = "`Domain` is not supported yet; it comes with more domains \
    (#11); a module has one domain or none, so it needs no `Domain` value";

/// The text of `S003` at a first argument of `Instance` that is not a module.
pub(crate) const INSTANCE_TEXT: &str = "the first argument of `Instance` is not a module; write \
    the module first, for example `Instance[Counter, 8]`";
