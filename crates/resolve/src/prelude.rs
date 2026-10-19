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

/// What a name node of a prelude struct points to.
#[derive(Clone, Copy)]
pub(crate) enum Leaf {
    /// A name of the prelude, such as `Type`, `Bool`, `String`, `Nat`, or `List`.
    Prim(&'static str),
    /// The first parameter of its own struct.
    Param,
}

/// A prelude struct, as the declaration it acts as (design section 5.6).
pub(crate) struct PreludeStruct {
    pub(crate) name: &'static str,
    params: &'static [(&'static str, Leaf)],
    fields: &'static [(&'static str, Leaf)],
}

/// The name of the prelude struct that a port call finds.
pub(crate) const RESPONSE: &str = "ReadResponse";

/// The prelude structs, in the order of design section 5.6. They follow the user items. A field
/// type refers to a prelude struct by its index here, never through the item scope.
pub(crate) const STRUCTS: [PreludeStruct; 1] = [PreludeStruct {
    name: RESPONSE,
    params: &[("T", Leaf::Prim("Type"))],
    fields: &[("data", Leaf::Param), ("valid", Leaf::Prim("Bool"))],
}];

/// A prelude struct item, built already resolved, with the target of each name node in it.
pub(crate) struct Built {
    pub(crate) item: Item,
    pub(crate) uses: Vec<(NodeId, Leaf)>,
}

/// Numbers the nodes of the prelude struct items from 0 with `NodeId::prelude`, and records the
/// target of each name node.
struct Builder {
    next: usize,
    uses: Vec<(NodeId, Leaf)>,
}

impl Builder {
    const POS: Pos = Pos { line: 0, col: 0 };

    fn id(&mut self) -> NodeId {
        self.next += 1;
        NodeId::prelude(self.next - 1)
    }

    fn ident(&mut self, name: &str) -> Ident {
        Ident {
            pos: Self::POS,
            id: self.id(),
            name: name.to_owned(),
        }
    }

    /// A name node that points to `leaf` in the struct `s`: its id and its text.
    fn leaf(&mut self, leaf: Leaf, s: &PreludeStruct) -> (NodeId, String) {
        let id = self.id();
        self.uses.push((id, leaf));
        let text = match leaf {
            Leaf::Prim(name) => name,
            Leaf::Param => s.params.first().map_or("", |p| p.0),
        };
        (id, text.to_owned())
    }

    fn ty(&mut self, leaf: Leaf, s: &PreludeStruct) -> TypeExpr {
        let (id, name) = self.leaf(leaf, s);
        TypeExpr::Name {
            pos: Self::POS,
            id,
            name,
        }
    }

    fn item(&mut self, s: &PreludeStruct) -> Built {
        let name = self.ident(s.name);
        let params = s
            .params
            .iter()
            .map(|&(p, leaf)| Param {
                pos: Self::POS,
                mode: ParamMode::Comptime,
                name: self.ident(p),
                ty: self.ty(leaf, s),
            })
            .collect();
        let fields = s
            .fields
            .iter()
            .map(|&(f, ty)| StructField {
                name: self.ident(f),
                ty: self.ty(ty, s),
            })
            .collect();
        Built {
            item: Item::Struct {
                pos: Self::POS,
                name,
                params,
                fields,
            },
            uses: std::mem::take(&mut self.uses),
        }
    }
}

/// The prelude struct items, with no source position: each position is `0:0`. The resolver gives
/// their names their targets itself and never looks them up, so a user item `Bool` or `Type`
/// cannot change them.
pub(crate) fn build() -> Vec<Built> {
    let mut builder = Builder {
        next: 0,
        uses: Vec::new(),
    };
    STRUCTS.iter().map(|s| builder.item(s)).collect()
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
