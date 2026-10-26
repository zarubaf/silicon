// SPDX-License-Identifier: Apache-2.0
//! The prelude of slices 1 to 4. The prelude structs are items, built here already resolved.

use parse::ast::{Expr, Ident, Item, NodeId, Param, ParamMode, Pos, StructField, TypeExpr};

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
    /// The prelude struct with this index in [`STRUCTS`].
    Struct(usize),
}

/// The type of a field of a prelude struct.
#[derive(Clone, Copy)]
pub(crate) enum FieldTy {
    One(Leaf),
    /// `List[T]`.
    List(Leaf),
}

/// A prelude struct, as the declaration it acts as (design section 5.6).
pub(crate) struct PreludeStruct {
    pub(crate) name: &'static str,
    params: &'static [(&'static str, Leaf)],
    fields: &'static [(&'static str, FieldTy)],
}

/// The name of the prelude struct that a port call finds.
pub const RESPONSE: &str = "ReadResponse";

/// The names of the prelude types: the builtin types, then the prelude structs (design section
/// 5.6). A message names a user struct or enum with one of these names as `crate::X`.
pub const TYPE_NAMES: [&str; 20] = [
    "Bool",
    "UInt",
    "SInt",
    "Nat",
    "Int",
    "Unit",
    "Type",
    "String",
    "List",
    "Reg",
    "Wire",
    "Input",
    "Mem",
    "Instance",
    "ReadResponse",
    "FieldInfo",
    "TypeInfo",
    "VariantInfo",
    "PortKey",
    "PortInfo",
];

/// The index of `FieldInfo` in [`STRUCTS`]. A table without that struct fails to compile.
pub(crate) const FIELD_INFO: usize = {
    let mut k = 0;
    while !matches!(STRUCTS[k].name.as_bytes(), b"FieldInfo") {
        k += 1;
    }
    k
};

/// The index of `PortInfo` in [`STRUCTS`]. A table without that struct fails to compile.
pub(crate) const PORT_INFO: usize = {
    let mut k = 0;
    while !matches!(STRUCTS[k].name.as_bytes(), b"PortInfo") {
        k += 1;
    }
    k
};

/// The prelude structs, in the order of design section 5.6. They follow the user items. A field
/// type refers to a prelude struct by its index here, never through the item scope.
pub(crate) const STRUCTS: [PreludeStruct; 6] = [
    PreludeStruct {
        name: RESPONSE,
        params: &[("T", Leaf::Prim("Type"))],
        fields: &[
            ("data", FieldTy::One(Leaf::Param)),
            ("valid", FieldTy::One(Leaf::Prim("Bool"))),
        ],
    },
    PreludeStruct {
        name: "FieldInfo",
        params: &[],
        fields: &[
            ("name", FieldTy::One(Leaf::Prim("String"))),
            ("ty", FieldTy::One(Leaf::Prim("Type"))),
        ],
    },
    PreludeStruct {
        name: "TypeInfo",
        params: &[],
        fields: &[
            ("kind", FieldTy::One(Leaf::Prim("String"))),
            ("fields", FieldTy::List(Leaf::Struct(1))),
            ("element", FieldTy::One(Leaf::Prim("Type"))),
            ("length", FieldTy::One(Leaf::Prim("Nat"))),
            ("width", FieldTy::One(Leaf::Prim("Nat"))),
            ("variants", FieldTy::List(Leaf::Struct(3))),
        ],
    },
    PreludeStruct {
        name: "VariantInfo",
        params: &[],
        fields: &[
            ("name", FieldTy::One(Leaf::Prim("String"))),
            ("tag", FieldTy::One(Leaf::Prim("Nat"))),
            ("payload", FieldTy::List(Leaf::Prim("Type"))),
        ],
    },
    PreludeStruct {
        name: "PortKey",
        params: &[],
        fields: &[
            ("name", FieldTy::One(Leaf::Prim("String"))),
            ("indexed", FieldTy::One(Leaf::Prim("Bool"))),
            ("index", FieldTy::One(Leaf::Prim("Nat"))),
        ],
    },
    PreludeStruct {
        name: "PortInfo",
        params: &[],
        fields: &[
            ("key", FieldTy::One(Leaf::Struct(4))),
            ("ty", FieldTy::One(Leaf::Prim("Type"))),
            ("is_input", FieldTy::One(Leaf::Prim("Bool"))),
            ("domain", FieldTy::One(Leaf::Prim("String"))),
        ],
    },
];

/// A prelude struct item, built already resolved, with the target of each name node in it.
pub(crate) struct Built {
    pub(crate) item: Item,
    /// The name and the parameters of the struct, as in `item`.
    pub(crate) name: Ident,
    pub(crate) params: Vec<Ident>,
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
            Leaf::Struct(k) => STRUCTS.get(k).map_or("", |t| t.name),
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

    fn field_ty(&mut self, ty: FieldTy, s: &PreludeStruct) -> TypeExpr {
        match ty {
            FieldTy::One(leaf) => self.ty(leaf, s),
            FieldTy::List(leaf) => {
                let base = self.ty(Leaf::Prim("List"), s);
                let (id, name) = self.leaf(leaf, s);
                TypeExpr::Index {
                    pos: Self::POS,
                    base: Box::new(base),
                    args: vec![Expr::Name {
                        pos: Self::POS,
                        id,
                        name,
                    }],
                }
            }
        }
    }

    fn item(&mut self, s: &PreludeStruct) -> Built {
        let name = self.ident(s.name);
        let params: Vec<Param> = s
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
                ty: self.field_ty(ty, s),
            })
            .collect();
        Built {
            name: name.clone(),
            params: params.iter().map(|p| p.name.clone()).collect(),
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

/// The text of `S003` at `Domain`, which waits for more domains (#11).
pub(crate) const DOMAIN_TEXT: &str = "`Domain` is not supported yet; it comes with more domains \
    (#11); a module has one domain or none, so it needs no `Domain` value";

/// The text of `S003` at a first argument of `Instance` that is not a module.
pub(crate) const INSTANCE_TEXT: &str = "the first argument of `Instance` is not a module; write \
    the module first, for example `Instance[Counter, 8]`";

#[cfg(test)]
mod tests {
    use super::{Prelude, STRUCTS, TYPE_NAMES};

    /// Each name that `Prelude::of` knows, so that the test sees every prelude type.
    const ALL: [&str; 28] = [
        "Bool",
        "Nat",
        "Int",
        "Unit",
        "Type",
        "UInt",
        "SInt",
        "resize",
        "reinterpret",
        "static_assert",
        "error",
        "len",
        "data_bits",
        "String",
        "List",
        "list",
        "push",
        "pop",
        "str",
        "read_port",
        "write_port",
        "diagnostic",
        "Reg",
        "Wire",
        "Input",
        "Mem",
        "Instance",
        "read",
    ];

    /// `TYPE_NAMES` holds the prelude types of the resolver, then its prelude structs, as the
    /// Lean list `preludeTypeNames` does.
    #[test]
    fn the_type_names_are_the_prelude_types_and_structs() {
        let mut expected: Vec<&str> = ALL
            .iter()
            .copied()
            .filter(|n| Prelude::of(n).is_some_and(Prelude::is_type))
            .collect();
        expected.sort_unstable();
        let mut builtin: Vec<&str> = TYPE_NAMES[..TYPE_NAMES.len() - STRUCTS.len()].to_vec();
        builtin.sort_unstable();
        assert_eq!(builtin, expected);
        let structs: Vec<&str> = STRUCTS.iter().map(|s| s.name).collect();
        assert_eq!(TYPE_NAMES[TYPE_NAMES.len() - STRUCTS.len()..], structs[..]);
    }
}
