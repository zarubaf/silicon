// SPDX-License-Identifier: Apache-2.0
//! The `TypeInfo` of a type that the builder drew (front-end spec 9.3,
//! ADR 0032).
//!
//! The builder chooses the type of each name first and then writes the
//! program, so it knows the answer of each query. This module maps a drawn
//! type to the scalars that a query reads. It is no function from an
//! expression to a type: it takes the type that the builder drew for a
//! binding, a port, a resource, or a type literal. Each rule cites the
//! sentence of section 9.3 that it follows, and the unit tests below do the
//! same. The tests do not come from the run files of Lean, which can share a
//! misreading.

use super::reads_root;
use crate::program::{SExpr, STy, Ty};
use num_bigint::{BigInt, BigUint};

/// A type that the builder drew for a name or a literal that a query reads.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum RTy {
    Bool,
    /// `UInt[W]` with the width as the builder wrote it.
    UInt(SExpr),
    SInt(SExpr),
    /// `Reg[T]`, `Wire[T]`, and `Input[T]`.
    Reg(Box<RTy>),
    Wire(Box<RTy>),
    Input(Box<RTy>),
    /// `Unit`, `Type`, and `Instance[M, args]`.
    Unit,
    Type,
    Instance,
    /// `Mem[T, N]`.
    Mem(Box<RTy>, u32),
    /// A static type with no hardware width: `Nat`, `Int`, `String`, a
    /// list, a tuple, an array, a record, a function, or an enum.
    Static(STy),
}

/// The scalars of a `TypeInfo` that the queries read.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct Info {
    pub(super) kind: &'static str,
    pub(super) width: SExpr,
    pub(super) length: SExpr,
    /// The name and the type of each `FieldInfo`, in order.
    pub(super) fields: Vec<(String, RTy)>,
    pub(super) element: RTy,
    /// The name and the tag of each variant.
    pub(super) variants: Vec<(String, BigUint)>,
}

impl RTy {
    /// The drawn hardware type `t`. An enum is no hardware type here.
    pub(super) fn of(t: &Ty) -> Option<RTy> {
        match t {
            Ty::Bool => Some(RTy::Bool),
            Ty::UInt(w) => Some(RTy::UInt(w.clone())),
            Ty::SInt(w) => Some(RTy::SInt(w.clone())),
            Ty::Enum(_) => None,
            Ty::Query(t, _) => RTy::of(t),
        }
    }

    /// The static type `t`: a finite integer and a `Bool` have the width of
    /// the hardware type.
    pub(super) fn from_static(t: &STy) -> RTy {
        match t {
            STy::Bool => RTy::Bool,
            STy::UInt(w) => RTy::UInt(int(*w)),
            STy::SInt(w) => RTy::SInt(int(*w)),
            other => RTy::Static(other.clone()),
        }
    }

    /// Whether a width of the type names the root `root`.
    pub(super) fn reads(&self, root: &str) -> bool {
        match self {
            RTy::UInt(w) | RTy::SInt(w) => reads_root(w, root),
            RTy::Reg(t) | RTy::Wire(t) | RTy::Input(t) | RTy::Mem(t, _) => t.reads(root),
            RTy::Bool | RTy::Unit | RTy::Type | RTy::Instance | RTy::Static(_) => false,
        }
    }

    /// The hardware data type of a name, or of the element of its handle.
    pub(super) fn data_ty(&self) -> Option<&RTy> {
        match self {
            RTy::Bool | RTy::UInt(_) | RTy::SInt(_) => Some(self),
            RTy::Reg(t) | RTy::Wire(t) | RTy::Input(t) => t.data_ty(),
            RTy::Unit | RTy::Type | RTy::Instance | RTy::Mem(..) | RTy::Static(_) => None,
        }
    }

    /// The width and the signedness of a type of finite integers, or of
    /// the element of a handle.
    pub(super) fn data(&self) -> Option<(SExpr, bool)> {
        match self {
            RTy::UInt(w) => Some((w.clone(), false)),
            RTy::SInt(w) => Some((w.clone(), true)),
            RTy::Reg(t) | RTy::Wire(t) | RTy::Input(t) => t.data(),
            RTy::Bool | RTy::Unit | RTy::Type | RTy::Instance | RTy::Mem(..) | RTy::Static(_) => {
                None
            }
        }
    }

    /// The element of a handle, for a query on the data it holds.
    pub(super) fn handled(&self) -> Option<&RTy> {
        match self {
            RTy::Reg(t) | RTy::Wire(t) | RTy::Input(t) => Some(t),
            _ => None,
        }
    }
}

fn int(n: u32) -> SExpr {
    SExpr::Int(BigInt::from(n), crate::program::Radix::Dec)
}

/// The `TypeInfo` of `t`.
pub(super) fn info(t: &RTy) -> Info {
    // "A field that a kind does not use has its default: `list(FieldInfo)`,
    // `Unit`, 0, 0, and `list(VariantInfo)`."
    let plain = |kind, width| Info {
        kind,
        width,
        length: int(0),
        fields: Vec::new(),
        element: RTy::Unit,
        variants: Vec::new(),
    };
    match t {
        // "`Bool` sets `width` to 1, and `UInt[W]` and `SInt[W]` set it to `W`."
        RTy::Bool => plain("bool", int(1)),
        RTy::UInt(w) => plain("uint", w.clone()),
        RTy::SInt(w) => plain("sint", w.clone()),
        // "`List[T]`, `Reg[T]`, `Wire[T]`, `Input[T]`, and `Mem[T, N]` set
        // `element` to `T`." The other fields keep their default, so the
        // width of a register is 0, not the width of `T`.
        RTy::Reg(e) => handle("reg", e),
        RTy::Wire(e) => handle("wire", e),
        RTy::Input(e) => handle("input", e),
        // "`Mem[T, N]` also sets `length` to `N`."
        RTy::Mem(e, n) => Info {
            length: int(*n),
            ..handle("mem", e)
        },
        RTy::Unit => plain("unit", int(0)),
        RTy::Type => plain("type", int(0)),
        // "`Instance[M, args]` shows no ports", and has the `element` `Unit`.
        RTy::Instance => plain("instance", int(0)),
        RTy::Static(s) => static_info(s, plain),
    }
}

fn handle(kind: &'static str, element: &RTy) -> Info {
    Info {
        kind,
        width: int(0),
        length: int(0),
        fields: Vec::new(),
        element: element.clone(),
        variants: Vec::new(),
    }
}

fn static_info(t: &STy, plain: impl Fn(&'static str, SExpr) -> Info) -> Info {
    match t {
        STy::Nat => plain("nat", int(0)),
        STy::Int => plain("int", int(0)),
        STy::Str => plain("string", int(0)),
        STy::Fn(_) => plain("function", int(0)),
        // "A list has the `length` 0, because its type has no length."
        STy::List(e) => Info {
            element: RTy::from_static(e),
            ..plain("list", int(0))
        },
        // "An array, a tuple, and a record have the `width` 0, also when
        // they are hardware data." "An array sets `element` and `length`."
        STy::Array(e, n) => Info {
            length: int(*n),
            element: RTy::from_static(e),
            ..plain("array", int(0))
        },
        // "A tuple and a record set `fields` in order and `length` to the
        // number of fields." "A tuple has the field names `0`, `1`, and so
        // on."
        STy::Tuple(ts) => Info {
            length: int(u32::try_from(ts.len()).unwrap_or(u32::MAX)),
            fields: ts
                .iter()
                .enumerate()
                .map(|(i, t)| (i.to_string(), RTy::from_static(t)))
                .collect(),
            ..plain("tuple", int(0))
        },
        // "A record of a declared struct has its declared names."
        STy::Record(r) => Info {
            length: int(u32::try_from(r.fields.len()).unwrap_or(u32::MAX)),
            fields: r
                .fields
                .iter()
                .map(|(f, t)| (f.clone(), RTy::from_static(t)))
                .collect(),
            ..plain("record", int(0))
        },
        // "An enum sets `element` to its tag type `UInt[W]`, `width` to its
        // `data_bits`, and `variants` to one `VariantInfo` for each
        // variant, in declaration order. Its `fields` is empty and its
        // `length` is 0."
        STy::Enum(d) => Info {
            element: RTy::UInt(int(d.tag_width)),
            variants: d
                .variants
                .iter()
                .map(|v| (v.name.clone(), v.tag.clone()))
                .collect(),
            ..plain("enum", int(d.data_bits()))
        },
        // A finite integer and a `Bool` are no static types here: see
        // `RTy::from_static`.
        STy::Bool => plain("bool", int(1)),
        STy::UInt(w) => plain("uint", int(*w)),
        STy::SInt(w) => plain("sint", int(*w)),
    }
}

/// The bits of a static type of hardware data.
fn static_bits(t: &STy) -> Option<u32> {
    match t {
        STy::Bool => Some(1),
        STy::UInt(w) | STy::SInt(w) => Some(*w),
        STy::Tuple(ts) => ts.iter().map(static_bits).sum(),
        STy::Array(e, n) => static_bits(e).map(|b| b * n),
        STy::Record(r) => r.fields.iter().map(|(_, t)| static_bits(t)).sum(),
        STy::Enum(d) => Some(d.data_bits()),
        STy::Nat | STy::Int | STy::Str | STy::List(_) | STy::Fn(_) => None,
    }
}

/// `data_bits(T)`, if `t` is hardware data: "`data_bits(T)` gives their bit
/// count". A handle, a function, and a container of `Int` are no data.
pub(super) fn data_bits(t: &RTy) -> Option<SExpr> {
    match t {
        RTy::Bool => Some(int(1)),
        RTy::UInt(w) | RTy::SInt(w) => Some(w.clone()),
        RTy::Static(s) => static_bits(s).map(int),
        RTy::Reg(_)
        | RTy::Wire(_)
        | RTy::Input(_)
        | RTy::Mem(..)
        | RTy::Unit
        | RTy::Type
        | RTy::Instance => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{EnumDef, RecTy, Variant};

    fn eight() -> RTy {
        RTy::UInt(int(8))
    }

    fn pair() -> STy {
        STy::Tuple(vec![STy::Int, STy::Bool])
    }

    /// "`Bool` sets `width` to 1."
    #[test]
    fn bool_has_the_width_1() {
        let i = info(&RTy::Bool);
        assert_eq!((i.kind, i.width), ("bool", int(1)));
    }

    /// "`UInt[W]` and `SInt[W]` set it to `W`."
    #[test]
    fn a_finite_integer_has_its_width() {
        assert_eq!(info(&eight()).width, int(8));
        assert_eq!(info(&RTy::SInt(int(3))).kind, "sint");
        assert_eq!(info(&RTy::from_static(&STy::UInt(4))).width, int(4));
    }

    /// "A field that a kind does not use has its default": a scalar type has
    /// the element `Unit`, no length, no field, and no variant.
    #[test]
    fn a_scalar_has_the_defaults() {
        for t in [eight(), RTy::Static(STy::Nat), RTy::Static(STy::Str)] {
            let i = info(&t);
            assert_eq!(
                (i.length, i.fields, i.element, i.variants),
                (int(0), vec![], RTy::Unit, vec![])
            );
        }
    }

    /// "`Reg[T]` ... set `element` to `T`", and the other fields keep their
    /// default, so the width of a register is 0.
    #[test]
    fn a_handle_has_the_element_and_the_width_0() {
        for (t, kind) in [
            (RTy::Reg(Box::new(eight())), "reg"),
            (RTy::Wire(Box::new(eight())), "wire"),
            (RTy::Input(Box::new(eight())), "input"),
        ] {
            let i = info(&t);
            assert_eq!((i.kind, i.width, i.element), (kind, int(0), eight()));
        }
    }

    /// "`Mem[T, N]` also sets `length` to `N`."
    #[test]
    fn a_memory_has_the_length() {
        let i = info(&RTy::Mem(Box::new(eight()), 16));
        assert_eq!((i.kind, i.length, i.element), ("mem", int(16), eight()));
    }

    /// The kinds `nat`, `int`, `string`, `function`, `unit`, `type`, and
    /// `instance` (F33) have the width 0 and the defaults.
    #[test]
    fn the_plain_kinds_have_the_width_0() {
        let fun = STy::Fn(Box::new(crate::program::FnTy {
            params: vec![],
            ret: STy::Int,
        }));
        for (t, kind) in [
            (RTy::Static(STy::Nat), "nat"),
            (RTy::Static(STy::Int), "int"),
            (RTy::Static(STy::Str), "string"),
            (RTy::Static(fun), "function"),
            (RTy::Unit, "unit"),
            (RTy::Type, "type"),
            (RTy::Instance, "instance"),
        ] {
            let i = info(&t);
            assert_eq!((i.kind, i.width), (kind, int(0)));
        }
    }

    /// "`List[T]` ... set `element` to `T`", and "A list has the `length`
    /// 0".
    #[test]
    fn a_list_has_the_element_and_no_length() {
        let i = info(&RTy::Static(STy::List(Box::new(STy::Int))));
        assert_eq!(
            (i.kind, i.length, i.element),
            ("list", int(0), RTy::Static(STy::Int))
        );
    }

    /// "An array sets `element` and `length`", with the `width` 0.
    #[test]
    fn an_array_has_the_element_and_the_length() {
        let i = info(&RTy::Static(STy::Array(Box::new(STy::Bool), 3)));
        assert_eq!(
            (i.kind, i.width, i.length, i.element),
            ("array", int(0), int(3), RTy::Bool)
        );
    }

    /// "A tuple and a record set `fields` in order and `length` to the number
    /// of fields", and "A tuple has the field names `0`, `1`".
    #[test]
    fn a_tuple_has_numbered_fields() {
        let i = info(&RTy::Static(pair()));
        let names: Vec<&str> = i.fields.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!((i.kind, i.length, names), ("tuple", int(2), vec!["0", "1"]));
    }

    /// "A record of a declared struct has its declared names", and the
    /// `width` 0, also when it is hardware data.
    #[test]
    fn a_record_has_its_declared_names() {
        let rec = RecTy {
            name: "S0".to_owned(),
            args: vec![],
            fields: vec![
                ("m0".to_owned(), STy::UInt(4)),
                ("m1".to_owned(), STy::Bool),
            ],
        };
        let i = info(&RTy::Static(STy::Record(Box::new(rec))));
        assert_eq!(
            (i.kind, i.width, i.length, i.fields[0].0.as_str()),
            ("record", int(0), int(2), "m0")
        );
        assert_eq!(i.fields[0].1, RTy::UInt(int(4)));
    }

    fn op() -> EnumDef {
        let variant = |name: &str, tag: u8, payload| Variant {
            name: name.to_owned(),
            tag: BigUint::from(tag),
            payload,
        };
        EnumDef {
            name: "E0".to_owned(),
            tag_width: 2,
            variants: vec![
                variant("A", 0, vec![]),
                variant("B", 3, vec![crate::program::Scalar::UInt(5)]),
            ],
        }
    }

    /// "An enum sets `element` to its tag type `UInt[W]`, `width` to its
    /// `data_bits`, and `variants` ... in declaration order. Its `fields` is
    /// empty and its `length` is 0."
    #[test]
    fn an_enum_has_the_tag_type_and_the_variants() {
        let i = info(&RTy::Static(STy::Enum(Box::new(op()))));
        assert_eq!(
            (i.kind, i.width, i.length, i.element, i.fields.len()),
            ("enum", int(7), int(0), RTy::UInt(int(2)), 0)
        );
        let tags: Vec<(&str, BigUint)> = i
            .variants
            .iter()
            .map(|(n, t)| (n.as_str(), t.clone()))
            .collect();
        assert_eq!(
            tags,
            vec![("A", BigUint::from(0u8)), ("B", BigUint::from(3u8))]
        );
    }

    /// "`data_bits(T)` gives their bit count": a handle, a function, and a
    /// container of `Int` have none, and an enum has its `data_bits`.
    #[test]
    fn data_bits_is_the_width_of_data() {
        assert_eq!(data_bits(&eight()), Some(int(8)));
        assert_eq!(data_bits(&RTy::Bool), Some(int(1)));
        assert_eq!(data_bits(&RTy::Reg(Box::new(eight()))), None);
        assert_eq!(data_bits(&RTy::Static(pair())), None);
        let flags = STy::Tuple(vec![STy::UInt(3), STy::Bool]);
        assert_eq!(data_bits(&RTy::Static(flags)), Some(int(4)));
        assert_eq!(
            data_bits(&RTy::Static(STy::Enum(Box::new(op())))),
            Some(int(7))
        );
    }
}
