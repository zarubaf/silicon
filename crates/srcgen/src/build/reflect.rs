// SPDX-License-Identifier: Apache-2.0
//! The `TypeInfo` of a type that the builder drew (front-end spec 9.3,
//! ADR 0032).
//!
//! The builder chooses the type of each name first and then writes the
//! program, so it knows the answer of each query. This module maps a drawn
//! type to the scalars that a query reads. It is no function from an
//! expression to a type: it takes the type that the builder drew for a
//! binding, a port, or a resource. Each rule cites the sentence of section
//! 9.3 that it follows, and the unit tests below do the same. The tests do
//! not come from the run files of Lean, which can share a misreading.

use super::reads_root;
use crate::program::{SExpr, Ty};

/// A type that the builder drew for a name that a query can read.
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
}

impl RTy {
    /// The drawn hardware type `t`. An enum is not reflected yet.
    pub(super) fn of(t: &Ty) -> Option<RTy> {
        match t {
            Ty::Bool => Some(RTy::Bool),
            Ty::UInt(w) => Some(RTy::UInt(w.clone())),
            Ty::SInt(w) => Some(RTy::SInt(w.clone())),
            Ty::Enum(_) => None,
        }
    }

    /// Whether a width of the type names the root `root`.
    pub(super) fn reads(&self, root: &str) -> bool {
        match self {
            RTy::Bool => false,
            RTy::UInt(w) | RTy::SInt(w) => reads_root(w, root),
            RTy::Reg(t) | RTy::Wire(t) | RTy::Input(t) => t.reads(root),
        }
    }

    /// The width and the signedness of a type of finite integers, or of
    /// the element of a handle.
    pub(super) fn data(&self) -> Option<(SExpr, bool)> {
        match self {
            RTy::UInt(w) => Some((w.clone(), false)),
            RTy::SInt(w) => Some((w.clone(), true)),
            RTy::Bool => None,
            RTy::Reg(t) | RTy::Wire(t) | RTy::Input(t) => t.data(),
        }
    }
}

/// The scalars of a `TypeInfo` that the queries read.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct Info {
    pub(super) kind: &'static str,
    pub(super) width: SExpr,
    pub(super) length: SExpr,
    /// The number of entries of `fields`.
    pub(super) fields: usize,
    /// The type in `element`, if the kind uses it.
    pub(super) element: Option<RTy>,
}

fn int(n: u32) -> SExpr {
    SExpr::Int(num_bigint::BigInt::from(n), crate::program::Radix::Dec)
}

/// The `TypeInfo` of `t`.
pub(super) fn info(t: &RTy) -> Info {
    // "A field that a kind does not use has its default: `list(FieldInfo)`,
    // `Unit`, 0, 0, and `list(VariantInfo)`."
    let plain = |kind, width| Info {
        kind,
        width,
        length: int(0),
        fields: 0,
        element: None,
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
    }
}

fn handle(kind: &'static str, element: &RTy) -> Info {
    Info {
        kind,
        width: int(0),
        length: int(0),
        fields: 0,
        element: Some(element.clone()),
    }
}

/// `data_bits(T)`, if `t` is hardware data: "`data_bits(T)` gives their bit
/// count". A handle is no data.
pub(super) fn data_bits(t: &RTy) -> Option<SExpr> {
    match t {
        RTy::Bool => Some(int(1)),
        RTy::UInt(w) | RTy::SInt(w) => Some(w.clone()),
        RTy::Reg(_) | RTy::Wire(_) | RTy::Input(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eight() -> RTy {
        RTy::UInt(int(8))
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
    }

    /// "A field that a kind does not use has its default: ... 0, 0": a scalar
    /// type has no length, no field, and no element.
    #[test]
    fn a_scalar_has_the_defaults() {
        let i = info(&eight());
        assert_eq!((i.length, i.fields, i.element), (int(0), 0, None));
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
            assert_eq!((i.kind, i.width, i.element), (kind, int(0), Some(eight())));
        }
    }

    /// "`data_bits(T)` gives their bit count": a handle has none.
    #[test]
    fn data_bits_is_the_width_of_data() {
        assert_eq!(data_bits(&eight()), Some(int(8)));
        assert_eq!(data_bits(&RTy::Bool), Some(int(1)));
        assert_eq!(data_bits(&RTy::Reg(Box::new(eight()))), None);
    }
}
