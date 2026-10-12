// SPDX-License-Identifier: Apache-2.0
//! The static types and their table, as Lean `Source.Value` defines the type values. A type is
//! an id in the table `Types`: a copy and an equality of types are constant work, and the id
//! carries the size and the depth of its type.

use crate::int::Int;
use crate::text::Text;
use crate::value::{Len, Sink, int_size, list, node, width_int};
use std::collections::BTreeMap;
use std::fmt::Write;

/// A type as a static value: the scalar types of slice 1 with a width from 1 to 65536, `()`,
/// and the container types. A tuple type has at least one element type: `()` is `Unit`. The
/// length of an array type is any natural number, as the type does not hold the elements.
///
/// This is one node of the table `Types`. The parts of a container type are ids, so a type
/// is never copied by its parts. The hardware values hold only scalar types of this form.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ty {
    Bool,
    Nat,
    Int,
    UInt(u32),
    SInt(u32),
    Unit,
    Array(TyId, Int),
    Tuple(Vec<TyId>),
}

/// A type in the table `Types`. Two ids of one table are equal exactly if their types are
/// structurally equal. The id carries the recursive size and the depth of its type, as the
/// type metadata of design section 5.4, so a copy of an id is constant work.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyId {
    index: usize,
    size: u64,
    depth: u64,
}

impl TyId {
    /// The number of nodes of the type term, plus the size of each integer in it.
    #[must_use]
    pub fn size(self) -> u64 {
        self.size
    }

    /// The depth of section 5.5: 1 for a scalar type, and 1 more than its deepest part.
    #[must_use]
    pub fn depth(self) -> u64 {
        self.depth
    }
}

/// One type of the table with its metadata.
struct Entry {
    ty: Ty,
    text_len: u64,
}

/// The table of the static types of one elaboration. A structurally equal type has one id, so
/// a copy of a type and an equality of two types are constant work. A container type holds
/// the ids of its parts, so a new type costs work in its own arity only. The table grows only
/// with charged work: each new type pays its recursive size at its constructor.
#[derive(Default)]
pub struct Types {
    entries: Vec<Entry>,
    index: BTreeMap<Ty, TyId>,
    /// The common type of each pair of types that joined, or `None` if they have none.
    joins: BTreeMap<(TyId, TyId), Option<TyId>>,
    /// The work of the lookups: 1 for each type and 1 for each part of a container type. The
    /// type of a value adds 1 for each node that its walk visits.
    #[cfg(test)]
    pub(crate) work: u64,
}

/// The type that an absent id names. The table makes each id, so no id finds it.
static ABSENT: Ty = Ty::Unit;

impl Types {
    /// The id of `ty`. A new type gets its metadata from the ids of its parts.
    pub fn mk(&mut self, ty: Ty) -> TyId {
        #[cfg(test)]
        {
            self.work += 1 + match &ty {
                Ty::Tuple(parts) => parts.len() as u64,
                _ => 0,
            };
        }
        if let Some(id) = self.index.get(&ty) {
            return *id;
        }
        let (size, depth) = Types::metadata(&ty);
        let id = TyId {
            index: self.entries.len(),
            size,
            depth,
        };
        let mut len = Len::default();
        self.write_node(&ty, &mut len);
        self.entries.push(Entry {
            ty: ty.clone(),
            text_len: len.0,
        });
        self.index.insert(ty, id);
        id
    }

    /// The recursive size and the depth of a new type.
    fn metadata(ty: &Ty) -> (u64, u64) {
        match ty {
            Ty::Bool | Ty::Nat | Ty::Int | Ty::Unit => (1, 1),
            Ty::UInt(w) | Ty::SInt(w) => (1 + int_size(&width_int(*w)), 1),
            Ty::Array(elem, len) => (
                1u64.saturating_add(elem.size).saturating_add(int_size(len)),
                1 + elem.depth,
            ),
            Ty::Tuple(parts) => (
                parts
                    .iter()
                    .fold(1u64, |sum, part| sum.saturating_add(part.size)),
                1 + parts.iter().map(|part| part.depth).max().unwrap_or(0),
            ),
        }
    }

    #[must_use]
    pub fn array(&mut self, elem: TyId, len: Int) -> TyId {
        self.mk(Ty::Array(elem, len))
    }

    #[must_use]
    pub fn tuple(&mut self, parts: Vec<TyId>) -> TyId {
        self.mk(Ty::Tuple(parts))
    }

    /// The common type of `lhs` and `rhs` if they joined before: `Some(None)` if they have
    /// none.
    pub(crate) fn joined(&self, lhs: TyId, rhs: TyId) -> Option<&Option<TyId>> {
        self.joins.get(&(lhs, rhs))
    }

    /// Keeps the common type of the pair `key`.
    pub(crate) fn join(&mut self, key: (TyId, TyId), joined: Option<TyId>) {
        self.joins.insert(key, joined);
    }

    /// The type with the id `t`.
    #[must_use]
    pub fn get(&self, t: TyId) -> &Ty {
        self.entries.get(t.index).map_or(&ABSENT, |e| &e.ty)
    }

    /// The id of the part `k` of the container type `t`: the element type of an array, or
    /// the type of the element `k` of a tuple.
    #[must_use]
    pub fn part(&self, t: TyId, k: usize) -> Option<TyId> {
        match self.get(t) {
            Ty::Array(elem, _) => Some(*elem),
            Ty::Tuple(parts) => parts.get(k).copied(),
            _ => None,
        }
    }

    /// The length in bytes of the serialization of `t`.
    pub(crate) fn text_len(&self, t: TyId) -> u64 {
        self.entries.get(t.index).map_or(0, |e| e.text_len)
    }

    #[must_use]
    pub fn serialize(&self, t: TyId) -> String {
        let mut out = String::new();
        self.write(t, &mut out);
        out
    }

    /// The serialization of `t` into `out`. A part of a container type waits on the stack of
    /// the walk, so the walk does not recurse.
    pub(crate) fn write(&self, t: TyId, out: &mut String) {
        let mut work = vec![TyPiece::Ty(t)];
        while let Some(piece) = work.pop() {
            match piece {
                TyPiece::Text(text) => out.push_str(text),
                TyPiece::Len(len) => write!(out, " {len})").unwrap_or_default(),
                TyPiece::Ty(t) => match self.get(t) {
                    Ty::Array(elem, len) => {
                        out.push_str("(array ");
                        work.push(TyPiece::Len(len));
                        work.push(TyPiece::Ty(*elem));
                    }
                    Ty::Tuple(parts) => {
                        out.push_str("(tuple (");
                        work.push(TyPiece::Text("))"));
                        push_parts(&mut work, parts, " ");
                    }
                    ty => self.write_node(ty, out),
                },
            }
        }
    }

    /// The node `ty` with each part of a container type as a call of `out.ty`. A sink that
    /// writes the text of a part walks it again, so only `Len`, whose `ty` reads the table,
    /// calls this for a container type.
    fn write_node<S: Sink>(&self, ty: &Ty, out: &mut S) {
        match ty {
            Ty::Bool => out.write_str("bool").unwrap_or_default(),
            Ty::Nat => out.write_str("nat").unwrap_or_default(),
            Ty::Int => out.write_str("int").unwrap_or_default(),
            Ty::Unit => out.write_str("unit").unwrap_or_default(),
            Ty::UInt(w) => write!(out, "(uint {w})").unwrap_or_default(),
            Ty::SInt(w) => write!(out, "(sint {w})").unwrap_or_default(),
            Ty::Array(elem, len) => node(out, "array", |out| {
                out.write_str(" ").unwrap_or_default();
                out.ty(self, *elem);
                write!(out, " {len}").unwrap_or_default();
            }),
            Ty::Tuple(parts) => node(out, "tuple", |out| {
                out.write_str(" ").unwrap_or_default();
                list(out, parts, |part, out| out.ty(self, *part));
            }),
        }
    }

    /// The source form, for a message.
    #[must_use]
    pub fn text(&self, t: TyId) -> String {
        self.text_of(self.get(t))
    }

    /// The source form of the node `ty`, for a message. A text stops after `TEXT_LIMIT`
    /// bytes, because a type shares its parts and its text can be far longer than its size.
    #[must_use]
    pub fn text_of(&self, ty: &Ty) -> String {
        let mut out = Text::default();
        out.ty_node(ty);
        out.finish(self)
    }
}

/// A piece of the text of a type that waits on the stack of a walk.
enum TyPiece<'a> {
    Ty(TyId),
    Text(&'static str),
    Len(&'a Int),
}

/// Pushes the parts of a tuple, so that they come off the stack in order with `sep` between.
fn push_parts(work: &mut Vec<TyPiece<'_>>, parts: &[TyId], sep: &'static str) {
    for (k, part) in parts.iter().enumerate().rev() {
        work.push(TyPiece::Ty(*part));
        if k > 0 {
            work.push(TyPiece::Text(sep));
        }
    }
}

impl Ty {
    /// `UInt[W]` or `SInt[W]`.
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Ty::UInt(_) | Ty::SInt(_))
    }
}
