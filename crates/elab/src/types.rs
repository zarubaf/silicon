// SPDX-License-Identifier: Apache-2.0
//! The static types and their table, as Lean `Source.Value` defines the type values. A type is
//! an id in the table `Types`: a copy and an equality of types are constant work, and the id
//! carries the size and the depth of its type.
//!
//! The table also holds the struct specializations (design section 5.6). A specialization
//! owns its static arguments and its field types, and its struct type carries the metadata of
//! section 5.4, so no operation walks the field types again.

use crate::int::Int;
use crate::serial::{self, Item, Len};
use crate::text::Text;
use crate::value::{Value, int_size, width_int, width_size};
use std::collections::BTreeMap;
use std::hash::{DefaultHasher, Hash, Hasher};

/// A type as a static value: the scalar types of slice 1 with a width from 1 to 65536, `()`,
/// `Type`, and the container types. A tuple type has at least one element type: `()` is
/// `Unit`. The length of an array type is any natural number, as the type does not hold the
/// elements. A struct type is a specialization of the table.
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
    Type,
    Array(TyId, Int),
    Tuple(Vec<TyId>),
    Struct(SpecId),
}

/// A type in the table `Types`. Two ids of one table are equal exactly if their types are
/// structurally equal. The id carries the recursive size and the depth of its type, as the
/// type metadata of design section 5.4, so a copy of an id is constant work.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyId {
    index: usize,
    size: u64,
    depth: u64,
}

impl TyId {
    /// Feeds the id to `h`.
    pub fn hash_into(self, h: &mut impl Hasher) {
        h.write_usize(self.index);
    }

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

/// A struct specialization in the table `Types`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpecId(usize);

/// The type metadata of section 5.4 without the depth, which the id carries. It holds the bit
/// width as hardware data, the leaf count, and the recursive size of the zero value. It also
/// tells if the type is hardware data. The three numbers of a type that is not hardware data
/// have no meaning, but both front ends compute them by the same rules, so they charge the
/// same.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Meta {
    pub width: Int,
    pub leaves: Int,
    pub zero_size: Int,
    pub data: bool,
}

impl Meta {
    fn new(width: u64, leaves: u64, zero_size: u64, data: bool) -> Meta {
        Meta {
            width: Int::from_u64(width),
            leaves: Int::from_u64(leaves),
            zero_size: Int::from_u64(zero_size),
            data,
        }
    }

    /// The metadata of the scalar types. `Bool`, `UInt[W]`, `SInt[W]`, and `Unit` are hardware
    /// data. `Nat`, `Int`, and `Type` are not, and their three numbers are 0.
    fn scalar(ty: &Ty) -> Meta {
        match ty {
            Ty::Bool => Meta::new(1, 1, 1, true),
            Ty::UInt(w) | Ty::SInt(w) => Meta::new(u64::from(*w), 1, width_size(*w), true),
            Ty::Unit => Meta::new(0, 0, 1, true),
            _ => Meta::new(0, 0, 0, false),
        }
    }

    /// The metadata of `[T; N]` from the metadata of `T`: the product rule of section 5.4.
    #[must_use]
    pub fn array(&self, n: &Int) -> Meta {
        Meta {
            width: n.mul(&self.width),
            leaves: n.mul(&self.leaves),
            zero_size: Int::from_u64(1).add(&n.mul(&self.zero_size)),
            data: self.data,
        }
    }

    /// The sums of the parts of a tuple or a record: the zero value is a node with the zero of
    /// each part.
    #[must_use]
    pub fn sum<'a>(parts: impl IntoIterator<Item = &'a Meta>) -> Meta {
        let (mut width, mut leaves, mut zero, mut data) =
            (Int::zero(), Int::zero(), Int::from_u64(1), true);
        for m in parts {
            width = width.add(&m.width);
            leaves = leaves.add(&m.leaves);
            zero = zero.add(&m.zero_size);
            data &= m.data;
        }
        Meta {
            width,
            leaves,
            zero_size: zero,
            data,
        }
    }

    /// The charge of `array(n)` at the node of `[T; N]`, before the type exists: each of the
    /// three products charges as a multiplication of static integers.
    #[must_use]
    pub fn array_charge(&self, n: &Int) -> u128 {
        u128::from(int_size(n))
            * (u128::from(int_size(&self.width))
                + u128::from(int_size(&self.leaves))
                + u128::from(int_size(&self.zero_size)))
    }

    /// The sizes of the four integers of the metadata with the depth `depth`. A type
    /// constructor that makes them charges this.
    #[must_use]
    pub fn int_charge(&self, depth: u64) -> u128 {
        u128::from(int_size(&self.width))
            + u128::from(int_size(&self.leaves))
            + u128::from(int_size(&self.zero_size))
            + u128::from(int_size(&Int::from_u64(depth)))
    }
}

/// One type of the table with its metadata.
struct Entry {
    ty: Ty,
    text_len: u64,
    meta: Meta,
    /// The depth of the zero value of the type, from the type alone (section 5.5).
    zero_depth: u64,
}

/// The state of a struct specialization.
enum SpecState {
    InProgress,
    Done { ty: TyId, fields: Vec<TyId> },
}

/// A struct specialization (section 5.6): the struct item, its name, its static arguments
/// after their typed use, and its state. A done entry holds its struct type and its field
/// types.
pub struct Spec {
    item: usize,
    name: String,
    args: Vec<Value>,
    state: SpecState,
}

impl Spec {
    /// The static arguments, as the key of the specialization.
    #[must_use]
    pub fn args(&self) -> &[Value] {
        &self.args
    }

    /// The name of the struct item.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// The result of a join of two types: the units that its walk charged, and the common type.
#[derive(Clone)]
pub struct Joined {
    pub charge: Int,
    pub ty: Option<TyId>,
}

/// The fingerprint of a struct item and its arguments. A bucket of the index holds the
/// specializations with one fingerprint, and the arguments decide.
fn fingerprint<'a>(item: usize, args: impl IntoIterator<Item = &'a Value>) -> u64 {
    let mut h = DefaultHasher::new();
    item.hash(&mut h);
    for arg in args {
        arg.hash_into(&mut h);
    }
    h.finish()
}

/// The table of the static types of one elaboration. A structurally equal type has one id, so
/// a copy of a type and an equality of two types are constant work. A container type holds
/// the ids of its parts, so a new type costs work in its own arity only. The table grows only
/// with charged work: each new type pays its recursive size at its constructor.
#[derive(Default)]
pub struct Types {
    entries: Vec<Entry>,
    index: BTreeMap<Ty, TyId>,
    /// The join of each pair of types that joined: its charge and its common type, if any.
    joins: BTreeMap<(TyId, TyId), Joined>,
    specs: Vec<Spec>,
    /// The specializations by the fingerprint of their item and arguments.
    spec_index: BTreeMap<u64, Vec<SpecId>>,
    /// The work of the lookups: 1 for each type and 1 for each part of a container type. The
    /// type of a value adds 1 for each node that its walk visits.
    #[cfg(test)]
    work: std::cell::Cell<u64>,
}

/// The type that an absent id names. The table makes each id, so no id finds it.
static ABSENT: Ty = Ty::Unit;

impl Types {
    /// Counts `n` steps of work, for the tests of the work of the table.
    #[cfg(test)]
    pub(crate) fn tick(&self, n: u64) {
        self.work.set(self.work.get() + n);
    }

    /// Counts the lookup of `ty`: 1 for the type and 1 for each part of a tuple type.
    #[cfg(test)]
    fn tick_lookup(&self, ty: &Ty) {
        self.tick(
            1 + match ty {
                Ty::Tuple(parts) => parts.len() as u64,
                _ => 0,
            },
        );
    }

    /// The steps of work so far.
    #[cfg(test)]
    pub(crate) fn work(&self) -> u64 {
        self.work.get()
    }

    /// The id of `ty`, which is not a struct type. A new type gets its metadata from the ids
    /// of its parts. The caller pays the work of a metadata number that it can compute
    /// before: see `meta_of` and `mk_with`.
    pub fn mk(&mut self, ty: Ty) -> TyId {
        #[cfg(test)]
        self.tick_lookup(&ty);
        if let Some(id) = self.index.get(&ty) {
            return *id;
        }
        let meta = self.meta_of(&ty);
        self.insert(ty, meta)
    }

    /// The id of `ty`, which is not a struct type, with the metadata `meta` that the caller
    /// computed from `meta_of` to charge it.
    pub fn mk_with(&mut self, ty: Ty, meta: Meta) -> TyId {
        #[cfg(test)]
        self.tick_lookup(&ty);
        if let Some(id) = self.index.get(&ty) {
            return *id;
        }
        self.insert(ty, meta)
    }

    /// The metadata of a type that is not a struct type, from the metadata of its parts. A
    /// struct type gets its metadata from `struct_meta`.
    #[must_use]
    pub fn meta_of(&self, ty: &Ty) -> Meta {
        match ty {
            Ty::Array(elem, len) => self.meta(*elem).array(len),
            Ty::Tuple(parts) => Meta::sum(parts.iter().map(|part| self.meta(*part))),
            scalar => Meta::scalar(scalar),
        }
    }

    /// Adds the type `ty` with its metadata to the table.
    fn insert(&mut self, ty: Ty, meta: Meta) -> TyId {
        let (size, depth) = self.shape(&ty);
        self.insert_shaped(ty, size, depth, meta)
    }

    fn insert_shaped(&mut self, ty: Ty, size: u64, depth: u64, meta: Meta) -> TyId {
        let id = TyId {
            index: self.entries.len(),
            size,
            depth,
        };
        let mut len = Len::default();
        serial::write(self, Item::Node(&ty), &mut len);
        let zero_depth = self.zero_depth_of(&ty, depth);
        self.entries.push(Entry {
            ty: ty.clone(),
            text_len: len.0,
            meta,
            zero_depth,
        });
        self.index.insert(ty, id);
        id
    }

    /// The recursive size and the depth of a type that is not a struct type. A struct type
    /// gets its size from its arguments and its depth from `struct_meta`.
    #[must_use]
    pub fn shape(&self, ty: &Ty) -> (u64, u64) {
        match ty {
            Ty::Bool | Ty::Nat | Ty::Int | Ty::Unit | Ty::Type | Ty::Struct(_) => (1, 1),
            Ty::UInt(w) | Ty::SInt(w) => (1 + int_size(&width_int(*w)), 1),
            Ty::Array(elem, len) => Types::array_shape(*elem, len),
            Ty::Tuple(parts) => Types::tuple_shape(parts),
        }
    }

    /// The recursive size and the depth of `[elem; len]`, before the type exists.
    #[must_use]
    pub fn array_shape(elem: TyId, len: &Int) -> (u64, u64) {
        (
            1u64.saturating_add(elem.size).saturating_add(int_size(len)),
            1 + elem.depth,
        )
    }

    /// The recursive size and the depth of a tuple of `parts`, before the type exists.
    #[must_use]
    pub fn tuple_shape(parts: &[TyId]) -> (u64, u64) {
        (
            parts
                .iter()
                .fold(1u64, |sum, part| sum.saturating_add(part.size)),
            1 + parts.iter().map(|part| part.depth).max().unwrap_or(0),
        )
    }

    /// The depth of the zero value of a type from the type alone: an array of length 0 has
    /// the depth of its type, another array 1 more than the zero of its element, and a
    /// record 1 more than its struct type. Thus no walk enters the field types of a struct.
    fn zero_depth_of(&self, ty: &Ty, depth: u64) -> u64 {
        match ty {
            Ty::Array(elem, len) if len.is_zero() => 1 + elem.depth,
            Ty::Array(elem, _) => 1 + self.zero_depth(*elem),
            Ty::Tuple(parts) => {
                1 + parts
                    .iter()
                    .map(|part| self.zero_depth(*part))
                    .max()
                    .unwrap_or(0)
            }
            Ty::Struct(_) => 1 + depth,
            _ => 1,
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

    /// The join of `lhs` and `rhs` if they joined before.
    #[must_use]
    pub fn joined(&self, lhs: TyId, rhs: TyId) -> Option<&Joined> {
        self.joins.get(&(lhs, rhs))
    }

    /// Keeps the join of the pair `key`.
    pub fn join(&mut self, key: (TyId, TyId), joined: Joined) {
        self.joins.insert(key, joined);
    }

    /// The type with the id `t`.
    #[must_use]
    pub fn get(&self, t: TyId) -> &Ty {
        self.entries.get(t.index).map_or(&ABSENT, |e| &e.ty)
    }

    /// The metadata of the type `t`.
    #[must_use]
    pub fn meta(&self, t: TyId) -> &Meta {
        static ABSENT_META: std::sync::LazyLock<Meta> =
            std::sync::LazyLock::new(|| Meta::scalar(&Ty::Unit));
        self.entries.get(t.index).map_or(&ABSENT_META, |e| &e.meta)
    }

    /// The depth of the zero value of `t`, from the type alone.
    #[must_use]
    pub fn zero_depth(&self, t: TyId) -> u64 {
        self.entries.get(t.index).map_or(1, |e| e.zero_depth)
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
    #[must_use]
    pub fn text_len(&self, t: TyId) -> u64 {
        self.entries.get(t.index).map_or(0, |e| e.text_len)
    }

    #[must_use]
    pub fn serialize(&self, t: TyId) -> String {
        let mut out = String::new();
        serial::write(self, Item::Ty(t), &mut out);
        out
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
        out.ty_node(self, ty);
        out.finish(self)
    }

    /// The specialization `s`.
    #[must_use]
    pub fn spec(&self, s: SpecId) -> &Spec {
        static ABSENT_SPEC: std::sync::LazyLock<Spec> = std::sync::LazyLock::new(|| Spec {
            item: 0,
            name: String::new(),
            args: Vec::new(),
            state: SpecState::InProgress,
        });
        self.specs.get(s.0).unwrap_or(&ABSENT_SPEC)
    }

    /// The struct type of the specialization `s`, if it is done.
    fn spec_ty(&self, s: SpecId) -> Option<TyId> {
        match &self.spec(s).state {
            SpecState::Done { ty, .. } => Some(*ty),
            SpecState::InProgress => None,
        }
    }

    /// The specialization of the struct item `item` with the arguments `args`, and its struct
    /// type if it is done. The fingerprint narrows the search, and the arguments decide.
    #[must_use]
    pub fn find_spec(&self, item: usize, args: &[&Value]) -> Option<(SpecId, Option<TyId>)> {
        #[cfg(test)]
        self.tick(1 + args.len() as u64);
        let bucket = self
            .spec_index
            .get(&fingerprint(item, args.iter().copied()))?;
        let found = bucket.iter().copied().find(|s| {
            let spec = self.spec(*s);
            spec.item == item
                && spec.args.len() == args.len()
                && spec.args.iter().zip(args).all(|(a, b)| a == *b)
        })?;
        Some((found, self.spec_ty(found)))
    }

    /// Starts the specialization of the struct item `item` named `name`. The caller paid the
    /// size of the arguments, which it moves here.
    pub fn begin_spec(&mut self, name: &str, item: usize, args: Vec<Value>) -> SpecId {
        #[cfg(test)]
        self.tick(1 + args.len() as u64);
        let s = SpecId(self.specs.len());
        self.spec_index
            .entry(fingerprint(item, &args))
            .or_default()
            .push(s);
        self.specs.push(Spec {
            item,
            name: name.to_owned(),
            args,
            state: SpecState::InProgress,
        });
        s
    }

    /// The metadata and the depth of the struct type of `s` from its field types `fields`, as
    /// Lean `Meta.struct` computes them: the depth counts the static arguments too.
    #[must_use]
    pub fn struct_meta(&self, s: SpecId, fields: &[TyId]) -> (Meta, u64) {
        let metas = Meta::sum(fields.iter().map(|f| self.meta(*f)));
        let deepest = fields
            .iter()
            .map(|f| f.depth)
            .chain(self.spec(s).args.iter().map(Value::depth))
            .max()
            .unwrap_or(0);
        (metas, 1 + deepest)
    }

    /// Completes the specialization `s` with its field types and its metadata, and gives its
    /// struct type. The caller checked the depth and paid the charge.
    pub fn finish_spec(&mut self, s: SpecId, fields: Vec<TyId>, meta: Meta, depth: u64) -> TyId {
        let size = self
            .spec(s)
            .args
            .iter()
            .fold(1u64, |sum, arg| sum.saturating_add(arg.size()));
        let ty = self.insert_shaped(Ty::Struct(s), size, depth, meta);
        if let Some(spec) = self.specs.get_mut(s.0) {
            spec.state = SpecState::Done { ty, fields };
        }
        ty
    }

    /// The struct item and the field types of the struct type `t`.
    #[must_use]
    pub fn fields(&self, t: TyId) -> Option<(usize, &[TyId])> {
        let Ty::Struct(s) = self.get(t) else {
            return None;
        };
        let spec = self.spec(*s);
        match &spec.state {
            SpecState::Done { fields, .. } => Some((spec.item, fields)),
            SpecState::InProgress => None,
        }
    }

    /// The zero value of the hardware data type `t` (section 5.6): 0 for each integer leaf
    /// and `false` for each `Bool` leaf. A record takes the field types of its struct. The
    /// walk keeps its own stack, and it builds an array from one copy of its zero element.
    #[must_use]
    pub fn zero(&self, t: TyId) -> Option<Value> {
        enum Step {
            Visit(TyId),
            Array(TyId, usize),
            Tuple(usize),
            Record(TyId, usize),
        }
        let mut done: Vec<Value> = Vec::new();
        let mut work = vec![Step::Visit(t)];
        while let Some(step) = work.pop() {
            match step {
                Step::Visit(t) => match self.get(t) {
                    Ty::Bool => done.push(Value::Bool(false)),
                    Ty::UInt(w) => done.push(Value::UInt(crate::int::finite(*w, 0)?)),
                    Ty::SInt(w) => done.push(Value::SInt(crate::int::finite(*w, 0)?)),
                    Ty::Unit => done.push(Value::Unit),
                    Ty::Array(elem, len) => {
                        let n = len.to_u64().and_then(|n| usize::try_from(n).ok())?;
                        if n == 0 {
                            done.push(Value::Array(*elem, Vec::new()));
                        } else {
                            work.push(Step::Array(*elem, n));
                            work.push(Step::Visit(*elem));
                        }
                    }
                    Ty::Tuple(parts) => {
                        work.push(Step::Tuple(parts.len()));
                        work.extend(parts.iter().rev().map(|part| Step::Visit(*part)));
                    }
                    Ty::Struct(_) => {
                        let (_, fields) = self.fields(t)?;
                        work.push(Step::Record(t, fields.len()));
                        work.extend(fields.iter().rev().map(|f| Step::Visit(*f)));
                    }
                    Ty::Nat | Ty::Int | Ty::Type => return None,
                },
                Step::Array(elem, n) => {
                    let first = done.pop()?;
                    let mut xs = Vec::with_capacity(n);
                    xs.resize(n - 1, first.clone());
                    xs.push(first);
                    done.push(Value::Array(elem, xs));
                }
                Step::Tuple(n) => {
                    let xs = done.split_off(done.len().checked_sub(n)?);
                    done.push(Value::Tuple(xs));
                }
                Step::Record(t, n) => {
                    let xs = done.split_off(done.len().checked_sub(n)?);
                    done.push(Value::Record(t, xs));
                }
            }
        }
        done.pop()
    }
}

impl Ty {
    /// `UInt[W]` or `SInt[W]`.
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Ty::UInt(_) | Ty::SInt(_))
    }
}
