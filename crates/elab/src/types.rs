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
/// `Type`, `String`, and the container types, which include `List[T]`. A tuple type has at least one element type: `()` is
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
    /// `String`, a static type only.
    String,
    /// `List[T]`, a static type only. Its length is a value, not a part of the type.
    List(TyId),
    /// `fn (T, mut U) -> V`, a static type only. It keeps the `mut` mark of each parameter.
    Fn(Vec<TyParam>, TyId),
}

/// A parameter type of a function type, with its `mut` mark.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyParam {
    pub mutable: bool,
    pub ty: TyId,
}

/// A type in the table `Types`. Two ids of one table are equal exactly if their types are
/// structurally equal. The id carries the recursive size and the depth of its type, as the
/// type metadata of design section 5.4, so a copy of an id is constant work.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyId {
    index: usize,
    size: u64,
    depth: u64,
    strings: bool,
    funcs: bool,
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

    /// Whether `String` is `self` or a part of it, at any depth. A value of another type
    /// holds no string.
    #[must_use]
    pub fn holds_string(self) -> bool {
        self.strings
    }

    /// Whether a function type is `self` or a part of it, at any depth (the function flag of
    /// the type metadata). A struct type reads its field types only. A value of a type with
    /// the flag has no `==`.
    #[must_use]
    pub fn holds_fn(self) -> bool {
        self.funcs
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
    /// data. `Nat`, `Int`, `Type`, `String`, and `List[T]` are not, and their three numbers are
    /// 0. The depth of a list is in its id.
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
    /// each part. `touched` counts the words that the additions touch, for the tests.
    #[must_use]
    pub fn sum<'a>(parts: impl IntoIterator<Item = &'a Meta>, touched: &mut u64) -> Meta {
        let parts: Vec<&Meta> = parts.into_iter().collect();
        let mut data = true;
        for m in &parts {
            data &= m.data;
        }
        Meta {
            width: ascending_sum(parts.iter().map(|m| &m.width).collect(), 0, touched),
            leaves: ascending_sum(parts.iter().map(|m| &m.leaves).collect(), 0, touched),
            zero_size: ascending_sum(parts.iter().map(|m| &m.zero_size).collect(), 1, touched),
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

/// `start` plus the sum of `terms`. Each addition is in place, and the terms come in the
/// ascending order of their sizes. Thus the sum is never larger than a few words above the
/// term that it adds, and a carry never runs through a large sum many times: the work is in
/// the sum of the sizes of the terms and their number, which `read_charge` pays. `touched`
/// counts the words of each term and of its carry.
fn ascending_sum(mut terms: Vec<&Int>, start: u64, touched: &mut u64) -> Int {
    terms.sort_by_key(|t| int_size(t));
    let mut sum = Int::from_u64(start);
    for t in terms {
        #[cfg(test)]
        let before = sum.words();
        sum.add_assign(t);
        *touched += int_size(t);
        #[cfg(test)]
        {
            let after = sum.words();
            let from = usize::try_from(int_size(t)).unwrap_or(usize::MAX);
            *touched += after
                .iter()
                .enumerate()
                .skip(from)
                .filter(|(i, w)| before.get(*i) != Some(*w))
                .count() as u64;
        }
    }
    sum
}

/// One type of the table with its metadata.
struct Entry {
    ty: Ty,
    meta: Meta,
    /// The depth of the zero value of the type, from the type alone (section 5.5).
    zero_depth: u64,
    /// For a tuple or a struct type, the bit offset of each part in a word of the type: the
    /// sum of the widths of the parts before it, saturated. Thus a step on the base of a word
    /// reads one number (`Types::offset`) and sums nothing. The offsets of a type that is no
    /// memory word never serve, so a width above `u64` saturates.
    prefix: Vec<u64>,
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
    /// Whether the struct item is the prelude struct `ReadResponse`.
    prelude: bool,
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

    /// Whether the struct item is the prelude struct `ReadResponse`.
    #[must_use]
    pub fn prelude(&self) -> bool {
        self.prelude
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

/// The work of a hash and a comparison of `v`: 1 for each node and each word of an integer. A
/// type is an id, so it is 1.
#[cfg(test)]
fn read_work(v: &Value) -> u64 {
    let mut sum = 0;
    let mut work = vec![v];
    while let Some(v) = work.pop() {
        sum += match v {
            Value::Int(n) => int_size(n),
            Value::Str(s) => 1 + s.len() as u64,
            Value::Array(_, xs)
            | Value::Tuple(_, xs)
            | Value::Record(_, xs)
            | Value::List(_, xs) => {
                work.extend(xs);
                1
            }
            _ => 1,
        };
    }
    sum
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
    /// The name of each function item that a function value names, by its item. A value holds
    /// the item, so a copy of it copies no name.
    fn_names: BTreeMap<usize, String>,
    /// The specializations by the fingerprint of their item and arguments.
    spec_index: BTreeMap<u64, Vec<SpecId>>,
    /// The work of the lookups: 1 for each type and 1 for each part of a container type. The
    /// type of a value adds 1 for each node that its walk visits.
    #[cfg(test)]
    work: std::sync::atomic::AtomicU64,
}

impl Types {
    /// Counts `n` steps of work, for the tests of the work of the table.
    #[cfg(test)]
    pub(crate) fn tick(&self, n: u64) {
        self.work.fetch_add(n, std::sync::atomic::Ordering::Relaxed);
        crate::counters::add(crate::counters::Count::Table, n);
    }

    /// Counts the lookup of `ty`: 1 for the type and 1 for each part of a tuple type.
    #[cfg(test)]
    fn tick_lookup(&self, ty: &Ty) {
        self.tick(
            1 + match ty {
                Ty::Tuple(parts) => parts.len() as u64,
                Ty::Fn(params, _) => params.len() as u64 + 1,
                _ => 0,
            },
        );
    }

    /// The steps of work so far.
    #[cfg(test)]
    pub(crate) fn work(&self) -> u64 {
        self.work.load(std::sync::atomic::Ordering::Relaxed)
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

    /// The id of `ty` if the table holds it. Each type of a port, a register, or a binding was
    /// made by the table, so the lowering finds its id without a change of the table.
    #[must_use]
    pub fn id_of(&self, ty: &Ty) -> Option<TyId> {
        self.index.get(ty).copied()
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
            Ty::Tuple(parts) => self.sum(parts),
            scalar => Meta::scalar(scalar),
        }
    }

    /// Adds the type `ty` with its metadata to the table.
    fn insert(&mut self, ty: Ty, meta: Meta) -> TyId {
        let (size, depth) = self.shape(&ty);
        let strings = match &ty {
            Ty::String => true,
            Ty::Array(elem, _) | Ty::List(elem) => elem.strings,
            Ty::Tuple(parts) => parts.iter().any(|part| part.strings),
            Ty::Fn(params, ret) => ret.strings || params.iter().any(|p| p.ty.strings),
            _ => false,
        };
        let funcs = match &ty {
            Ty::Fn(..) => true,
            Ty::Array(elem, _) | Ty::List(elem) => elem.funcs,
            Ty::Tuple(parts) => parts.iter().any(|part| part.funcs),
            _ => false,
        };
        let prefix = match &ty {
            Ty::Tuple(parts) => self.prefix_of(parts),
            _ => Vec::new(),
        };
        self.insert_shaped(ty, (size, depth), (strings, funcs), meta, prefix)
    }

    /// The offsets of the parts `parts`: for each, the sum of the widths of the parts before it.
    fn prefix_of(&self, parts: &[TyId]) -> Vec<u64> {
        let mut sum = 0u64;
        parts
            .iter()
            .map(|part| {
                let before = sum;
                sum = sum.saturating_add(self.meta(*part).width.to_u64().unwrap_or(u64::MAX));
                before
            })
            .collect()
    }

    fn insert_shaped(
        &mut self,
        ty: Ty,
        (size, depth): (u64, u64),
        (strings, funcs): (bool, bool),
        meta: Meta,
        prefix: Vec<u64>,
    ) -> TyId {
        let id = TyId {
            index: self.entries.len(),
            size,
            depth,
            strings,
            funcs,
        };
        let zero_depth = self.zero_depth_of(&ty, depth);
        self.entries.push(Entry {
            ty: ty.clone(),
            meta,
            zero_depth,
            prefix,
        });
        self.index.insert(ty, id);
        id
    }

    /// The recursive size and the depth of a type that is not a struct type. A struct type
    /// gets its size from its arguments and its depth from `struct_meta`.
    #[must_use]
    pub fn shape(&self, ty: &Ty) -> (u64, u64) {
        match ty {
            Ty::Bool | Ty::Nat | Ty::Int | Ty::Unit | Ty::Type | Ty::String | Ty::Struct(_) => {
                (1, 1)
            }
            Ty::UInt(w) | Ty::SInt(w) => (1 + int_size(&width_int(*w)), 1),
            Ty::Array(elem, len) => Types::array_shape(*elem, len),
            Ty::Tuple(parts) => Types::tuple_shape(parts),
            Ty::List(elem) => (1u64.saturating_add(elem.size), 1 + elem.depth),
            Ty::Fn(params, ret) => Types::fn_shape(params, *ret),
        }
    }

    /// The recursive size and the depth of a function type, before the type exists: 1 node,
    /// the parts, and 1 node for each `mut` mark. A mark adds no depth.
    #[must_use]
    pub fn fn_shape(params: &[TyParam], ret: TyId) -> (u64, u64) {
        let size = params.iter().fold(1u64.saturating_add(ret.size), |sum, p| {
            sum.saturating_add(p.ty.size)
                .saturating_add(u64::from(p.mutable))
        });
        let deepest = params.iter().map(|p| p.ty.depth).fold(ret.depth, u64::max);
        (size, 1 + deepest)
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

    #[must_use]
    pub fn list(&mut self, elem: TyId) -> TyId {
        self.mk(Ty::List(elem))
    }

    #[must_use]
    pub fn function(&mut self, params: Vec<TyParam>, ret: TyId) -> TyId {
        self.mk(Ty::Fn(params, ret))
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

    /// The entry of the id `t`. Only a table makes an id, so an id that this table does not
    /// hold is a bug of the caller (an id of another table), never an input of the user.
    /// Thus a lookup stops at once, and it never answers with a default type.
    fn entry(&self, t: TyId) -> &Entry {
        let Some(entry) = self.entries.get(t.index) else {
            panic!("the type id {} is not in this table of types", t.index);
        };
        entry
    }

    /// The type with the id `t`.
    #[must_use]
    pub fn get(&self, t: TyId) -> &Ty {
        &self.entry(t).ty
    }

    /// The metadata of the type `t`.
    #[must_use]
    pub fn meta(&self, t: TyId) -> &Meta {
        &self.entry(t).meta
    }

    /// The metadata sums of the parts `parts` of a tuple or a struct type, as Lean `Meta.sum`
    /// computes them. The work reads each integer of each part, which `read_charge` pays.
    #[must_use]
    pub fn sum(&self, parts: &[TyId]) -> Meta {
        let mut touched = 0;
        let meta = Meta::sum(parts.iter().map(|part| self.meta(*part)), &mut touched);
        #[cfg(test)]
        self.tick(touched);
        meta
    }

    /// The charge of the reads of `sum` over `parts`, as Lean `Meta.readCharge`: the
    /// sizes of the four integers of each part. It bounds the work of the additions.
    #[must_use]
    pub fn read_charge(&self, parts: &[TyId]) -> u128 {
        parts
            .iter()
            .map(|part| self.meta(*part).int_charge(part.depth))
            .sum()
    }

    /// The bit offset of the part `k` in a word of the container type `t` (section 7.6). The
    /// first leaf is in the least significant bits. For an array it is `k` times the width of
    /// the element, and for a tuple or a struct type the sum of the widths of the earlier parts.
    /// The type stores the sums, so the work is constant.
    #[must_use]
    pub fn offset(&self, t: TyId, k: u64) -> u64 {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Offsets, 1);
        match self.get(t) {
            Ty::Array(elem, _) => self
                .meta(*elem)
                .width
                .to_u64()
                .unwrap_or(u64::MAX)
                .saturating_mul(k),
            Ty::Tuple(_) | Ty::Struct(_) => usize::try_from(k)
                .ok()
                .and_then(|k| self.entry(t).prefix.get(k))
                .copied()
                .unwrap_or(0),
            _ => 0,
        }
    }

    /// The depth of the zero value of `t`, from the type alone.
    #[must_use]
    pub fn zero_depth(&self, t: TyId) -> u64 {
        self.entry(t).zero_depth
    }

    /// The id of the part `k` of the container type `t`: the element type of an array or a
    /// list, or the type of the element `k` of a tuple.
    #[must_use]
    pub fn part(&self, t: TyId, k: usize) -> Option<TyId> {
        match self.get(t) {
            Ty::Array(elem, _) | Ty::List(elem) => Some(*elem),
            Ty::Tuple(parts) => parts.get(k).copied(),
            _ => None,
        }
    }

    /// The length in bytes of the serialization of `t`, if the table holds `t`. It computes
    /// the length of each part once, and no text of a type is built.
    #[must_use]
    pub fn text_len(&self, t: TyId) -> Option<u64> {
        self.entries.get(t.index)?;
        Some(Len::default().type_len(self, t))
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

    /// Keeps the name of the function item `item`, once.
    pub fn name_fn(&mut self, item: usize, name: &str) {
        self.fn_names.entry(item).or_insert_with(|| name.to_owned());
    }

    /// The name of the function item `item`.
    #[must_use]
    pub fn fn_name(&self, item: usize) -> &str {
        self.fn_names.get(&item).map_or("", String::as_str)
    }

    /// The specialization `s`.
    ///
    /// # Panics
    ///
    /// If `s` is not from this table, which is a bug of the caller.
    #[must_use]
    pub fn spec(&self, s: SpecId) -> &Spec {
        let Some(spec) = self.specs.get(s.0) else {
            panic!("the specialization {} is not in this table of types", s.0);
        };
        spec
    }

    /// The struct type of the specialization `s`, if it is done.
    fn spec_ty(&self, s: SpecId) -> Option<TyId> {
        match &self.spec(s).state {
            SpecState::Done { ty, .. } => Some(*ty),
            SpecState::InProgress => None,
        }
    }

    /// The specialization of the struct item `item` with the arguments `args`, and its struct
    /// type if it is done. The fingerprint narrows the search, and the arguments decide. The
    /// hash and the comparison read each argument in full, so the caller pays their sizes.
    #[must_use]
    pub fn find_spec(&self, item: usize, args: &[&Value]) -> Option<(SpecId, Option<TyId>)> {
        #[cfg(test)]
        self.tick(1 + args.iter().map(|v| read_work(v)).sum::<u64>());
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

    /// Starts the specialization of the struct item `item` named `name`, which is the prelude
    /// struct if `prelude`. The caller paid the size of the arguments, which it moves here.
    pub fn begin_spec(
        &mut self,
        name: &str,
        item: usize,
        args: Vec<Value>,
        prelude: bool,
    ) -> SpecId {
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
            prelude,
        });
        s
    }

    /// The metadata and the depth of the struct type of `s` from its field types `fields`, as
    /// Lean `Meta.struct` computes them: the depth counts the static arguments too.
    #[must_use]
    pub fn struct_meta(&self, s: SpecId, fields: &[TyId]) -> (Meta, u64) {
        (self.sum(fields), self.struct_depth(s, fields))
    }

    /// The depth of the struct type of `s` from its field types `fields`: 1 more than the
    /// deepest field type and static argument. It needs no metadata sum.
    #[must_use]
    pub fn struct_depth(&self, s: SpecId, fields: &[TyId]) -> u64 {
        1 + fields
            .iter()
            .map(|f| f.depth)
            .chain(self.spec(s).args.iter().map(Value::depth))
            .max()
            .unwrap_or(0)
    }

    /// Completes the specialization `s` with its field types and its metadata, and gives its
    /// struct type. The caller checked the depth and paid the charge.
    pub fn finish_spec(&mut self, s: SpecId, fields: Vec<TyId>, meta: Meta, depth: u64) -> TyId {
        let size = self
            .spec(s)
            .args
            .iter()
            .fold(1u64, |sum, arg| sum.saturating_add(arg.size()));
        let strings = fields.iter().any(|field| field.strings);
        // The function flag of a struct reads the field types, not the static arguments.
        let funcs = fields.iter().any(|field| field.funcs);
        let prefix = self.prefix_of(&fields);
        let ty = self.insert_shaped(Ty::Struct(s), (size, depth), (strings, funcs), meta, prefix);
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
                    Ty::Nat | Ty::Int | Ty::Type | Ty::String | Ty::List(_) | Ty::Fn(..) => {
                        return None;
                    }
                },
                Step::Array(elem, n) => {
                    let first = done.pop()?;
                    let mut xs = Vec::with_capacity(n);
                    if n > 1 {
                        xs.resize(n - 1, first.clone());
                    }
                    xs.push(first);
                    done.push(Value::Array(elem, xs));
                }
                Step::Tuple(n) => {
                    let xs = done.split_off(done.len().checked_sub(n)?);
                    done.push(Value::tuple(xs));
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
