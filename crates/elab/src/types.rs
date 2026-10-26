// SPDX-License-Identifier: Apache-2.0
//! The static types and their table, as Lean `Source.Value` defines the type values. A type is
//! an id in the table `Types`: a copy and an equality of types are constant work, and the id
//! carries the size and the depth of its type.
//!
//! The table also holds the struct specializations (design section 5.6). A specialization
//! owns its static arguments and its field types, and its struct type carries the metadata of
//! section 5.4, so no operation walks the field types again.

use crate::int::Int;
use crate::names::Sym;
use crate::serial::{self, Item, Len};
use crate::text::Text;
use crate::value::{Value, int_size, width_int, width_size};
use core_ir::Bits;
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
    /// An enum, by its item (section 5.4). The table of enums holds its widths and variants.
    Enum(EnumId),
    /// `String`, a static type only.
    String,
    /// `List[T]`, a static type only. Its length is a value, not a part of the type.
    List(TyId),
    /// `fn (T, mut U) -> V`, a static type only. It keeps the `mut` mark of each parameter.
    Fn(Vec<TyParam>, TyId),
    /// `Reg[T]`, a static type only: the handle of a register of the data type `T` (section 5.1).
    Reg(TyId),
    /// `Wire[T]`, a static type only.
    Wire(TyId),
    /// `Input[T]`, a static type only.
    Input(TyId),
    /// `Mem[T, N]`, a static type only: the handle of a memory of `N` words of the data type `T`.
    Mem(TyId, Int),
    /// `Instance[M, args]`, a static type only, by its entry in the table of instance types.
    Instance(InstId),
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
    /// The flags of the type metadata, as the bits `STRINGS`, `FUNCS`, `ENUMS`, and `HANDLES`.
    flags: u8,
}

/// The flag bits of a `TyId`.
const STRINGS: u8 = 1;
const FUNCS: u8 = 2;
const ENUMS: u8 = 4;
const HANDLES: u8 = 8;

/// The bit `flag` when `on`, else none.
fn bit(on: bool, flag: u8) -> u8 {
    if on { flag } else { 0 }
}

impl TyId {
    fn has(self, flag: u8) -> bool {
        self.flags & flag != 0
    }

    /// Feeds the id to `h`.
    pub fn hash_into(self, h: &mut impl Hasher) {
        h.write_usize(self.index);
    }

    /// The number of nodes of the type term, plus the size of each integer in it. This is the
    /// fifth metadata number of design section 5.4. A read takes constant work. A saturated
    /// number is above each budget. Lean `Ty.size` computes the same number with a walk.
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
        self.has(STRINGS)
    }

    /// Whether a function type is `self` or a part of it, at any depth (the function flag of
    /// the type metadata). A struct type reads its field types only. A value of a type with
    /// the flag has no `==`.
    #[must_use]
    pub fn holds_fn(self) -> bool {
        self.has(FUNCS)
    }

    /// Whether an enum type is `self` or a part of it, at any depth (the enum flag of the type
    /// metadata). A struct type reads its field types only. A value of a type with the flag
    /// has no `==`.
    #[must_use]
    pub fn holds_enum(self) -> bool {
        self.has(ENUMS)
    }

    /// Whether a handle type is `self` or a part of it, at any depth (the handle flag of the
    /// type metadata). A struct type reads its field types only, and a function type does not
    /// take the flag of its parts. A value of a type with the flag is never static
    /// (section 5.1).
    #[must_use]
    pub fn holds_handles(self) -> bool {
        self.has(HANDLES)
    }
}

/// A struct specialization in the table `Types`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SpecId(usize);

/// An instance type `Instance[M, args]` in the table `Types`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstId(usize);

/// An instance type (section 5.4): the module item, its name, and its converted arguments. The
/// arguments are static values, so a `Vec<Value>` cannot be the key of the index of types. The
/// table finds an instance type by the fingerprint of its item and its arguments, as it finds a
/// struct specialization.
pub struct InstTy {
    item: usize,
    name: String,
    args: Vec<Value>,
}

impl InstTy {
    /// The index of the module item.
    #[must_use]
    pub fn item(&self) -> usize {
        self.item
    }

    /// The name of the module item.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The converted arguments of the module.
    #[must_use]
    pub fn args(&self) -> &[Value] {
        &self.args
    }
}

/// An enum type: the index of its item.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumId(usize);

impl EnumId {
    /// The index of the enum item.
    #[must_use]
    pub fn item(self) -> usize {
        self.0
    }
}

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

/// A struct specialization (section 5.6): its key, its name, its static arguments after their
/// typed use, and its state. A done entry holds its struct type and its field types.
pub struct Spec {
    key: SpecKey,
    name: String,
    args: Vec<Value>,
    state: SpecState,
    origin: Origin,
}

/// What identifies a struct specialization: a struct item, or the field list of a generated
/// record type.
enum SpecKey {
    Item(usize),
    Generated(Generated),
}

/// The origin of a struct type (section 5.6): a struct item of the user, a prelude struct, or a
/// generated record type of `@Struct`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    User,
    Prelude,
    Generated,
}

impl Origin {
    /// The token of the origin in the serialization of a struct type.
    #[must_use]
    pub fn token(self) -> &'static str {
        match self {
            Origin::User => "root",
            Origin::Prelude => "prelude",
            Origin::Generated => "gstruct",
        }
    }
}

/// The symbol of a field name as a key of a member map. In the tests, each compare of two keys
/// counts, so a test sees the work of the map and not only the number of its calls.
#[derive(Clone, Copy, Debug)]
pub struct Member(pub Sym);

impl PartialEq for Member {
    fn eq(&self, other: &Member) -> bool {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Mapped, 1);
        self.0 == other.0
    }
}

impl Eq for Member {}

impl PartialOrd for Member {
    fn partial_cmp(&self, other: &Member) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Member {
    fn cmp(&self, other: &Member) -> std::cmp::Ordering {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Mapped, 1);
        self.0.cmp(&other.0)
    }
}

/// The fields of a generated record type (section 5.6): the name of each field, the symbol of
/// each name in the order of the fields, and the number of each field by its symbol.
#[derive(Debug)]
pub struct Generated {
    names: Vec<String>,
    order: Vec<Sym>,
    members: BTreeMap<Member, usize>,
}

impl Generated {
    /// The fields with the names `names`, whose symbols `order` give the member map `members`.
    #[must_use]
    pub fn new(names: Vec<String>, order: Vec<Sym>, members: BTreeMap<Member, usize>) -> Self {
        Generated {
            names,
            order,
            members,
        }
    }

    /// The name of each field, in order.
    #[must_use]
    pub fn names(&self) -> &[String] {
        &self.names
    }
}

impl Spec {
    /// The static arguments, as the key of the specialization.
    #[must_use]
    pub fn args(&self) -> &[Value] {
        &self.args
    }

    /// The name of the struct item. A generated record type has none.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The origin of the struct type.
    #[must_use]
    pub fn origin(&self) -> Origin {
        self.origin
    }

    /// The fields of the struct type if it is a generated record type.
    #[must_use]
    pub fn generated(&self) -> Option<&Generated> {
        match &self.key {
            SpecKey::Generated(g) => Some(g),
            SpecKey::Item(_) => None,
        }
    }

    /// The field types of a done entry, in order.
    #[must_use]
    pub fn field_types(&self) -> &[TyId] {
        match &self.state {
            SpecState::Done { fields, .. } => fields,
            SpecState::InProgress => &[],
        }
    }
}

/// What names the parts of a type with named parts.
#[derive(Clone, Copy, Debug)]
pub enum PartNames<'a> {
    /// The field names of the struct item.
    Struct(usize),
    /// The field names of a generated record type.
    Generated(&'a Generated),
    /// The names `tag` and `payload` of an enum.
    Enum,
}

impl<'a> PartNames<'a> {
    /// The struct item whose field names name the parts. An enum and a generated record type
    /// have none.
    #[must_use]
    pub fn item(self) -> Option<usize> {
        match self {
            PartNames::Struct(item) => Some(item),
            PartNames::Generated(_) | PartNames::Enum => None,
        }
    }

    /// The symbols of the field names of a struct type, in the order of the fields: for a
    /// struct item from the table `order` of the struct items. An enum has no field.
    #[must_use]
    pub fn order<'t>(self, order: &'t [Vec<Sym>]) -> Option<&'t [Sym]>
    where
        'a: 't,
    {
        match self {
            PartNames::Struct(item) => order.get(item).map(Vec::as_slice),
            PartNames::Generated(g) => Some(&g.order),
            PartNames::Enum => None,
        }
    }

    /// The number of the field with the symbol `y` in a struct type: for a struct item from the
    /// table `members` of the struct items. An enum has no field.
    #[must_use]
    pub fn number(self, members: &[BTreeMap<Sym, usize>], y: Sym) -> Option<usize> {
        match self {
            PartNames::Struct(item) => members.get(item)?.get(&y).copied(),
            PartNames::Generated(g) => g.members.get(&Member(y)).copied(),
            PartNames::Enum => None,
        }
    }
}

/// The named parts of a type (`Types::parts`): where their names come from, and their types.
#[derive(Clone, Copy, Debug)]
pub struct Parts<'a> {
    pub names: PartNames<'a>,
    pub types: &'a [TyId],
}

impl Parts<'_> {
    /// The struct item whose field names name the parts. An enum has no field.
    #[must_use]
    pub fn item(&self) -> Option<usize> {
        self.names.item()
    }
}

/// The names of the two parts of an enum.
pub const ENUM_PART_NAMES: [&str; 2] = ["tag", "payload"];

/// A variant of a done enum: its tag value, converted to `UInt[W]`, and its payload types.
pub struct Variant {
    pub tag: Bits,
    pub payload: Vec<TyId>,
}

/// An enum in the table of enums (section 5.6), by its item. A done entry holds the enum type,
/// the tag width `W`, the payload width `P`, the types of its parts, and its variants in
/// declaration order. Its tag map gives the variant of each tag value. An enum that is not
/// started has no entry.
enum EnumState {
    InProgress,
    Done(DoneEnum),
}

struct DoneEnum {
    ty: TyId,
    tag_width: u32,
    payload_width: u32,
    /// `UInt[W]`, then `UInt[P]` when `P` is not 0.
    parts: Vec<TyId>,
    variants: Vec<Variant>,
    /// The index of the variant with each tag value.
    tags: BTreeMap<Int, usize>,
}

/// An enum in the table: its name and its state.
struct EnumEntry {
    name: String,
    state: EnumState,
}

/// Where an enum item stands in the table of enums.
pub enum EnumStatus {
    /// No use yet.
    Fresh,
    /// Its checks run.
    InProgress,
    /// Done, with its enum type.
    Done(TyId),
}

/// The widths of a done enum: the tag width `W` and the payload width `P`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Widths {
    pub tag: u32,
    pub payload: u32,
}

/// The result of a join of two types: the units that its walk charged, and the common type.
/// A pair with a handle type that is not one type stops the walk, and `clash` holds the pair.
#[derive(Clone)]
pub struct Joined {
    pub charge: Int,
    pub ty: Option<TyId>,
    pub clash: Option<(TyId, TyId)>,
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

/// The fingerprint of a generated record type: the symbols of its field names and its field
/// types, in order. A bucket of the index holds the entries with one fingerprint, and the field
/// lists decide.
fn gen_fingerprint(order: &[Sym], types: &[TyId]) -> u64 {
    let mut h = DefaultHasher::new();
    order.hash(&mut h);
    for t in types {
        t.hash_into(&mut h);
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
    /// The enums by their item.
    enums: BTreeMap<usize, EnumEntry>,
    /// The name of each function item that a function value names, by its item. A value holds
    /// the item, so a copy of it copies no name.
    fn_names: BTreeMap<usize, String>,
    /// The specializations by the fingerprint of their item and arguments.
    spec_index: BTreeMap<u64, Vec<SpecId>>,
    /// The generated record types by the fingerprint of their symbols and field types. Their
    /// key never holds a value, so the index of types needs no `Vec<Value>`.
    gen_index: BTreeMap<u64, Vec<SpecId>>,
    /// The instance types, and their ids by the fingerprint of their item and arguments.
    insts: Vec<InstTy>,
    inst_index: BTreeMap<u64, Vec<(InstId, TyId)>>,
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
                Ty::Instance(i) => 1 + self.insts.get(i.0).map_or(0, |t| t.args.len() as u64),
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
        let (size, depth) = Types::shape(&ty);
        let strings = match &ty {
            Ty::String => true,
            Ty::Array(elem, _)
            | Ty::List(elem)
            | Ty::Reg(elem)
            | Ty::Wire(elem)
            | Ty::Input(elem)
            | Ty::Mem(elem, _) => elem.holds_string(),
            Ty::Tuple(parts) => parts.iter().any(|part| part.holds_string()),
            Ty::Fn(params, ret) => ret.holds_string() || params.iter().any(|p| p.ty.holds_string()),
            _ => false,
        };
        let funcs = match &ty {
            Ty::Fn(..) => true,
            Ty::Array(elem, _)
            | Ty::List(elem)
            | Ty::Reg(elem)
            | Ty::Wire(elem)
            | Ty::Input(elem)
            | Ty::Mem(elem, _) => elem.holds_fn(),
            Ty::Tuple(parts) => parts.iter().any(|part| part.holds_fn()),
            _ => false,
        };
        let enums = match &ty {
            Ty::Enum(_) => true,
            Ty::Array(elem, _)
            | Ty::List(elem)
            | Ty::Reg(elem)
            | Ty::Wire(elem)
            | Ty::Input(elem)
            | Ty::Mem(elem, _) => elem.holds_enum(),
            Ty::Tuple(parts) => parts.iter().any(|part| part.holds_enum()),
            Ty::Fn(params, ret) => ret.holds_enum() || params.iter().any(|p| p.ty.holds_enum()),
            _ => false,
        };
        let handles = match &ty {
            Ty::Reg(_) | Ty::Wire(_) | Ty::Input(_) | Ty::Mem(..) | Ty::Instance(_) => true,
            Ty::Array(elem, _) | Ty::List(elem) => elem.holds_handles(),
            Ty::Tuple(parts) => parts.iter().any(|part| part.holds_handles()),
            _ => false,
        };
        let prefix = match &ty {
            Ty::Tuple(parts) => self.prefix_of(parts),
            _ => Vec::new(),
        };
        self.insert_shaped(
            ty,
            (size, depth),
            (strings, funcs, enums, handles),
            meta,
            prefix,
        )
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
        (strings, funcs, enums, handles): (bool, bool, bool, bool),
        meta: Meta,
        prefix: Vec<u64>,
    ) -> TyId {
        let id = TyId {
            index: self.entries.len(),
            size,
            depth,
            flags: bit(strings, STRINGS)
                | bit(funcs, FUNCS)
                | bit(enums, ENUMS)
                | bit(handles, HANDLES),
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
    pub fn shape(ty: &Ty) -> (u64, u64) {
        match ty {
            Ty::Bool
            | Ty::Nat
            | Ty::Int
            | Ty::Unit
            | Ty::Type
            | Ty::String
            | Ty::Struct(_)
            | Ty::Instance(_)
            | Ty::Enum(_) => (1, 1),
            Ty::UInt(w) | Ty::SInt(w) => (1 + int_size(&width_int(*w)), 1),
            Ty::Array(elem, len) => Types::array_shape(*elem, len),
            Ty::Tuple(parts) => Types::tuple_shape(parts),
            Ty::List(elem) | Ty::Reg(elem) | Ty::Wire(elem) | Ty::Input(elem) => {
                (1u64.saturating_add(elem.size), 1 + elem.depth)
            }
            Ty::Mem(elem, depth) => (
                1u64.saturating_add(elem.size)
                    .saturating_add(int_size(depth)),
                1 + elem.depth,
            ),
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
            Ty::Struct(_) | Ty::Enum(_) => 1 + depth,
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
    pub fn reg(&mut self, data: TyId) -> TyId {
        self.mk(Ty::Reg(data))
    }

    #[must_use]
    pub fn wire(&mut self, data: TyId) -> TyId {
        self.mk(Ty::Wire(data))
    }

    #[must_use]
    pub fn input(&mut self, data: TyId) -> TyId {
        self.mk(Ty::Input(data))
    }

    #[must_use]
    pub fn mem(&mut self, word: TyId, depth: Int) -> TyId {
        self.mk(Ty::Mem(word, depth))
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
            Ty::Tuple(_) | Ty::Struct(_) | Ty::Enum(_) => usize::try_from(k)
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

    /// The length in bytes of the serialization of `t`. It computes the length of each part
    /// once, and no text of a type is built.
    #[must_use]
    pub fn text_len(&self, t: TyId) -> u64 {
        self.entry(t);
        Len::default().type_len(self, t)
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
    pub fn text_of<'a>(&'a self, ty: &'a Ty) -> String {
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
            matches!(spec.key, SpecKey::Item(i) if i == item)
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
            key: SpecKey::Item(item),
            name: name.to_owned(),
            args,
            state: SpecState::InProgress,
            origin: if prelude {
                Origin::Prelude
            } else {
                Origin::User
            },
        });
        s
    }

    /// The instance type `s`.
    ///
    /// # Panics
    ///
    /// If `s` is not from this table, which is a bug of the caller.
    #[must_use]
    pub fn inst(&self, s: InstId) -> &InstTy {
        let Some(inst) = self.insts.get(s.0) else {
            panic!("the instance type {} is not in this table of types", s.0);
        };
        inst
    }

    /// The recursive size and the depth of an instance type with the converted arguments
    /// `args`, before the type exists: 1 plus the sizes of the arguments, and 1 plus the deepest
    /// argument.
    #[must_use]
    pub fn inst_shape(args: &[Value]) -> (u64, u64) {
        (
            args.iter()
                .fold(1u64, |sum, arg| sum.saturating_add(arg.size())),
            1 + args.iter().map(Value::depth).max().unwrap_or(0),
        )
    }

    /// The instance type of the module item `item` named `name` with the converted arguments
    /// `args`. The fingerprint narrows the search, and the arguments decide. The hash and the
    /// comparison read each argument in full, and the size of the type reads them again, so the
    /// caller pays their sizes. A new type has the size 1 plus the sizes of its arguments, as a
    /// struct type does, and the depth 1 plus the deepest argument.
    pub fn instance(&mut self, item: usize, name: &str, args: Vec<Value>) -> TyId {
        let shape = Types::inst_shape(&args);
        self.instance_shaped(item, name, args, shape)
    }

    /// `instance` for a caller that has the shape of the arguments (`inst_shape`) already.
    pub fn instance_shaped(
        &mut self,
        item: usize,
        name: &str,
        args: Vec<Value>,
        (size, depth): (u64, u64),
    ) -> TyId {
        #[cfg(test)]
        self.tick(1 + args.iter().map(read_work).sum::<u64>());
        let print = fingerprint(item, &args);
        let found = self.inst_index.get(&print).and_then(|bucket| {
            bucket.iter().copied().find(|(i, _)| {
                let inst = self.inst(*i);
                inst.item == item && inst.args == args
            })
        });
        if let Some((_, ty)) = found {
            return ty;
        }
        let i = InstId(self.insts.len());
        self.insts.push(InstTy {
            item,
            name: name.to_owned(),
            args,
        });
        let ty = self.insert_shaped(
            Ty::Instance(i),
            (size, depth),
            (false, false, false, true),
            Meta::new(0, 0, 0, false),
            Vec::new(),
        );
        self.inst_index.entry(print).or_default().push((i, ty));
        ty
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
        self.seal_spec(s, size, fields, meta, depth)
    }

    /// Completes the specialization `s` with the recursive size `size` of its struct type, its
    /// field types, and its metadata, and gives its struct type.
    fn seal_spec(
        &mut self,
        s: SpecId,
        size: u64,
        fields: Vec<TyId>,
        meta: Meta,
        depth: u64,
    ) -> TyId {
        let strings = fields.iter().any(|field| field.holds_string());
        // The function flag of a struct reads the field types, not the static arguments.
        let funcs = fields.iter().any(|field| field.holds_fn());
        let enums = fields.iter().any(|field| field.holds_enum());
        let handles = fields.iter().any(|field| field.holds_handles());
        let prefix = self.prefix_of(&fields);
        let ty = self.insert_shaped(
            Ty::Struct(s),
            (size, depth),
            (strings, funcs, enums, handles),
            meta,
            prefix,
        );
        if let Some(spec) = self.specs.get_mut(s.0) {
            spec.state = SpecState::Done { ty, fields };
        }
        ty
    }

    /// The depth of a generated record type with the field types `types`: 1 more than its
    /// deepest field type. It has no static argument.
    #[must_use]
    pub fn generated_depth(types: &[TyId]) -> u64 {
        1 + types.iter().map(|t| t.depth).max().unwrap_or(0)
    }

    /// The generated record type with the field symbols `order` and the field types `types`, if
    /// the table holds it. The fingerprint narrows the search, and the field lists decide. The
    /// caller charged the size of the type, which pays for the hash and the compare.
    #[must_use]
    pub fn find_generated(&self, order: &[Sym], types: &[TyId]) -> Option<TyId> {
        #[cfg(test)]
        self.tick(1 + order.len() as u64);
        let bucket = self.gen_index.get(&gen_fingerprint(order, types))?;
        let found = bucket.iter().copied().find(|s| {
            let spec = self.spec(*s);
            let SpecKey::Generated(g) = &spec.key else {
                return false;
            };
            g.order.len() == order.len()
                && g.order
                    .iter()
                    .zip(order)
                    .zip(spec.field_types().iter().zip(types))
                    .all(|((a, b), (x, y))| {
                        #[cfg(test)]
                        crate::counters::add(crate::counters::Count::Matched, 1);
                        a == b && x == y
                    })
        })?;
        self.spec_ty(found)
    }

    /// The generated record type with the fields `fields`, the field types `types`, the metadata
    /// `meta`, and the depth `depth`. The caller found no entry for the field list
    /// (`find_generated`), checked the limit, and paid the charges. The size of the type is 1
    /// plus 1 and the length of each name plus the size of each field type (Lean `Ty.size`).
    pub fn make_generated(
        &mut self,
        fields: Generated,
        types: Vec<TyId>,
        meta: Meta,
        depth: u64,
    ) -> TyId {
        #[cfg(test)]
        {
            self.tick(1 + types.len() as u64);
            crate::counters::add(crate::counters::Count::Generated, 1);
        }
        // A name is an identifier after the name rule, so its length in bytes is its length in
        // characters.
        let size = fields
            .names
            .iter()
            .zip(&types)
            .fold(1u64, |sum, (name, t)| {
                sum.saturating_add(1 + name.len() as u64)
                    .saturating_add(t.size)
            });
        let print = gen_fingerprint(&fields.order, &types);
        let s = SpecId(self.specs.len());
        self.gen_index.entry(print).or_default().push(s);
        self.specs.push(Spec {
            key: SpecKey::Generated(fields),
            name: String::new(),
            args: Vec::new(),
            state: SpecState::InProgress,
            origin: Origin::Generated,
        });
        self.seal_spec(s, size, types, meta, depth)
    }

    /// The named parts of the type `t`, in packing order: the field types of a struct type,
    /// from its done entry. An enum type has the parts `tag` of type `UInt[W]` and `payload` of
    /// type `UInt[P]`, without `payload` when `P` is 0. Each walk over the parts of a type with
    /// named parts reads them here and nowhere else. A type without named parts and an entry
    /// that is not done give `None`.
    #[must_use]
    pub fn parts(&self, t: TyId) -> Option<Parts<'_>> {
        match self.get(t) {
            Ty::Struct(s) => {
                let spec = self.spec(*s);
                match &spec.state {
                    SpecState::Done { fields, .. } => Some(Parts {
                        names: match &spec.key {
                            SpecKey::Item(item) => PartNames::Struct(*item),
                            SpecKey::Generated(g) => PartNames::Generated(g),
                        },
                        types: fields,
                    }),
                    SpecState::InProgress => None,
                }
            }
            Ty::Enum(_) => Some(Parts {
                names: PartNames::Enum,
                types: &self.done_enum(t)?.parts,
            }),
            _ => None,
        }
    }

    /// The done entry of the enum type `t`.
    fn done_enum(&self, t: TyId) -> Option<&DoneEnum> {
        let Ty::Enum(e) = self.get(t) else {
            return None;
        };
        match &self.enums.get(&e.0)?.state {
            EnumState::Done(done) => Some(done),
            EnumState::InProgress => None,
        }
    }

    /// The tag width and the payload width of the enum type `t`.
    #[must_use]
    pub fn widths(&self, t: TyId) -> Option<Widths> {
        let done = self.done_enum(t)?;
        Some(Widths {
            tag: done.tag_width,
            payload: done.payload_width,
        })
    }

    /// The variants of the enum type `t`, in declaration order.
    #[must_use]
    pub fn variants(&self, t: TyId) -> Option<&[Variant]> {
        Some(&self.done_enum(t)?.variants)
    }

    /// The index of the variant of the enum type `t` with the tag value `tag`.
    #[must_use]
    pub fn variant_of_tag(&self, t: TyId, tag: &Int) -> Option<usize> {
        self.done_enum(t)?.tags.get(tag).copied()
    }

    /// The name of the enum type `t`.
    #[must_use]
    pub fn enum_name(&self, e: EnumId) -> &str {
        self.enums.get(&e.0).map_or("", |entry| entry.name.as_str())
    }

    /// Where the enum item `item` stands in the table of enums.
    #[must_use]
    pub fn enum_status(&self, item: usize) -> EnumStatus {
        match self.enums.get(&item).map(|entry| &entry.state) {
            None => EnumStatus::Fresh,
            Some(EnumState::InProgress) => EnumStatus::InProgress,
            Some(EnumState::Done(done)) => EnumStatus::Done(done.ty),
        }
    }

    /// Starts the checks of the enum item `item` named `name`.
    pub fn begin_enum(&mut self, item: usize, name: &str) {
        self.enums.insert(
            item,
            EnumEntry {
                name: name.to_owned(),
                state: EnumState::InProgress,
            },
        );
    }

    /// Completes the enum item `item` with its widths, its variants, their tag map, and its
    /// metadata `meta`, and gives its enum type. The caller paid the charge. The type has the size 1 and the
    /// depth of its metadata.
    pub fn finish_enum(
        &mut self,
        item: usize,
        (tag_width, payload_width): (u32, u32),
        variants: Vec<Variant>,
        tags: BTreeMap<Int, usize>,
        meta: Meta,
        depth: u64,
    ) -> TyId {
        let mut parts = vec![self.mk(Ty::UInt(tag_width))];
        if payload_width > 0 {
            parts.push(self.mk(Ty::UInt(payload_width)));
        }
        let prefix = self.prefix_of(&parts);
        let ty = self.insert_shaped(
            Ty::Enum(EnumId(item)),
            (1, depth),
            (false, false, true, false),
            meta,
            prefix,
        );
        if let Some(entry) = self.enums.get_mut(&item) {
            entry.state = EnumState::Done(DoneEnum {
                ty,
                tag_width,
                payload_width,
                parts,
                variants,
                tags,
            });
        }
        ty
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
            #[cfg(test)]
            if matches!(step, Step::Visit(_)) {
                crate::counters::add(crate::counters::Count::TypeNodes, 1);
            }
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
                        let fields = self.parts(t)?.types;
                        work.push(Step::Record(t, fields.len()));
                        work.extend(fields.iter().rev().map(|f| Step::Visit(*f)));
                    }
                    Ty::Enum(_) => {
                        let widths = self.widths(t)?;
                        let tag = crate::int::finite(widths.tag, 0)?;
                        let payload = match widths.payload {
                            0 => None,
                            p => Some(crate::int::finite(p, 0)?),
                        };
                        done.push(Value::Enum(t, tag, payload));
                    }
                    Ty::Nat
                    | Ty::Int
                    | Ty::Type
                    | Ty::String
                    | Ty::List(_)
                    | Ty::Fn(..)
                    | Ty::Reg(_)
                    | Ty::Wire(_)
                    | Ty::Input(_)
                    | Ty::Mem(..)
                    | Ty::Instance(_) => {
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

    /// `Reg[T]`, `Wire[T]`, `Input[T]`, `Mem[T, N]`, or `Instance[M, args]`.
    #[must_use]
    pub fn is_handle(&self) -> bool {
        matches!(
            self,
            Ty::Reg(_) | Ty::Wire(_) | Ty::Input(_) | Ty::Mem(..) | Ty::Instance(_)
        )
    }
}
