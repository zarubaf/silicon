// SPDX-License-Identifier: Apache-2.0
//! One mutation of a typed program (front-end spec 11.4, mode 3).
//!
//! The mutation edits a copy of the items and prints it with the one
//! printer, so each mutant parses. The original program elaborates, and
//! each pass of the front ends stops the run (spec 6.2). A mutation that
//! adds one error of an early pass therefore fixes the first code, and
//! `Mutant::expect` predicts it:
//!
//! - A copy of a declaration is `S002` (pass 2): all local kinds and the
//!   items share one namespace in a scope, and the copy is in that scope.
//! - A name reference `q0` is `S003` (pass 3): `q` is no prefix of the
//!   builder, and the resolver checks each name, also in dead code.
//! - A deleted declaration that its item still mentions (an item: that
//!   any item still mentions) is `S003`. Generated names are unique in an
//!   item, so no other declaration catches the use.
//! - One argument more or less in a call of a named function is `S007`
//!   (pass 4), on all code. In a call through a function value, pass 5
//!   finds it when the call runs: `S007` where the site always runs (the
//!   top frame of a module, outside a lazy operand or branch), else no
//!   prediction. A `const` runs at its first use, so it predicts nothing.
//! - A deleted `:=` in the top frame of a module body is `S018` (pass 5):
//!   each module of a program has a context, so its top frame runs, and
//!   nothing else fails.
//!
//! - A deleted call of a helper with a handle formal in the top frame of a
//!   module body leaves the resources of its actuals unbound: `S018`. A
//!   deleted `write_port` there leaves its memory without a write: `S018`.
//! - A binding that is copied right after itself in the top frame of a
//!   module body (`DuplicateBind`) is a second binding of one resource,
//!   or a second `write_port`: `S018` (pass 5), and nothing else fails
//!   before it. A binding is a `:=`, a `write_port`, or a call of a helper
//!   with a handle formal.
//!
//! - A `mut` actual whose root is no longer mutable is `S008` (pass 4) if
//!   a named function, `push`, or `pop` has the root as its `mut` actual.
//!   An assignment to the root gives no prediction, even with such a use.
//!   A `pop` of the receiver in the arguments of a receiver call on a list
//!   is `S008` (pass 4), on all code. In a call through a function value,
//!   pass 5 finds the window when the call runs: `S008` where the site
//!   always runs, else no prediction.
//!
//! - A call of a function that runs a `diagnostic`, or that writes back a
//!   `mut` actual of the module frame, in an arm of a hardware `if` or in
//!   a width is `S016` (pass 5, spec 9.4), where the site always runs. A
//!   hardware `if` evaluates both arms, but its condition must be a port
//!   or a register, or the negation of one: the front ends fold any other
//!   condition that is static by value, and that `if` takes one arm. A
//!   site in a branch, a loop, a lazy operand, or another item than a
//!   module body predicts nothing.
//!
//! - A `match` whose arms no longer cover each value, or that has an arm
//!   after `_` or an arm twice, is `S021` (pass 5, spec 5.6) where the
//!   `match` always runs. The arms cover each value by construction, so
//!   `DeleteArm` is certain for the arm `_` of a match and for any arm of a
//!   match without `_`, and it predicts nothing for another arm. Two
//!   variants with one tag are `S021` at the first use of the enum, which
//!   is certain where the enum is used in the top frame of a module.
//!
//! - Two binders with one name, and an extra or a missing argument of a
//!   constructor or of a variant pattern, are `S002` (pass 2) and `S007`
//!   (pass 4) on all code. A missing binder is one that is `_` or that no
//!   arm reads, because pass 3 sees a missing name first.
//!
//! - A pattern of another kind than its scrutinee (`PatternSwap`), `==` on
//!   enums (`EnumEq`), and a call `E(0)` of an enum type (`EnumCall`) are
//!   `S010`. A static `Int` operand that becomes a `match` on a port with
//!   two unequal static arms is `S011`. They are certain where the site
//!   always runs. A literal that passes the scrutinee type (`PatternFit`,
//!   known for a port with a literal width), a tag of `2^W` (`TagFit`),
//!   and a variant of 65537 payload bits (`PayloadOverflow`) are `S012`.
//!   The two tag kinds are certain where the top frame of a module uses
//!   the enum.
//!
//! - A copy of an indexed declaration `req[k]` is `S019` ("Family key
//!   twice", pass 5) where the copy always runs. A name gone with its last
//!   indexed declaration is `S003` if the item still mentions it, as a
//!   deleted declaration is; another indexed declaration of the name keeps
//!   the family, so that case predicts nothing. `Rename` and the checks of
//!   a mention see `req[k]` and `u.req[k]` as a mention of `req` and `u`.
//! - A family key of `2^32` (`KeyRange`) is `S012` (pass 5). A family key
//!   that is a `Bool` or a finite integer, and an `as` key that is an
//!   integer (`KeyType`), are `S010`. A scalar port with the `as` key of a
//!   family of the module body (`ScalarFamily`) is `S019`, also if the
//!   body declares no entry of that family before the port, because the
//!   table of public names holds each family of the body from the start. An
//!   `as` key with a name that breaks the name rule, and a scalar `PortKey`
//!   with the index 1 (`BadName`), are `S022`. The four kinds are certain
//!   where the site always runs.
//!
//! - A builtin with a name that is none (`BuiltinName`, also a name of 70
//!   characters), with one operand more or less (`BuiltinArity`), and the
//!   operand of `@TypeOf` or `@ports` that is an operator (`QueryOperand`)
//!   are `S001` in all code. A builtin with an index in a type position
//!   (`IndexBuiltinType`) is `S007`, and a port in a key of a query
//!   (`KeyHardware`) is `S005`, in all code. The kinds of pass 5 are certain
//!   where the site always runs: the domain as the operand of `@TypeOf`
//!   (`NoType`), a string index in a query (`StringIndex`), a comparison of
//!   ports as the argument of `@typeInfo` (`QueryHardware`, `S011`), a value
//!   there (`TypeInfoValue`), an own port as the operand of `@ports`
//!   (`PortsValue`), the `TypeInfo` of a type in a type position
//!   (`BuiltinType`), a call with an effect or a mutation in a key of a query
//!   (`KeyEffect` and `KeyMutation`, `S016`), a field more or less in a
//!   constructor of a generated record type (`ConstructorArity`, `S007`), and
//!   its zero when it is no hardware data (`ZeroNonData`, `S010`). A generated
//!   record type is elaborated at its first use, so a change in the argument
//!   of `@Struct`, in a field name, in a field type that is the alias itself,
//!   or a user struct `FieldInfo` (`StructArg`, `FieldName`, `SelfStruct`,
//!   `UserFieldInfo`) predicts nothing.
//!
//! Any other mutation can fail in pass 5 at a point that depends on the
//! values, or pass, so its prediction is `None`.

use super::program::{Item, Program, render_items};
use walk::Walk;

mod uses;
mod walk;

#[cfg(test)]
mod tests;

/// A mutant: its source text, what the mutation did, and the first code
/// that both front ends must report, where the pass order makes it certain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mutant {
    pub text: String,
    pub what: String,
    pub expect: Option<&'static str>,
}

/// The kinds of mutation, in the cyclic order of the fallback.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// A statement of a module or helper body, or an item other than the
    /// top module, goes.
    Delete,
    /// A declaration statement or an item, copied right after itself.
    Duplicate,
    /// A name reference becomes `q0`.
    Rename,
    /// The last argument of an instance or a call goes.
    DropArg,
    /// An instance or a call gets the argument `0` at its end.
    AddArg,
    /// A width `w` becomes `(w + 1)`.
    Widen,
    /// A width becomes `0`.
    ZeroWidth,
    /// A static expression becomes `(1 / 0)`.
    Fault,
    /// The `let mut` root of a `mut` actual becomes `let`.
    Immutable,
    /// An argument of a receiver call on a list becomes `pop` of the list:
    /// the `pop` is in the window of the receiver.
    Window,
    /// The same, in a call through a function value.
    ValueWindow,
    /// A static operand in an arm becomes a call of a function that runs a
    /// `diagnostic`: a graph effect in an arm.
    ArmEffect,
    /// A width becomes a call of that function: a graph effect in a type.
    TypeEffect,
    /// A static operand in an arm becomes a call that takes a `let mut`
    /// static `Int` from before the arm as its `mut` actual: a write-back
    /// in an arm.
    ArmMutation,
    /// The same for a width.
    TypeMutation,
    /// An arm of a `match` goes.
    DeleteArm,
    /// An arm of a `match` is copied right after itself.
    DuplicateArm,
    /// The arm `_` moves before the last arm.
    WildFirst,
    /// A `_` joins the arms of a `match` that covers each value.
    DeadWild,
    /// The tag of a variant becomes the tag of the first variant.
    SameTag,
    /// Two binders of a pattern get one name.
    DupBinder,
    /// An arm gets a pattern of another kind: a literal, `true`, or a
    /// variant for the other kinds.
    PatternSwap,
    /// An enum value becomes `e == e`.
    EnumEq,
    /// The zero `E()` of an enum becomes `E(0)`.
    EnumCall,
    /// A static `Int` operand becomes a `match` on a port with two
    /// unequal static arms.
    ArmStage,
    /// The tag of a variant becomes `2^W`.
    TagFit,
    /// A literal of a pattern passes the scrutinee type.
    PatternFit,
    /// A variant with a payload of 65537 bits joins an enum.
    PayloadOverflow,
    /// A binding statement or a binding call is copied right after itself.
    DuplicateBind,
    /// A key of a family becomes `2^32`.
    KeyRange,
    /// A key of a family becomes a `Bool` or a finite integer, and an `as`
    /// key an integer.
    KeyType,
    /// A scalar port gets the `as` key of a family of the module body.
    ScalarFamily,
    /// An `as` key breaks the name rule, or a scalar `PortKey` gets the
    /// index 1.
    BadName,
    /// The key of an `@field` becomes a value of another type.
    FieldKeyType,
    /// The `String` key of an `@field` names no field and no port.
    NoField,
    /// A `Nat` key of an `@field` becomes `-1` or `99`, and the index of an
    /// entry key becomes `99` or `2^32`.
    FieldRange,
    /// The base of an `@field` becomes a `String`.
    FieldBase,
    /// The base of an `@field` becomes an enum value.
    EnumField,
    /// The key of an `@field` becomes the name of a port.
    KeyNotStatic,
    /// A read of a child through `@field` selects an input of the child.
    ReadInput,
    /// The key of an entry of a family becomes the scalar `PortKey` of the
    /// family.
    FamilyValue,
    /// A scalar `PortKey` gets the index 1.
    ScalarKeyIndex,
    /// A key of a `:=` target calls a function that runs a `diagnostic`.
    TargetKey,
    /// The step before a key that runs a `diagnostic` gets a key out of
    /// range.
    EarlyStep,
    /// The key of an `@field` becomes a hardware value.
    KeyValue,
    /// A key of a `:=` target calls a function that changes a root.
    TargetMutation,
    /// The target of a `:=` becomes an `@field` on a static integer.
    TargetBase,
    /// A child gets a local container and an assignment to its port.
    PortPlace,
    /// A read of a port of a child becomes the read of the child.
    InstanceData,
    /// Two fields of the literal list of an alias of `@Struct` swap.
    FieldSwap,
    /// A constructor of a generated record type that comes from a declared
    /// struct becomes the constructor of that struct.
    NominalStruct,
    /// A builtin gets a name that is no builtin.
    BuiltinName,
    /// A builtin gets one operand more or less.
    BuiltinArity,
    /// The operand of `@TypeOf` or `@ports` becomes an operator.
    QueryOperand,
    /// A builtin in a type position gets an index.
    IndexBuiltinType,
    /// The operand of `@TypeOf` becomes the domain.
    NoType,
    /// The operand of a query indexes a string.
    StringIndex,
    /// The argument of `@typeInfo` becomes a port.
    QueryHardware,
    /// A key of a query becomes a port.
    KeyHardware,
    /// The argument of `@typeInfo` becomes a value.
    TypeInfoValue,
    /// The operand of `@ports` becomes an own port.
    PortsValue,
    /// A type position gets the `TypeInfo` of its type.
    BuiltinType,
    /// A constructor of a generated record type gets a field more or less.
    ConstructorArity,
    /// A key of a query calls a function that runs a `diagnostic`.
    KeyEffect,
    /// A key of a query calls a function that changes a root.
    KeyMutation,
    /// The argument of `@Struct` becomes a value.
    StructArg,
    /// A field name of `@Struct` breaks the name rule, or repeats.
    FieldName,
    /// A user struct `FieldInfo` hides the prelude one.
    UserFieldInfo,
    /// A generated record type has itself as a field type.
    SelfStruct,
    /// A constructor of a generated record type that is no hardware data
    /// loses its fields: the zero of a type that has none.
    ZeroNonData,
}

const KINDS: [Kind; 70] = [
    Kind::Delete,
    Kind::Duplicate,
    Kind::Rename,
    Kind::DropArg,
    Kind::AddArg,
    Kind::Widen,
    Kind::ZeroWidth,
    Kind::Fault,
    Kind::Immutable,
    Kind::Window,
    Kind::ValueWindow,
    Kind::ArmEffect,
    Kind::TypeEffect,
    Kind::ArmMutation,
    Kind::TypeMutation,
    Kind::DeleteArm,
    Kind::DuplicateArm,
    Kind::WildFirst,
    Kind::DeadWild,
    Kind::SameTag,
    Kind::DupBinder,
    Kind::PatternSwap,
    Kind::EnumEq,
    Kind::EnumCall,
    Kind::ArmStage,
    Kind::TagFit,
    Kind::PatternFit,
    Kind::PayloadOverflow,
    Kind::DuplicateBind,
    Kind::KeyRange,
    Kind::KeyType,
    Kind::ScalarFamily,
    Kind::BadName,
    Kind::FieldKeyType,
    Kind::NoField,
    Kind::FieldRange,
    Kind::FieldBase,
    Kind::EnumField,
    Kind::KeyNotStatic,
    Kind::ReadInput,
    Kind::FamilyValue,
    Kind::ScalarKeyIndex,
    Kind::TargetKey,
    Kind::EarlyStep,
    Kind::KeyValue,
    Kind::TargetMutation,
    Kind::TargetBase,
    Kind::PortPlace,
    Kind::InstanceData,
    Kind::FieldSwap,
    Kind::NominalStruct,
    Kind::BuiltinName,
    Kind::BuiltinArity,
    Kind::QueryOperand,
    Kind::IndexBuiltinType,
    Kind::NoType,
    Kind::StringIndex,
    Kind::QueryHardware,
    Kind::KeyHardware,
    Kind::TypeInfoValue,
    Kind::PortsValue,
    Kind::BuiltinType,
    Kind::ConstructorArity,
    Kind::KeyEffect,
    Kind::KeyMutation,
    Kind::StructArg,
    Kind::FieldName,
    Kind::UserFieldInfo,
    Kind::SelfStruct,
    Kind::ZeroNonData,
];

/// The kinds of ports at the end of `KINDS`, and the draws in `PORT_ODDS`
/// that pick one of them.
const PORT_KINDS: usize = 4;
const PORT_ODDS: usize = 8;
/// The kinds before the kinds of ports, and the kinds of `@field` at the end
/// of `KINDS`. One draw in `FIELD_ODDS` of those that do not pick a kind of
/// ports picks a kind of `@field`.
const OLD_KINDS: usize = 29;
const FIELD_KINDS: usize = 11;
const FIELD_ODDS: usize = 6;
/// A program with a site of `EarlyStep` picks that kind in one draw in
/// `EARLY_ODDS`. The site is rare, so the plain share of the kind would
/// leave it nearly untested. The draw reads the digits above all the other
/// splits, so the earlier draws keep their kinds.
const EARLY_ODDS: usize = 4;
const EARLY_SPLIT: usize = PORT_ODDS * FIELD_ODDS * FIELD_KINDS;
/// The kinds of queries at the end of `KINDS`. A draw in `QUERY_ODDS`, read
/// from the digits above those of `EarlyStep`, picks one of them, if the
/// program has a site of one. The other draws keep the kinds that they had
/// before the queries.
const QUERY_KINDS: usize = 19;
const QUERY_ODDS: usize = 4;
const QUERY_SPLIT: usize = EARLY_SPLIT * EARLY_ODDS;
/// The kinds of the gaps of `@field` sit between those of `@field` and those
/// of queries. A draw in `GAP_ODDS`, read from the digits above those of the
/// queries, picks one of them, if the program has a site of one. The other
/// draws keep the kinds that they had before.
const GAP_KINDS: usize = 7;
const GAP_ODDS: usize = 6;
const GAP_SPLIT: usize = QUERY_SPLIT * QUERY_ODDS * QUERY_KINDS;

/// The value `2^w`, or for a signed type the value `-2^(w - 1) - 1`, that
/// no value of the type `w` bits wide has. Three kinds use it: a tag, and a
/// literal of an unsigned and of a signed scrutinee.
fn beyond(signed: bool, width: u32) -> num_bigint::BigInt {
    let one = num_bigint::BigInt::from(1);
    if signed {
        -(one.clone() << width.saturating_sub(1)) - one
    } else {
        one << width
    }
}

/// The number of kinds that come before the kinds of `match` and enums.
const EARLIER: usize = 15;

/// The name of the function that runs a `diagnostic`.
const EFFECT_FN: &str = "e0";

/// The name of the function with a `mut` formal that it never changes.
const KEEP_FN: &str = "p0";

impl Kind {
    /// The function that the mutant adds, with its newline.
    fn function(self) -> String {
        match self {
            Kind::ArmEffect | Kind::TypeEffect | Kind::TargetKey | Kind::KeyEffect => format!(
                "comptime fn {EFFECT_FN}(x: Int) -> Int {{\n    diagnostic(\"{EFFECT_FN}\", x);\n    return x;\n}}\n"
            ),
            Kind::ArmMutation | Kind::TypeMutation | Kind::KeyMutation | Kind::TargetMutation => {
                format!("comptime fn {KEEP_FN}(mut n: Int, x: Int) -> Int {{\n    return x;\n}}\n")
            }
            _ => String::new(),
        }
    }
}

/// The mutant of `program` for the kind `kind % KINDS.len()`, or for the next kind
/// in cyclic order that has a site, at the site `site % count` in the
/// pre-order of the items.
#[must_use]
pub fn mutate(program: &Program, kind: u32, site: u32) -> Mutant {
    // One draw in `PORT_ODDS` picks a kind of ports, the others keep their
    // kinds. A program without a site of ports falls back to the earlier
    // kinds.
    let old_kinds = OLD_KINDS;
    let spare = kind as usize / PORT_ODDS;
    let early = (kind as usize / EARLY_SPLIT) % EARLY_ODDS == EARLY_ODDS - 1
        && sites(Kind::EarlyStep, &program.items, &program.top) > 0;
    // One draw in `QUERY_ODDS` of the digits above those of `EarlyStep` picks
    // a kind of queries, or the next one in cyclic order that has a site.
    let queries = KINDS.len() - QUERY_KINDS;
    let pick = (kind as usize / (QUERY_SPLIT * QUERY_ODDS)) % QUERY_KINDS;
    let query = ((kind as usize / QUERY_SPLIT) % QUERY_ODDS == QUERY_ODDS - 1)
        .then(|| {
            (0..QUERY_KINDS)
                .map(|i| queries + (pick + i) % QUERY_KINDS)
                .find(|&i| {
                    KINDS
                        .get(i)
                        .is_some_and(|&k| sites(k, &program.items, &program.top) > 0)
                })
        })
        .flatten();
    // The kinds of the gaps come after the kinds of `@field`.
    let gaps = OLD_KINDS + PORT_KINDS + FIELD_KINDS;
    let gap_pick = (kind as usize / (GAP_SPLIT * GAP_ODDS)) % GAP_KINDS;
    let gap = ((kind as usize / GAP_SPLIT) % GAP_ODDS == GAP_ODDS - 1)
        .then(|| {
            (0..GAP_KINDS)
                .map(|i| gaps + (gap_pick + i) % GAP_KINDS)
                .find(|&i| {
                    KINDS
                        .get(i)
                        .is_some_and(|&k| sites(k, &program.items, &program.top) > 0)
                })
        })
        .flatten();
    let first = if early {
        OLD_KINDS + PORT_KINDS + FIELD_KINDS - 1
    } else if let Some(query) = query {
        query
    } else if let Some(gap) = gap {
        gap
    } else if kind as usize % PORT_ODDS == PORT_ODDS - 1 {
        old_kinds + spare % PORT_KINDS
    } else if spare % FIELD_ODDS == FIELD_ODDS - 1 {
        old_kinds + PORT_KINDS + (spare / FIELD_ODDS) % FIELD_KINDS
    } else {
        kind as usize % old_kinds
    };
    // A kind without a site falls back to the earlier kinds, as it did
    // before the kinds of `match`, so that a program without a `match`
    // does not give the next kind in the list all the draws of the new ones.
    let old = first % EARLIER;
    let order = std::iter::once(first)
        .chain((0..EARLIER).map(|i| (old + i) % EARLIER))
        .chain(EARLIER..KINDS.len());
    let mutant = order.filter_map(|i| KINDS.get(i)).find_map(|&kind| {
        let count = sites(kind, &program.items, &program.top);
        if count == 0 {
            return None;
        }
        let mut items = program.items.clone();
        let (what, expect) = apply(kind, &mut items, &program.top, site as usize % count)?;
        Some(Mutant {
            text: render_items(&items) + &kind.function(),
            what,
            expect,
        })
    });
    // A built program has the `:=` of a top output, a `Delete` site. The
    // equal text shows the bug to `diff-si`.
    mutant.unwrap_or_else(|| Mutant {
        text: program.text(),
        what: "no mutation site".to_owned(),
        expect: None,
    })
}

/// The number of sites of `kind` in `items`.
fn sites(kind: Kind, items: &[Item], top: &str) -> usize {
    let mut w = Walk::new(kind, top, None);
    w.items(&mut items.to_vec());
    w.seen
}

/// Applies `kind` at the site `site` and gives what it did and the
/// predicted code, or `None` if `site` is not below `sites`.
fn apply(
    kind: Kind,
    items: &mut Vec<Item>,
    top: &str,
    site: usize,
) -> Option<(String, Option<&'static str>)> {
    let mut w = Walk::new(kind, top, Some(site));
    w.items(items);
    let Hit { what, effect } = w.hit?;
    let expect = match effect {
        Effect::Code(c) => c,
        Effect::Gone(name, scope) => {
            let scope = match scope {
                Some(i) => items.get(i..=i).unwrap_or_default(),
                None => items.as_slice(),
            };
            mentions(&name, scope).then_some("S003")
        }
    };
    Some((what, expect))
}

/// Whether a name reference in `items` is `name`: a value, an assignment
/// target, the instance of a field, an instance module, or a callee. The
/// guard `x == 0` of a `comptime fn` is no walked expression, so neither
/// this check nor `Rename` sees it. That costs no prediction: the guard
/// names the first parameter, and no mutation deletes a parameter.
fn mentions(name: &str, items: &[Item]) -> bool {
    let mut w = Walk::new(Kind::Rename, "", None);
    w.items(&mut items.to_vec());
    w.names.iter().any(|n| n == name)
}

/// The effect of a mutation on the first error.
enum Effect {
    Code(Option<&'static str>),
    /// The declaration of a name went: `S003` if the item at the index
    /// (all items if `None`) still mentions it.
    Gone(String, Option<usize>),
}

struct Hit {
    what: String,
    effect: Effect,
}
