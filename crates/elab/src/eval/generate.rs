// SPDX-License-Identifier: Apache-2.0
//! The builtin `@Struct(fs)` of Lean `Source.Eval.Reflect` (`structArg`, `genFields`, and
//! `generated`) and `Eval.eval` (design sections 6.2 and 9.3). The argument evaluates under the
//! guard `Arg` and its copy charges. The kind check follows, then each field in order, the
//! limit of the new type, the size of its term, its metadata sums, and the look-up in the table
//! of generated record types. A hit charges the same as a miss.
//!
//! The walk reads each name after its own charge, and the member map orders the symbols, so a
//! second field name costs `O(log F)` compares. It never goes into a field type: it reads the
//! stored numbers of its id.

use super::name::name_rule;
use super::place::chain;
use super::types::at_use;
use super::{ArgRec, Evaluator, GuardKind, Out, Res, at, fail, need};
use crate::Code;
use crate::hw::{Part, Seen, Val};
use crate::int::Int;
use crate::limit;
use crate::ops::str_text;
use crate::types::{Generated, Member, Origin, Ty, TyId, Types};
use crate::value::Value;
use parse::ast::{Builtin, Expr, Pos};
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

/// The prelude struct that holds one field of the argument.
const FIELD_INFO: &str = "FieldInfo";

/// Whether the struct type `t` is the prelude `FieldInfo`.
fn is_prelude_field_info(tys: &Types, t: TyId) -> bool {
    match tys.get(t) {
        Ty::Struct(s) => {
            let spec = tys.spec(*s);
            spec.origin() == Origin::Prelude && spec.name() == FIELD_INFO
        }
        _ => false,
    }
}

/// Whether the type `t`, or the element type of an array or a list type `t`, is a user struct
/// `FieldInfo`. It hides the prelude one.
fn holds_user_field_info(tys: &Types, t: TyId) -> bool {
    let user = |u: TyId| match tys.get(u) {
        Ty::Struct(s) => {
            let spec = tys.spec(*s);
            spec.origin() == Origin::User && spec.name() == FIELD_INFO
        }
        _ => false,
    };
    match tys.get(t) {
        Ty::Array(e, _) | Ty::List(e) => user(*e),
        _ => user(t),
    }
}

/// The name and the type of each record of the argument, if it is an array or a list of the
/// prelude `FieldInfo` (Lean `structArg`). It checks every record before any charge, as Lean
/// does, and reads no part of a record other than its two leaves.
fn field_list<'v>(tys: &Types, seen: Seen<'v>) -> Option<Vec<(&'v str, TyId)>> {
    match seen {
        Seen::Static(Value::Array(t, xs) | Value::List(t, xs))
            if is_prelude_field_info(tys, *t) =>
        {
            xs.iter()
                .map(|x| match x {
                    Value::Record(_, parts) => match parts.as_slice() {
                        [Value::Str(name), Value::Type(t)] => Some((name.as_str(), *t)),
                        _ => None,
                    },
                    _ => None,
                })
                .collect()
        }
        _ => None,
    }
}

impl Evaluator<'_> {
    /// `@Struct(arg)` at `pos`, after its node charged (section 6.2, **`@Struct` order**,
    /// steps 2 to 9).
    pub(super) fn struct_builtin(&mut self, pos: Pos, arg: &Expr) -> Res<Out> {
        let rec = if chain(arg).is_some() {
            ArgRec::Place
        } else {
            ArgRec::Node
        };
        let out = self.guarded(GuardKind::Arg(Builtin::Struct), |ev| {
            ev.with_arg(rec, |ev| {
                let o = ev.eval(arg)?;
                need(arg, o)
            })
        })?;
        self.charge(pos, self.size(&out))?;
        let out = self.empty_fields(pos, out)?;
        let t = self.generated(pos, arg.pos(), &out)?;
        Ok(Out::Made(Val::Static(Value::Type(t))))
    }

    /// A `[]` that waits for its type takes its typed use at `[FieldInfo; 0]`. This is a use of
    /// the prelude struct `FieldInfo`, and its errors are at the `@` (step 4).
    fn empty_fields(&mut self, pos: Pos, out: Out) -> Res<Out> {
        if !matches!(self.store.seen(&out), Seen::Pending(_, Part::Empty(_))) {
            return Ok(out);
        }
        let typed = self
            .spec(pos, self.file.field_info_struct(), &[])
            .and_then(|field| {
                let t = self.tys.array(field, Int::from_u64(0));
                self.settle(pos, t, out)
            });
        at_use(pos, typed)
    }

    /// The `S010` of the kind check at the argument `at_arg` (step 4). A user struct
    /// `FieldInfo` has its own text. Each other value is "Argument of `@Struct`".
    fn struct_arg_error<T>(&self, at_arg: Pos, out: &Out) -> Res<T> {
        let seen = self.store.seen(out);
        let user = match seen {
            Seen::Static(Value::Array(t, _) | Value::List(t, _)) => {
                holds_user_field_info(&self.tys, *t)
            }
            Seen::Static(Value::Record(t, _)) => holds_user_field_info(&self.tys, *t),
            Seen::Agg(a) => a
                .stored_ty()
                .is_some_and(|t| holds_user_field_info(&self.tys, t)),
            _ => false,
        };
        let about = self.about(seen);
        if user {
            return fail(
                Code::S010,
                at_arg,
                format!(
                    "`@Struct` takes the prelude `FieldInfo`, not {about}; a user struct \
                     `FieldInfo` hides the prelude one, so rename it, or take the fields from \
                     `@typeInfo(T).fields`"
                ),
            );
        }
        fail(
            Code::S010,
            at_arg,
            format!(
                "`@Struct` takes a `List[FieldInfo]` or a `[FieldInfo; N]`, not {about}; build \
                 each field with the prelude `FieldInfo(name, ty)`"
            ),
        )
    }

    /// The generated record type of the argument `out` at the `@` `pos` (steps 4 to 9). Each name
    /// charges its size as a string, which counts characters, before the name rule. The symbol
    /// goes into the member map, and a symbol that the map holds is "Second field name". Then
    /// the metadata gets its size limit, the term charges its size, and the sums charge. The
    /// look-up comes last.
    fn generated(&mut self, pos: Pos, at_arg: Pos, out: &Out) -> Res<TyId> {
        let seen = self.store.seen(out);
        let Some(fields) = field_list(&self.tys, seen) else {
            return self.struct_arg_error(at_arg, out);
        };
        let mut members = BTreeMap::new();
        let mut order = Vec::with_capacity(fields.len());
        let mut types = Vec::with_capacity(fields.len());
        let mut names = Vec::with_capacity(fields.len());
        let mut term = 1u128;
        for (k, (name, t)) in fields.into_iter().enumerate() {
            let chars = name.chars().count() as u64;
            #[cfg(test)]
            crate::counters::add(crate::counters::Count::Scanned, chars);
            let cost = 1 + u128::from(chars);
            self.fuel.pay(cost).map_err(at(pos))?;
            term += cost;
            name_rule(pos, name, "field")?;
            let y = self.syms.symbol_of(name);
            match members.entry(Member(y)) {
                Entry::Occupied(first) => {
                    return fail(
                        Code::S022,
                        pos,
                        format!(
                            "the field `{}` occurs at the indices {} and {k} of `@Struct`; give \
                             each field its own name",
                            str_text(name),
                            first.get()
                        ),
                    );
                }
                Entry::Vacant(slot) => {
                    slot.insert(k);
                }
            }
            order.push(y);
            names.push(name.to_owned());
            types.push(t);
        }
        limit::metadata(limit::sum_bits(types.iter().map(|t| self.tys.meta(*t))))
            .map_err(at(pos))?;
        let term = types
            .iter()
            .fold(term, |sum, t| sum.saturating_add(u128::from(t.size())));
        self.charge(pos, term)?;
        let depth = Types::generated_depth(&types);
        let meta = self.sums(pos, &types, depth)?;
        if let Some(t) = self.tys.find_generated(&order, &types) {
            return Ok(t);
        }
        let fields = Generated::new(names, order, members);
        Ok(self.tys.make_generated(fields, types, meta, depth))
    }
}
