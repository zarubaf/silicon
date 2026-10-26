// SPDX-License-Identifier: Apache-2.0
//! Generated record types: `type D0 = @Struct(...);` (front-end spec 9.3,
//! ADR 0032).
//!
//! The builder draws the fields of each type, so it knows which lists are
//! equal: the identity of a type is the `id` of its draw, and two aliases
//! with one id are one type. The builder has no function that decides
//! whether two lists are equal. An alias is a struct for the evaluator, so
//! the constructor, the zero, `data_bits`, and the field reads of a
//! generated record use the evaluator of declared structs.
//!
//! The list of fields has the forms that the spec names: a literal, `[]`, a
//! `comptime fn` that builds it with `list` and `push`, and the fields of a
//! struct. A type can come again from the fields of an earlier one (the same
//! type), or with two fields swapped (another type). A declared struct stays
//! nominal. Every draw comes from the query tape, and a program with no
//! query has no alias.

use super::stat::{Reach, int};
use super::{Builder, Built, Ctx, Names};
use crate::eval::{Value, record_ty};
use crate::program::{
    FieldTy, Item, QExpr, Query, RecTy, SExpr, STy, Stmt, StructDef, field_info, list_text,
};
use num_bigint::BigInt;

/// The most generated types of a program, and the most fields of one.
const GENERATED: u32 = 2;
const FIELDS: u32 = 4;
/// A field name of this many characters is valid, and a message cuts it
/// (#386).
const LONG_NAME: usize = 70;

/// A generated record type.
#[derive(Clone, Debug)]
pub(super) struct Gen {
    pub(super) def: StructDef,
    pub(super) rec: RecTy,
    /// The identity: types with one id are one type.
    pub(super) id: usize,
    /// The struct that the list came from, with its arguments: one list for
    /// each spelling.
    from: Option<String>,
    form: QExpr,
    helper: Option<String>,
}

impl Gen {
    /// Whether the type is hardware data, so that `data_bits` and `T()` are
    /// valid.
    pub(super) fn data(&self) -> bool {
        self.rec.zeroable() && !self.rec.fields.is_empty()
    }
}

fn struct_of(form: QExpr) -> QExpr {
    QExpr::Builtin("Struct".to_owned(), vec![form])
}

fn fields_of(name: &str) -> QExpr {
    let info = QExpr::Builtin("typeInfo".to_owned(), vec![QExpr::Text(name.to_owned())]);
    QExpr::Read(Box::new(info), ".fields".to_owned())
}

impl Builder {
    pub(super) fn alias_items(&self) -> impl Iterator<Item = Item> + '_ {
        self.gens.iter().map(|g| Item::Alias {
            def: g.def.clone(),
            id: g.id,
            form: g.form.clone(),
            helper: g.helper.clone(),
        })
    }

    /// The types `G<k>`, after the declared structs and before the consts.
    pub(super) fn generated(&mut self) -> Built {
        if !self.query_on {
            return Ok(());
        }
        self.on_query(|b| {
            for k in 0..b.tape.below(GENERATED + 1) {
                let g = b.generated_type(k as usize)?;
                b.query_bytes +=
                    crate::program::qexpr(&g.form).len() + g.helper.as_ref().map_or(0, String::len);
                b.gens.push(g);
                b.refresh()?;
                // The record type needs the alias in the scope.
                let rec = record_ty(&format!("D{k}"), &[], &b.scope)?;
                if let Some(g) = b.gens.last_mut() {
                    g.rec = rec;
                }
            }
            Ok(())
        })
    }

    /// The fields of a new type: hardware data, or values.
    fn gen_fields(&mut self) -> Vec<(String, FieldTy)> {
        let hardware = self.tape.flag();
        let count = self.tape.between(2, FIELDS);
        (0..count)
            .map(|i| {
                let name = if self.tape.below(16) == 0 {
                    format!("m{i}{}", "a".repeat(LONG_NAME - 2))
                } else {
                    format!("m{i}")
                };
                (name, self.gen_field_ty(hardware))
            })
            .collect()
    }

    fn gen_field_ty(&mut self, hardware: bool) -> FieldTy {
        if hardware {
            let w = int(i64::from(self.tape.between(1, 12)));
            return match self.tape.below(4) {
                0 => FieldTy::Static(STy::Bool),
                1 | 2 => FieldTy::UInt(w),
                _ => FieldTy::SInt(w),
            };
        }
        let earlier: Vec<&Gen> = self.gens.iter().collect();
        match self.tape.below(8) {
            0 => FieldTy::Static(STy::Bool),
            1 => {
                let n = self.tape.between(1, 3);
                let leaf = if self.tape.flag() {
                    STy::Int
                } else {
                    STy::Bool
                };
                FieldTy::Static(STy::Array(Box::new(leaf), n))
            }
            2 if !earlier.is_empty() => {
                let g = earlier[self.tape.index(earlier.len())];
                FieldTy::Static(STy::Record(Box::new(g.rec.clone())))
            }
            3 if !self.enums.is_empty() => {
                let def = self.enums[self.tape.index(self.enums.len())].clone();
                FieldTy::Static(STy::Enum(Box::new(def)))
            }
            _ => FieldTy::Static(STy::Int),
        }
    }

    /// The identity of a list of fields: the id of an earlier type with an
    /// equal list, else a new one. Equal lists make one type in the language.
    fn id_of(&self, fields: &[(String, FieldTy)], fresh: usize) -> usize {
        self.gens
            .iter()
            .find(|g| g.def.fields == fields)
            .map_or(fresh, |g| g.id)
    }

    /// The type `G<k>`: a list of fields, a spelling, and an identity.
    fn generated_type(&mut self, k: usize) -> Built<Gen> {
        let name = format!("D{k}");
        let fresh = self.gens.iter().map(|g| g.id + 1).max().unwrap_or(0);
        let earlier = self.gens.get(self.tape.index(self.gens.len())).cloned();
        let draw = self.tape.below(12);
        // The fields of a declared struct can have a tuple type, which has no
        // spelling as a type expression: only the round trip names them.
        let draw = match &earlier {
            Some(g) if !g.def.fields.iter().all(|(_, t)| spellable(t)) && matches!(draw, 1..=3) => {
                0
            }
            _ => draw,
        };
        let (fields, id, from, form, helper) = match (draw, earlier) {
            // The same list again: the fields of an earlier type.
            (0 | 8 | 10, Some(g)) => (
                g.def.fields.clone(),
                g.id,
                g.from.clone(),
                struct_of(fields_of(&g.def.name)),
                None,
            ),
            // The same list, spelled out again.
            (1, Some(g)) => {
                let form = struct_of(QExpr::Text(list_text(&g.def.fields)));
                (g.def.fields.clone(), g.id, g.from.clone(), form, None)
            }
            // The same list, built with `list` and `push`.
            (2, Some(g)) => {
                let (call, helper) = push_helper(k, &g.def.fields);
                (
                    g.def.fields.clone(),
                    g.id,
                    g.from.clone(),
                    struct_of(QExpr::Text(call)),
                    Some(helper),
                )
            }
            // Two fields swapped: another type.
            (3, Some(g)) if g.def.fields.len() >= 2 => {
                let mut fields = g.def.fields.clone();
                fields.swap(0, 1);
                let form = struct_of(QExpr::Text(list_text(&fields)));
                let id = self.id_of(&fields, fresh);
                (fields, id, None, form, None)
            }
            // The fields of a declared struct, which stays nominal.
            (4, _) if !self.structs.is_empty() => {
                let def = self.structs[self.tape.index(self.structs.len())].clone();
                let args: Vec<Value> = (0..def.params.len())
                    .map(|_| Value::Int(BigInt::from(self.tape.between(1, 12))))
                    .collect();
                let rt = record_ty(&def.name, &args, &self.scope)?;
                let text = STy::Record(Box::new(rt.clone())).text();
                let fields: Vec<(String, FieldTy)> = rt
                    .fields
                    .iter()
                    .map(|(f, t)| (f.clone(), field_ty_of(t)))
                    .collect();
                let id = self
                    .gens
                    .iter()
                    .find(|g| g.from.as_deref() == Some(text.as_str()))
                    .map_or_else(|| self.id_of(&fields, fresh), |g| g.id);
                let form = struct_of(fields_of(&text));
                (fields, id, Some(text), form, None)
            }
            // No field.
            (5 | 9, _) => {
                let form = struct_of(QExpr::Text("[]".to_owned()));
                let id = self.id_of(&[], fresh);
                (Vec::new(), id, None, form, None)
            }
            // A list that a function builds.
            (6 | 7, _) => {
                let fields = self.gen_fields();
                let (call, helper) = push_helper(k, &fields);
                let id = self.id_of(&fields, fresh);
                (fields, id, None, struct_of(QExpr::Text(call)), Some(helper))
            }
            _ => {
                let fields = self.gen_fields();
                let form = struct_of(QExpr::Text(list_text(&fields)));
                let id = self.id_of(&fields, fresh);
                (fields, id, None, form, None)
            }
        };
        let def = StructDef {
            name: name.clone(),
            params: Vec::new(),
            fields,
        };
        Ok(Gen {
            rec: RecTy {
                name,
                args: Vec::new(),
                fields: Vec::new(),
            },
            def,
            id,
            from,
            form,
            helper,
        })
    }
}

/// Whether the type of a field has a spelling as a type expression: a tuple
/// type does not, because `(Int, Bool)` is a tuple of two types.
fn spellable(t: &FieldTy) -> bool {
    fn static_type(t: &STy) -> bool {
        match t {
            STy::Tuple(_) => false,
            STy::Array(t, _) | STy::List(t) => static_type(t),
            _ => true,
        }
    }
    match t {
        FieldTy::Static(t) => static_type(t),
        _ => true,
    }
}

/// The field type of a static type.
fn field_ty_of(t: &STy) -> FieldTy {
    match t {
        STy::UInt(w) => FieldTy::UInt(int(i64::from(*w))),
        STy::SInt(w) => FieldTy::SInt(int(i64::from(*w))),
        other => FieldTy::Static(other.clone()),
    }
}

/// The call `L<k>()` and the `comptime fn` that builds the list of fields
/// with `list` and `push`.
fn push_helper(k: usize, fields: &[(String, FieldTy)]) -> (String, String) {
    let name = format!("L{k}");
    let mut lines = vec![
        format!("comptime fn {name}() -> List[FieldInfo] {{"),
        "    let mut fs = list(FieldInfo);".to_owned(),
    ];
    lines.extend(
        fields
            .iter()
            .map(|f| format!("    push(fs, {});", field_info(f))),
    );
    lines.push("    return fs;".to_owned());
    lines.push("}".to_owned());
    (format!("{name}()"), lines.join("\n") + "\n")
}

/// `e`, a constructor or a zero of a record type, with the head `name`.
fn named(e: SExpr, name: &str) -> SExpr {
    match e {
        SExpr::Record(_, targs, fields) => SExpr::Record(name.to_owned(), targs, fields),
        SExpr::Zero(_, targs) => SExpr::Zero(name.to_owned(), targs),
        other => other,
    }
}

impl Builder {
    /// A group that uses a generated type, if the program has one: a value
    /// and a read of its fields, a typed use through an equal alias, a test
    /// of the identity, or the zero and `data_bits` of a type of hardware
    /// data. Gives whether it made a group.
    pub(super) fn struct_group(
        &mut self,
        ctx: &Ctx,
        names: &mut Names,
        out: &mut Vec<Stmt>,
    ) -> bool {
        let Some(g) = self.gens.get(self.tape.index(self.gens.len())).cloned() else {
            return false;
        };
        let r = self.reach(ctx);
        let made = match self.tape.below(4) {
            0 => self.struct_value(ctx, &g, &g, r, names, out),
            1 => {
                let same: Vec<Gen> = self
                    .gens
                    .iter()
                    .filter(|o| o.id == g.id && o.def.name != g.def.name)
                    .cloned()
                    .collect();
                match same.get(self.tape.index(same.len())) {
                    Some(other) => self.struct_value(ctx, &g, other, r, names, out),
                    None => false,
                }
            }
            2 => self.struct_identity(ctx, &g, names, out),
            _ => self.struct_bits(ctx, &g, names, out),
        };
        if made {
            note!(self, struct_groups);
            self.query_bytes += 120;
        }
        made
    }

    /// `let s: T = U(...);` and a record of a scalar field of it. `T` and `U`
    /// are one type: the annotation `T` and the constructor of the alias `u`.
    fn struct_value(
        &mut self,
        ctx: &Ctx,
        ty: &Gen,
        u: &Gen,
        r: Reach<'_>,
        names: &mut Names,
        out: &mut Vec<Stmt>,
    ) -> bool {
        let value = named(self.record(&u.rec, super::stat::DEPTH, r), &u.def.name);
        if self.values(&value, &ctx.envs).is_none() {
            return false;
        }
        let name = names.fresh("s");
        let read = ty.rec.fields.iter().find_map(|(f, t)| {
            let field = SExpr::Field(Box::new(SExpr::Name(name.clone())), f.clone());
            match t {
                STy::Int | STy::Bool => Some(field),
                STy::Array(..) => Some(SExpr::Len(Box::new(field))),
                _ => None,
            }
        });
        out.push(Stmt::StaticLet(
            name.clone(),
            STy::Record(Box::new(ty.rec.clone())),
            value,
        ));
        if let Some(read) = read {
            let message = self.next_message();
            out.push(Stmt::Diagnostic(message, read));
        }
        true
    }

    /// `let s: Bool = (A == B);`: two aliases of one identity, the round
    /// trip through `@typeInfo`, or a declared struct, which stays nominal.
    fn struct_identity(
        &mut self,
        ctx: &Ctx,
        g: &Gen,
        names: &mut Names,
        out: &mut Vec<Stmt>,
    ) -> bool {
        let other = self.gens.get(self.tape.index(self.gens.len())).cloned();
        let text = |t: &str| QExpr::Text(t.to_owned());
        let (form, held) = match (self.tape.below(6), other) {
            (0 | 1, Some(o)) => (
                QExpr::Eq(Box::new(text(&g.def.name)), Box::new(text(&o.def.name))),
                g.id == o.id,
            ),
            (2 | 3, _) => (
                QExpr::Eq(
                    Box::new(struct_of(fields_of(&g.def.name))),
                    Box::new(text(&g.def.name)),
                ),
                true,
            ),
            _ => {
                let Some(s) = self.structs.iter().find(|d| d.params.is_empty()).cloned() else {
                    return false;
                };
                (
                    QExpr::Eq(
                        Box::new(struct_of(fields_of(&s.name))),
                        Box::new(text(&s.name)),
                    ),
                    false,
                )
            }
        };
        if self.values(&SExpr::Bool(held), &ctx.envs).is_none() {
            return false;
        }
        let name = names.fresh("s");
        let query = SExpr::Query(Box::new(Query {
            form,
            value: SExpr::Bool(held),
        }));
        out.push(Stmt::StaticLet(name.clone(), STy::Bool, query));
        let message = self.next_message();
        out.push(Stmt::Diagnostic(message, SExpr::Name(name)));
        true
    }

    /// `let s: T = T();` and `data_bits(T)`, if `T` is hardware data.
    fn struct_bits(&mut self, ctx: &Ctx, g: &Gen, names: &mut Names, out: &mut Vec<Stmt>) -> bool {
        if !g.data() {
            return false;
        }
        let zero = SExpr::Zero(g.def.name.clone(), Vec::new());
        if self.values(&zero, &ctx.envs).is_none() {
            return false;
        }
        let name = names.fresh("s");
        out.push(Stmt::StaticLet(
            name,
            STy::Record(Box::new(g.rec.clone())),
            zero,
        ));
        let bits = SExpr::DataBits(g.def.name.clone(), Vec::new());
        let message = self.next_message();
        out.push(Stmt::Diagnostic(message, bits));
        true
    }
}
