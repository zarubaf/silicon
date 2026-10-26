// SPDX-License-Identifier: Apache-2.0
//! The builtin `@ports(h)` of Lean `Source.Eval.Reflect` (`portsArg`, `portsOf`) and `Eval.eval`
//! (design sections 6.2 and 9.3). The operand is a place that the walk of a query reaches
//! (`query_operand`). Its part must be an `Instance` handle. The result is the list of `PortInfo`
//! records of the child, in the order of the schema of its interface.
//!
//! The schema is sorted once, when the instantiation ends (`Iface::of`), so a call sorts nothing.
//! The call charges 1 for each port from the count of the schema. That charge pays for one pass
//! over the stored numbers: the depth of the result gets its check, then its recursive size
//! charges. The pass reads the stored depth and size of each port type and the length of each
//! name, and it never walks a type. A name and a domain are ASCII (the lexer and `S022`), so the
//! length in bytes is the number of characters. Only after the size charge the list exists, so no
//! name is copied before it.

use super::container::bounded;
use super::reflect::{Operand, Part};
use super::{Evaluator, Out, Res, at, fail};
use crate::Code;
use crate::hw::{Handle, Port, Seen, Val};
use crate::int::Int;
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Builtin, Expr, Pos};

/// The fix `{h}` of "`@ports` of a non-instance" for a part that is not a container of instances.
const INSTANCE_HINT: &str =
    "pass the name of an instance, for example `u` of `instance u = M(...);`";

impl Evaluator<'_> {
    /// `@ports(operand)` at `pos`, after its node charged (section 6.2, **`@ports` order**, steps
    /// 2 to 8): the walk of the operand, the kind check, the use of `PortInfo`, the charges, and
    /// the list.
    pub(super) fn ports_builtin(&mut self, pos: Pos, operand: &Expr) -> Res<Out> {
        let part = self.query_operand(Builtin::Ports, pos, operand)?;
        let inst = self.ports_arg(operand.pos(), &part)?;
        let info = self.spec(pos, self.file.port_info_struct(), &[])?;
        Ok(Out::Made(Val::Static(self.ports_value(pos, info, inst)?)))
    }

    /// The done instantiation of the handle that the operand reaches. Another part is `S010` at
    /// the operand `pos`, with no copy charge. It names a part that keeps only its type by that
    /// type, and a value in the form of slice 3b. The check reads the part and its type only.
    fn ports_arg(&self, pos: Pos, operand: &Operand) -> Res<usize> {
        let seen = match operand {
            Operand::Part(Part::Held(r, _)) => self.store.at(r),
            Operand::Part(Part::Handle(h)) => Seen::Handle(h),
            Operand::Part(Part::Entry(t)) => {
                let about = format!("a value of `{}`", self.tys.text(*t));
                return Self::not_instance(pos, &about, INSTANCE_HINT);
            }
            Operand::Part(Part::Type(t)) => {
                return Self::not_instance(pos, &self.query_part_text(*t), INSTANCE_HINT);
            }
            Operand::Out(o) => self.store.seen(o),
        };
        match seen {
            Seen::Handle(Handle::Inst { inst, .. }) => Ok(*inst),
            seen => Self::not_instance(pos, &self.about(seen), self.ports_hint(seen)),
        }
    }

    /// The `S010` "`@ports` of a non-instance" at `pos` for the part `about` with the fix `hint`.
    fn not_instance<T>(pos: Pos, about: &str, hint: &str) -> Res<T> {
        fail(
            Code::S010,
            pos,
            format!("`@ports` takes an instance handle, not {about}; {hint}"),
        )
    }

    /// The fix `{h}` of the part `seen` (Lean `portsHint`). It reads the part and its type, in
    /// constant work. An array or a list of an `Instance` element type selects one instance. A
    /// `Type` value of an `Instance` type has no ports. Each other part gets the general fix. A
    /// container of registers has the handle flag too, so the element type decides.
    fn ports_hint(&self, seen: Seen<'_>) -> &'static str {
        match seen {
            Seen::Agg(a) if a.stored_ty().is_some_and(|t| self.of_instances(t)) => {
                "select one instance, for example `xs[0]`"
            }
            Seen::Static(Value::Type(t)) if matches!(self.tys.get(*t), Ty::Instance(_)) => {
                "a type has no ports; pass the handle of `instance u = M(...);`"
            }
            _ => INSTANCE_HINT,
        }
    }

    /// Whether `t` is an array or a list whose element type is an `Instance`.
    fn of_instances(&self, t: TyId) -> bool {
        match self.tys.get(t) {
            Ty::Array(e, _) | Ty::List(e) => matches!(self.tys.get(*e), Ty::Instance(_)),
            _ => false,
        }
    }

    /// The type `PortKey`: the first field type of `PortInfo`. The first use of `PortInfo`
    /// completed it, and neither struct has a parameter, so no specialization is in progress.
    fn port_key_ty(&self, info: TyId) -> TyId {
        let Some(key) = self.tys.parts(info).and_then(|p| p.types.first().copied()) else {
            panic!("the use of PortInfo completed PortKey");
        };
        key
    }

    /// The `PortInfo` list of the done instantiation `inst` at `pos`, after the use of `PortInfo`
    /// gave `info` (steps 5 to 8). The count charges first. The depth check and the size charge
    /// follow from the stored numbers, before any record exists.
    fn ports_value(&mut self, pos: Pos, info: TyId, inst: usize) -> Res<Value> {
        let key = self.port_key_ty(info);
        let schema = self.elab.schema(inst);
        let texts = &self.syms.texts;
        let name = |q: &Port| texts.get(q.sym).map_or("", String::as_str);
        let domain = self
            .elab
            .interface(inst)
            .and_then(|i| i.domain)
            .and_then(|d| texts.get(d))
            .map_or("", String::as_str);
        self.fuel.pay(schema.len() as u128).map_err(at(pos))?;
        let (mut size, mut types) = (1u128, 0);
        for q in schema {
            // The record, the key record with its name, flag, and number, the type, the direction,
            // and the domain. The number of an entry is a word, so its size is 1.
            let key_size = 1 + (1 + name(q).len() as u128) + 1 + 1;
            size += 1 + key_size + u128::from(q.ty.size()) + 1 + (1 + domain.len() as u128);
            types = types.max(q.ty.depth());
        }
        let key_depth = 1 + key.depth().max(1);
        let ports = if schema.is_empty() {
            0
        } else {
            1 + info.depth().max(key_depth).max(types).max(1)
        };
        bounded(self.limit, self.site, pos, 1 + info.depth().max(ports))?;
        self.fuel.pay(size).map_err(at(pos))?;
        let list = schema
            .iter()
            .map(|q| {
                #[cfg(test)]
                crate::counters::add(crate::counters::Count::Reflected, 1);
                #[cfg(test)]
                crate::counters::add(
                    crate::counters::Count::TextBytes,
                    (name(q).len() + domain.len()) as u64,
                );
                let number = Int::from_u64(u64::from(q.key.unwrap_or(0)));
                let port_key = vec![
                    Value::Str(name(q).to_owned()),
                    Value::Bool(q.key.is_some()),
                    Value::Int(number),
                ];
                Value::Record(
                    info,
                    vec![
                        Value::Record(key, port_key),
                        Value::Type(q.ty),
                        Value::Bool(q.input),
                        Value::Str(domain.to_owned()),
                    ],
                )
            })
            .collect();
        Ok(Value::List(info, list))
    }
}
