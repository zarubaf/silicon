// SPDX-License-Identifier: Apache-2.0
//! `@ports(h)`: the `PortInfo` list of a child (front-end spec 9.3, ADR
//! 0032).
//!
//! The builder knows the ports of a child from its signature and its plan,
//! the same plan that the twin carries out, so the list needs no walk of the
//! source. The tests of `rows` cite the sentences of section 9.3. A query
//! reads scalars of the list: its length, and the direction, the key, the
//! domain, and the type of one port.

use super::ports::{Dir, PortHelper};
use super::query::{builtin, is, read};
use super::reflect::RTy;
use super::{Builder, Sig};
use crate::program::{PTy, QExpr, SExpr, STy, Ty, string};
use crate::public::Public;
use num_bigint::BigInt;

/// One `PortInfo` of a child.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct Row {
    pub(super) public: Public,
    pub(super) input: bool,
    /// The type of the port, if a query reflects it.
    pub(super) ty: Option<RTy>,
    /// The type as the plan declares it.
    pub(super) plan_ty: PTy,
}

/// A child that a query can read: its name, its `PortInfo` list, and its
/// domain.
#[derive(Clone, Debug)]
pub(super) struct Kid {
    pub(super) name: String,
    pub(super) rows: Vec<Row>,
    pub(super) domain: &'static str,
    /// The static `let` that holds the list, if one does: a read names the
    /// `let` and not the call.
    pub(super) bound: Option<String>,
}

impl Kid {
    /// The list: `@ports(u)`, or the `let` that holds it.
    pub(super) fn list(&self) -> QExpr {
        match &self.bound {
            Some(name) => QExpr::Text(name.clone()),
            None => builtin("ports", QExpr::Text(self.name.clone())),
        }
    }
}

/// The `PortInfo` list of the module `sig` with the type of each port as
/// `ty` gives it: the ports of its body, of its helpers, and its family
/// entries, in port-layout order.
pub(super) fn rows(sig: &Sig, helpers: &[PortHelper], ty: impl Fn(&Ty) -> Option<RTy>) -> Vec<Row> {
    let own = |names: &[(String, Ty)], input| -> Vec<Row> {
        names
            .iter()
            .map(|(n, t)| Row {
                public: Public::scalar(n),
                input,
                ty: ty(t),
                plan_ty: PTy::Data(t.clone()),
            })
            .collect()
    };
    let enums = |names: &[(String, crate::program::EnumDef)], input| -> Vec<Row> {
        names
            .iter()
            .map(|(n, d)| Row {
                public: Public::scalar(n),
                input,
                ty: Some(RTy::Static(STy::Enum(Box::new(d.clone())))),
                plan_ty: PTy::Data(Ty::Enum(d.name.clone())),
            })
            .collect()
    };
    let declared = sig.plan.declared(helpers).into_iter().map(|d| Row {
        public: d.public,
        input: d.dir == Dir::In,
        ty: match &d.ty {
            PTy::Data(t) => ty(t),
            // An empty port has the type `Unit`.
            PTy::Unit => Some(RTy::Unit),
        },
        plan_ty: d.ty,
    });
    let mut out: Vec<Row> = own(&sig.inputs, true)
        .into_iter()
        .chain(own(&sig.outputs, false))
        .chain(enums(&sig.enum_inputs, true))
        .chain(enums(&sig.enum_outputs, false))
        .chain(declared)
        .collect();
    // Section 7.5: "The port layout sorts the inputs by public basename, then
    // by the numeric key, and then the outputs in the same way."
    out.sort_by(|a, b| (!a.input, &a.public).cmp(&(!b.input, &b.public)));
    out
}

fn int(n: usize) -> SExpr {
    SExpr::Int(BigInt::from(n), crate::program::Radix::Dec)
}

impl Builder {
    /// A read of the `PortInfo` list of the child `kid`: the query and its
    /// static result. A numeric read has a number, and a `Bool` read
    /// a Boolean, so a `varying` read is numeric only. The `ty` of a port
    /// also gives a type value, which the other reads take.
    pub(super) fn ports_read(&mut self, kid: &Kid, varying: bool) -> Option<(QExpr, SExpr)> {
        let list = || kid.list();
        // Half of the draws take an entry of a family, if there is one.
        let keyed: Vec<usize> = (0..kid.rows.len())
            .filter(|&k| kid.rows.get(k).is_some_and(|r| r.public.key.is_some()))
            .collect();
        let k = match keyed.get(self.tape.index(keyed.len())) {
            Some(&k) if self.tape.flag() => k,
            _ => self.tape.index(kid.rows.len()),
        };
        let row = kid.rows.get(k)?;
        let at = |suffix: &str| read(list(), &format!("[{k}]{suffix}"));
        let numbers = [
            (QExpr::Call("len", Box::new(list())), int(kid.rows.len())),
            (
                at(".key.index"),
                int(row.public.key.map_or(0, |k| k as usize)),
            ),
            (
                QExpr::Call("len", Box::new(at(".domain"))),
                int(kid.domain.len()),
            ),
        ];
        if varying || self.tape.below(4) == 0 {
            return numbers.get(self.tape.index(numbers.len())).cloned();
        }
        let tags = [
            (at(".is_input"), row.input),
            (at(".key.indexed"), row.public.key.is_some()),
        ];
        match self.tape.below(5) {
            0 | 4 => {
                let name = if self.tape.flag() {
                    row.public.base.clone()
                } else {
                    format!("{}x", row.public.base)
                };
                let held = name == row.public.base;
                Some((is(at(".key.name"), &name), SExpr::Bool(held)))
            }
            1 => {
                let domain = if self.tape.flag() {
                    kid.domain
                } else {
                    "clock"
                };
                let held = domain == kid.domain;
                Some((is(at(".domain"), domain), SExpr::Bool(held)))
            }
            _ => {
                let (form, value) = tags.get(self.tape.index(tags.len()))?.clone();
                Some((form, SExpr::Bool(value)))
            }
        }
    }

    /// The type of a port of `kid` as a type value: `@field(ps[k], "ty")`
    /// or `ps[k].ty`, and the drawn type.
    pub(super) fn port_type(&mut self, kid: &Kid) -> Option<(QExpr, RTy)> {
        let typed: Vec<(usize, &RTy)> = kid
            .rows
            .iter()
            .enumerate()
            .filter_map(|(k, r)| r.ty.as_ref().map(|t| (k, t)))
            .collect();
        let (k, t) = *typed.get(self.tape.index(typed.len()))?;
        let list = kid.list();
        let form = if self.tape.flag() {
            read(list, &format!("[{k}].ty"))
        } else {
            let part = read(list, &format!("[{k}]"));
            QExpr::Builtin("field".to_owned(), vec![part, QExpr::Text(string("ty"))])
        };
        Some((form, t.clone()))
    }

    /// The groups of statements and the numbers that read a child through
    /// `@ports`: one read of the list or of a port, or a read of the type
    /// of a port.
    pub(super) fn ports_group(&mut self) -> Option<(QExpr, SExpr, Option<RTy>)> {
        // Three draws in four take a child with 3 ports or more, if there is
        // one: the cost of its list shows in the budget.
        let wide: Vec<&Kid> = self.kids.iter().filter(|k| k.rows.len() >= 3).collect();
        let pick = self.tape.index(wide.len());
        let all = self.tape.index(self.kids.len());
        let kid = match wide.get(pick) {
            Some(kid) if self.tape.below(4) != 0 => (*kid).clone(),
            _ => self.kids.get(all)?.clone(),
        };
        note!(self, query_wide, kid.rows.len() >= 3);
        if self.tape.below(3) == 0
            && let Some((tq, t)) = self.port_type(&kid)
        {
            let (form, value) = if self.tape.flag() {
                self.test(tq, &t)
            } else {
                self.size(&tq, &t, false)
            };
            return Some((form, value, Some(t)));
        }
        let (form, value) = self.ports_read(&kid, false)?;
        Some((form, value, None))
    }

    /// `rows` for a child of the builder: the types of the ports with the
    /// arguments of the instance in place of its parameters.
    pub(super) fn kid_rows(&self, child: &super::inst::Child) -> Vec<Row> {
        rows(&child.sig, &self.port_helpers, |t| {
            super::query::outer_ty(child, t)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::ports::{Form, PortPlan, Shape};
    use super::*;
    use crate::program::Radix;

    fn uint(w: i64) -> Ty {
        Ty::UInt(SExpr::Int(BigInt::from(w), Radix::Dec))
    }

    fn sig(clocked: bool) -> Sig {
        Sig {
            name: "M1".to_owned(),
            params: Vec::new(),
            clocked,
            inputs: vec![("i0".to_owned(), uint(8))],
            outputs: vec![("o0".to_owned(), Ty::Bool)],
            enum_inputs: Vec::new(),
            enum_outputs: Vec::new(),
            plan: PortPlan::default(),
            wraps: None,
        }
    }

    fn literal(t: &Ty) -> Option<RTy> {
        RTy::of(t)
    }

    fn rows_of(s: &Sig) -> Vec<Row> {
        rows(s, &[], literal)
    }

    /// "The result is a `List[PortInfo]` ..., one `PortInfo` per port": the
    /// ports of the body.
    #[test]
    fn a_port_of_the_body_has_one_row() {
        let rows = rows(&sig(true), &[], literal);
        assert_eq!(rows.len(), 2);
    }

    /// "`ty` is the data type `T` of the port, also for an input. It is not
    /// `Input[T]`." "`is_input` is `true` for an input and `false` for an
    /// output."
    #[test]
    fn the_type_of_an_input_is_its_data_type() {
        let rows = rows(&sig(true), &[], literal);
        assert_eq!(
            (rows[0].input, rows[0].ty.clone()),
            (
                true,
                Some(RTy::UInt(SExpr::Int(BigInt::from(8), Radix::Dec)))
            )
        );
        assert_eq!(
            (rows[1].input, rows[1].ty.clone()),
            (false, Some(RTy::Bool))
        );
    }

    /// "`key` is `PortKey(n, false, 0)` for a scalar port with the public
    /// name `n`. It is `PortKey(n, true, k)` for the family entry `n[k]`." "in
    /// port-layout order": the bare name before its keys, the keys as
    /// numbers.
    #[test]
    fn a_family_entry_has_an_indexed_key_and_the_layout_orders_them() {
        let mut s = sig(true);
        s.plan.forms.push(Form::Family {
            dir: Dir::In,
            fam: "A0".to_owned(),
            shape: Shape::Top(vec![(10, PTy::Data(uint(4))), (2, PTy::Unit)]),
        });
        let rows = rows(&s, &[], literal);
        let names: Vec<String> = rows.iter().map(|r| r.public.to_string()).collect();
        assert_eq!(names, ["A0[2]", "A0[10]", "i0", "o0"]);
        // The inputs come first, then the outputs.
        s.plan.forms.push(Form::Family {
            dir: Dir::Out,
            fam: "Z0".to_owned(),
            shape: Shape::Top(vec![(1, PTy::Data(uint(4)))]),
        });
        let rows = rows_of(&s);
        let names: Vec<String> = rows.iter().map(|r| r.public.to_string()).collect();
        assert_eq!(names, ["A0[2]", "A0[10]", "i0", "Z0[1]", "o0"]);
        assert_eq!(rows[0].public.key, Some(2));
        // "also an empty port": it has a row, with the type `Unit`.
        assert_eq!(rows[0].ty, Some(RTy::Unit));
    }
}
