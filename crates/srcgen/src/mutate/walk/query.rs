// SPDX-License-Identifier: Apache-2.0
//! The sites of the kinds of queries (front-end spec 6.2, 9.3). Each rewrite
//! changes one query, one type position, or one alias of `@Struct`.
//!
//! An error of the parser or of pass 4 holds in all code: an unknown
//! builtin, a wrong number of operands, an operand that is no place, and an
//! index on a builtin in a type position. An error of pass 5 holds where the
//! site always runs. A generated record type is elaborated at its first use,
//! so a change in an alias predicts no code: the front ends must agree on the
//! first error, and on its text.

use super::super::{EFFECT_FN, Effect, KEEP_FN, Kind};
use super::{Domain, Walk};
use crate::program::{FieldTy, Item, QExpr, Query, SExpr, STy, StructDef};

/// The name of 70 characters that a message cuts at 64 (section 5.5).
const LONG: usize = 70;

/// Visits the nodes of `e` in pre-order until `f` changes one.
fn each(e: &mut QExpr, f: &mut impl FnMut(&mut QExpr) -> bool) -> bool {
    if f(e) {
        return true;
    }
    match e {
        QExpr::Builtin(_, args) => args.iter_mut().any(|a| each(a, f)),
        QExpr::Call(_, a) | QExpr::Read(a, _) => each(a, f),
        QExpr::Eq(a, b) => each(a, f) || each(b, f),
        QExpr::Text(_) => false,
    }
}

/// The span of the last `[digits]` in `text`: the index of a static place.
fn index_span(text: &str) -> Option<(usize, usize)> {
    let end = text.rfind(']')?;
    let start = text[..end].rfind('[')?;
    let digits = &text[start + 1..end];
    (!digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())).then_some((start + 1, end))
}

impl Walk<'_> {
    /// A hit with the code `code`, certain in all code, or at a site that
    /// always runs.
    fn query_hit(&mut self, what: &str, code: &'static str, everywhere: bool) {
        let code = (everywhere || self.always).then_some(code);
        self.hit(format!("{what} in {}", self.item), Effect::Code(code));
    }

    /// The sites of the nodes of a query.
    pub(super) fn query_sites(&mut self, q: &mut Query) -> bool {
        let mut form = std::mem::replace(&mut q.form, QExpr::Text(String::new()));
        let hit = each(&mut form, &mut |node| self.node_sites(node));
        q.form = form;
        hit
    }

    /// The sites of one node.
    fn node_sites(&mut self, node: &mut QExpr) -> bool {
        let QExpr::Builtin(name, args) = node else {
            return false;
        };
        if self.site(Kind::BuiltinName) {
            let long = self.seen.is_multiple_of(2);
            *name = if long {
                "a".repeat(LONG)
            } else {
                "Nope".to_owned()
            };
            self.query_hit("rename a builtin", "S001", true);
            return true;
        }
        if self.site(Kind::BuiltinArity) {
            if args.is_empty() || self.seen.is_multiple_of(2) {
                args.pop();
            } else {
                args.push(QExpr::Text("0".to_owned()));
            }
            self.query_hit("change the number of operands of a builtin", "S001", true);
            return true;
        }
        let operand = matches!(name.as_str(), "TypeOf" | "ports");
        if let (true, [QExpr::Text(text)]) = (operand, &mut args[..])
            && self.operand_sites(name, text)
        {
            return true;
        }
        if name == "typeInfo"
            && let Some(first) = args.first_mut()
            && self.argument_sites(first)
        {
            return true;
        }
        false
    }

    /// The sites of the operand `text` of `@TypeOf` or `@ports`.
    fn operand_sites(&mut self, builtin: &str, text: &mut String) -> bool {
        if self.site(Kind::QueryOperand) {
            "(1 + 1)".clone_into(text);
            self.query_hit("make the operand of a query an operator", "S001", true);
            return true;
        }
        let input = self.inputs.first().cloned();
        if builtin == "ports"
            && let Some(input) = &input
            && self.site(Kind::PortsValue)
        {
            text.clone_from(input);
            self.query_hit("give @ports an own port", "S010", false);
            return true;
        }
        if builtin == "TypeOf" && self.domain == Domain::Clocked && self.site(Kind::NoType) {
            "clock".clone_into(text);
            self.query_hit("ask @TypeOf for the type of the domain", "S010", false);
            return true;
        }
        if let Some(s) = self.strs.first().cloned()
            && self.site(Kind::StringIndex)
        {
            *text = format!("{s}[0]");
            self.query_hit("index a string in a query", "S010", false);
            return true;
        }
        let Some((start, end)) = index_span(text) else {
            return false;
        };
        let digits = text[start..end].to_owned();
        if let Some(input) = input
            && self.site(Kind::KeyHardware)
        {
            text.replace_range(start..end, &input);
            // Pass 4 sees the name of a port in a key on all code (`S005`).
            self.query_hit("give a key of a query a port", "S005", true);
            return true;
        }
        if self.site(Kind::KeyEffect) {
            text.replace_range(start..end, &format!("{EFFECT_FN}({digits})"));
            self.query_hit(
                "call a function with an effect in a query key",
                "S016",
                false,
            );
            return true;
        }
        if let Some(root) = self.counter()
            && self.site(Kind::KeyMutation)
        {
            text.replace_range(start..end, &format!("{KEEP_FN}({root}, {digits})"));
            self.query_hit("change a root in a query key", "S016", false);
            return true;
        }
        false
    }

    /// The sites of the argument of `@typeInfo`.
    fn argument_sites(&mut self, arg: &mut QExpr) -> bool {
        if let Some(input) = self.inputs.first().cloned()
            && self.site(Kind::QueryHardware)
        {
            // A bare port in the raw argument is a value that is no `Type`
            // (S010); a comparison of ports is a hardware value (S011).
            *arg = QExpr::Text(format!("({input} == {input})"));
            self.query_hit("give @typeInfo a hardware value", "S011", false);
            return true;
        }
        if self.site(Kind::TypeInfoValue) {
            *arg = QExpr::Text("3".to_owned());
            self.query_hit("give @typeInfo a value", "S010", false);
            return true;
        }
        false
    }

    /// The sites of a type position that a query spells.
    pub(super) fn query_type_sites(&mut self, form: &mut QExpr) -> bool {
        if self.site(Kind::IndexBuiltinType) {
            let inner = std::mem::replace(form, QExpr::Text(String::new()));
            *form = QExpr::Read(Box::new(inner), "[3]".to_owned());
            self.query_hit("index a builtin in a type position", "S007", true);
            return true;
        }
        if self.site(Kind::BuiltinType) {
            let inner = std::mem::replace(form, QExpr::Text(String::new()));
            *form = QExpr::Builtin("typeInfo".to_owned(), vec![inner]);
            self.query_hit("give a type position a TypeInfo", "S010", false);
            return true;
        }
        false
    }

    /// The sites of a constructor of a generated record type: one field more
    /// or less is `S007`, and no field at all is the zero, which a type with a
    /// field that is no hardware data does not have (`S010`).
    pub(super) fn constructor_sites(&mut self, name: &str, fields: &mut Vec<SExpr>) -> bool {
        let Some(&(_, data)) = self.aliases.iter().find(|(a, _)| a == name) else {
            return false;
        };
        if fields.is_empty() {
            return false;
        }
        let zero = SExpr::Int(num_bigint::BigInt::from(0), crate::program::Radix::Dec);
        if self.site(Kind::ConstructorArity) {
            // One field less would be the zero, so a type of one field gets
            // a field more.
            if fields.len() >= 2 && self.seen.is_multiple_of(2) {
                fields.pop();
            } else {
                fields.push(zero);
            }
            self.query_hit(
                &format!("change the fields of a constructor of {name}"),
                "S007",
                false,
            );
            return true;
        }
        if !data && self.site(Kind::ZeroNonData) {
            fields.clear();
            self.query_hit(&format!("make the zero of {name}"), "S010", false);
            return true;
        }
        false
    }

    /// The sites of the alias `def` of `@Struct`: the argument, a field name,
    /// and a field type that is the alias itself.
    pub(super) fn alias_sites(
        &mut self,
        def: &StructDef,
        form: &mut QExpr,
        helper: Option<&String>,
    ) -> bool {
        let QExpr::Builtin(_, args) = form else {
            return false;
        };
        let Some(QExpr::Text(list)) = args.first_mut() else {
            return false;
        };
        if self.site(Kind::StructArg) {
            "5".clone_into(list);
            self.hit(
                format!("give @Struct a value in {}", def.name),
                Effect::Code(None),
            );
            return true;
        }
        let literal = helper.is_none() && list.starts_with("[FieldInfo(\"");
        if literal && self.site(Kind::FieldName) {
            let first = def
                .fields
                .first()
                .map(|(n, _)| n.clone())
                .unwrap_or_default();
            let second = def.fields.get(1).map(|(n, _)| n.clone());
            let bad = match (self.seen % 3, second) {
                (0, Some(second)) => format!("FieldInfo(\"{second}\""),
                (1, _) => "FieldInfo(\"0\"".to_owned(),
                _ => "FieldInfo(\"let\"".to_owned(),
            };
            let old = format!("FieldInfo(\"{first}\"");
            *list = list.replacen(&old, &bad, 1);
            if bad == old {
                // The first and the second name are one: nothing changed.
                list.push(' ');
            }
            self.hit(
                format!("give a field of {} a bad name", def.name),
                Effect::Code(None),
            );
            return true;
        }
        let static_field = def
            .fields
            .iter()
            .find(|(_, t)| matches!(t, FieldTy::Static(STy::Int)));
        if literal
            && let Some((name, _)) = static_field
            && self.site(Kind::SelfStruct)
        {
            let old = format!("FieldInfo(\"{name}\", Int)");
            let new = format!("FieldInfo(\"{name}\", {})", def.name);
            *list = list.replacen(&old, &new, 1);
            self.hit(
                format!("make {} a field type of itself", def.name),
                Effect::Code(None),
            );
            return true;
        }
        false
    }

    /// `UserFieldInfo`: a user struct `FieldInfo` hides the prelude one.
    pub(super) fn user_field_info(&mut self, items: &mut Vec<Item>) -> bool {
        let aliases = items.iter().any(|i| matches!(i, Item::Alias { .. }));
        if !aliases || !self.site(Kind::UserFieldInfo) {
            return false;
        }
        let def = StructDef {
            name: "FieldInfo".to_owned(),
            params: Vec::new(),
            fields: vec![("a".to_owned(), FieldTy::Static(STy::Int))],
        };
        items.insert(0, Item::Struct(def));
        self.hit("add a user struct FieldInfo".to_owned(), Effect::Code(None));
        true
    }
}
