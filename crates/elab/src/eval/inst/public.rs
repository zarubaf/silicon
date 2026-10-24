// SPDX-License-Identifier: Apache-2.0
//! The public names of the ports of an owner and the ports with their `as` keys, as Lean
//! `Elab.publicOf`, `Elab.port`, `Elab.portKey`, and `Elab.keyed` define them (design sections
//! 5.6 and 6.2).
//!
//! The owner has one table of public names (`Work::publics`). A name there has one form and the
//! position of its first declaration. The static families of the module body are not copied into
//! the table: a look-up reads the table and then those families (`public_of`). A port belongs to
//! the owner also when a helper declares it, so a call frame does not change its name.
//!
//! The order of a port with an `as` key follows section 6.2. The name charges its size as a
//! string before the scan of the name rule and the look-up of its symbol. The symbol is the only
//! copy of a new name: a port, an entry, and the tables hold the symbol, and a text renders once,
//! at the error that wins.

use super::PortDecl;
use crate::Code;
use crate::agg::{Agg, Base};
use crate::eval::inst::family::FamKey;
use crate::eval::{Evaluator, GuardKind, Res, at, fail, need};
use crate::hw::{Kind, Seen, Val};
use crate::names::{PathId, Sym};
use crate::ops::{int_text, str_text};
use crate::types::{Ty, TyId};
use crate::value::Value;
use parse::ast::{Expr, Pos};
use resolve::DeclId;
use syntax::SyntaxKind;

/// The form of a public name of the owner (section 5.6): a scalar port, or a port family with its
/// direction, `true` for an input.
#[derive(Clone, Copy)]
pub(crate) enum Public {
    Scalar,
    Family(bool),
}

/// The key of the table of public names. Every compare of two keys is one unit of work that the
/// tests count, whatever structure holds the keys, so a table that searches a list counts its
/// scan.
#[derive(Clone, Copy)]
pub(crate) struct PubKey(pub(crate) Sym);

impl PartialEq for PubKey {
    fn eq(&self, other: &PubKey) -> bool {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Publics, 1);
        self.0 == other.0
    }
}

impl Eq for PubKey {}

impl PartialOrd for PubKey {
    fn partial_cmp(&self, other: &PubKey) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PubKey {
    fn cmp(&self, other: &PubKey) -> std::cmp::Ordering {
        #[cfg(test)]
        crate::counters::add(crate::counters::Count::Publics, 1);
        self.0.cmp(&other.0)
    }
}

/// The position `b` of an earlier declaration in a message.
fn at_text(b: Pos) -> String {
    format!("{}:{}", b.line, b.col)
}

/// The `S022` error "Name rule" of section 6.2 at `kp`, for the name `s` of the kind `kind`.
fn name_rule<T>(kp: Pos, s: &str, kind: &str) -> Res<T> {
    fail(
        Code::S022,
        kp,
        format!(
            "`{}` is not a valid {} name; use an ASCII letter or `_`, then letters, digits, or \
             `_`",
            str_text(s),
            kind
        ),
    )
}

/// The `S022` error "Keyword name" of section 6.2 at `kp`, for the name `s` of the kind `kind`.
fn keyword_name<T>(kp: Pos, s: &str, kind: &str) -> Res<T> {
    fail(
        Code::S022,
        kp,
        format!(
            "`{}` is a keyword, so it cannot be a {} name; choose another name",
            str_text(s),
            kind
        ),
    )
}

/// The `S019` error "Scalar port and port family" of section 6.2 at `pos`, for the public name
/// `x` with the other declaration at `b`.
pub(super) fn scalar_family<T>(pos: Pos, x: &str, b: Pos) -> Res<T> {
    fail(
        Code::S019,
        pos,
        format!(
            "`{}` names a scalar port and a port family, here and at {}; give one of them \
             another key with `as`",
            str_text(x),
            at_text(b)
        ),
    )
}

/// The `S019` error "Public family with two directions" of section 6.2 at `pos`, for the family
/// `x` with the other declaration at `b`.
pub(super) fn directions<T>(pos: Pos, x: &str, b: Pos) -> Res<T> {
    fail(
        Code::S019,
        pos,
        format!(
            "the port family `{}` has an input entry and an output entry, here and at {}; give \
             the entries of one direction another key with `as`",
            str_text(x),
            at_text(b)
        ),
    )
}

impl Evaluator<'_> {
    /// The text of the public name `sym`.
    pub(in crate::eval) fn name_text(&self, sym: Sym) -> &str {
        self.syms.texts.get(sym).map_or("", String::as_str)
    }

    /// Enters the public name `sym` with the form `form`, declared at `pos`, into the table of
    /// the owner. Its call frame is the current one.
    pub(in crate::eval) fn publish(&mut self, sym: Sym, form: Public, pos: Pos) {
        let call = self.call;
        self.elab
            .work
            .publics
            .insert(PubKey(sym), (form, pos, call));
    }

    /// The public name `sym` in the table of the owner: its form, the position of its first
    /// declaration, and the call frame of that declaration. The table holds each static family
    /// of the module body from the start, at its first indexed declaration in the frame 0. They
    /// are in `Syms::families`, so the look-up reads the table and then them, with no copy for an
    /// instantiation.
    pub(in crate::eval) fn public_of(&self, sym: Sym) -> Option<(Public, Pos, usize)> {
        let work = &self.elab.work;
        if let Some(&e) = work.publics.get(&PubKey(sym)) {
            return Some(e);
        }
        let (input, pos) = *self.syms.families.get(work.owner)?.get(&sym)?;
        Some((Public::Family(input), pos, 0))
    }

    /// Reserves the core name `sym` in the root frame, as the bindings of the name count it. The
    /// result is `true` when a declaration took the name before.
    fn reserve(&mut self, sym: Sym) -> bool {
        let key = (crate::eval::ROOT.id, sym);
        let v = self.naming.versions.get(&key).copied().unwrap_or(0);
        self.naming.versions.insert(key, v + 1);
        v != 0
    }

    /// The scalar port with the public name `sym` at `pos` (section 6.2, steps 9 to 11 of the
    /// port order). The table of public names holds no other port of the name. A scalar port there
    /// is "Public name twice". When one statement of a function runs again in another call, it is
    /// "Public name twice in a helper" (`again`). A family there is "Scalar port and port family".
    /// Then the name takes its core name in the root frame. An earlier binding of the module body
    /// with the name is "Port name taken". The port has no call frame (section 7.3). An output
    /// with an `as` key has its `binder` for its `S018` text.
    pub(in crate::eval) fn port(
        &mut self,
        pos: Pos,
        input: bool,
        sym: Sym,
        (ty, tid): (Ty, TyId),
        binder: Option<Sym>,
    ) -> Res<Val> {
        match self.public_of(sym) {
            Some((Public::Scalar, b, call)) => {
                let x = str_text(self.name_text(sym));
                return match self.again(pos, (b, call)) {
                    Some(h) => fail(
                        Code::S019,
                        pos,
                        format!(
                            "`{}` declares the port `{x}` again in a second call; give each \
                             call its own port name, for example from a parameter in the `as` key",
                            self.item_name(h)
                        ),
                    ),
                    None => fail(
                        Code::S019,
                        pos,
                        format!(
                            "the port name `{x}` is declared here and at {}; give one of them \
                             another key with `as`, for example from a parameter",
                            at_text(b)
                        ),
                    ),
                };
            }
            Some((Public::Family(_), b, _)) => {
                return scalar_family(pos, self.name_text(sym), b);
            }
            None => self.publish(sym, Public::Scalar, pos),
        }
        if self.reserve(sym) {
            return fail(
                Code::S019,
                pos,
                format!(
                    "the port name `{}` is already the core name of a hardware `let`, a \
                     resource, or an instance of this module; rename that declaration or the \
                     port",
                    str_text(self.name_text(sym))
                ),
            );
        }
        self.elab.work.add_port(PortDecl {
            sym,
            key: None,
            input,
            ty,
            tid,
            pos,
        });
        let path = self.paths.child(None, sym);
        self.port_value(pos, input, path, tid, (sym, None), binder)
    }

    /// The value of the port at `path`, scalar or family entry (`key`). An input refers to its
    /// name. An empty one stays a reference, so only a read of it pays its zero (`name`). An
    /// output is a resource that needs one binding.
    pub(in crate::eval) fn port_value(
        &mut self,
        pos: Pos,
        input: bool,
        path: PathId,
        tid: TyId,
        name: (Sym, Option<u32>),
        binder: Option<Sym>,
    ) -> Res<Val> {
        if !input {
            return Ok(self.resource(Kind::Output, path, tid, pos, name, binder));
        }
        let r = Agg::Ref(Base::Name(path), tid);
        if self.tys.meta(tid).leaves.is_zero() {
            Ok(Val::Agg(Box::new(r)))
        } else {
            self.normalize(pos, r)
        }
    }

    /// Whether the type `t` is the prelude struct `PortKey`. A user struct of this name is
    /// another type.
    fn is_port_key(&self, t: TyId) -> bool {
        match self.tys.get(t) {
            Ty::Struct(s) => {
                let spec = self.tys.spec(*s);
                spec.prelude() && spec.name() == "PortKey"
            }
            _ => false,
        }
    }

    /// The public name that the static `as` key `v` gives at `kp`, and the family key of an entry (section 6.2, steps 6 and 7 of the port order). A `String`
    /// is a scalar name. A record of the prelude struct `PortKey` is a scalar name with the index
    /// 0, or an entry with an index below 2^32. Each other value is `S010` "Port key type". The
    /// index check reads the bit length, so it takes constant work, and the index renders only in
    /// an error.
    fn port_key<'v>(&self, kp: Pos, v: &'v Value) -> Res<(&'v str, Option<u32>)> {
        if let Value::Str(x) = v {
            return Ok((x, None));
        }
        if let Value::Record(t, fields) = v
            && self.is_port_key(*t)
            && let [Value::Str(x), Value::Bool(indexed), Value::Int(k)] = fields.as_slice()
        {
            if !indexed {
                return if k.is_zero() {
                    Ok((x, None))
                } else {
                    fail(
                        Code::S022,
                        kp,
                        format!(
                            "a scalar `PortKey` has the index 0, but it has {}; set `indexed` to \
                             `true`, or the index to 0",
                            int_text(k)
                        ),
                    )
                };
            }
            return FamKey::of_int(k).key(kp).map(|k| (x.as_str(), Some(k)));
        }
        fail(
            Code::S010,
            kp,
            format!(
                "an `as` key is a static `String` or `PortKey`, not {}; write the public name as \
                 a string, for example `as \"req_0\"`",
                self.about(Seen::Static(v))
            ),
        )
    }

    /// The port with the binder `id`, the type `t`, and the `as` key `key` at `pos` (section 6.2,
    /// steps 4 to 11 of the port order). The key evaluates in a structural context of the kind
    /// `Name` and is static (`S011`). It gives the public name and the key of an entry
    /// (`port_key`). The name charges its size, 1 plus its characters (section 5.4). This charge
    /// comes before the scan of the name rule and the look-up of the symbol. A name that is not an
    /// identifier is `S022` "Name rule", and a keyword is `S022` "Keyword name". Then the port
    /// exists by its public name, as a scalar port (`port`) or a family entry (`declare_entry`).
    /// The result is its value, for the binder.
    pub(in crate::eval) fn keyed_port(
        &mut self,
        pos: Pos,
        input: bool,
        id: DeclId,
        t: (Ty, TyId),
        key: &Expr,
    ) -> Res<Val> {
        let o = self.guarded(GuardKind::Name, |ev| {
            let o = ev.eval(key)?;
            need(key, o)
        })?;
        let kp = key.pos();
        self.check_static(kp, &o)?;
        let (x, index) = self.port_key(kp, self.store.value(&o))?;
        self.fuel
            .pay(1 + x.chars().count() as u128)
            .map_err(at(kp))?;
        if !syntax::is_identifier(x) {
            return name_rule(kp, x, "port");
        }
        if SyntaxKind::keyword(x).is_some() {
            return keyword_name(kp, x, "port");
        }
        let sym = self.syms.symbol_of(x);
        let binder = Some(self.sym(id));
        match index {
            None => self.port(pos, input, sym, t, binder),
            Some(k) => self.declare_entry(pos, input, (sym, k), t, binder),
        }
    }
}
