//! The names of section 7 of the front-end spec, as Lean `Source.Names` defines them: the core
//! name of a structural path, and the emitted module name of an `InstantiationId`.
//!
//! A name is a list of fields. The first field is a user field: a source name unchanged. Each
//! other field is a user field or a made field. `encode` joins the fields with one `$`. A made
//! field starts with a digit, so it never equals a user field. `decode` splits at each `$` and
//! reads the kind of each field from its first character. Thus `decode(encode(p)) == Some(p)`
//! for each valid name `p`.
//!
//! A call site, a version, and a temporary are `u64` values here: an elaboration within a
//! `u64` fuel makes no larger one. `decode` gives `None` for a larger number.

use crate::int::Int;
use crate::sha256;
use crate::value::{InstantiationId, Value};

/// The roles of section 7.2: clock, reset, call result, memory response, and memory request.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Role {
    Clk,
    Rst,
    Ret,
    Rdata,
    Rvalid,
    Ren,
    Raddr,
}

const ROLES: [Role; 7] = [
    Role::Clk,
    Role::Rst,
    Role::Ret,
    Role::Rdata,
    Role::Rvalid,
    Role::Ren,
    Role::Raddr,
];

impl Role {
    #[must_use]
    pub fn text(self) -> &'static str {
        match self {
            Role::Clk => "0clk",
            Role::Rst => "0rst",
            Role::Ret => "0ret",
            Role::Rdata => "0rdata",
            Role::Rvalid => "0rvalid",
            Role::Ren => "0ren",
            Role::Raddr => "0raddr",
        }
    }
}

/// A field of a name. Each variant except `User` is a made field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Field {
    User(String),
    Int(Int),
    Call(u64),
    Version(u64),
    Bool(bool),
    Digest(String),
    Temp(u64),
    Role(Role),
}

/// A name: a first user field, then the other fields in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Name {
    pub head: String,
    pub rest: Vec<Field>,
}

/// A user field is a source identifier: `[A-Za-z_][A-Za-z0-9_]*`.
#[must_use]
pub fn user_field(s: &str) -> bool {
    let mut chars = s.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn hex_digit(c: char) -> bool {
    c.is_ascii_digit() || ('a'..='f').contains(&c)
}

impl Field {
    #[must_use]
    pub fn valid(&self) -> bool {
        match self {
            Field::User(s) => user_field(s),
            Field::Digest(h) => !h.is_empty() && h.chars().all(hex_digit),
            _ => true,
        }
    }

    #[must_use]
    pub fn encode(&self) -> String {
        match self {
            Field::User(s) => s.clone(),
            Field::Int(n) if n.is_negative() => format!("{}n", n.neg()),
            Field::Int(n) => n.to_string(),
            Field::Call(k) => format!("{k}c"),
            Field::Version(k) => format!("{k}v"),
            Field::Bool(b) => if *b { "1b" } else { "0b" }.to_owned(),
            Field::Digest(h) => format!("0h{h}"),
            Field::Temp(k) => format!("{k}t"),
            Field::Role(r) => r.text().to_owned(),
        }
    }
}

impl Name {
    /// A valid name has only valid fields. Only a valid name has the round trip.
    #[must_use]
    pub fn valid(&self) -> bool {
        user_field(&self.head) && self.rest.iter().all(Field::valid)
    }

    /// True for a name with one field that equals a core keyword. It gets the field `0k`.
    #[must_use]
    pub fn keyword(&self) -> bool {
        self.rest.is_empty() && core_ir::text::is_keyword(&self.head)
    }

    /// The byte length of `encode`, known in time linear in the number of fields.
    #[must_use]
    pub fn byte_size(&self) -> u64 {
        if self.keyword() {
            return self.head.len() as u64 + 3;
        }
        let mut n = self.head.len() as u64;
        for f in &self.rest {
            n += 1 + f.encode().len() as u64;
        }
        n
    }
}

/// The core name: the fields joined with `$`, and `0k` after a keyword alone.
#[must_use]
pub fn encode(p: &Name) -> String {
    let mut out = p.head.clone();
    if p.keyword() {
        out.push_str("$0k");
    } else {
        for f in &p.rest {
            out.push('$');
            out.push_str(&f.encode());
        }
    }
    out
}

/// A decimal number without leading zeros.
fn decimal(ds: &str) -> Option<&str> {
    match ds.as_bytes() {
        [] | [b'0', _, ..] => None,
        _ => Some(ds),
    }
}

/// A made field: digits and one suffix letter, a role, or a digest.
fn made_field(s: &str) -> Option<Field> {
    if let Some(r) = ROLES.iter().find(|r| r.text() == s) {
        return Some(Field::Role(*r));
    }
    if let Some(h) = s.strip_prefix("0h") {
        let f = Field::Digest(h.to_owned());
        return f.valid().then_some(f);
    }
    let cut = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    let (ds, suffix) = s.split_at(cut);
    let n = decimal(ds);
    let small = || n.and_then(|d| d.parse::<u64>().ok());
    match suffix {
        "" => n.and_then(Int::from_decimal).map(Field::Int),
        "n" => n
            .and_then(Int::from_decimal)
            .filter(|k| !k.is_zero())
            .map(|k| Field::Int(k.neg())),
        "c" => small().map(Field::Call),
        "v" => small().map(Field::Version),
        "t" => small().map(Field::Temp),
        "b" => match n {
            Some("0") => Some(Field::Bool(false)),
            Some("1") => Some(Field::Bool(true)),
            _ => None,
        },
        _ => None,
    }
}

fn decode_field(s: &str) -> Option<Field> {
    if user_field(s) {
        Some(Field::User(s.to_owned()))
    } else {
        made_field(s)
    }
}

/// The inverse of `encode` on valid names. Any other text gives `None`.
#[must_use]
pub fn decode(s: &str) -> Option<Name> {
    let parts: Vec<&str> = s.split('$').collect();
    if let [h, "0k"] = parts.as_slice() {
        return core_ir::text::is_keyword(h).then(|| Name {
            head: (*h).to_owned(),
            rest: Vec::new(),
        });
    }
    let (h, rest) = parts.split_first()?;
    let mut fields = Vec::with_capacity(rest.len());
    for f in rest {
        fields.push(decode_field(f)?);
    }
    let p = Name {
        head: (*h).to_owned(),
        rest: fields,
    };
    (user_field(h) && !p.keyword()).then_some(p)
}

/// The first 16 hexadecimal digits of the SHA-256 of `s`: the digest of section 7.1.
#[must_use]
pub fn sha16(s: &str) -> String {
    let mut hex = sha256::hex(&sha256::hash(s.as_bytes()));
    hex.truncate(16);
    hex
}

/// The readable token of an argument. An integer above 256 bits has more than 64 digits.
fn readable(v: &Value) -> Option<Field> {
    match v {
        Value::Int(n) if n.log2() < 256 => Some(Field::Int(n.clone())),
        Value::Bool(b) => Some(Field::Bool(*b)),
        _ => None,
    }
}

/// The emitted module name of section 7.1 with the digest function `digest`. `serial` is the
/// serialization of `id`.
#[must_use]
pub fn module_name(digest: fn(&str) -> String, id: &InstantiationId, serial: &str) -> Name {
    let fields: Option<Vec<Field>> = id.args.iter().map(readable).collect();
    if let Some(rest) = fields {
        let p = Name {
            head: id.module.clone(),
            rest,
        };
        if p.byte_size() <= 64 {
            return p;
        }
    }
    Name {
        head: id.module.clone(),
        rest: vec![Field::Digest(digest(serial))],
    }
}

#[cfg(test)]
mod tests;
