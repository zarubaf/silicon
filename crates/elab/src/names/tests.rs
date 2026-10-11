// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Names` in Lean. The round trip `decode(encode(p)) ==
//! Some(p)` holds on each name of a generated set and on random names. The set has user names
//! equal to each core keyword, names close to the made fields, and each made field form. Each
//! encoded name matches the core name pattern and is not a core keyword.

use super::*;
use crate::value::Ty;
use proptest::prelude::*;

const KEYWORDS: [&str; 44] = [
    "design",
    "module",
    "extern",
    "input",
    "output",
    "clock",
    "bits",
    "deps",
    "let",
    "reg",
    "next",
    "mem",
    "write",
    "inst",
    "assign",
    "reset",
    "sync",
    "const",
    "not",
    "add",
    "sub",
    "mul",
    "and",
    "or",
    "xor",
    "shl",
    "shru",
    "shrs",
    "concat",
    "icmp",
    "mux",
    "extract",
    "replicate",
    "read",
    "eq",
    "ne",
    "ult",
    "ule",
    "ugt",
    "uge",
    "slt",
    "sle",
    "sgt",
    "sge",
];

/// User names: each core keyword, backend kinds, and names close to the made fields.
fn users() -> Vec<String> {
    let mut out: Vec<String> = KEYWORDS.iter().map(|k| (*k).to_owned()).collect();
    for u in [
        "clk",
        "rst",
        "silicon_reg_r",
        "x",
        "_",
        "_0k",
        "k0",
        "n5",
        "c3",
        "v2",
        "b1",
        "h0",
        "t4",
        "ret",
        "rdata",
        "A_b9",
        "Counter",
    ] {
        out.push(u.to_owned());
    }
    out
}

fn int(digits: &str) -> Int {
    match digits.strip_prefix('-') {
        Some(d) => Int::from_decimal(d).unwrap().neg(),
        None => Int::from_decimal(digits).unwrap(),
    }
}

/// Each made field form, with the boundary values of each number.
fn made() -> Vec<Field> {
    let mut out = vec![
        Field::Int(int("0")),
        Field::Int(int("5")),
        Field::Int(int("-5")),
        Field::Int(int("18446744073709551616")),
        Field::Int(int("-1")),
        Field::Call(0),
        Field::Call(3),
        Field::Version(1),
        Field::Version(12),
        Field::Bool(true),
        Field::Bool(false),
        Field::Digest("3f2a9c0b1d4e5f60".to_owned()),
        Field::Digest("0".to_owned()),
        Field::Temp(0),
        Field::Temp(4),
    ];
    out.extend(ROLES.iter().map(|r| Field::Role(*r)));
    out
}

fn fields() -> Vec<Field> {
    let mut out = made();
    out.extend(users().into_iter().map(Field::User));
    out
}

fn name(head: &str, rest: Vec<Field>) -> Name {
    Name {
        head: head.to_owned(),
        rest,
    }
}

/// Names of one, two, and three fields.
fn names() -> Vec<Name> {
    let mut out: Vec<Name> = users().iter().map(|u| name(u, vec![])).collect();
    for u in users() {
        for f in fields() {
            out.push(name(&u, vec![f]));
        }
    }
    for u in ["x", "add", "i"] {
        for f in fields() {
            for g in made() {
                out.push(name(u, vec![f.clone(), g]));
            }
        }
    }
    out
}

fn round_trip(p: &Name) -> bool {
    decode(&encode(p)).as_ref() == Some(p)
}

/// The core name pattern `[A-Za-z_][A-Za-z0-9_]*(\$[A-Za-z0-9_]+)*`, and no keyword.
fn legal(p: &Name) -> bool {
    let text = encode(p);
    let mut parts = text.split('$');
    let first = parts.next().unwrap_or("");
    user_field(first)
        && parts.all(|f| !f.is_empty() && f.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
        && !core_ir::text::is_keyword(&text)
}

#[test]
fn the_round_trip_on_the_generated_names() {
    let all = names();
    assert!(all.len() > 1000);
    for p in &all {
        assert!(p.valid(), "{p:?}");
        assert!(round_trip(p), "{p:?}");
        assert!(legal(p), "{p:?}");
        assert_eq!(p.byte_size(), encode(p).len() as u64, "{p:?}");
    }
}

#[test]
fn the_keyword_escape() {
    assert_eq!(encode(&name("add", vec![])), "add$0k");
    assert_eq!(encode(&name("add", vec![Field::Version(1)])), "add$1v");
    assert_eq!(encode(&name("addx", vec![])), "addx");
    assert_eq!(
        encode(&name(
            "i",
            vec![Field::Int(int("2")), Field::User("r".into())]
        )),
        "i$2$r"
    );
    assert_eq!(
        encode(&name("f", vec![Field::Call(0), Field::User("t".into())])),
        "f$0c$t"
    );
    assert_eq!(encode(&name("d", vec![Field::Role(Role::Clk)])), "d$0clk");
    assert_eq!(encode(&name("i", vec![Field::Int(int("-5"))])), "i$5n");
    assert_eq!(
        encode(&name(
            "Fifo",
            vec![Field::Int(int("16")), Field::Bool(true)]
        )),
        "Fifo$16$1b"
    );
}

#[test]
fn decode_accepts_only_the_encoded_texts() {
    for text in [
        "add",
        "x$0k",
        "add$0k$1v",
        "x$05",
        "x$0n",
        "x$2b",
        "x$0h",
        "x$0hA",
        "x$$y",
        "x$",
        "5$x",
        "",
        "x$0clkx",
    ] {
        assert_eq!(decode(text), None, "{text}");
    }
    assert_eq!(
        decode("x$0ret"),
        Some(name("x", vec![Field::Role(Role::Ret)]))
    );
}

/// A path shares its frame. Its name lists the fields from the outside in.
#[test]
fn a_path_shares_its_frame() {
    let texts = vec!["i".to_owned(), "r".to_owned()];
    let mut paths = Paths::default();
    let i = paths.child(None, 0);
    let frame = paths.push(i, Step::Int(int("2")));
    let r = paths.child(Some(frame), 1);
    assert_eq!(
        paths.name(r, &texts),
        name("i", vec![Field::Int(int("2")), Field::User("r".into())])
    );
    assert_eq!(paths.name(i, &texts), name("i", vec![]));
}

fn id(module: &str, args: Vec<Value>) -> InstantiationId {
    InstantiationId {
        module: module.to_owned(),
        args,
    }
}

fn emitted(i: &InstantiationId) -> String {
    encode(&module_name(sha16, i, &i.serialize()))
}

fn uint(w: u32, v: u64) -> Value {
    Value::UInt(crate::int::finite(w, v).unwrap())
}

fn sint(w: u32, v: u64) -> Value {
    Value::SInt(crate::int::finite(w, v).unwrap())
}

#[test]
fn the_readable_and_the_digest_module_names() {
    assert_eq!(
        emitted(&id("Counter", vec![Value::Int(int("8"))])),
        "Counter$8"
    );
    assert_eq!(
        emitted(&id("Fifo", vec![Value::Int(int("16")), Value::Bool(true)])),
        "Fifo$16$1b"
    );
    assert_eq!(emitted(&id("M", vec![Value::Int(int("-5"))])), "M$5n");
    assert_eq!(emitted(&id("Top", vec![])), "Top");
    assert_eq!(emitted(&id("add", vec![])), "add$0k");
    assert_eq!(
        emitted(&id("M", vec![Value::Str("a".into())])),
        format!("M$0h{}", sha16("(instantiation root M ((string \"a\")))"))
    );
    assert_eq!(
        emitted(&id("M", vec![Value::Type(Ty::Bool)])),
        format!("M$0h{}", sha16("(instantiation root M ((type bool)))"))
    );
}

/// The 64-byte limit: a name of 64 bytes stays readable, and one of 65 bytes takes the
/// digest. The limit holds also without arguments.
#[test]
fn the_limit_of_the_readable_form() {
    let long = |n: usize| "a".repeat(n);
    let five = || vec![Value::Int(int("5"))];
    assert_eq!(emitted(&id(&long(62), five())), format!("{}$5", long(62)));
    assert_eq!(
        emitted(&id(&long(63), five())),
        format!(
            "{}$0h{}",
            long(63),
            sha16(&format!("(instantiation root {} ((int 5)))", long(63)))
        )
    );
    assert_eq!(emitted(&id(&long(64), vec![])), long(64));
    assert!(emitted(&id(&long(65), vec![])).starts_with(&format!("{}$0h", long(65))));
    let pow10 = |k: usize| int(&format!("1{}", "0".repeat(k)));
    assert_eq!(
        emitted(&id("M", vec![Value::Int(pow10(61))])),
        format!("M$1{}", "0".repeat(61))
    );
    assert!(emitted(&id("M", vec![Value::Int(pow10(62))])).starts_with("M$0h"));
    let pow2 = Int::from_u64(1).shl(300);
    assert!(emitted(&id("M", vec![Value::Int(pow2)])).starts_with("M$0h"));
    // A keyword module without arguments keeps the readable form.
    assert!(module_name(sha16, &id("add", vec![]), "").rest.is_empty());
}

/// The sizes that the charges read equal the lengths of the texts.
#[test]
fn the_sizes_equal_the_lengths() {
    let ids = [
        id("C", vec![]),
        id("Counter", vec![Value::Int(int("8")), Value::Bool(true)]),
        id(
            "M",
            vec![Value::Str("a\"b\n".into()), Value::Int(int("-5"))],
        ),
        id("M", vec![Value::Type(Ty::UInt(8)), uint(8, 3), sint(4, 15)]),
    ];
    for i in &ids {
        let parts: Vec<String> = i.args.iter().map(Value::serialize).collect();
        assert_eq!(
            InstantiationId::render_size(&i.module, &parts),
            i.serialize().len() as u64
        );
        let n = module_name(sha16, i, &i.serialize());
        assert_eq!(n.byte_size(), encode(&n).len() as u64);
    }
}

/// Each emitted name is a legal core name with the round trip.
#[test]
fn each_emitted_name_is_legal() {
    for i in [
        id("Counter", vec![Value::Int(int("8"))]),
        id("add", vec![]),
        id("M", vec![Value::Str("x".into())]),
        id(&"a".repeat(70), vec![]),
    ] {
        let n = module_name(sha16, &i, &i.serialize());
        assert!(legal(&n) && round_trip(&n), "{n:?}");
    }
}

fn arb_user() -> impl Strategy<Value = String> {
    prop_oneof![
        "[A-Za-z_][A-Za-z0-9_]{0,6}",
        proptest::sample::select(KEYWORDS.to_vec()).prop_map(str::to_owned),
    ]
}

fn arb_field() -> impl Strategy<Value = Field> {
    prop_oneof![
        arb_user().prop_map(Field::User),
        any::<i64>().prop_map(|n| Field::Int(if n < 0 {
            Int::from_u64(n.unsigned_abs()).neg()
        } else {
            Int::from_u64(n.unsigned_abs())
        })),
        any::<u64>().prop_map(Field::Call),
        any::<u64>().prop_map(Field::Version),
        any::<bool>().prop_map(Field::Bool),
        "[0-9a-f]{1,16}".prop_map(Field::Digest),
        any::<u64>().prop_map(Field::Temp),
        proptest::sample::select(ROLES.to_vec()).prop_map(Field::Role),
    ]
}

proptest! {
    #[test]
    fn the_round_trip_on_random_names(
        head in arb_user(),
        rest in proptest::collection::vec(arb_field(), 0..5),
    ) {
        let p = Name { head, rest };
        prop_assert!(p.valid());
        prop_assert!(round_trip(&p));
        prop_assert!(legal(&p));
        prop_assert_eq!(p.byte_size(), encode(&p).len() as u64);
    }
}
