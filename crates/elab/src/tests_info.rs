// SPDX-License-Identifier: Apache-2.0
//! The cases of `Silicon.Source.Test.Eval` for `@typeInfo`: the record of each kind, its exact
//! cost, and the errors of the argument with their positions and texts. The expected values are
//! the output of Lean `silicon-check eval`. The units are its least fuel less the size of the
//! result, which the command charges after the evaluation.

use crate::tests::{exact, message, out};

/// The result of `eval` with the default budgets.
fn o(expr: &str) -> String {
    out(ITEMS, expr, 100_000_000, 1000)
}

const ITEMS: &str = "struct P {\n\
    \x20   a: UInt[8],\n\
    \x20   b: (Bool, UInt[4]),\n\
    }\n\
    struct G(comptime T: Type) {\n\
    \x20   v: T,\n\
    }\n\
    enum E: UInt[2] {\n\
    \x20   A = 0,\n\
    \x20   B(UInt[8]) = 1,\n\
    \x20   C(Bool, UInt[4]) = 2,\n\
    }\n\
    type BU = (Bool, UInt[4]);\n\
    fn note() -> Type {\n\
    \x20   diagnostic(\"k\", 0);\n\
    \x20   return Bool;\n\
    }";

#[test]
fn the_record_of_a_type_follows_the_kind() {
    assert_eq!(
        o("@typeInfo(Bool)"),
        "(record (struct prelude TypeInfo ()) ((string \"bool\") (list (struct prelude FieldInfo ()) ()) (type unit) (int 0) (int 1) (list (struct prelude VariantInfo ()) ())))"
    );
    assert_eq!(
        o("@typeInfo([UInt[8]; 4])"),
        "(record (struct prelude TypeInfo ()) ((string \"array\") (list (struct prelude FieldInfo ()) ()) (type (uint 8)) (int 4) (int 0) (list (struct prelude VariantInfo ()) ())))"
    );
    assert_eq!(
        o("@typeInfo(BU)"),
        "(record (struct prelude TypeInfo ()) ((string \"tuple\") (list (struct prelude FieldInfo ()) ((record (struct prelude FieldInfo ()) ((string \"0\") (type bool))) (record (struct prelude FieldInfo ()) ((string \"1\") (type (uint 4)))))) (type unit) (int 2) (int 0) (list (struct prelude VariantInfo ()) ())))"
    );
    assert_eq!(
        o("@typeInfo(P)"),
        "(record (struct prelude TypeInfo ()) ((string \"record\") (list (struct prelude FieldInfo ()) ((record (struct prelude FieldInfo ()) ((string \"a\") (type (uint 8)))) (record (struct prelude FieldInfo ()) ((string \"b\") (type (tuple (bool (uint 4)))))))) (type unit) (int 2) (int 0) (list (struct prelude VariantInfo ()) ())))"
    );
    assert_eq!(
        o("@typeInfo(E)"),
        "(record (struct prelude TypeInfo ()) ((string \"enum\") (list (struct prelude FieldInfo ()) ()) (type (uint 2)) (int 0) (int 10) (list (struct prelude VariantInfo ()) ((record (struct prelude VariantInfo ()) ((string \"A\") (int 0) (list type ()))) (record (struct prelude VariantInfo ()) ((string \"B\") (int 1) (list type ((type (uint 8)))))) (record (struct prelude VariantInfo ()) ((string \"C\") (int 2) (list type ((type bool) (type (uint 4))))))))))"
    );
    assert_eq!(
        o("@typeInfo(Mem[P, 4])"),
        "(record (struct prelude TypeInfo ()) ((string \"mem\") (list (struct prelude FieldInfo ()) ()) (type (struct root P ())) (int 4) (int 0) (list (struct prelude VariantInfo ()) ())))"
    );
    assert_eq!(
        o("@typeInfo(fn (Nat) -> Bool)"),
        "(record (struct prelude TypeInfo ()) ((string \"function\") (list (struct prelude FieldInfo ()) ()) (type unit) (int 0) (int 0) (list (struct prelude VariantInfo ()) ())))"
    );
    assert_eq!(
        o("@typeInfo(@typeInfo(P).fields[1].ty)"),
        "(record (struct prelude TypeInfo ()) ((string \"tuple\") (list (struct prelude FieldInfo ()) ((record (struct prelude FieldInfo ()) ((string \"0\") (type bool))) (record (struct prelude FieldInfo ()) ((string \"1\") (type (uint 4)))))) (type unit) (int 2) (int 0) (list (struct prelude VariantInfo ()) ())))"
    );
}

#[test]
fn the_cost_of_the_record_is_exact() {
    exact(ITEMS, "@typeInfo(Bool)", 95);
    exact(ITEMS, "@typeInfo(UInt[8])", 100);
    exact(ITEMS, "@typeInfo(Unit)", 95);
    exact(ITEMS, "@typeInfo(Nat)", 94);
    exact(ITEMS, "@typeInfo([UInt[8]; 4])", 112);
    exact(ITEMS, "@typeInfo(BU)", 131);
    exact(ITEMS, "@typeInfo(P)", 154);
    exact(ITEMS, "@typeInfo(G[UInt[8]])", 125);
    exact(ITEMS, "@typeInfo(E)", 190);
    exact(ITEMS, "@typeInfo(List[Nat])", 99);
    exact(ITEMS, "@typeInfo(Mem[P, 4])", 144);
    exact(ITEMS, "@typeInfo(Reg[P])", 141);
    exact(ITEMS, "@typeInfo(fn (Nat) -> Bool)", 104);
    exact(ITEMS, "@typeInfo(ReadResponse[UInt[8]])", 142);
    exact(ITEMS, "@typeInfo(@typeInfo(P).fields[1].ty)", 183);
}

#[test]
fn an_argument_that_is_no_type_is_s010_at_the_argument() {
    assert_eq!(o("@typeInfo(3)"), "S010 1:11");
    assert_eq!(
        message(ITEMS, "@typeInfo(3)"),
        "`@typeInfo` takes a type, not a value of `Int`; bind the value with `let x = ...;` and use `@typeInfo(@TypeOf(x))`"
    );
    assert_eq!(o("@typeInfo(P())"), "S010 1:11");
    assert_eq!(
        message(ITEMS, "@typeInfo(P())"),
        "`@typeInfo` takes a type, not a value of `P`; bind the value with `let x = ...;` and use `@typeInfo(@TypeOf(x))`"
    );
    assert_eq!(o("@typeInfo((Bool, UInt[8]))"), "S010 1:11");
    assert_eq!(
        message(ITEMS, "@typeInfo((Bool, UInt[8]))"),
        "`@typeInfo` takes a type, not a value of `(Type, Type)`; name the tuple type with `type T = (A, B);` and use `@typeInfo(T)`"
    );
    assert_eq!(o("@typeInfo([Bool, Bool])"), "S010 1:11");
    assert_eq!(
        message(ITEMS, "@typeInfo([Bool, Bool])"),
        "`@typeInfo` takes a type, not a value of `[Type; 2]`; name the array type with `type T = [A; N];` and use `@typeInfo(T)`"
    );
    assert_eq!(o("@typeInfo([])"), "S010 1:11");
    assert_eq!(
        message(ITEMS, "@typeInfo([])"),
        "`@typeInfo` takes a type, not `[]`; bind the value with `let x = ...;` and use `@typeInfo(@TypeOf(x))`"
    );
    assert_eq!(o("@typeInfo(note())"), "S016 15:5");
    assert_eq!(
        message(ITEMS, "@typeInfo(note())"),
        "an argument of `@typeInfo` has no graph effect such as `diagnostic`; call `diagnostic` before `@typeInfo`, keep the result in a `let`, and use that name in the argument"
    );
    assert_eq!(o("@typeInfo(P.a)"), "S010 1:11");
    assert_eq!(message(ITEMS, "@typeInfo(P.a)"), "a type has no field `a`");
}

#[test]
fn the_depth_of_the_record_is_checked_before_its_size_charges() {
    let at = |depth: u64| out(ITEMS, "@typeInfo(P)", 100_000_000, depth);
    // The first depths fail in the use of `TypeInfo`, at the position of its field types and of the
    // argument. A larger depth fails at the `@` with the depth of the record.
    assert_eq!(at(1), "S015 3:8");
    assert_eq!(at(2), "S015 1:11");
    assert_eq!(at(3), "S015 1:1");
    assert_eq!(at(5), "S015 1:1");
    assert!(at(6).starts_with("(record"));
    assert_eq!(
        crate::tests::message_with(
            ITEMS,
            "@typeInfo(P)",
            crate::Budget {
                fuel: 100_000_000,
                depth: 5
            }
        ),
        "the depth 6 goes above the nesting depth 5; raise --depth to at least 6"
    );
}
