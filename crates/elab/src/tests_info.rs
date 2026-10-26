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

const USER_FIELD_INFO: &str = "struct FieldInfo {\n\
    \x20   name: String,\n\
    \x20   ty: Type,\n\
    }";

const AB: &str = r#"@Struct([FieldInfo("a", UInt[8]), FieldInfo("b", Bool)])"#;

#[test]
fn a_struct_gives_a_generated_record_type() {
    assert_eq!(o(AB), "(type (gstruct ((\"a\" (uint 8)) (\"b\" bool))))");
    assert_eq!(o("@Struct([])"), "(type (gstruct ()))");
    assert_eq!(
        o(r#"@Struct([FieldInfo("a", @Struct([FieldInfo("x", Bool)]))])"#),
        "(type (gstruct ((\"a\" (gstruct ((\"x\" bool)))))))"
    );
    assert_eq!(
        o(r#"@Struct([FieldInfo("a", UInt[8])])(7)"#),
        "(record (gstruct ((\"a\" (uint 8)))) ((uint 8 7)))"
    );
    assert_eq!(
        o(&format!("{AB}()")),
        "(record (gstruct ((\"a\" (uint 8)) (\"b\" bool))) ((uint 8 0) (bool false)))"
    );
    assert_eq!(o(&format!("data_bits({AB})")), "(int 9)");
}

#[test]
fn a_generated_record_type_is_equal_by_its_field_list() {
    let same = r#"@Struct([FieldInfo("a", UInt[8])]) == @Struct([FieldInfo("a", UInt[8])])"#;
    assert_eq!(o(same), "(bool true)");
    let other = r#"@Struct([FieldInfo("a", UInt[8])]) == @Struct([FieldInfo("b", UInt[8])])"#;
    assert_eq!(o(other), "(bool false)");
    // A declared struct stays nominal.
    assert_eq!(o("@Struct(@typeInfo(P).fields) == P"), "(bool false)");
    let round = format!("@Struct(@typeInfo({AB}).fields) == {AB}");
    assert_eq!(o(&round), "(bool true)");
}

#[test]
fn the_cost_of_a_struct_is_exact() {
    exact(ITEMS, AB, 96);
    exact(ITEMS, "@Struct([])", 24);
    exact(
        ITEMS,
        r#"@Struct([FieldInfo("a", @Struct([FieldInfo("x", Bool)]))])"#,
        107,
    );
    exact(ITEMS, r#"@Struct([FieldInfo("a", UInt[8])])(7)"#, 72);
    exact(ITEMS, &format!("{AB}()"), 100);
    exact(ITEMS, &format!("data_bits({AB})"), 99);
    exact(ITEMS, "@Struct(@typeInfo(P).fields) == P", 210);
    exact(
        ITEMS,
        r#"@Struct([FieldInfo("a", UInt[8])]) == @Struct([FieldInfo("a", UInt[8])])"#,
        124,
    );
    exact(
        ITEMS,
        r#"@typeInfo(@Struct([FieldInfo("a", UInt[8])]))"#,
        151,
    );
}

#[test]
fn the_errors_of_struct_have_their_positions_and_texts() {
    let at = |e: &str, code: &str| {
        assert_eq!(o(e), code, "{e}");
    };
    at(r#"@Struct([FieldInfo("1a", Bool)])"#, "S022 1:1");
    assert_eq!(
        message(ITEMS, r#"@Struct([FieldInfo("1a", Bool)])"#),
        "`1a` is not a valid field name; use an ASCII letter or `_`, then letters, digits, or `_`"
    );
    at(r#"@Struct([FieldInfo("fn", Bool)])"#, "S022 1:1");
    assert_eq!(
        message(ITEMS, r#"@Struct([FieldInfo("fn", Bool)])"#),
        "`fn` is a keyword, so it cannot be a field name; choose another name"
    );
    let twice = r#"@Struct([FieldInfo("a", Bool), FieldInfo("b", Bool), FieldInfo("a", Bool)])"#;
    at(twice, "S022 1:1");
    assert_eq!(
        message(ITEMS, twice),
        "the field `a` occurs at the indices 0 and 2 of `@Struct`; give each field its own name"
    );
    // The tuple names of `@typeInfo` break the name rule.
    at("@Struct(@typeInfo(BU).fields)", "S022 1:1");
    assert_eq!(
        message(ITEMS, "@Struct(@typeInfo(BU).fields)"),
        "`0` is not a valid field name; use an ASCII letter or `_`, then letters, digits, or `_`"
    );
    at("@Struct(3)", "S010 1:9");
    assert_eq!(
        message(ITEMS, "@Struct(3)"),
        "`@Struct` takes a `List[FieldInfo]` or a `[FieldInfo; N]`, not a value of `Int`; build each field with the prelude `FieldInfo(name, ty)`"
    );
    at("@Struct([[]])", "S010 1:9");
    assert_eq!(
        message(ITEMS, "@Struct([[]])"),
        "`@Struct` takes a `List[FieldInfo]` or a `[FieldInfo; N]`, not `[]`; build each field with the prelude `FieldInfo(name, ty)`"
    );
}

#[test]
fn a_user_field_info_hides_the_prelude_one() {
    let e = r#"@Struct([FieldInfo("a", Bool)])"#;
    assert_eq!(out(USER_FIELD_INFO, e, 100_000_000, 1000), "S010 1:9");
    assert_eq!(
        message(USER_FIELD_INFO, e),
        "`@Struct` takes the prelude `FieldInfo`, not a value of `[crate::FieldInfo; 1]`; a user struct `FieldInfo` hides the prelude one, so rename it, or take the fields from `@typeInfo(T).fields`"
    );
}

#[test]
fn a_name_charges_its_characters_before_the_name_rule() {
    // `aé` has 2 characters and 3 bytes, so the name charges 3 units, not 4.
    let e = r#"@Struct([FieldInfo("aé", Bool)])"#;
    let at = |fuel: u64| out(ITEMS, e, fuel, 1000);
    assert_eq!(at(48), "S022 1:1");
    assert_eq!(at(47), "S015 1:1");
    assert_eq!(
        message(ITEMS, e),
        "`aé` is not a valid field name; use an ASCII letter or `_`, then letters, digits, or `_`"
    );
}

#[test]
fn a_message_names_a_generated_record_type_by_its_fields() {
    let m = |e: &str| message(ITEMS, e);
    assert_eq!(
        m(&format!("UInt[8]({AB}())")),
        "expected UInt[8], but the value is @Struct { a: UInt[8], b: Bool }"
    );
    assert_eq!(
        m("UInt[8](@Struct([])())"),
        "expected UInt[8], but the value is @Struct {}"
    );
    assert_eq!(
        m(r#"UInt[8](@Struct([FieldInfo("a", @Struct([FieldInfo("x", Bool)]))])())"#),
        "expected UInt[8], but the value is @Struct { a: @Struct { x: Bool } }"
    );
    // A name has the limit of a string in a message.
    let long = "a".repeat(65);
    assert_eq!(
        m(&format!(
            r#"UInt[8](@Struct([FieldInfo("{long}", Bool)])())"#
        )),
        format!(
            "expected UInt[8], but the value is @Struct {{ {}... (65 characters): Bool }}",
            "a".repeat(64)
        )
    );
    assert_eq!(
        m(r#"@Struct([FieldInfo("a", UInt[8]), FieldInfo("b", Bool)])(1, 2, 3)"#),
        "a struct constructor takes 0 or 2 argument(s), but it has 3; pass one value for each field, or none for the zero"
    );
}
