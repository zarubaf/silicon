// SPDX-License-Identifier: Apache-2.0
//! The AST dump of section 11.1 of the front-end design. The bytes follow the module doc of
//! `Silicon/Source/Print.lean`, which is the normative text.
//!
//! The dump recurses over the AST, so its depth of calls is at most about twice the syntax
//! depth of the parse that made the AST. `Parse::dump` runs it on a stack for that depth.

use crate::ast::{Expr, Ident, Item, Param, Stmt, StructField, TypeExpr};
use std::fmt::{Debug, Write};

/// The dump of a file: one line for each item, and an LF ends each line.
#[must_use]
pub(crate) fn dump(items: &[Item]) -> String {
    let mut out = String::new();
    for item in items {
        item_dump(item, &mut out);
        out.push('\n');
    }
    out
}

/// A string literal with the escapes of the grammar, as `Print.quote` in Lean writes it. The
/// AST dump and the serialization of a static string share it.
pub fn quote(text: &str, out: &mut String) {
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// The name of a constructor: its Lean name is the lowercase name of the variant.
fn constructor(value: &impl Debug, out: &mut String) {
    write!(out, "{}", format!("{value:?}").to_ascii_lowercase()).ok();
}

fn boolean(value: bool, out: &mut String) {
    out.push_str(if value { "true" } else { "false" });
}

fn ident(name: &Ident, out: &mut String) {
    quote(&name.name, out);
}

/// A node: `(name` and the fields, each after a space, and `)`.
fn node(name: &str, out: &mut String, fields: impl FnOnce(&mut String)) {
    out.push('(');
    out.push_str(name);
    fields(out);
    out.push(')');
}

/// A list: `(` the elements with one space between two, and `)`.
fn list<T>(items: &[T], out: &mut String, each: impl Fn(&T, &mut String)) {
    out.push('(');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        each(item, out);
    }
    out.push(')');
}

/// `none`, or `(some <value>)`.
fn option<T>(value: Option<&T>, out: &mut String, each: impl FnOnce(&T, &mut String)) {
    match value {
        None => out.push_str("none"),
        Some(value) => node("some", out, |out| {
            out.push(' ');
            each(value, out);
        }),
    }
}

fn expr(e: &Expr, out: &mut String) {
    let sp = |out: &mut String| out.push(' ');
    match e {
        Expr::Num { value, .. } => node("num", out, |out| {
            sp(out);
            out.push_str(value.as_str());
        }),
        Expr::Bool { value, .. } => node("bool", out, |out| {
            sp(out);
            boolean(*value, out);
        }),
        Expr::Str { value, .. } => node("str", out, |out| {
            sp(out);
            quote(value, out);
        }),
        Expr::Name { name, .. } => node("name", out, |out| {
            sp(out);
            quote(name, out);
        }),
        Expr::Unary { op, arg, .. } => node("unary", out, |out| {
            sp(out);
            constructor(op, out);
            sp(out);
            expr(arg, out);
        }),
        Expr::Binary { op, lhs, rhs, .. } => node("binary", out, |out| {
            sp(out);
            constructor(op, out);
            sp(out);
            expr(lhs, out);
            sp(out);
            expr(rhs, out);
        }),
        Expr::Cond { cond, yes, no, .. } => node("cond", out, |out| {
            for part in [cond, yes, no] {
                sp(out);
                expr(part, out);
            }
        }),
        Expr::Call { callee, args, .. } => node("call", out, |out| {
            sp(out);
            expr(callee, out);
            sp(out);
            list(args, out, expr);
        }),
        Expr::Method {
            recv, name, args, ..
        } => node("method", out, |out| {
            sp(out);
            expr(recv, out);
            sp(out);
            ident(name, out);
            sp(out);
            list(args, out, expr);
        }),
        Expr::Index { base, args, .. } => node("index", out, |out| {
            sp(out);
            expr(base, out);
            sp(out);
            list(args, out, expr);
        }),
        Expr::Field { base, field, .. } => node("field", out, |out| {
            sp(out);
            expr(base, out);
            sp(out);
            ident(field, out);
        }),
        Expr::Unit { .. } => node("unit", out, |_| {}),
        Expr::Tuple { elems, .. } => node("tuple", out, |out| {
            sp(out);
            list(elems, out, expr);
        }),
        Expr::Array { elems, .. } => node("array", out, |out| {
            sp(out);
            list(elems, out, expr);
        }),
        Expr::Select { base, index, .. } => node("select", out, |out| {
            sp(out);
            expr(base, out);
            sp(out);
            out.push_str(index.as_str());
        }),
        Expr::ArrayType { elem, len, .. } => node("arraytype", out, |out| {
            sp(out);
            type_expr(elem, out);
            sp(out);
            expr(len, out);
        }),
    }
}

fn type_expr(t: &TypeExpr, out: &mut String) {
    match t {
        TypeExpr::Name { name, .. } => node("name", out, |out| {
            out.push(' ');
            quote(name, out);
        }),
        TypeExpr::Index { base, args, .. } => node("index", out, |out| {
            out.push(' ');
            type_expr(base, out);
            out.push(' ');
            list(args, out, expr);
        }),
        TypeExpr::Unit { .. } => node("unit", out, |_| {}),
        TypeExpr::Tuple { elems, .. } => node("tuple", out, |out| {
            out.push(' ');
            list(elems, out, type_expr);
        }),
        TypeExpr::Array { elem, len, .. } => node("array", out, |out| {
            out.push(' ');
            type_expr(elem, out);
            out.push(' ');
            expr(len, out);
        }),
    }
}

/// The fields of a node, each after a space.
macro_rules! fields {
    ($out:ident; $($part:expr),* $(,)?) => {{
        $( $out.push(' '); $part; )*
    }};
}

fn stmt(s: &Stmt, out: &mut String) {
    match s {
        Stmt::Local {
            mutable,
            name,
            ty,
            value,
            ..
        } => node("local", out, |out| {
            fields!(out; boolean(*mutable, out), ident(name, out),
                option(ty.as_ref(), out, type_expr), expr(value, out));
        }),
        Stmt::Assign { target, value, .. } => node("assign", out, |out| {
            fields!(out; expr(target, out), expr(value, out));
        }),
        Stmt::Connect { target, value, .. } => node("connect", out, |out| {
            fields!(out; expr(target, out), expr(value, out));
        }),
        Stmt::Reg { name, ty, init, .. } => node("reg", out, |out| {
            fields!(out; ident(name, out), type_expr(ty, out), expr(init, out));
        }),
        Stmt::Wire { name, ty, .. } => node("wire", out, |out| {
            fields!(out; ident(name, out), type_expr(ty, out));
        }),
        Stmt::Input { name, ty, .. } => node("input", out, |out| {
            fields!(out; ident(name, out), type_expr(ty, out));
        }),
        Stmt::Output { name, ty, .. } => node("output", out, |out| {
            fields!(out; ident(name, out), type_expr(ty, out));
        }),
        Stmt::Inst {
            name, module, args, ..
        } => node("inst", out, |out| {
            fields!(out; ident(name, out), ident(module, out), list(args, out, expr));
        }),
        Stmt::Ret { value, .. } => node("ret", out, |out| {
            fields!(out; option(value.as_ref(), out, expr));
        }),
        Stmt::CtIf { cond, yes, no, .. } => node("ctif", out, |out| {
            fields!(out; expr(cond, out), list(yes, out, stmt),
                option(no.as_ref(), out, |no, out| list(no, out, stmt)));
        }),
        Stmt::CtFor {
            var, lo, hi, body, ..
        } => node("ctfor", out, |out| {
            fields!(out; ident(var, out), expr(lo, out), expr(hi, out), list(body, out, stmt));
        }),
        Stmt::Block { body, .. } => node("block", out, |out| {
            fields!(out; list(body, out, stmt));
        }),
        Stmt::Expr { value, .. } => node("expr", out, |out| {
            fields!(out; expr(value, out));
        }),
        Stmt::Alias { name, ty, .. } => node("alias", out, |out| {
            fields!(out; ident(name, out), type_expr(ty, out));
        }),
    }
}

fn param(p: &Param, out: &mut String) {
    node("param", out, |out| {
        fields!(out; constructor(&p.mode, out), ident(&p.name, out), type_expr(&p.ty, out));
    });
}

fn struct_field(f: &StructField, out: &mut String) {
    node("structfield", out, |out| {
        fields!(out; ident(&f.name, out), type_expr(&f.ty, out));
    });
}

fn item_dump(item: &Item, out: &mut String) {
    match item {
        Item::Const {
            name, ty, value, ..
        } => node("const", out, |out| {
            fields!(out; ident(name, out), type_expr(ty, out), expr(value, out));
        }),
        Item::Fn {
            comptime,
            name,
            params,
            ret,
            body,
            ..
        } => node("fn", out, |out| {
            fields!(out; boolean(*comptime, out), ident(name, out), list(params, out, param),
                type_expr(ret, out), list(body, out, stmt));
        }),
        Item::Module {
            name,
            params,
            domains,
            body,
            ..
        } => node("module", out, |out| {
            fields!(out; ident(name, out), list(params, out, param),
                option(domains.as_ref(), out, |ds, out| list(ds, out, ident)),
                list(body, out, stmt));
        }),
        Item::Struct {
            name,
            params,
            fields,
            ..
        } => node("struct", out, |out| {
            fields!(out; ident(name, out), list(params, out, param),
                list(fields, out, struct_field));
        }),
        Item::Alias { name, ty, .. } => node("alias", out, |out| {
            fields!(out; ident(name, out), type_expr(ty, out));
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::dump;
    use crate::parse;

    /// The dump of a source text that has no error.
    fn dump_of(source: &str) -> String {
        let parsed = parse(source).unwrap();
        assert!(parsed.errors.is_empty(), "{source}: {:?}", parsed.errors);
        dump(parsed.ast.as_deref().unwrap_or_default())
    }

    /// The dump of the expression `e` in a constant.
    fn expr_of(e: &str) -> String {
        let text = dump_of(&format!("const X: T = {e};"));
        let body = text
            .strip_prefix("(const \"X\" (name \"T\") ")
            .unwrap_or(&text);
        body.strip_suffix(")\n").unwrap_or(body).to_owned()
    }

    /// The dump of the statement `s` in a module.
    fn stmt_of(s: &str) -> String {
        let text = dump_of(&format!("module M() {{ {s} }}"));
        let body = text
            .strip_prefix("(module \"M\" () none (")
            .unwrap_or(&text);
        body.strip_suffix("))\n").unwrap_or(body).to_owned()
    }

    #[test]
    fn no_items_dump_to_nothing() {
        assert_eq!(dump_of(""), "");
        assert_eq!(dump_of("// a\n"), "");
    }

    #[test]
    fn expressions() {
        assert_eq!(expr_of("42"), "(num 42)");
        assert_eq!(expr_of("0xff"), "(num 255)");
        assert_eq!(expr_of("0b101"), "(num 5)");
        assert_eq!(expr_of("007"), "(num 7)");
        assert_eq!(expr_of("true"), "(bool true)");
        assert_eq!(expr_of("false"), "(bool false)");
        assert_eq!(expr_of("\"a\""), "(str \"a\")");
        assert_eq!(expr_of("x"), "(name \"x\")");
        assert_eq!(expr_of("!x"), "(unary not (name \"x\"))");
        assert_eq!(expr_of("~x"), "(unary inv (name \"x\"))");
        assert_eq!(expr_of("-x"), "(unary neg (name \"x\"))");
        assert_eq!(expr_of("a +% b"), "(binary addw (name \"a\") (name \"b\"))");
        assert_eq!(
            expr_of("if (c) { 1 } else { 2 }"),
            "(cond (name \"c\") (num 1) (num 2))"
        );
        assert_eq!(expr_of("f()"), "(call (name \"f\") ())");
        assert_eq!(expr_of("f(1, 2)"), "(call (name \"f\") ((num 1) (num 2)))");
        assert_eq!(expr_of("a[1]"), "(index (name \"a\") ((num 1)))");
        assert_eq!(expr_of("a.b"), "(field (name \"a\") \"b\")");
    }

    #[test]
    fn every_binary_operator_has_its_name() {
        let ops = [
            ("||", "lor"),
            ("&&", "land"),
            ("|", "or"),
            ("^", "xor"),
            ("&", "and"),
            ("==", "eq"),
            ("!=", "ne"),
            ("<", "lt"),
            ("<=", "le"),
            (">", "gt"),
            (">=", "ge"),
            ("<<", "shl"),
            (">>", "shr"),
            ("+", "add"),
            ("-", "sub"),
            ("+%", "addw"),
            ("-%", "subw"),
            ("*", "mul"),
            ("/", "div"),
            ("%", "rem"),
            ("*%", "mulw"),
        ];
        for (op, name) in ops {
            assert_eq!(
                expr_of(&format!("a {op} b")),
                format!("(binary {name} (name \"a\") (name \"b\"))")
            );
        }
    }

    #[test]
    fn strings_escape_like_the_grammar() {
        assert_eq!(
            expr_of(r#""a\"b\\c\nd\re\tf""#),
            r#"(str "a\"b\\c\nd\re\tf")"#
        );
        assert_eq!(expr_of("\"é∀\""), "(str \"é∀\")");
    }

    #[test]
    fn a_number_has_any_size() {
        let big = "123456789012345678901234567890";
        assert_eq!(expr_of(big), format!("(num {big})"));
    }

    #[test]
    fn statements() {
        assert_eq!(stmt_of("let x = 1;"), "(local false \"x\" none (num 1))");
        assert_eq!(
            stmt_of("let mut x: UInt[8] = 1;"),
            "(local true \"x\" (some (index (name \"UInt\") ((num 8)))) (num 1))"
        );
        assert_eq!(stmt_of("x = 1;"), "(assign (name \"x\") (num 1))");
        assert_eq!(stmt_of("x := 1;"), "(connect (name \"x\") (num 1))");
        assert_eq!(stmt_of("reg r: T = 0;"), "(reg \"r\" (name \"T\") (num 0))");
        assert_eq!(stmt_of("wire w: T;"), "(wire \"w\" (name \"T\"))");
        assert_eq!(stmt_of("input i: T;"), "(input \"i\" (name \"T\"))");
        assert_eq!(stmt_of("output o: T;"), "(output \"o\" (name \"T\"))");
        assert_eq!(
            stmt_of("instance u = Child(1);"),
            "(inst \"u\" \"Child\" ((num 1)))"
        );
        assert_eq!(stmt_of("return;"), "(ret none)");
        assert_eq!(stmt_of("return 1;"), "(ret (some (num 1)))");
        assert_eq!(
            stmt_of("comptime if (c) { x; }"),
            "(ctif (name \"c\") ((expr (name \"x\"))) none)"
        );
        assert_eq!(
            stmt_of("comptime if (c) { } else { x; }"),
            "(ctif (name \"c\") () (some ((expr (name \"x\")))))"
        );
        assert_eq!(
            stmt_of("comptime for i in 0 .. 4 { x; }"),
            "(ctfor \"i\" (num 0) (num 4) ((expr (name \"x\"))))"
        );
        assert_eq!(stmt_of("{ }"), "(block ())");
        assert_eq!(stmt_of("x;"), "(expr (name \"x\"))");
        assert_eq!(stmt_of("x; y;"), "(expr (name \"x\")) (expr (name \"y\"))");
    }

    #[test]
    fn type_forms() {
        assert_eq!(
            expr_of("[UInt[8]; 4]"),
            "(arraytype (index (name \"UInt\") ((num 8))) (num 4))"
        );
        assert_eq!(
            expr_of("[T; 4]()"),
            "(call (arraytype (name \"T\") (num 4)) ())"
        );
        assert_eq!(
            stmt_of("type A = [UInt[8]; 4];"),
            "(alias \"A\" (array (index (name \"UInt\") ((num 8))) (num 4)))"
        );
        assert_eq!(
            dump_of("struct P(comptime W: Nat) { a: UInt[W], b: Bool, }"),
            "(struct \"P\" ((param true \"W\" (name \"Nat\"))) ((structfield \"a\" \
             (index (name \"UInt\") ((name \"W\")))) (structfield \"b\" (name \"Bool\"))))\n"
        );
        assert_eq!(dump_of("struct P {}"), "(struct \"P\" () ())\n");
        assert_eq!(dump_of("struct P() {}"), "(struct \"P\" () ())\n");
        assert_eq!(
            dump_of("type A = (T, U);"),
            "(alias \"A\" (tuple ((name \"T\") (name \"U\"))))\n"
        );
    }

    #[test]
    fn items() {
        assert_eq!(
            dump_of("const C: T = 1;\nconst D: T = 2;"),
            "(const \"C\" (name \"T\") (num 1))\n(const \"D\" (name \"T\") (num 2))\n"
        );
        assert_eq!(
            dump_of("fn f() -> T { }"),
            "(fn false \"f\" () (name \"T\") ())\n"
        );
        assert_eq!(
            dump_of("comptime fn f(a: T, comptime n: Nat) -> T { return a; }"),
            "(fn true \"f\" ((param false \"a\" (name \"T\")) (param true \"n\" (name \"Nat\"))) \
             (name \"T\") ((ret (some (name \"a\")))))\n"
        );
        assert_eq!(
            dump_of("module M(comptime n: Nat) { }"),
            "(module \"M\" ((param true \"n\" (name \"Nat\"))) none ())\n"
        );
        assert_eq!(
            dump_of("module M() domains(clk) { }"),
            "(module \"M\" () (some (\"clk\")) ())\n"
        );
    }
}
