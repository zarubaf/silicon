// SPDX-License-Identifier: Apache-2.0
use crate::ast::{BuiltinArgs, Expr, FnParam, Item, ParamMode, PortForm, Pos, Stmt, TypeExpr};
use crate::{Code, DEFAULT_SYNTAX_DEPTH, Parse};
use proptest::prelude::*;

/// Parses with the default syntax depth. The stack is virtual memory, so the tests expect it.
fn parse(input: &str) -> Parse {
    crate::parse(input).unwrap()
}

fn parse_with_depth(input: &str, depth: usize) -> Parse {
    crate::parse_with_depth(input, depth).unwrap()
}

fn pos(line: usize, col: usize) -> Pos {
    Pos { line, col }
}

/// The first error as code, line, and column.
fn first_error(input: &str) -> Option<(Code, usize, usize)> {
    parse(input)
        .errors
        .first()
        .map(|e| (e.code, e.pos.line, e.pos.col))
}

/// The first error as code, line, and column, with a syntax depth of 64.
fn first_error_64(input: &str) -> Option<(Code, usize, usize)> {
    parse_with_depth(input, 64)
        .errors
        .first()
        .map(|e| (e.code, e.pos.line, e.pos.col))
}

/// An expression as a short S-expression, to compare shapes.
fn sx(e: &Expr) -> String {
    let list = |xs: &[Expr]| xs.iter().map(sx).collect::<Vec<_>>().join(" ");
    match e {
        Expr::Num { value, .. } => value.as_str().to_owned(),
        Expr::Bool { value, .. } => value.to_string(),
        Expr::Str { value, .. } => format!("{value:?}"),
        Expr::Name { name, .. } => name.clone(),
        Expr::Unary { op, arg, .. } => {
            format!("({} {})", format!("{op:?}").to_lowercase(), sx(arg))
        }
        Expr::Binary { op, lhs, rhs, .. } => {
            format!(
                "({} {} {})",
                format!("{op:?}").to_lowercase(),
                sx(lhs),
                sx(rhs)
            )
        }
        Expr::Cond { cond, yes, no, .. } => format!("(if {} {} {})", sx(cond), sx(yes), sx(no)),
        Expr::Call { callee, args, .. } => format!("(call {} {})", sx(callee), list(args)),
        Expr::Index { base, args, .. } => format!("(index {} {})", sx(base), list(args)),
        Expr::Method {
            recv, name, args, ..
        } => format!("(method {} {} {})", sx(recv), name.name, list(args)),
        Expr::Field { base, field, .. } => format!("(field {} {})", sx(base), field.name),
        Expr::Unit { .. } => "()".to_owned(),
        Expr::Tuple { elems, .. } => format!("(tuple {})", list(elems)),
        Expr::Array { elems, .. } => format!("(array {})", list(elems)),
        Expr::Select { base, index, .. } => format!("(select {} {})", sx(base), index.as_str()),
        Expr::Path { ty, variant, .. } => format!("(path {} {})", ty.name, variant.name),
        Expr::Match { scrut, arms, .. } => format!(
            "(match {} {})",
            sx(scrut),
            arms.iter()
                .map(|a| sx(&a.value))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        Expr::Builtin { args, .. } => bx(args),
        Expr::ArrayType { elem, len, .. } => format!("(arraytype {} {})", tx(elem), sx(len)),
        Expr::FnType { params, ret, .. } => format!("(fntype {})", fx(params, ret)),
    }
}

/// A builtin as a short S-expression: `(@name operands)`.
fn bx(args: &BuiltinArgs) -> String {
    format!(
        "(@{} {})",
        args.builtin().name(),
        args.operands().map(sx).collect::<Vec<_>>().join(" ")
    )
}

/// The parameters and the result type of a function type: `[mut ]T ... -> R`.
fn fx(params: &[FnParam], ret: &TypeExpr) -> String {
    let params: Vec<String> = params
        .iter()
        .map(|p| format!("{}{}", if p.mutable { "mut " } else { "" }, tx(&p.ty)))
        .collect();
    format!("({}) -> {}", params.join(" "), tx(ret))
}

/// A type expression as a short S-expression.
fn tx(t: &TypeExpr) -> String {
    let list = |xs: &[Expr]| xs.iter().map(sx).collect::<Vec<_>>().join(" ");
    match t {
        TypeExpr::Name { name, .. } => name.clone(),
        TypeExpr::Index { base, args, .. } => format!("(index {} {})", tx(base), list(args)),
        TypeExpr::Unit { .. } => "()".to_owned(),
        TypeExpr::Tuple { elems, .. } => {
            format!(
                "(tuple {})",
                elems.iter().map(tx).collect::<Vec<_>>().join(" ")
            )
        }
        TypeExpr::Array { elem, len, .. } => format!("(array {} {})", tx(elem), sx(len)),
        TypeExpr::Fn { params, ret, .. } => format!("(fn {})", fx(params, ret)),
        TypeExpr::Builtin { args, .. } => bx(args),
    }
}

/// The AST of `const X: T = <expr>;` as the shape of the expression.
fn shape(expr: &str) -> String {
    let parsed = parse(&format!("const X: T = {expr};"));
    assert!(parsed.errors.is_empty(), "{expr}: {:?}", parsed.errors);
    match parsed.ast.as_deref() {
        Some([Item::Const { value, .. }]) => sx(value),
        other => panic!("{other:?}"),
    }
}

fn body(stmts: &str) -> Vec<Stmt> {
    let parsed = parse(&format!("module M() {{ {stmts} }}"));
    assert!(parsed.errors.is_empty(), "{stmts}: {:?}", parsed.errors);
    match parsed.ast.as_deref() {
        Some([Item::Module { body, .. }]) => body.clone(),
        other => panic!("{other:?}"),
    }
}

fn assert_lossless(parsed: &Parse, input: &str) {
    assert_eq!(parsed.syntax().text().to_string(), input);
}

#[test]
fn empty_and_trivia_only() {
    for input in ["", "  \n", "// x\n/* y */"] {
        let parsed = parse(input);
        assert!(parsed.errors.is_empty());
        assert_eq!(parsed.ast, Some(vec![]));
        assert_lossless(&parsed, input);
    }
}

#[test]
fn const_item() {
    let parsed = parse("const W: Nat = 8;");
    let Some(
        [
            Item::Const {
                pos: p,
                name,
                ty,
                value,
            },
        ],
    ) = parsed.ast.as_deref()
    else {
        panic!("{parsed:?}");
    };
    assert_eq!(*p, pos(1, 1));
    assert_eq!((name.pos, name.name.as_str()), (pos(1, 7), "W"));
    let TypeExpr::Name {
        pos: ty_pos,
        name: ty_name,
        ..
    } = ty
    else {
        panic!("expected a type name");
    };
    assert_eq!((*ty_pos, ty_name.as_str()), (pos(1, 10), "Nat"));
    assert_eq!(sx(value), "8");
}

#[test]
fn name_nodes_have_ids_in_source_order() {
    let parsed = parse("const W: Nat = a + b.c;");
    let Some(
        [
            Item::Const {
                name,
                ty: TypeExpr::Name { id: ty, .. },
                value: Expr::Binary { lhs, rhs, .. },
                ..
            },
        ],
    ) = parsed.ast.as_deref()
    else {
        panic!("{parsed:?}");
    };
    let (Expr::Name { id: a, .. }, Expr::Field { base, field, .. }) = (&**lhs, &**rhs) else {
        panic!("expected `a + b.c`");
    };
    let Expr::Name { id: b, .. } = &**base else {
        panic!("expected `b`");
    };
    let ids = [name.id, *ty, *a, *b, field.id];
    assert!(ids.windows(2).all(|w| w[0] < w[1]), "{ids:?}");
}

#[test]
fn fn_item_and_params() {
    let parsed = parse("comptime fn f(comptime n: Nat, b: Bool,) -> UInt[n] { return n; }");
    let Some(
        [
            Item::Fn {
                pos: p,
                comptime,
                name,
                params,
                ret,
                body,
            },
        ],
    ) = parsed.ast.as_deref()
    else {
        panic!("{parsed:?}");
    };
    assert_eq!(*p, pos(1, 1));
    assert!(*comptime);
    assert_eq!(name.name, "f");
    assert_eq!(params.len(), 2);
    assert_eq!(
        (params[0].mode, params[1].mode),
        (ParamMode::Comptime, ParamMode::None)
    );
    assert_eq!(params[0].pos, pos(1, 15));
    assert!(matches!(ret, TypeExpr::Index { args, .. } if args.len() == 1));
    assert!(matches!(
        body.as_slice(),
        [Stmt::Ret { value: Some(_), .. }]
    ));
    let plain = parse("fn g() -> Bool { }");
    assert!(matches!(
        plain.ast.as_deref(),
        Some([Item::Fn {
            comptime: false,
            ..
        }])
    ));
}

#[test]
fn module_with_domains() {
    let parsed = parse("module M(comptime W: Nat) domains(clk) { }");
    let Some(
        [
            Item::Module {
                params,
                domains,
                body,
                ..
            },
        ],
    ) = parsed.ast.as_deref()
    else {
        panic!("{parsed:?}");
    };
    assert_eq!(params[0].mode, ParamMode::Comptime);
    let domains = domains.as_deref().unwrap_or_default();
    assert_eq!(domains.len(), 1);
    assert_eq!(
        (domains[0].pos, domains[0].name.as_str()),
        (pos(1, 35), "clk")
    );
    assert!(body.is_empty());
    let none = parse("module M() { }");
    assert!(
        matches!(none.ast.as_deref(), Some([Item::Module { domains, .. }]) if domains.is_none())
    );
    let empty = parse("module M() domains() { }");
    assert!(
        matches!(empty.ast.as_deref(), Some([Item::Module { domains: Some(d), .. }]) if d.is_empty())
    );
}

#[test]
fn statements() {
    let stmts = body(
        "let a = 1; let mut b: UInt[8] = 2; input i: Bool; output o: UInt[W + 1]; \
         reg r: UInt[8] = 0; wire w: Bool; instance u = Counter(8, true); \
         b = a; w := i; u.x := o; return; { let c = 1; } f(1);",
    );
    let kinds: Vec<&str> = stmts
        .iter()
        .map(|s| match s {
            Stmt::Local {
                mutable: true,
                ty: Some(_),
                ..
            } => "let mut",
            Stmt::Local { .. } => "let",
            Stmt::Assign { .. } => "assign",
            Stmt::Connect { .. } => "connect",
            Stmt::Reg { .. } => "reg",
            Stmt::Wire { .. } => "wire",
            Stmt::Mem { .. } => "mem",
            Stmt::Input { .. } => "input",
            Stmt::Output { .. } => "output",
            Stmt::Inst { args, .. } if args.len() == 2 => "inst",
            Stmt::Inst { .. } => "inst?",
            Stmt::Ret { value: None, .. } => "ret",
            Stmt::Ret { .. } => "ret?",
            Stmt::CtIf { .. } => "ctif",
            Stmt::CtFor { .. } => "ctfor",
            Stmt::Block { body, .. } if body.len() == 1 => "block",
            Stmt::Block { .. } => "block?",
            Stmt::Expr { .. } => "expr",
            Stmt::Alias { .. } => "alias",
        })
        .collect();
    assert_eq!(
        kinds,
        [
            "let", "let mut", "input", "output", "reg", "wire", "inst", "assign", "connect",
            "connect", "ret", "block", "expr"
        ]
    );
}

#[test]
fn assignment_targets() {
    let stmts = body("a.b.c = 3; x := y;");
    let [
        Stmt::Assign { target, .. },
        Stmt::Connect { target: t2, .. },
    ] = stmts.as_slice()
    else {
        panic!("{stmts:?}");
    };
    assert_eq!(sx(target), "(field (field a b) c)");
    assert_eq!(sx(t2), "x");
}

#[test]
fn comptime_statements() {
    let stmts = body(
        "comptime if (W > 1) { let a = 1; } else { let b = 2; } \
         comptime if (true) { } \
         comptime for i in 0..W + 1 { x := i; }",
    );
    let [
        Stmt::CtIf {
            yes, no: Some(no), ..
        },
        Stmt::CtIf { no: None, .. },
        Stmt::CtFor {
            var, lo, hi, body, ..
        },
    ] = stmts.as_slice()
    else {
        panic!("{stmts:?}");
    };
    assert_eq!((yes.len(), no.len(), body.len()), (1, 1, 1));
    assert_eq!(
        (var.name.as_str(), sx(lo), sx(hi)),
        ("i", "0".into(), "(add W 1)".into())
    );
}

#[test]
fn precedence_from_low_to_high() {
    assert_eq!(shape("a || b && c"), "(lor a (land b c))");
    assert_eq!(shape("a && b | c"), "(land a (or b c))");
    assert_eq!(shape("a | b ^ c"), "(or a (xor b c))");
    assert_eq!(shape("a ^ b & c"), "(xor a (and b c))");
    assert_eq!(shape("a & b == c"), "(and a (eq b c))");
    assert_eq!(shape("a == b << c"), "(eq a (shl b c))");
    assert_eq!(shape("a << b + c"), "(shl a (add b c))");
    assert_eq!(shape("a + b * c"), "(add a (mul b c))");
    assert_eq!(shape("a * -b"), "(mul a (neg b))");
    assert_eq!(shape("-a.b"), "(neg (field a b))");
    assert_eq!(shape("(a + b) * c"), "(mul (add a b) c)");
}

#[test]
fn associativity() {
    assert_eq!(shape("a - b - c"), "(sub (sub a b) c)");
    assert_eq!(shape("a +% b -% c"), "(subw (addw a b) c)");
    assert_eq!(
        shape("a * b / c % d *% e"),
        "(mulw (rem (div (mul a b) c) d) e)"
    );
    assert_eq!(shape("a >> b << c"), "(shl (shr a b) c)");
    assert_eq!(shape("a < b"), "(lt a b)");
    assert_eq!(shape("(a < b) == (c >= d)"), "(eq (lt a b) (ge c d))");
    assert_eq!(shape("!~-a"), "(not (inv (neg a)))");
}

#[test]
fn comparisons_do_not_chain() {
    assert_eq!(
        first_error("const X: T = a < b < c;"),
        Some((Code::S001, 1, 20))
    );
    assert_eq!(
        first_error("const X: T = a == b != c;"),
        Some((Code::S001, 1, 21))
    );
    assert_eq!(
        first_error("const X: T = a < b + c == d;"),
        Some((Code::S001, 1, 24))
    );
}

#[test]
fn postfix_and_conditional() {
    assert_eq!(shape("f(1, 2,)(3)"), "(call (call f 1 2) 3)");
    assert_eq!(shape("UInt[W + 1]"), "(index UInt (add W 1))");
    assert_eq!(
        shape("(a.b.c)(1)[2]"),
        "(index (call (field (field a b) c) 1) 2)"
    );
    assert_eq!(shape("f()"), "(call f )");
    assert_eq!(shape("if (a) { 1 } else { b + 2 }"), "(if a 1 (add b 2))");
    assert_eq!(
        shape("x +% (if (a) { 1 } else { 2 })"),
        "(addw x (if a 1 2))"
    );
    assert_eq!(
        first_error("const X: T = x +% if (a) { 1 } else { 2 };"),
        Some((Code::S001, 1, 19))
    );
}

#[test]
fn literals() {
    assert_eq!(shape("007"), "7");
    assert_eq!(shape("0xFf"), "255");
    assert_eq!(shape("0b101"), "5");
    assert_eq!(shape("0"), "0");
    assert_eq!(shape("0x00"), "0");
    assert_eq!(
        shape("0xFFFFFFFFFFFFFFFFFFFFFFFF"),
        "79228162514264337593543950335"
    );
    assert_eq!(
        shape("123456789012345678901234567890"),
        "123456789012345678901234567890"
    );
    assert_eq!(shape(r#""a\n\"\\\t\rb""#), r#""a\n\"\\\t\rb""#);
    assert_eq!(shape("true"), "true");
    assert_eq!(shape("false"), "false");
}

#[test]
fn positions_are_first_tokens_in_characters() {
    // The string holds two characters of two bytes each, so the next column counts one each.
    let parsed = parse("const S: Str = \"éé\";\n  fn f() -> T { let é = 1; }");
    assert!(
        !parsed.errors.is_empty(),
        "é is not an identifier character"
    );
    let parsed = parse("const S: Str = \"éé\";\r\n\tfn f() -> T { x(\"é\") + (y); }");
    let Some([Item::Const { value, .. }, Item::Fn { pos: p, body, .. }]) = parsed.ast.as_deref()
    else {
        panic!("{parsed:?}");
    };
    assert_eq!(
        value,
        &Expr::Str {
            pos: pos(1, 16),
            value: "éé".into()
        }
    );
    assert_eq!(*p, pos(2, 2));
    let [
        Stmt::Expr {
            pos: sp,
            value: Expr::Binary {
                pos: bp, lhs, rhs, ..
            },
        },
    ] = body.as_slice()
    else {
        panic!("{body:?}");
    };
    assert_eq!((*sp, *bp), (pos(2, 16), pos(2, 16)));
    assert!(matches!(**lhs, Expr::Call { pos: p, .. } if p == pos(2, 16)));
    assert!(matches!(**rhs, Expr::Name { pos: p, .. } if p == pos(2, 26)));
}

#[test]
fn field_name_has_its_own_position() {
    let stmts = body("a.bc;");
    let [
        Stmt::Expr {
            value: Expr::Field { pos: p, field, .. },
            ..
        },
    ] = stmts.as_slice()
    else {
        panic!("{stmts:?}");
    };
    assert_eq!((*p, field.pos), (pos(1, 14), pos(1, 16)));
}

#[test]
fn later_slice_syntax_is_s004() {
    let cases = [
        ("import a::b as c;", 1, 1),
        ("pub fn f() -> T { }", 1, 1),
        ("import a;", 1, 1),
        ("pub module M() { }", 1, 1),
        ("extern module M() = \"m\" { }", 1, 1),
        ("module M() conforms A() using B() { }", 1, 12),
        ("module M() domains(a, b) { }", 1, 23),
        ("module M(x: Nat) { }", 1, 10), // S001: a module parameter needs comptime
        ("fn f(x: a::T) -> T { }", 1, 10),
        ("module M() { reg r: T in d = 0; }", 1, 23),
        ("module M() { wire w: T in d; }", 1, 24),
        ("module M() { instance u = A() with { }; }", 1, 31),
        ("module M() { instance u = a::A(); }", 1, 28),
        ("const X: T = a::b::c;", 1, 18),
        ("const X: T::U = f;", 1, 11),
        ("const X: a::T = f;", 1, 11),
        ("enum E(T): U {}", 1, 7),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, line, col)| {
            let code = if input.starts_with("module M(x") {
                Code::S001
            } else {
                Code::S004
            };
            first_error(input) != Some((code, *line, *col))
        })
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
}

#[test]
fn syntax_errors_are_s001_at_the_first_bad_token() {
    let cases = [
        ("const", 1, 6),
        ("const match: T = 1;", 1, 7),
        ("fn f(enum: T) -> T { }", 1, 6),
        ("const X: T = a => b;", 1, 16),
        ("const X: T = 1 + match (x) { _ => 1 };", 1, 18),
        ("const X: T = ;", 1, 14),
        ("const X: T = 1", 1, 15),
        ("const X: T = 1;\n\nfoo", 3, 1),
        ("comptime", 1, 9),
        ("comptime for", 1, 10),
        ("fn f() { }", 1, 8),
        ("fn f() -> T { let x = 1 }", 1, 25),
        ("fn f() -> T { x + = 1; }", 1, 19),
        ("const X: T = @foo(1);", 1, 15),
        ("const X: T = 12ab;", 1, 16),
        ("const X: T = x[];", 1, 16),
        ("const X: T = a + b = c;", 1, 20),
        ("module M() { f(x) = 1; }", 1, 19),
        ("module M() { if (a) { 1 } }", 1, 27),
        ("module M() { comptime { } }", 1, 23),
        ("module M() { ; }", 1, 14),
        ("const X: T = 1;\n/* open", 2, 1),
        ("const X: T = \"open;", 1, 14),
        ("const X: T = 1 $ 2;", 1, 16),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, line, col)| first_error(input) != Some((Code::S001, *line, *col)))
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
}

#[test]
fn the_first_error_is_the_first_in_position_order() {
    // A lexical error after a syntax error does not come first.
    assert_eq!(first_error("const X = 1; $"), Some((Code::S001, 1, 9)));
    // A lexical error before the syntax error comes first.
    assert_eq!(first_error("const X $ ; import"), Some((Code::S001, 1, 9)));
    // S004 and S001 compete by position only.
    assert_eq!(first_error("import x; $"), Some((Code::S004, 1, 1)));
    assert_eq!(first_error("$ import x;"), Some((Code::S001, 1, 1)));
}

#[test]
fn every_body_parses_a_port() {
    for stmt in [
        "input a: Bool;",
        "output a: Bool;",
        "input a[1]: Bool;",
        "output a: Bool as \"b\";",
    ] {
        for head in ["fn f() -> Nat", "comptime fn f() -> Nat", "module M()"] {
            let src = format!("{head} {{\n  {stmt}\n}}\n");
            assert_eq!(first_error(&src), None, "{src}");
        }
    }
}

#[test]
fn a_plain_fn_has_resource_statements() {
    for stmt in [
        "reg a: Bool = false;",
        "wire a: Bool;",
        "mem m: [Bool; 4];",
        "instance u = M();",
        "a := true;",
    ] {
        let src = format!("fn f() -> Nat {{\n  {stmt}\n  return 1;\n}}\n");
        assert_eq!(first_error(&src), None, "{stmt}");
    }
}

#[test]
fn recovery_reports_later_errors() {
    let input = "const A: T = ;\ncomptime fn f() -> T { let = 1; reg r: T = 0; x +; }\nimport x;\nconst B: T = 1;\nconst C: T = ;";
    let parsed = parse(input);
    let found: Vec<_> = parsed.errors.iter().map(|e| (e.code, e.pos.line)).collect();
    assert_eq!(
        found,
        [
            (Code::S001, 1),
            (Code::S001, 2),
            (Code::S001, 2),
            (Code::S004, 3),
            (Code::S001, 5)
        ]
    );
    assert!(parsed.ast.is_none());
    assert_lossless(&parsed, input);
    assert!(parsed.errors.windows(2).all(|w| w[0].pos <= w[1].pos));
}

#[test]
fn recovery_keeps_the_items_after_an_error() {
    let parsed = parse("pub fn f() -> T { }\nmodule M() { let = ; wire w: T; }\nconst C: T = ;");
    let lines: Vec<_> = parsed.errors.iter().map(|e| (e.code, e.pos.line)).collect();
    assert_eq!(lines, [(Code::S004, 1), (Code::S001, 2), (Code::S001, 3)]);
}

#[test]
fn height_is_limited_to_64() {
    // A leaf has height 1, each node of the AST adds 1, and parentheses make no node. The
    // error is at the first token of the outermost expression or type with height 65.
    let at = |n: usize| Some((Code::S001, 1, n));
    let call = |n: usize| format!("const X: T = {}1{};", "f(".repeat(n), ")".repeat(n));
    assert_eq!(first_error_64(&call(63)), None);
    assert_eq!(first_error_64(&call(64)), at(14));
    let unary = |n: usize| format!("const X: T = {}1;", "-".repeat(n));
    assert_eq!(first_error_64(&unary(63)), None);
    assert_eq!(first_error_64(&unary(64)), at(14));
    let chain = |n: usize| format!("const X: T = {};", vec!["a"; n].join(" + "));
    assert_eq!(first_error_64(&chain(64)), None);
    assert_eq!(first_error_64(&chain(65)), at(14));
    let field = |n: usize| format!("const X: T = a{};", ".b".repeat(n));
    assert_eq!(first_error_64(&field(63)), None);
    assert_eq!(first_error_64(&field(64)), at(14));
    // The error is at the outermost expression, not at the deep form.
    let inner = format!("const X: T = y + {}1{};", "f(".repeat(64), ")".repeat(64));
    assert_eq!(first_error_64(&inner), at(14));
    let ty = |n: usize| format!("const X: {}T{} = 1;", "A[".repeat(n), "]".repeat(n));
    assert_eq!(first_error_64(&ty(63)), None);
    assert_eq!(first_error_64(&ty(64)), at(10));
    let chain_ty = |n: usize| format!("const X: T{} = 1;", "[1]".repeat(n));
    assert_eq!(first_error_64(&chain_ty(63)), None);
    assert_eq!(first_error_64(&chain_ty(64)), at(10));
    // The type and the value of one statement are two outermost forms.
    let two = format!(
        "module M() {{ let x: T{} = {}1; }}",
        "[1]".repeat(64),
        "-".repeat(64),
    );
    assert_eq!(first_error_64(&two), at(21));
    // An `instance` argument is outermost.
    let inst = format!("module M() {{ instance i = N({}1); }}", "-".repeat(64));
    assert_eq!(first_error_64(&inst), at(29));
    // The height of a statement or an item is not limited.
    let long = format!("module M() {{ {} }}", "x; ".repeat(1000));
    assert_eq!(first_error_64(&long), None);
}

#[test]
fn parentheses_make_no_node() {
    // Height 3: a name and two unary operators.
    let input = "const X: T = (-(-a));";
    assert!(parse_with_depth(input, 3).errors.is_empty());
    let errors = parse_with_depth(input, 2).errors.clone();
    assert_eq!(errors.len(), 1);
    assert_eq!((errors[0].pos.line, errors[0].pos.col), (1, 14));
}

#[test]
fn brackets_nest_at_most_64_deep() {
    let at = |n: usize| Some((Code::S001, 1, n));
    let paren = |n: usize| format!("const X: T = {}1{};", "(".repeat(n), ")".repeat(n));
    assert_eq!(first_error_64(&paren(64)), None);
    assert_eq!(first_error_64(&paren(65)), at(14 + 64));
    let blocks = |n: usize| format!("module M() {}{}", "{".repeat(n), "}".repeat(n));
    assert_eq!(first_error_64(&blocks(63)), None);
    // The 65th bracket is the `{` at column 12 + 64, and `(` of the module is closed.
    assert_eq!(first_error_64(&blocks(65)), at(12 + 64));
    // The three kinds of brackets count together.
    let mixed = format!("const X: T = {}1;", "f(a[(".repeat(22));
    assert_eq!(first_error_64(&mixed), at(122));
}

#[test]
fn a_height_error_loses_to_any_other_error() {
    let high = "const X: T = a + a + a + a;";
    assert_eq!(first_error_64(high), None);
    let first = |input: &str, depth: usize| {
        parse_with_depth(input, depth)
            .errors
            .first()
            .map(|e| (e.code, e.pos.line, e.pos.col))
    };
    assert_eq!(first(high, 3), Some((Code::S001, 1, 14)));
    // A syntax error after the high expression wins.
    assert_eq!(
        first("const X: T = a + a + a + a;\nconst Y: T = ;", 3),
        Some((Code::S001, 2, 14))
    );
    // So does a later slice error, and a lexical error.
    assert_eq!(
        first("const X: T = a + a + a + a;\nimport x;", 3),
        Some((Code::S004, 2, 1))
    );
    assert_eq!(
        first("const X: T = a + a + a + a; $", 3),
        Some((Code::S001, 1, 29))
    );
    // An error that comes before the high expression also wins, by position.
    assert_eq!(
        first("const X: T = ;\nconst Y: T = a + a + a + a;", 3),
        Some((Code::S001, 1, 14))
    );
}

#[test]
fn deep_input_does_not_overflow_the_stack() {
    for open in [
        "(",
        "-",
        "f(",
        "{",
        "a[",
        "if (",
        "module M() {",
        "@TypeOf(",
        "@field(a, ",
        "@field(",
    ] {
        let input = open.repeat(100_000);
        let parsed = parse(&input);
        assert!(!parsed.errors.is_empty());
        assert_lossless(&parsed, &input);
    }
    let chain = format!("const X: T = {};", vec!["a.b(1)"; 100_000].join(" + "));
    assert!(!parse(&chain).errors.is_empty());
}

#[test]
fn comments_and_whitespace_stay_in_the_tree() {
    let input = "// a\nconst /* b */ X: T = 1; // c\n";
    let parsed = parse(input);
    assert!(parsed.errors.is_empty());
    assert_lossless(&parsed, input);
}

#[test]
fn a_chain_of_else_if_is_a_syntax_error_without_deep_recursion() {
    // The grammar of the slice has no `else if`, so the first `if` after `else` is the error.
    let input = format!(
        "const X: T = if (a) {{ 1 }}{};",
        " else if (a) { 1 }".repeat(1_000_000)
    );
    let parsed = parse(&input);
    assert_eq!(parsed.errors.first().map(|e| e.pos.col), Some(32));
}

proptest! {
    #[test]
    fn brackets_in_any_order_stay_in_the_stack_for_a_small_depth(
        input in "[(){}\\[\\]a;+,-]{0,600}|((\\{|\\(|\\[|\\)|\\}|\\]|-|a|;|f\\(){0,600})"
    ) {
        let parsed = parse_with_depth(&input, 2);
        assert_lossless(&parsed, &input);
    }

    #[test]
    fn no_panic_and_lossless_on_any_string(input in any::<String>()) {
        let parsed = parse(&input);
        prop_assert_eq!(parsed.syntax().text().to_string(), input);
        prop_assert_eq!(parsed.ast.is_some(), parsed.errors.is_empty());
        prop_assert!(parsed.errors.windows(2).all(|w| w[0].pos <= w[1].pos));
    }

    #[test]
    fn no_panic_and_lossless_on_token_soup(input in "[a-z0-9 \\n\"/*\\\\@:=<>+%.&|!{}()\\[\\];,^~-]{0,120}|(const|fn|module|let|mut|reg|wire|input|output|instance|comptime|if|else|for|in|return|domains|struct|import|x|1|\\(|\\)|\\{|\\}|;|:|=|:=|,|\\+| ){0,40}") {
        let parsed = parse(&input);
        prop_assert_eq!(parsed.syntax().text().to_string(), input);
        prop_assert_eq!(parsed.ast.is_some(), parsed.errors.is_empty());
    }
}

#[test]
fn a_missing_or_wrong_opening_delimiter_is_s001() {
    let cases = [
        ("module M() { instance u = Child 123); }", 1, 33),
        ("module M() { instance u = Child[1]; }", 1, 32),
        ("module M() { instance u = Child; }", 1, 32),
        ("module M() { instance u = Child(; }", 1, 33),
    ];
    for (input, line, col) in cases {
        let parsed = parse(input);
        assert!(parsed.ast.is_none(), "{input}");
        assert_eq!(first_error(input), Some((Code::S001, line, col)), "{input}");
    }
}

#[test]
fn many_errors_on_one_line_scale_linearly() {
    // Each `$` is an error token, so the line holds 50 000 errors. A quadratic scan
    // would need more than 10^9 steps, and the timeout of nextest stops a hang.
    let input = "$ ".repeat(50_000);
    let parsed = parse(&input);
    assert_eq!(parsed.errors.len(), 50_000);
    assert_eq!(parsed.errors[49_999].pos, pos(1, 99_999));
}

#[test]
fn rules_of_the_lean_parser() {
    let cases = [
        // A path in an operand has two parts: a third part is S004 at the second `::`.
        ("const X: T = x+a::f::h(1);", Code::S004, 1, 20),
        ("const X: T = x.f+a::g::h(1);", Code::S004, 1, 22),
        // `mut`: S001 at a module parameter. A path in a function parameter is S004.
        ("module M(mut x: T) { }", Code::S001, 1, 10),
        ("module M(comptime mut x: T) { }", Code::S001, 1, 19),
        ("struct P(mut x: T) { }", Code::S001, 1, 10),
        ("struct P(comptime mut W: Nat) { }", Code::S001, 1, 19),
        // A function parameter has at most one mark: S001 where the name is due.
        ("fn f(comptime mut x: T) -> T { }", Code::S001, 1, 15),
        ("fn f(mut comptime x: T) -> T { }", Code::S001, 1, 10),
        ("fn f(mut mut x: T) -> T { }", Code::S001, 1, 10),
        ("fn f(comptime comptime x: T) -> T { }", Code::S001, 1, 15),
        ("fn f(x: T, mut: T) -> T { }", Code::S001, 1, 15),
        (
            "comptime fn f(comptime mut x: T) -> T { }",
            Code::S001,
            1,
            24,
        ),
        ("fn f(x: a::T) -> T { }", Code::S004, 1, 10),
        // The arity of a builtin is S001 at its name, after all operands. A syntax error in an
        // operand comes first.
        ("const X: T = @TypeOf(a.b, c);", Code::S001, 1, 15),
        ("const X: T = @TypeOf(f(a, b), (c)), d);", Code::S001, 1, 15),
        ("const X: T = @TypeOf(a, b", Code::S001, 1, 26),
        ("const X: T = (a $ , b);", Code::S001, 1, 17),
        ("const X: T = (@TypeOf(a, b));", Code::S001, 1, 16),
        ("const X: T = @TypeOf(a, $);", Code::S001, 1, 25),
        ("const X: T = @TypeOf();", Code::S001, 1, 15),
        ("const X: T = @typeInfo();", Code::S001, 1, 15),
        ("const X: T = @typeInfo(a, b);", Code::S001, 1, 15),
        ("const X: T = @typeInfo(a $);", Code::S001, 1, 26),
        ("module M() { @typeInfo(x) = 1; }", Code::S001, 1, 27),
        ("const X: T = @field(a);", Code::S001, 1, 15),
        ("const X: T = @field(a, b, c);", Code::S001, 1, 15),
        ("module M() { @field(a, 1 +) = e; }", Code::S001, 1, 27),
        // The operand of `@TypeOf` is a place, else S001 at its first token, also a `(`.
        ("const X: T = @TypeOf(1);", Code::S001, 1, 22),
        ("const X: T = @TypeOf(f(x));", Code::S001, 1, 22),
        ("const X: T = @TypeOf(a + b);", Code::S001, 1, 22),
        ("const X: T = @TypeOf((a + b));", Code::S001, 1, 22),
        ("const X: T = @TypeOf(a.m(x));", Code::S001, 1, 22),
        ("const X: T = @TypeOf(E::V);", Code::S001, 1, 22),
        ("const X: T = @TypeOf(@TypeOf(a));", Code::S001, 1, 22),
        ("const X: T = @TypeOf(@field(f(x), 0));", Code::S001, 1, 22),
        // Another name after `@` is "Not a builtin" at the name.
        ("const X: T = @x(y);", Code::S001, 1, 15),
        ("module M() { @x(y); }", Code::S001, 1, 15),
        ("module M() { f(x)[0] = e; }", Code::S001, 1, 22),
        ("module M() { f(x) = e; }", Code::S001, 1, 19),
        // A third part of a path, also in parentheses: S004 at the second `::`.
        ("const X: T = (a::b::c);", Code::S004, 1, 19),
        ("const X: T = ab::c::d;", Code::S004, 1, 19),
        // A statement with `if` is an expression statement and needs a `;`.
        ("module M() { if (a) { 1 } else { 2 } }", Code::S001, 1, 38),
        // The path of a type and of a module is one name.
        ("module M() { instance u = a::B(); }", Code::S004, 1, 28),
        ("const X: a::T = 1;", Code::S004, 1, 11),
        // A builtin in a type reads as in an expression. Another name is S001.
        ("const X: @TypeOf(1) = 1;", Code::S001, 1, 18),
        ("const X: @foo(1) = 1;", Code::S001, 1, 11),
        ("const X: @ = 1;", Code::S001, 1, 12),
        // A second domain needs a name after the comma.
        ("module M() domains(a, b) { }", Code::S004, 1, 23),
        ("module M() domains(a, 1) { }", Code::S001, 1, 23),
        ("module M() domains(a b) { }", Code::S001, 1, 22),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, code, line, col)| first_error(input) != Some((*code, *line, *col)))
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
    for ok in [
        "const X: T = (x.f)(1);",
        "const X: T = (a);",
        "const X: T = (a[1, 2]);",
        "const X: T = (a < b) < c;",
        "module M() { if (a) { 1 } else { 2 }; }",
        "module M() domains(a,) { }",
        "module M() { a.b = 1; a.b.c := 2; }",
        "const X: T = @TypeOf(x);",
        "const X: T = @TypeOf((a));",
        "const X: T = @TypeOf((a).b[1].0);",
        "const X: T = @TypeOf(@field(a, k));",
        "const X: T = @typeInfo(Nat);",
        "const X: T = @typeInfo(a + b);",
        "const X: T = @typeInfo(f(x));",
        "const X: T = @typeInfo(@typeInfo(a));",
        "const X: T = @typeInfo(@TypeOf(a));",
        "const X: T = @typeInfo([UInt[8]; 4]);",
        "const X: T = @typeInfo(fn (T) -> U);",
        "module M() { @typeInfo(x); }",
        "const X: T = @field(a[1, 2], b);",
        "const X: T = @field(f(x), 1 + 2);",
        "const X: T = @field(@field(a, 0), \"f\").g[0] + 1;",
        "module M() { @TypeOf(x); }",
        "module M() { @field(x, \"i\") = e; }",
        "module M() { @field(a.b, \"c\") := e; }",
        "module M() { @field(a, \"0\") = e; }",
        "module M() { @field(a, 0x1) = e; }",
        "module M() { @field(a, if (c) { 1 } else { 2 }) = e; }",
        "module M() { @field(a, f(x)).b = e; }",
        "module M() { @field(a, 0)[1].0 = e; }",
    ] {
        assert_eq!(first_error(ok), None, "{ok}");
    }
}

/// The AST of `const X: <ty> = 0;` as its dump, without the item around the type.
fn type_dump(ty: &str) -> String {
    let parsed = parse(&format!("const X: {ty} = 0;"));
    assert!(parsed.errors.is_empty(), "{ty}: {:?}", parsed.errors);
    let text = parsed.dump().unwrap().unwrap();
    let body = text.strip_prefix("(const \"X\" ").unwrap_or(&text);
    body.strip_suffix(" (num 0))\n").unwrap_or(body).to_owned()
}

#[test]
fn container_expressions() {
    for (input, want) in [
        ("()", "()"),
        ("(a)", "a"),
        ("(a,)", "(tuple a)"),
        ("(a, (b, c),)", "(tuple a (tuple b c))"),
        ("[]", "(array )"),
        ("[a, [], ()]", "(array a (array ) ())"),
        ("[if (c) { 1 } else { 2 },]", "(array (if c 1 2))"),
        ("t.0", "(select t 0)"),
        ("t.0x1.0b10", "(select (select t 1) 2)"),
        ("(x, true).0", "(select (tuple x true) 0)"),
        ("t.0(x)", "(call (select t 0) x)"),
        ("a[0].1.f", "(field (select (index a 0) 1) f)"),
        ("-t.1", "(neg (select t 1))"),
    ] {
        assert_eq!(shape(input), want, "{input}");
    }
}

#[test]
fn enums_and_paths_dump_like_lean() {
    let dump = |source: &str| {
        let parsed = parse(source);
        assert!(parsed.errors.is_empty(), "{source}: {:?}", parsed.errors);
        parsed.dump().unwrap().unwrap()
    };
    let e = |x: &str| {
        dump(&format!("const X: T = {x};"))
            .strip_prefix("(const \"X\" (name \"T\") ")
            .and_then(|d| d.strip_suffix(")\n"))
            .unwrap()
            .to_owned()
    };
    assert_eq!(e("Op::Add"), "(path \"Op\" \"Add\")");
    assert_eq!(
        e("Op::Load(x, 1)"),
        "(call (path \"Op\" \"Load\") ((name \"x\") (num 1)))"
    );
    assert_eq!(e("a::b.c"), "(field (path \"a\" \"b\") \"c\")");
    assert_eq!(
        dump("enum Op: UInt[2] { Add = 0, Load(UInt[8]) = 1, Pair(Bool, UInt[4],) = 2, }"),
        "(enum \"Op\" (index (name \"UInt\") ((num 2))) ((variant \"Add\" () (num 0)) \
         (variant \"Load\" ((index (name \"UInt\") ((num 8)))) (num 1)) \
         (variant \"Pair\" ((name \"Bool\") (index (name \"UInt\") ((num 4)))) (num 2))))\n"
    );
    assert_eq!(dump("enum E: T { A() = 0 }"), dump("enum E: T { A = 0 }"));
    assert_eq!(
        dump("enum E: UInt[1] {}"),
        "(enum \"E\" (index (name \"UInt\") ((num 1))) ())\n"
    );
}

#[test]
fn enum_and_path_errors_have_the_lean_positions() {
    let cases = [
        ("enum E: T { A }", Code::S001, 1, 15),
        ("enum E: T { A(B) }", Code::S001, 1, 18),
        ("enum E: T { A = 0 B = 1 }", Code::S001, 1, 19),
        ("enum E: T { A = 0,, }", Code::S001, 1, 19),
        ("enum E { A = 0 }", Code::S001, 1, 8),
        ("enum E: T { A(,) = 0 }", Code::S001, 1, 15),
        ("enum E(comptime W: Nat): T { A = 0 }", Code::S004, 1, 7),
        ("module M() {}\nenum E(): T {}", Code::S004, 2, 7),
        ("const X: T = a::;", Code::S001, 1, 17),
        ("const X: T = a::1;", Code::S001, 1, 17),
        ("const X: T = a::b::;", Code::S004, 1, 18),
        ("fn f() -> T { Op::Add = 1; }", Code::S001, 1, 23),
    ];
    for (input, code, line, col) in cases {
        assert_eq!(first_error(input), Some((code, line, col)), "{input}");
    }
    assert_eq!(
        parse("enum E(T): U {}").errors[0].message,
        "an enum with parameters is not supported yet; remove the parameters, and give each \
         payload a fixed type"
    );
    assert_eq!(
        parse("const X: a::T = 1;").errors[0].message,
        "a package path is not supported yet; in this slice, a path is a variant `E::V` of an \
         enum `E`, in an expression or a pattern"
    );
    assert_eq!(
        parse("struct S { a: T(1) }").errors[0].message,
        "a type function call is not supported yet"
    );
}

const PATTERN_TEXT: &str = "expected a pattern: an integer, `true`, `false`, `E::V(..)`, or `_`; compare with a constant in an `if`";

/// The dump of the expression `e` in a `const`.
fn expr_dump(e: &str) -> String {
    let text = parse(&format!("const X: T = {e};"))
        .dump()
        .unwrap()
        .unwrap();
    text.strip_prefix("(const \"X\" (name \"T\") ")
        .and_then(|t| t.strip_suffix(")\n"))
        .unwrap_or(&text)
        .to_owned()
}

#[test]
fn match_dumps_like_lean() {
    assert_eq!(
        expr_dump(
            "match (x) { 0 => 1, -3 => 2, true => a, false => b, Op::Add => 3, \
             Op::Load(v) => v, Op::Pair(a, _,) => a, _ => 2, }"
        ),
        "(match (name \"x\") ((arm (int false 0) (num 1)) (arm (int true 3) (num 2)) \
         (arm (bool true) (name \"a\")) (arm (bool false) (name \"b\")) \
         (arm (variant \"Op\" \"Add\" ()) (num 3)) \
         (arm (variant \"Op\" \"Load\" ((some \"v\"))) (name \"v\")) \
         (arm (variant \"Op\" \"Pair\" ((some \"a\") none)) (name \"a\")) (arm (wild) (num 2))))"
    );
    assert_eq!(
        expr_dump("match (x) { Op::Add() => 1 }"),
        expr_dump("match (x) { Op::Add => 1 }")
    );
    assert_eq!(expr_dump("match (x) {}"), "(match (name \"x\") ())");
    assert_eq!(
        expr_dump("match (x) { _ => match (y) { _ => 1 } }"),
        "(match (name \"x\") ((arm (wild) (match (name \"y\") ((arm (wild) (num 1)))))))"
    );
    assert_eq!(
        expr_dump("if (match (x) { _ => c }) { 1 } else { 2 }"),
        "(cond (match (name \"x\") ((arm (wild) (name \"c\")))) (num 1) (num 2))"
    );
    assert_eq!(
        expr_dump("f(match (x) { _ => 1 })"),
        "(call (name \"f\") ((match (name \"x\") ((arm (wild) (num 1))))))"
    );
    assert_eq!(
        expr_dump("a + (match (x) { _ => 1 })"),
        "(binary add (name \"a\") (match (name \"x\") ((arm (wild) (num 1)))))"
    );
    assert_eq!(
        expr_dump("match (x) { 0x10 => 1 }"),
        expr_dump("match (x) { 16 => 1 }")
    );
}

#[test]
fn match_statements_parse() {
    for source in [
        "fn f() -> T { return match (x) { _ => 0 }; }",
        "fn f() -> T { match (x) { _ => 0 }; }",
        "fn f() -> T { let y = match (x) { true => 1, false => 2 }; return y; }",
    ] {
        let parsed = parse(source);
        assert!(parsed.errors.is_empty(), "{source}: {:?}", parsed.errors);
    }
}

#[test]
fn match_errors_are_at_the_first_bad_token() {
    let cases = [
        ("const X: T = match (x) { a => 1 };", Code::S001, 1, 28),
        (
            "const X: T = match (x) { E::V(F::W) => 1 };",
            Code::S001,
            1,
            32,
        ),
        (
            "const X: T = match (x) { E::V(1) => 1 };",
            Code::S001,
            1,
            31,
        ),
        (
            "const X: T = match (x) { E::V(a b) => 1 };",
            Code::S001,
            1,
            33,
        ),
        ("const X: T = match (x) { E::1 => 1 };", Code::S001, 1, 29),
        ("const X: T = match (x) { (1) => 1 };", Code::S001, 1, 26),
        ("const X: T = match (x) { 1 + 2 => 1 };", Code::S001, 1, 28),
        ("const X: T = match (x) { 1..3 => 1 };", Code::S001, 1, 27),
        ("const X: T = match (x) { 1 | 2 => 1 };", Code::S001, 1, 28),
        ("const X: T = match (x) { - x => 1 };", Code::S001, 1, 28),
        ("const X: T = match (x) { _::V => 1 };", Code::S001, 1, 27),
        ("const X: T = match (x) { E::_ => 1 };", Code::S001, 1, 29),
        (
            "const X: T = match (x) { E::_(a) => 1 };",
            Code::S001,
            1,
            29,
        ),
        (
            "const X: T = match (x) { E::V::W => 1 };",
            Code::S004,
            1,
            30,
        ),
        ("const X: T = match x { _ => 1 };", Code::S001, 1, 20),
        (
            "const X: T = match (x) { 1 => 1 2 => 3 };",
            Code::S001,
            1,
            33,
        ),
        ("const X: T = match (x) { 1 => 1,, };", Code::S001, 1, 33),
        (
            "const X: T = match (x) { _ => 1 + match (y) { _ => 1 } };",
            Code::S001,
            1,
            35,
        ),
        ("const X: T = match (x) { _ => 1 } + 1;", Code::S001, 1, 35),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, code, line, col)| first_error(input) != Some((*code, *line, *col)))
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
    assert_eq!(
        parse("const X: T = match (x) { a => 1 };").errors[0].message,
        PATTERN_TEXT
    );
    assert_eq!(
        parse("const X: T = match (x) { E::_ => 1 };").errors[0].message,
        "a variant pattern names a variant, not `_`; write `_` alone to match each other value"
    );
}

#[test]
fn a_trailing_comma_ends_the_binders_of_a_pattern() {
    assert_eq!(
        expr_dump("match (e) { Op::Load(a,) => a }"),
        expr_dump("match (e) { Op::Load(a) => a }")
    );
}

#[test]
fn container_expressions_dump_like_lean() {
    let dump = |e: &str| {
        let text = parse(&format!("const X: T = {e};"))
            .dump()
            .unwrap()
            .unwrap();
        text.strip_prefix("(const \"X\" (name \"T\") ")
            .and_then(|t| t.strip_suffix(")\n"))
            .unwrap_or(&text)
            .to_owned()
    };
    assert_eq!(dump("()"), "(unit)");
    assert_eq!(dump("(a,)"), "(tuple ((name \"a\")))");
    assert_eq!(dump("[]"), "(array ())");
    assert_eq!(
        dump("[a, [], ()]"),
        "(array ((name \"a\") (array ()) (unit)))"
    );
    assert_eq!(dump("t.0x1.0b10"), "(select (select (name \"t\") 1) 2)");
    assert_eq!(
        dump("t.0(x)"),
        "(call (select (name \"t\") 0) ((name \"x\")))"
    );
}

#[test]
fn container_types_dump_like_lean() {
    assert_eq!(type_dump("()"), "(unit)");
    assert_eq!(type_dump("(T)"), "(name \"T\")");
    assert_eq!(type_dump("(T,)"), "(tuple ((name \"T\")))");
    assert_eq!(
        type_dump("(T, (), [U; N + 1],)"),
        "(tuple ((name \"T\") (unit) (array (name \"U\") (binary add (name \"N\") (num 1)))))"
    );
    assert_eq!(
        type_dump("[[Bool; 2]; 3]"),
        "(array (array (name \"Bool\") (num 2)) (num 3))"
    );
    assert_eq!(type_dump("(T)[1]"), "(index (name \"T\") ((num 1)))");
}

#[test]
fn places_have_indexes_and_selectors() {
    let stmts = body("a[i] = 1; t.0 := x; a[i].0x1.f[j] = 1; a[i, j] = 1;");
    let targets: Vec<String> = stmts
        .iter()
        .map(|s| match s {
            Stmt::Assign { target, .. } | Stmt::Connect { target, .. } => sx(target),
            other => panic!("{other:?}"),
        })
        .collect();
    assert_eq!(
        targets,
        [
            "(index a i)",
            "(select t 0)",
            "(index (field (select (index a i) 1) f) j)",
            "(index a i j)",
        ]
    );
    let stmts = body("a[i] + 1; t.1;");
    assert!(matches!(
        stmts.as_slice(),
        [Stmt::Expr { .. }, Stmt::Expr { .. }]
    ));
}

#[test]
fn a_select_keeps_the_position_of_its_literal() {
    let parsed = parse("module M() { a.1[0] = x; }");
    let Some([Item::Module { body, .. }]) = parsed.ast.as_deref() else {
        panic!("no module");
    };
    let [Stmt::Assign { pos: p, target, .. }] = body.as_slice() else {
        panic!("no assignment");
    };
    let Expr::Index { pos: q, base, .. } = target else {
        panic!("no index");
    };
    let Expr::Select {
        pos: r, lit_pos, ..
    } = &**base
    else {
        panic!("no select");
    };
    assert_eq!(
        (*p, *q, *r, *lit_pos),
        (pos(1, 14), pos(1, 14), pos(1, 14), pos(1, 16))
    );
}

#[test]
fn container_forms_give_s001_and_s004_like_lean() {
    let cases = [
        ("const X: T = [a, b; c];", Code::S001, 1, 16),
        ("const X: T = (T; 4);", Code::S001, 1, 16),
        ("const X: T = (,);", Code::S001, 1, 15),
        ("const X: T = (a b);", Code::S001, 1, 17),
        ("const X: T = (a,,);", Code::S001, 1, 17),
        ("const X: T = [,];", Code::S001, 1, 15),
        ("const X: T = [a b];", Code::S001, 1, 17),
        ("const X: T = t.\"s\";", Code::S001, 1, 16),
        ("const X: T = x.f(;", Code::S001, 1, 18),
        ("const X: T = x.f(a b);", Code::S001, 1, 20),
        ("const X: T = x.f(a,,);", Code::S001, 1, 20),
        ("module M() { f(x)[0] = 1; }", Code::S001, 1, 22),
        ("module M() { a.0(x) = 1; }", Code::S001, 1, 21),
        ("module M() { (a,) = 1; }", Code::S001, 1, 19),
        ("module M() { [a][0] = 1; }", Code::S001, 1, 21),
        ("module M() { a[] = 1; }", Code::S001, 1, 16),
        ("module M() { a.x(1) = 1; }", Code::S001, 1, 21),
        ("module M() { x.f().g = 1; }", Code::S001, 1, 22),
        ("module M() { mem m: [T; 4] in d; }", Code::S004, 1, 28),
        ("const A: (,) = 0;", Code::S001, 1, 11),
        ("const A: (T U) = 0;", Code::S001, 1, 13),
        ("const A: (T, U V) = 0;", Code::S001, 1, 16),
        ("const A: [] = 0;", Code::S001, 1, 11),
        ("const A: [T] = 0;", Code::S001, 1, 12),
        ("const A: [T, U] = 0;", Code::S001, 1, 12),
        ("const A: [T; ] = 0;", Code::S001, 1, 14),
        ("const A: (T)(x) = 0;", Code::S004, 1, 13),
        ("const A: [T; 2](x) = 0;", Code::S004, 1, 16),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, code, line, col)| first_error(input) != Some((*code, *line, *col)))
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
}

#[test]
fn array_types_in_expressions_give_s001_at_the_first_non_type_token() {
    let cases = [
        ("const X: T = [0; 4];", Code::S001, 1, 15),
        ("const X: T = [a + b; 4];", Code::S001, 1, 17),
        ("const X: T = [a.b; 4];", Code::S001, 1, 16),
        ("const X: T = [[a, b]; 4];", Code::S001, 1, 17),
        ("const X: T = [[0; 2]; 4];", Code::S001, 1, 16),
        ("const X: T = [T $; 4];", Code::S001, 1, 17),
        ("const X: T = [T; ];", Code::S001, 1, 18),
        ("const X: T = [T; 4; 5];", Code::S001, 1, 19),
        ("const X: T = [(a; b)];", Code::S001, 1, 17),
        ("const X: T = [f(x); 4];", Code::S004, 1, 16),
        ("const X: T = [a.f(x); 4];", Code::S001, 1, 16),
        ("const X: T = [a::T; 4];", Code::S004, 1, 16),
        ("struct P(W: Nat) { }", Code::S001, 1, 10),
        ("struct P(mut comptime W: Nat) { }", Code::S001, 1, 10),
        ("struct P { a }", Code::S001, 1, 14),
        ("struct P { a: T(x) }", Code::S004, 1, 16),
        ("type A = ;", Code::S001, 1, 10),
        ("pub struct P { }", Code::S004, 1, 1),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, code, line, col)| first_error(input) != Some((*code, *line, *col)))
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
}

#[test]
fn array_types_in_expressions_parse() {
    for (input, shape_text) in [
        ("[UInt[8]; 4]", "(arraytype (index UInt 8) 4)"),
        ("f(a, [T; 4])", "(call f a (arraytype T 4))"),
        ("[[T; 2]; N]", "(arraytype (array T 2) N)"),
        ("[(T, ()); 4]", "(arraytype (tuple T ()) 4)"),
        ("[(T); 4]", "(arraytype T 4)"),
        ("[T; 4]()", "(call (arraytype T 4) )"),
        ("[T; 4][1]", "(index (arraytype T 4) 1)"),
        ("[@TypeOf(x); 4]", "(arraytype (@TypeOf x) 4)"),
        (
            "[[T; 2], [U; 3]]",
            "(array (arraytype T 2) (arraytype U 3))",
        ),
    ] {
        assert_eq!(shape(input), shape_text, "{input}");
    }
    let stmts = body("[T; 4]; type A = [T; 4];");
    assert!(matches!(
        stmts.as_slice(),
        [Stmt::Expr { .. }, Stmt::Alias { .. }]
    ));
}

#[test]
fn a_chain_of_array_types_and_type_arguments_drops_without_recursion() {
    let n = 1000;
    let input = format!("const X: T = {}0{};", "[U[".repeat(n), "]; 1]".repeat(n));
    let parsed = parse(&input);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    drop(parsed);
}

#[test]
fn struct_and_alias_items_keep_their_positions() {
    let parsed = parse("struct P(comptime W: Nat) {\n  a: T,\n}\ntype A = T;");
    let Some(
        [
            Item::Struct {
                pos: p,
                name,
                params,
                fields,
            },
            Item::Alias {
                pos: q,
                name: alias,
                ..
            },
        ],
    ) = parsed.ast.as_deref()
    else {
        panic!("{parsed:?}");
    };
    assert_eq!(
        (*p, name.pos, params[0].pos),
        (pos(1, 1), pos(1, 8), pos(1, 10))
    );
    assert_eq!(
        (params[0].name.pos, fields[0].name.pos),
        (pos(1, 19), pos(2, 3))
    );
    assert_eq!((*q, alias.pos), (pos(4, 1), pos(4, 6)));
    let none = parse("struct P {} struct Q() {}");
    assert!(matches!(
        none.ast.as_deref(),
        Some([Item::Struct { params: a, .. }, Item::Struct { params: b, .. }])
            if a.is_empty() && b.is_empty()
    ));
}

#[test]
fn container_heights_follow_the_ast() {
    // A selector adds one to the height, and `[]` and `()` have height 1.
    let selects = |n: usize| format!("const X: T = t{};", ".0".repeat(n));
    assert_eq!(first_error_64(&selects(63)), None);
    assert_eq!(first_error_64(&selects(64)), Some((Code::S001, 1, 14)));
    let arrays = |n: usize| format!("const X: T = {}{};", "[".repeat(n), "]".repeat(n));
    assert_eq!(first_error_64(&arrays(64)), None);
    let tuples = format!("const X: T = {}x{};", "(".repeat(63), ",)".repeat(63));
    assert_eq!(first_error_64(&tuples), None);
    // A group adds nothing.
    let groups = format!("const X: T = {}x{};", "(".repeat(60), ")".repeat(60));
    assert_eq!(first_error_64(&groups), None);
}

#[test]
fn a_deep_container_value_dumps_and_drops() {
    let n = 3000;
    let input = format!(
        "const X: {}T{} = {}0{};",
        "(".repeat(n),
        ",)".repeat(n),
        "[".repeat(n),
        "]".repeat(n)
    );
    let parsed = crate::parse_with_depth(&input, 4096).unwrap();
    assert!(parsed.errors.is_empty());
    assert!(parsed.dump().unwrap().unwrap().len() > n);
}

#[test]
fn lookahead_work_is_linear() {
    // Each line would scan to the end of the input if the look ahead had no stop.
    let n = 20_000;
    for unit in ["a[;\n", "(;\n", "a.b[;\n", "a[{\n"] {
        let input = format!("module M() {{ {}", unit.repeat(n));
        let parsed = parse(&input);
        assert!(!parsed.errors.is_empty());
        assert_eq!(parsed.syntax().text().to_string(), input);
    }
}

/// The decimal digits of 2^65536.
fn two_pow_65536() -> String {
    let hex = format!("1{}", "0".repeat(16384));
    crate::ast::Nat::from_digits(&hex, 16).as_str().to_owned()
}

#[test]
fn a_number_is_below_2_pow_65536() {
    let literal = |text: &str| first_error(&format!("const X: T = {text};"));
    let hit = Some((Code::S001, 1, 14));
    // Hexadecimal and binary: 2^65536 - 1 passes and 2^65536 fails.
    assert_eq!(literal(&format!("0x{}", "f".repeat(16384))), None);
    assert_eq!(literal(&format!("0x1{}", "0".repeat(16384))), hit);
    assert_eq!(literal(&format!("0b{}", "1".repeat(65536))), None);
    assert_eq!(literal(&format!("0b1{}", "0".repeat(65536))), hit);
    // Decimal, with the exact check at the boundary.
    let limit = two_pow_65536();
    assert_eq!(limit.len(), 19729);
    let mut below = limit.clone().into_bytes();
    assert_eq!(below.pop(), Some(b'6'));
    below.push(b'5');
    assert_eq!(literal(&String::from_utf8(below).unwrap_or_default()), None);
    assert_eq!(literal(&limit), hit);
    assert_eq!(literal(&format!("1{}", "0".repeat(19729))), hit);
    // Leading zeros do not count.
    assert_eq!(literal(&format!("0x{}f", "0".repeat(100_000))), None);
    assert_eq!(literal(&format!("0b{}1", "0".repeat(100_000))), None);
    assert_eq!(literal(&format!("{}7", "0".repeat(100_000))), None);
    assert_eq!(literal(&format!("0x000{}", "f".repeat(16384))), None);
    // A huge literal fails at once.
    assert_eq!(literal(&"9".repeat(1_000_000)), hit);
    assert_eq!(literal(&format!("0x{}", "f".repeat(1_000_000))), hit);
}

#[test]
fn the_default_syntax_depth_is_4096() {
    let max = DEFAULT_SYNTAX_DEPTH;
    assert_eq!(max, 4096);
    let at = |n: usize| Some((Code::S001, 1, n));
    let nest = |n: usize| format!("const X: T = {}1{};", "(".repeat(n), ")".repeat(n));
    assert_eq!(first_error(&nest(max)), None);
    assert_eq!(first_error(&nest(max + 1)), at(14 + max));
    let call = |n: usize| format!("const X: T = {}1{};", "f(".repeat(n), ")".repeat(n));
    // The calls make the height, and the brackets are the limit for the error below it.
    assert_eq!(first_error(&call(max - 1)), None);
    assert_eq!(first_error(&call(max)), at(14));
    assert_eq!(first_error(&call(max + 1)), at(15 + 2 * max));
    let ty = |n: usize| format!("const X: {}T{} = 1;", "A[".repeat(n), "]".repeat(n));
    assert_eq!(first_error(&ty(max - 1)), None);
    assert_eq!(first_error(&ty(max)), at(10));
    assert_eq!(first_error(&ty(max + 1)), at(11 + 2 * max));
    let blocks = |n: usize| format!("module M() {}{}", "{".repeat(n), "}".repeat(n));
    assert_eq!(first_error(&blocks(max)), None);
    assert_eq!(first_error(&blocks(max + 1)), at(12 + max));
    // A chain has height 4096 and no bracket: it passes, and one more operand fails.
    let chain = |n: usize| format!("const X: T = {};", vec!["a"; n].join(" + "));
    assert_eq!(first_error(&chain(max)), None);
    assert_eq!(first_error(&chain(max + 1)), at(14));
    let unary = |n: usize| format!("const X: T = {}1;", "-".repeat(n));
    assert_eq!(first_error(&unary(max - 1)), None);
    assert_eq!(first_error(&unary(max)), at(14));
}

#[test]
fn a_million_open_brackets_give_s001_at_the_first_excess() {
    let max = DEFAULT_SYNTAX_DEPTH;
    for open in ["(", "f(", "a[", "if (a) { ", "{"] {
        let input = format!("module M() {}", open.repeat(1_000_000));
        let parsed = parse(&input);
        let first = parsed.errors.first().map(|e| (e.code, e.pos.line));
        assert_eq!(first, Some((Code::S001, 1)), "{open}");
    }
    // The first bracket above the depth, with `(` of the module closed after its parameters.
    let input = format!("module M() {}", "{".repeat(1_000_000));
    assert_eq!(first_error(&input), Some((Code::S001, 1, 12 + max)));
    let input = format!("const X: T = {}", "(".repeat(1_000_000));
    assert_eq!(first_error(&input), Some((Code::S001, 1, 14 + max)));
}

#[test]
fn a_million_long_chain_gives_the_height_error_at_the_first_token() {
    let at = Some((Code::S001, 1, 14));
    let sum = format!("const X: T = {};", vec!["a"; 1_000_000].join("+"));
    assert_eq!(first_error(&sum), at);
    let neg = format!("const X: T = {}1;", "-".repeat(1_000_000));
    assert_eq!(first_error(&neg), at);
    let field = format!("const X: T = a{};", ".b".repeat(1_000_000));
    assert_eq!(first_error(&field), at);
    let index = format!("const X: T = a{};", "[1]".repeat(1_000_000));
    assert_eq!(first_error(&index), Some((Code::S001, 1, 14)));
    // The tree stays lossless and shallow, so freeing it needs a small stack.
    let parsed = parse(&neg);
    assert_lossless(&parsed, &neg);
    let mut depth = 0;
    let mut node = parsed.syntax();
    while let Some(child) = node.first_child() {
        node = child;
        depth += 1;
    }
    assert!(depth <= 4 * DEFAULT_SYNTAX_DEPTH + 16, "{depth}");
}

#[test]
fn a_small_depth_bounds_the_tree_of_any_input() {
    // With the depth 1 the stack has about 1 MiB, so a deep tree would overflow it.
    for input in [
        format!("const X: T = {}1;", "-".repeat(200_000)),
        format!("const X: T = {};", vec!["a"; 200_000].join("+")),
        format!("module M() {}", "{ ) ".repeat(100_000)),
        format!("module M() {}", "{ ] ( ".repeat(50_000)),
    ] {
        let parsed = parse_with_depth(&input, 1);
        assert!(!parsed.errors.is_empty());
        assert_lossless(&parsed, &input);
    }
}

#[test]
fn the_syntax_depth_is_a_parameter() {
    let input = "const X: T = ((1));";
    assert!(parse_with_depth(input, 2).errors.is_empty());
    let errors = parse_with_depth(input, 1).errors.clone();
    assert_eq!(errors.len(), 1);
    assert_eq!((errors[0].pos.line, errors[0].pos.col), (1, 15));
    let high = parse_with_depth("const X: T = a + b;", 1).errors.clone();
    assert_eq!(high.len(), 1);
    assert!(high[0].message.contains("higher than 1 levels"));
}

#[test]
fn a_depth_outside_the_cap_is_an_error_value() {
    for depth in [0, crate::MAX_SYNTAX_DEPTH + 1, usize::MAX] {
        let err = crate::parse_with_depth("", depth).unwrap_err();
        assert_eq!(err, crate::DepthError::Range(depth));
    }
}

#[test]
fn the_depth_65536_works_at_the_cap() {
    let max = crate::MAX_SYNTAX_DEPTH;
    let at = |n: usize| Some((Code::S001, 1, n));
    let first = |input: &str| {
        parse_with_depth(input, max)
            .errors
            .first()
            .map(|e| (e.code, e.pos.line, e.pos.col))
    };
    let nest = |n: usize| format!("const X: T = {}1{};", "(".repeat(n), ")".repeat(n));
    assert_eq!(first(&nest(max)), None);
    assert_eq!(first(&nest(max + 1)), at(14 + max));
    // Height 65536 inside brackets of depth 65536.
    let input = format!(
        "const X: T = {}{}1{};",
        "(".repeat(max),
        "-".repeat(max - 1),
        ")".repeat(max)
    );
    let parsed = parse_with_depth(&input, max);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    assert!(parsed.dump().unwrap().is_some());
    let high = format!("const X: T = {}1;", "-".repeat(max));
    assert_eq!(first(&high), at(14));
}

#[test]
fn a_port_family_entry_has_a_key() {
    let dump = |input: &str| parse(input).dump().unwrap().unwrap().trim_end().to_owned();
    assert_eq!(
        dump("module M(comptime N: Nat) { input req[N + 1]: UInt[8]; output o: Bool; }"),
        "(module \"M\" ((param comptime \"N\" (name \"Nat\"))) none \
         ((input \"req\" (some (binary add (name \"N\") (num 1))) \
         (index (name \"UInt\") ((num 8)))) (output \"o\" none (name \"Bool\"))))"
    );
    assert_eq!(
        dump("module M() { output g[2]: Bool; }"),
        "(module \"M\" () none ((output \"g\" (some (num 2)) (name \"Bool\"))))"
    );
    let body = body("input req[i]: T; output g[1]: T;");
    let (
        Stmt::Input {
            form: PortForm::Indexed(i),
            ..
        },
        Stmt::Output {
            form: PortForm::Indexed(g),
            ..
        },
    ) = (&body[0], &body[1])
    else {
        panic!("expected two indexed ports");
    };
    assert_eq!((sx(i), sx(g)), ("i".to_owned(), "1".to_owned()));
}

#[test]
fn the_key_of_a_port_family_is_one_expression() {
    for (input, line, col) in [
        ("module M() { input i[]: T; }", 1, 22),
        ("module M() { input i[a, b]: T; }", 1, 23),
        ("module M() { output o[1: T; }", 1, 24),
        ("module M() { input i[1] T; }", 1, 25),
    ] {
        assert_eq!(first_error(input), Some((Code::S001, line, col)), "{input}");
    }
}

#[test]
fn an_indexed_port_takes_no_as_key() {
    let parsed = parse("module M() { input i[1]: T as 1; }");
    let error = &parsed.errors[0];
    assert_eq!((error.code, error.pos), (Code::S001, pos(1, 28)));
    assert_eq!(
        error.message,
        "an indexed port takes no `as` key; declare a scalar port with `as PortKey(\"i\", true, k)`"
    );
}

#[test]
fn an_as_key_is_one_expression_after_the_type() {
    let dump = |input: &str| parse(input).dump().unwrap().unwrap().trim_end().to_owned();
    assert_eq!(
        dump("module M() { input a: UInt[8] as \"x\" + str(N); output b: Bool as k; }"),
        "(module \"M\" () none ((input \"a\" (keyed (binary add (str \"x\") (call (name \"str\") \
         ((name \"N\"))))) (index (name \"UInt\") ((num 8)))) \
         (output \"b\" (keyed (name \"k\")) (name \"Bool\"))))"
    );
    for (input, line, col) in [
        ("module M() { input a: T as ; }", 1, 28),
        ("module M() { input a: T as 1 }", 1, 30),
        ("module M() { input a: T as 1 as 2; }", 1, 30),
    ] {
        assert_eq!(first_error(input), Some((Code::S001, line, col)), "{input}");
    }
}

#[test]
fn a_key_at_the_syntax_depth_limit_parses_dumps_and_drops() {
    let max = DEFAULT_SYNTAX_DEPTH;
    let key = |n: usize| format!("{}1{}", "(".repeat(n), ")".repeat(n));
    // The module and the key share the depth, as a bracket of `[ ]` counts too.
    let at = format!("module M() {{ input r[{}]: T; }}", key(max - 3));
    let parsed = parse(&at);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    assert!(parsed.ast.is_some());
    assert!(
        parsed
            .dump()
            .unwrap()
            .is_some_and(|d| d.contains("(some (num 1))"))
    );
    drop(parsed);
    let over = format!("module M() {{ input r[{}]: T; }}", key(max));
    let parsed = parse(&over);
    assert_eq!(parsed.errors.first().map(|e| e.code), Some(Code::S001));
    assert!(parsed.ast.is_none());
    // A chain at the height limit is a key as well.
    let chain = format!(
        "module M() {{ output r[{}]: T; }}",
        vec!["a"; max - 2].join(" + ")
    );
    let parsed = parse(&chain);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    assert!(parsed.dump().unwrap().is_some());
}

#[test]
fn a_deep_ast_dumps_and_drops_on_the_stack_for_the_depth() {
    let max = DEFAULT_SYNTAX_DEPTH;
    // Blocks and a chain at the limit: about two levels of the AST for each level of the depth.
    let input = format!(
        "module M() {}{};{}",
        "{".repeat(max - 1),
        vec!["a"; max].join(" + "),
        " }".repeat(max - 1)
    );
    let parsed = parse(&input);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    let dump = parsed.dump().unwrap();
    assert!(dump.is_some_and(|d| d.starts_with("(module")));
}

#[test]
fn a_node_starts_at_its_first_token() {
    // Lowering takes the position of a node from its start, so no node may start with trivia.
    let input = "// a\nconst /* b */ X: T = /* c */ ( /* d */ a /* e */ + b ) // f\n  + f(/* g */1,\n 2) + a.b;\nmodule M() { /* i */ let x = /* j */ -1; { /* k */ } if (a) { 1 } else { /* l */ 2 }; }";
    let parsed = parse(input);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    // The root holds the first trivia, and lowering never asks for its position.
    for node in parsed.syntax().descendants().skip(1) {
        let first = node
            .descendants_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| !t.kind().is_trivia());
        if let Some(first) = first {
            assert_eq!(
                node.text_range().start(),
                first.text_range().start(),
                "{node:?}"
            );
        }
    }
}

#[test]
fn lowering_is_linear() {
    // Both inputs parse without error, and lowering of each took the square of the length.
    let chain = format!("const X: T = {};", vec!["a"; 4096].join(" + "));
    assert!(parse(&chain).errors.is_empty());
    let flat = format!("module M() {{ {} }}", "x := y;\n".repeat(100_000));
    assert!(parse(&flat).errors.is_empty());
    let items = "const X: T = 1;\n".repeat(100_000);
    assert!(parse(&items).errors.is_empty());
}

#[test]
fn a_large_number_ends_the_look_ahead_like_a_lexical_error() {
    // The token list of the Lean lexer ends at the number, so the look ahead does not see
    // the delimiters after it, and the error is S001 at the number, not S004 before it.
    let big = format!("0x1{}", "0".repeat(16384));
    let tuple = format!("const X: T = ({big},1);");
    assert_eq!(first_error(&tuple), Some((Code::S001, 1, 15)));
    let place = format!("module M() {{ a[{big}] = 1; }}");
    assert_eq!(first_error(&place), Some((Code::S001, 1, 16)));
}

#[test]
fn a_deep_result_is_safe_on_the_stack_of_a_test_thread() {
    // This thread has the default stack of a test. The parse and the dump run on their own
    // thread with the stack for the depth. The drop, and the reads, run here.
    let max = crate::MAX_SYNTAX_DEPTH;
    let unary = format!("const X: T = {}1;", "-".repeat(max - 1));
    let brackets = format!("const X: T = {}1{};", "(".repeat(max), ")".repeat(max));
    for input in [unary, brackets] {
        let parsed = parse_with_depth(&input, max);
        assert!(parsed.errors.is_empty());
        assert!(parsed.ast.is_some());
        assert!(
            parsed
                .dump()
                .unwrap()
                .is_some_and(|d| d.starts_with("(const"))
        );
        drop(parsed);
    }
}

#[test]
fn into_ast_gives_the_items_and_the_depth_or_the_parse() {
    let (items, depth) = parse_with_depth("const A: Nat = 1;", 7).into_ast().unwrap();
    assert_eq!((items.len(), depth), (1, 7));
    assert!(parse("const A: Nat = ;").into_ast().is_err());
}

/// The result of `parse_expr`: the shape, or the first error as code, line, and column.
fn expr_result(input: &str, depth: usize) -> Result<String, (Code, usize, usize)> {
    crate::parse_expr(input, depth)
        .unwrap()
        .map(|e| sx(e.expr()))
        .map_err(|errors| {
            let e = &errors[0];
            (e.code, e.pos.line, e.pos.col)
        })
}

#[test]
fn an_expression_of_the_command_line() {
    let ok = |input: &str| expr_result(input, DEFAULT_SYNTAX_DEPTH);
    assert_eq!(ok("1 + 2 * 3").unwrap(), "(add 1 (mul 2 3))");
    assert_eq!(ok(" UInt[8](3) ").unwrap(), "(call (index UInt 8) 3)");
    assert_eq!(ok("if (a) { b } else { c }").unwrap(), "(if a b c)");
    assert_eq!(ok("1 +"), Err((Code::S001, 1, 4)));
    assert_eq!(ok("1 2"), Err((Code::S001, 1, 3)));
    assert_eq!(ok(""), Err((Code::S001, 1, 1)));
    assert_eq!(ok("1; 2"), Err((Code::S001, 1, 2)));
    assert_eq!(ok("1 $"), Err((Code::S001, 1, 3)));
    // A bracket above the depth ranks before a height error.
    assert_eq!(expr_result("((1)) $", 1), Err((Code::S001, 1, 2)));
    assert_eq!(expr_result("-(-1)", 2), Err((Code::S001, 1, 1)));
    assert_eq!(expr_result("-(-1)", 3).unwrap(), "(neg (neg 1))");
    assert!(matches!(
        crate::parse_expr("1", 0),
        Err(crate::DepthError::Range(0))
    ));
}

#[test]
fn a_receiver_call_lowers_with_the_positions_of_lean() {
    let parsed = parse("const X: T = (a).f(x);");
    let Some([Item::Const { value, .. }]) = parsed.ast.as_deref() else {
        panic!("{parsed:?}");
    };
    let Expr::Method {
        pos: p,
        recv,
        name,
        args,
        ..
    } = value
    else {
        panic!("not a method");
    };
    assert_eq!(*p, pos(1, 14));
    assert!(matches!(&**recv, Expr::Name { pos: q, .. } if *q == pos(1, 15)));
    assert_eq!(name.pos, pos(1, 18));
    assert!(matches!(args.as_slice(), [Expr::Name { pos: r, .. }] if *r == pos(1, 20)));
    assert_eq!(shape("x.f().g()"), "(method (method x f ) g )");
}

#[test]
fn a_function_parameter_has_the_mode_of_its_mark() {
    let parsed = parse("fn f(x: T,\n  mut y: T, comptime z: T) -> T {}");
    let Some([Item::Fn { params, .. }]) = parsed.ast.as_deref() else {
        panic!("{parsed:?}");
    };
    let modes: Vec<_> = params.iter().map(|p| p.mode).collect();
    assert_eq!(
        modes,
        [ParamMode::None, ParamMode::Mut, ParamMode::Comptime]
    );
    assert_eq!(params[1].pos, pos(2, 3));
    assert_eq!(params[1].name.pos, pos(2, 7));
}

#[test]
fn a_method_chain_is_bound_by_the_syntax_depth() {
    let chain = |n: usize| format!("const X: T = x{};", ".f()".repeat(n));
    assert_eq!(first_error_64(&chain(63)), None);
    assert_eq!(first_error_64(&chain(64)), Some((Code::S001, 1, 14)));
    assert_eq!(first_error(&chain(4095)), None);
    assert_eq!(first_error(&chain(4096)), Some((Code::S001, 1, 14)));
    let long = format!("module M() {{ {} }}", "x.f(y).g(z.h());".repeat(10_000));
    assert_eq!(first_error(&long), None);
}

/// The type of `const X: <ty> = 0;` as the shape of the type.
fn type_shape(ty: &str) -> String {
    let parsed = parse(&format!("const X: {ty} = 0;"));
    assert!(parsed.errors.is_empty(), "{ty}: {:?}", parsed.errors);
    match parsed.ast.as_deref() {
        Some([Item::Const { ty, .. }]) => tx(ty),
        other => panic!("{other:?}"),
    }
}

#[test]
fn function_types_parse_in_an_expression() {
    for (input, shape_text) in [
        ("fn () -> T", "(fntype () -> T)"),
        ("fn (T, mut U) -> V", "(fntype (T mut U) -> V)"),
        ("fn (T,) -> U", "(fntype (T) -> U)"),
        ("fn (mut T,) -> U", "(fntype (mut T) -> U)"),
        ("fn (A) -> fn (B) -> T", "(fntype (A) -> (fn (B) -> T))"),
        // The result type takes the suffixes.
        ("fn () -> UInt[8]", "(fntype () -> (index UInt 8))"),
        (
            "fn (UInt[8]) -> (T, U)",
            "(fntype ((index UInt 8)) -> (tuple T U))",
        ),
        // A function type is a unary operand.
        ("-fn () -> T", "(neg (fntype () -> T))"),
        ("a + fn () -> T", "(add a (fntype () -> T))"),
        ("fn () -> T + a", "(add (fntype () -> T) a)"),
        ("f(fn () -> T, a)", "(call f (fntype () -> T) a)"),
        // A group makes the function type the base of a suffix.
        ("(fn () -> T)[8]", "(index (fntype () -> T) 8)"),
        ("(fn () -> T)(a)", "(call (fntype () -> T) a)"),
        ("[fn () -> T; 4]", "(arraytype (fn () -> T) 4)"),
    ] {
        assert_eq!(shape(input), shape_text, "{input}");
    }
}

#[test]
fn function_types_parse_in_a_type() {
    for (input, shape_text) in [
        ("fn (T, mut U) -> V", "(fn (T mut U) -> V)"),
        ("fn (A) -> fn (B) -> T", "(fn (A) -> (fn (B) -> T))"),
        ("fn () -> UInt[8]", "(fn () -> (index UInt 8))"),
        ("(fn () -> T)", "(fn () -> T)"),
        ("(fn () -> T)[8]", "(index (fn () -> T) 8)"),
        ("(fn () -> T, U)", "(tuple (fn () -> T) U)"),
        ("[fn () -> T; 2]", "(array (fn () -> T) 2)"),
        ("fn (fn (A) -> B) -> C", "(fn ((fn (A) -> B)) -> C)"),
    ] {
        assert_eq!(type_shape(input), shape_text, "{input}");
    }
    let stmts = body("let f: fn (T) -> U = g; type F = fn () -> T;");
    assert!(matches!(
        stmts.as_slice(),
        [
            Stmt::Local {
                ty: Some(TypeExpr::Fn { .. }),
                ..
            },
            Stmt::Alias {
                ty: TypeExpr::Fn { .. },
                ..
            }
        ]
    ));
}

#[test]
fn function_types_keep_their_positions() {
    let parsed = parse("const X: fn () -> T = -fn (T) -> fn () -> U;");
    let Some([Item::Const { ty, value, .. }]) = parsed.ast.as_deref() else {
        panic!("{:?}", parsed.errors);
    };
    assert!(matches!(ty, TypeExpr::Fn { pos: p, .. } if *p == pos(1, 10)));
    let Expr::Unary { arg, .. } = value else {
        panic!("not a unary");
    };
    let Expr::FnType { pos: at, ret, .. } = &**arg else {
        panic!("not a function type");
    };
    assert_eq!(*at, pos(1, 24));
    assert!(matches!(&**ret, TypeExpr::Fn { pos: p, .. } if *p == pos(1, 34)));
}

#[test]
fn function_type_errors_are_at_the_offending_token() {
    for (input, code, col) in [
        ("const X: T = fn (comptime T) -> U;", Code::S001, 18),
        ("const X: T = fn (T, comptime U) -> V;", Code::S001, 21),
        ("const X: T = fn (mut comptime T) -> U;", Code::S001, 22),
        ("const X: fn (comptime T) -> U = 0;", Code::S001, 14),
        ("const X: T = fn (T) U;", Code::S001, 21),
        ("const X: T = fn (T -> U;", Code::S001, 20),
        ("const X: T = fn (,) -> U;", Code::S001, 18),
        ("const X: T = fn (x: T) -> U;", Code::S001, 19),
        ("const X: T = fn (T U) -> V;", Code::S001, 20),
        ("const X: T = fn (T) -> ;", Code::S001, 24),
        ("const X: T = fn T -> U;", Code::S001, 17),
        ("const X: T = fn (mut mut T) -> U;", Code::S001, 22),
    ] {
        assert_eq!(first_error(input), Some((code, 1, col)), "{input}");
    }
}

#[test]
fn the_height_of_a_function_type_is_one_plus_the_largest_part() {
    let at = |n: usize| Some((Code::S001, 1, n));
    // A chain of n function types has the height n + 1.
    let chain = |n: usize| format!("const X: T = {}T;", "fn () -> ".repeat(n));
    assert_eq!(first_error_64(&chain(63)), None);
    assert_eq!(first_error_64(&chain(64)), at(14));
    let chain_ty = |n: usize| format!("const X: {}T = 0;", "fn () -> ".repeat(n));
    assert_eq!(first_error_64(&chain_ty(63)), None);
    assert_eq!(first_error_64(&chain_ty(64)), at(10));
    // The parameter types count in the same way, and a `mut` mark adds none.
    for mark in ["", "mut "] {
        let nested = |n: usize| {
            format!(
                "const X: T = {}T{};",
                format!("fn ({mark}").repeat(n),
                ") -> T".repeat(n)
            )
        };
        assert_eq!(first_error_64(&nested(63)), None, "{mark}");
        assert_eq!(first_error_64(&nested(64)), at(14), "{mark}");
    }
    // A unary operator adds 1 to the function type.
    let neg = |n: usize| format!("const X: T = -{}T;", "fn () -> ".repeat(n));
    assert_eq!(first_error_64(&neg(62)), None);
    assert_eq!(first_error_64(&neg(63)), at(14));
    // The suffixes of the result type add to its height.
    let suffix = |n: usize| format!("const X: T = fn () -> T{};", "[1]".repeat(n));
    assert_eq!(first_error_64(&suffix(62)), None);
    assert_eq!(first_error_64(&suffix(63)), at(14));
}

#[test]
fn a_million_long_chain_of_function_types_gives_the_height_error() {
    let chain = "fn () -> ".repeat(1_000_000);
    assert_eq!(
        first_error(&format!("const X: T = {chain}T;")),
        Some((Code::S001, 1, 14))
    );
    assert_eq!(
        first_error(&format!("const X: {chain}T = 0;")),
        Some((Code::S001, 1, 10))
    );
    let parsed = parse(&format!("const X: T = -{chain}T;"));
    assert_eq!(parsed.errors.len(), 1);
    assert!(parsed.ast.is_none());
}

#[test]
fn a_deep_chain_of_function_types_drops_without_recursion() {
    let n = 2000;
    let input = format!("const X: {0}T = {0}T;", "fn (U) -> ".repeat(n));
    let parsed = parse(&input);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    assert_lossless(&parsed, &input);
    drop(parsed);
    let nested = format!("const X: T = {}T{};", "fn (".repeat(n), ") -> T".repeat(n));
    let parsed = parse(&nested);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    drop(parsed);
}

#[test]
fn builtins_are_primaries_with_their_operands() {
    for (input, want) in [
        ("@TypeOf(x)", "(@TypeOf x)"),
        ("@TypeOf((x))", "(@TypeOf x)"),
        (
            "@TypeOf(a.b[1].0)",
            "(@TypeOf (select (index (field a b) 1) 0))",
        ),
        ("@field(a, \"f\")", "(@field a \"f\")"),
        ("@field(a, 1,)", "(@field a 1)"),
        ("@field(a, k).g[0]", "(index (field (@field a k) g) 0)"),
        ("1 + @TypeOf(x)", "(add 1 (@TypeOf x))"),
        ("@typeInfo(T)", "(@typeInfo T)"),
        ("@Struct(fs)", "(@Struct fs)"),
        ("@Struct([])", "(@Struct (array ))"),
        ("@Struct(f(x),)", "(@Struct (call f x))"),
        ("@Struct(fs).a", "(field (@Struct fs) a)"),
        ("@typeInfo(@Struct(a))", "(@typeInfo (@Struct a))"),
        ("@typeInfo(a + b)", "(@typeInfo (add a b))"),
        ("@typeInfo(f(x),)", "(@typeInfo (call f x))"),
        ("@typeInfo(T).fields", "(field (@typeInfo T) fields)"),
        ("@typeInfo(@TypeOf(x))", "(@typeInfo (@TypeOf x))"),
        ("@field(f(x), g(y))", "(@field (call f x) (call g y))"),
        ("@field(@field(a, 0), 1)", "(@field (@field a 0) 1)"),
        ("@field(a, 0)(x)", "(call (@field a 0) x)"),
    ] {
        assert_eq!(shape(input), want, "{input}");
    }
}

#[test]
fn ports_takes_a_place_and_is_no_place() {
    let cases = [
        // `@ports(u)` is no place, so it is no target, and no selection of it is one.
        ("module M() { @ports(u).a = 1; }", Code::S001, 1, 26),
        ("module M() { @ports(u)[0] = 1; }", Code::S001, 1, 27),
        ("module M() { @ports(u) = 1; }", Code::S001, 1, 24),
        // The operand of `@ports` is a place, as for `@TypeOf`.
        ("const X: T = @ports(1);", Code::S001, 1, 21),
        ("const X: T = @ports(f(x));", Code::S001, 1, 21),
        ("const X: T = @ports((a + b));", Code::S001, 1, 21),
        ("const X: T = @ports(E::V);", Code::S001, 1, 21),
        ("const X: T = @ports(@ports(u));", Code::S001, 1, 21),
        ("const X: T = @ports(@field(f(x), k));", Code::S001, 1, 21),
        ("const X: T = @ports();", Code::S001, 1, 15),
        ("const X: T = @ports(a, b);", Code::S001, 1, 15),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, code, line, col)| first_error(input) != Some((*code, *line, *col)))
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
}

#[test]
fn a_missing_builtin_name_has_the_text_of_lean() {
    for input in ["const X: @ = 1;", "const X: T = @;"] {
        let parsed = parse(input);
        assert_eq!(
            parsed.errors.first().map(|e| e.message.as_str()),
            Some("expected a builtin name"),
            "{input}"
        );
    }
}

#[test]
fn a_builtin_in_a_type_and_the_struct_builtin_follow_the_rules_of_a_builtin() {
    let cases = [
        // The same rules in an expression.
        ("const X: T = @Struct();", Code::S001, 1, 15),
        ("const X: T = @Struct(a, b);", Code::S001, 1, 15),
        ("module M() { @Struct(x) = 1; }", Code::S001, 1, 25),
        ("const X: @Struct() = 1;", Code::S001, 1, 11),
        ("const X: @Struct(a, b) = 1;", Code::S001, 1, 11),
        ("const X: @TypeOf() = 1;", Code::S001, 1, 11),
        ("const X: @Struct(fs)(1) = 1;", Code::S004, 1, 21),
        ("const X: @Struct(fs $) = 1;", Code::S001, 1, 21),
        ("const X: @ports() = 1;", Code::S001, 1, 11),
        ("const X: @ports(1) = 1;", Code::S001, 1, 17),
    ];
    let wrong: Vec<_> = cases
        .iter()
        .filter(|(input, code, line, col)| first_error(input) != Some((*code, *line, *col)))
        .map(|(input, ..)| (input, first_error(input)))
        .collect();
    assert_eq!(wrong, []);
}

#[test]
fn a_builtin_stands_in_a_type_position() {
    for (ty, want) in [
        ("@TypeOf(x)", "(@TypeOf x)"),
        ("@Struct(fs)", "(@Struct fs)"),
        ("@typeInfo(T)", "(@typeInfo T)"),
        ("@field(a, \"t\")", "(@field a \"t\")"),
        // The suffixes of a type follow the builtin.
        ("@TypeOf(x)[8]", "(index (@TypeOf x) 8)"),
        ("@ports(u)[0]", "(index (@ports u) 0)"),
        ("@Struct(fs)[8][2]", "(index (index (@Struct fs) 8) 2)"),
        // A builtin is a type form in each type position.
        ("[@TypeOf(x); 4]", "(array (@TypeOf x) 4)"),
        ("(@TypeOf(x), T)", "(tuple (@TypeOf x) T)"),
        ("(@TypeOf(x))", "(@TypeOf x)"),
        (
            "fn (@TypeOf(x), mut @Struct(fs)) -> @TypeOf(y)",
            "(fn ((@TypeOf x) mut (@Struct fs)) -> (@TypeOf y))",
        ),
    ] {
        assert_eq!(type_shape(ty), want, "{ty}");
    }
    let stmts = body("let x: @TypeOf(y) = 1; type A = @Struct([]);");
    assert!(matches!(
        stmts.as_slice(),
        [
            Stmt::Local {
                ty: Some(TypeExpr::Builtin { .. }),
                ..
            },
            Stmt::Alias {
                ty: TypeExpr::Builtin { .. },
                ..
            }
        ]
    ));
}

#[test]
fn a_builtin_type_has_the_position_of_its_at() {
    let parsed = parse("const X: @TypeOf(x)[8] = 0;");
    let Some([Item::Const { ty, .. }]) = parsed.ast.as_deref() else {
        panic!("{:?}", parsed.errors);
    };
    let TypeExpr::Index {
        pos: index, base, ..
    } = ty
    else {
        panic!("not an index");
    };
    assert_eq!(*index, pos(1, 10));
    assert!(matches!(&**base, TypeExpr::Builtin { pos: p, .. } if *p == pos(1, 10)));
}

#[test]
fn a_builtin_in_a_type_dumps_as_lean_prints_it() {
    for (ty, want) in [
        (
            "@TypeOf(x)",
            "(const \"X\" (builtin TypeOf ((name \"x\"))) (num 0))\n",
        ),
        (
            "@Struct(fs)[8]",
            "(const \"X\" (index (builtin Struct ((name \"fs\"))) ((num 8))) (num 0))\n",
        ),
        (
            "[@TypeOf(x); 4]",
            "(const \"X\" (array (builtin TypeOf ((name \"x\"))) (num 4)) (num 0))\n",
        ),
        (
            "@ports(u)[0]",
            "(const \"X\" (index (builtin ports ((name \"u\"))) ((num 0))) (num 0))\n",
        ),
    ] {
        let text = parse(&format!("const X: {ty} = 0;"))
            .dump()
            .unwrap()
            .unwrap();
        assert_eq!(text, want, "{ty}");
    }
}

#[test]
fn a_chain_of_builtins_in_a_type_drops_without_recursion() {
    let n = 1000;
    let input = format!("const X: {}T{} = 0;", "@typeInfo(".repeat(n), ")".repeat(n));
    let parsed = parse(&input);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    assert_lossless(&parsed, &input);
    drop(parsed);
}

#[test]
fn a_builtin_dumps_as_lean_prints_it() {
    for (input, want) in [
        ("@TypeOf(x)", "(builtin TypeOf ((name \"x\")))"),
        ("@typeInfo(T)", "(builtin typeInfo ((name \"T\")))"),
        ("@Struct(fs)", "(builtin Struct ((name \"fs\")))"),
        ("@Struct([])", "(builtin Struct ((array ())))"),
        (
            "@typeInfo(a + b)",
            "(builtin typeInfo ((binary add (name \"a\") (name \"b\"))))",
        ),
        (
            "@field(a.b, \"c\")",
            "(builtin field ((field (name \"a\") \"b\") (str \"c\")))",
        ),
        ("@ports(u)", "(builtin ports ((name \"u\")))"),
        (
            "@ports(us[0])",
            "(builtin ports ((index (name \"us\") ((num 0)))))",
        ),
        (
            "@ports(u.a)",
            "(builtin ports ((field (name \"u\") \"a\")))",
        ),
        (
            "@ports(@field(us, 0))",
            "(builtin ports ((builtin field ((name \"us\") (num 0)))))",
        ),
    ] {
        assert_eq!(expr_dump(input), want, "{input}");
    }
}

#[test]
fn the_text_of_a_builtin_error_equals_lean() {
    let long = "x".repeat(70);
    for (input, want) in [
        (
            "const X: T = @x(y);".to_owned(),
            "`@x` is not a builtin; use `@TypeOf`, `@typeInfo`, `@Struct`, `@field`, or `@ports`"
                .to_owned(),
        ),
        (
            format!("const X: T = @{long}(y);"),
            format!(
                "`@{}... (70 characters)` is not a builtin; use `@TypeOf`, `@typeInfo`, \
                 `@Struct`, `@field`, or `@ports`",
                "x".repeat(64)
            ),
        ),
        (
            "const X: @x(y) = 1;".to_owned(),
            "`@x` is not a builtin; use `@TypeOf`, `@typeInfo`, `@Struct`, `@field`, or `@ports`"
                .to_owned(),
        ),
        (
            "const X: T = @TypeOf(a, b);".to_owned(),
            "`@TypeOf` takes 1 argument(s), but it has 2; write `@TypeOf(x)`".to_owned(),
        ),
        (
            "const X: T = @field(a);".to_owned(),
            "`@field` takes 2 argument(s), but it has 1; write `@field(x, k)`".to_owned(),
        ),
        (
            "const X: T = @TypeOf(a + b);".to_owned(),
            "`@TypeOf` takes a name or a selection of a name; bind the value with `let` and \
             pass the name"
                .to_owned(),
        ),
        (
            "const X: T = @typeInfo(a, b);".to_owned(),
            "`@typeInfo` takes 1 argument(s), but it has 2; write `@typeInfo(T)`".to_owned(),
        ),
        (
            "const X: T = @ports(a, b);".to_owned(),
            "`@ports` takes 1 argument(s), but it has 2; write `@ports(h)`".to_owned(),
        ),
        (
            "const X: T = @ports();".to_owned(),
            "`@ports` takes 1 argument(s), but it has 0; write `@ports(h)`".to_owned(),
        ),
        (
            "const X: @ports(1) = 1;".to_owned(),
            "`@ports` takes a name or a selection of a name; bind the value with `let` and \
             pass the name"
                .to_owned(),
        ),
    ] {
        let errors = parse(&input).errors;
        assert_eq!(
            errors.first().map(|e| e.message.clone()),
            Some(want),
            "{input}"
        );
    }
}

#[test]
fn a_deep_chain_of_builtins_dumps_and_drops() {
    // Each `@field(` is a bracket and a level of the height, so the chain ends at the limit.
    let n = DEFAULT_SYNTAX_DEPTH - 2;
    let input = format!(
        "module M() {{ {}a{} = 1; }}",
        "@field(".repeat(n),
        ", 0)".repeat(n)
    );
    let parsed = parse(&input);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors.first());
    assert!(
        parsed
            .dump()
            .unwrap()
            .is_some_and(|d| d.contains("(builtin field"))
    );
    // One more level is above the limit: S001, never a stack overflow.
    let over = format!(
        "const X: T = {}a{};",
        "@field(".repeat(DEFAULT_SYNTAX_DEPTH + 1),
        ", 0)".repeat(DEFAULT_SYNTAX_DEPTH + 1)
    );
    assert_eq!(first_error(&over).map(|e| e.0), Some(Code::S001));
}
