// SPDX-License-Identifier: Apache-2.0
use crate::ast::{Expr, Item, Pos, Stmt, TypeExpr};
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
        Expr::Field { base, field, .. } => format!("(field {} {})", sx(base), field.name),
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
    assert!(params[0].comptime && !params[1].comptime);
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
    assert!(params[0].comptime);
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
        ("struct S { x: T }", 1, 1),
        ("type A = T;", 1, 1),
        ("extern module M() = \"m\" { }", 1, 1),
        ("module M() conforms A() using B() { }", 1, 12),
        ("module M() domains(a, b) { }", 1, 23),
        ("module M(x: Nat) { }", 1, 10), // S001: a module parameter needs comptime
        ("fn f(mut x: T) -> T { }", 1, 6),
        ("module M() { mem m: [T; 4]; }", 1, 14),
        ("module M() { type A = T; }", 1, 14),
        ("module M() { reg r: T in d = 0; }", 1, 23),
        ("module M() { wire w: T in d; }", 1, 24),
        ("module M() { input i[2]: T; }", 1, 21),
        ("module M() { input i: T as 1; }", 1, 25),
        ("module M() { instance u = A() with { }; }", 1, 31),
        ("module M() { instance u = a::A(); }", 1, 28),
        ("const X: T = (1, 2);", 1, 14),
        ("const X: T = ();", 1, 14),
        ("const X: T = [1, 2];", 1, 14),
        ("const X: T = x.0;", 1, 16),
        ("const X: T = @TypeOf(x);", 1, 14),
        ("const X: T = a::b;", 1, 15),
        ("const X: fn () -> T = f;", 1, 10),
        ("const X: (T, T) = f;", 1, 10),
        ("const X: [T; 4] = f;", 1, 10),
        ("const X: T() = f;", 1, 11),
        ("const X: a::T = f;", 1, 11),
        ("const X: T = fn () -> T;", 1, 14),
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
    assert_eq!(first_error("const X $ ; struct"), Some((Code::S001, 1, 9)));
    // S004 and S001 compete by position only.
    assert_eq!(first_error("struct S { } $"), Some((Code::S004, 1, 1)));
    assert_eq!(first_error("$ struct S { }"), Some((Code::S001, 1, 1)));
}

#[test]
fn a_plain_fn_has_no_hardware_statement() {
    for stmt in [
        "input a: Bool;",
        "output a: Bool;",
        "reg a: Bool = false;",
        "wire a: Bool;",
        "instance u = M();",
    ] {
        let src = format!("fn f() -> Nat {{\n  {stmt}\n  return 1;\n}}\n");
        assert_eq!(first_error(&src), Some((Code::S004, 2, 3)), "{stmt}");
        // `comptime fn` and `module` keep the statement. `typeck` checks the first.
        let comptime = format!("comptime fn f() -> Nat {{\n  {stmt}\n  return 1;\n}}\n");
        assert_eq!(first_error(&comptime), None, "{stmt}");
        let module = format!("module M() {{\n  {stmt}\n}}\n");
        assert_eq!(first_error(&module), None, "{stmt}");
    }
    // The rule ends with the body.
    let src = "fn f() -> Nat { return 1; }\nmodule M() { wire w: Bool; }\n";
    assert_eq!(first_error(src), None);
}

#[test]
fn recovery_reports_later_errors() {
    let input = "const A: T = ;\ncomptime fn f() -> T { let = 1; reg r: T = 0; x +; }\nstruct S { }\nconst B: T = 1;\nconst C: T = ;";
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
        first("const X: T = a + a + a + a;\nstruct S {}", 3),
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
    for open in ["(", "-", "f(", "{", "a[", "if (", "module M() {"] {
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
        // Receiver call: S004 at the `(`. A grouped selection is a call of a field.
        ("const X: T = x.f(1);", Code::S004, 1, 17),
        ("const X: T = x.f.g(1);", Code::S004, 1, 19),
        // `mut`: S001 at a module parameter, S004 at a function parameter.
        ("module M(mut x: T) { }", Code::S001, 1, 10),
        ("module M(comptime mut x: T) { }", Code::S001, 1, 19),
        ("fn f(mut x: T) -> T { }", Code::S004, 1, 6),
        // Tuples and units, with the look ahead for a comma.
        ("const X: T = (a.0, b);", Code::S004, 1, 14),
        ("const X: T = (f(a, b), (c)), d);", Code::S004, 1, 14),
        ("const X: T = (a, b", Code::S004, 1, 14),
        ("const X: T = (a $ , b);", Code::S001, 1, 17),
        ("const X: T = (a[1, 2], b);", Code::S004, 1, 14),
        ("const X: T = ((a, b));", Code::S004, 1, 15),
        // Targets with an index or a tuple field: S004 at the first name.
        ("module M() { x[i] = e; }", Code::S004, 1, 14),
        ("module M() { a.b[0] := e; }", Code::S004, 1, 14),
        ("module M() { a.0 = e; }", Code::S004, 1, 14),
        ("module M() { a.0x1 = e; }", Code::S004, 1, 14),
        ("module M() { a[1 +] = e; }", Code::S004, 1, 14),
        (
            "module M() { a[if (c) { 1 } else { 2 }] = e; }",
            Code::S004,
            1,
            14,
        ),
        ("module M() { a[f(x)].b = e; }", Code::S004, 1, 14),
        ("module M() { f(x)[0] = e; }", Code::S001, 1, 22),
        ("module M() { f(x) = e; }", Code::S001, 1, 19),
        // `x.0` in an expression, in any radix.
        ("const X: T = x.0x1;", Code::S004, 1, 16),
        ("const X: T = x.0b1;", Code::S004, 1, 16),
        // A statement with `if` is an expression statement and needs a `;`.
        ("module M() { if (a) { 1 } else { 2 } }", Code::S001, 1, 38),
        // A path is one name.
        ("module M() { instance u = a::B(); }", Code::S004, 1, 28),
        ("const X: a::T = 1;", Code::S004, 1, 11),
        // A builtin in a type is S004, as in an expression. Another name is S001.
        ("const X: @TypeOf(1) = 1;", Code::S004, 1, 10),
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
    ] {
        assert_eq!(first_error(ok), None, "{ok}");
    }
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
