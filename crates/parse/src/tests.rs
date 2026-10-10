use crate::ast::{Expr, Item, Pos, Stmt, TypeExpr};
use crate::{Code, Parse, parse};
use proptest::prelude::*;

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
    assert_eq!(
        *ty,
        TypeExpr::Name {
            pos: pos(1, 10),
            name: "Nat".into()
        }
    );
    assert_eq!(sx(value), "8");
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
fn recovery_reports_later_errors() {
    let input = "const A: T = ;\nfn f() -> T { let = 1; reg r: T = 0; x +; }\nstruct S { }\nconst B: T = 1;\nconst C: T = ;";
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
    // A leaf has height 1, and each node and each pair of parentheses adds 1. The error is at
    // the first token of the first form with height 65, which is the outermost form here.
    let at = |n: usize| Some((Code::S001, 1, n));
    let nest = |n: usize| format!("const X: T = {}1{};", "(".repeat(n), ")".repeat(n));
    assert_eq!(first_error(&nest(63)), None);
    assert_eq!(first_error(&nest(64)), at(14));
    let call = |n: usize| format!("const X: T = {}1{};", "f(".repeat(n), ")".repeat(n));
    assert_eq!(first_error(&call(63)), None);
    assert_eq!(first_error(&call(64)), at(14));
    let unary = |n: usize| format!("const X: T = {}1;", "-".repeat(n));
    assert_eq!(first_error(&unary(63)), None);
    assert_eq!(first_error(&unary(64)), at(14));
    let chain = |n: usize| format!("const X: T = {};", vec!["a"; n].join(" + "));
    assert_eq!(first_error(&chain(64)), None);
    assert_eq!(first_error(&chain(65)), at(14));
    // The form of height 65 is found when it ends, so a deeper form comes first.
    let inner = format!("const X: T = 1 + {}1{};", "(".repeat(64), ")".repeat(64));
    assert_eq!(first_error(&inner), at(18));
    let ty = |n: usize| format!("const X: {}T{} = 1;", "A[".repeat(n), "]".repeat(n));
    assert_eq!(first_error(&ty(63)), None);
    assert_eq!(first_error(&ty(64)), at(10));
    let chain_ty = |n: usize| format!("const X: T{} = 1;", "[1]".repeat(n));
    assert_eq!(first_error(&chain_ty(63)), None);
    assert_eq!(first_error(&chain_ty(64)), at(10));
    // The height of a statement or an item is not limited.
    let long = format!("module M() {{ {} }}", "x; ".repeat(1000));
    assert_eq!(first_error(&long), None);
}

#[test]
fn blocks_nest_at_most_64_deep() {
    let blocks = |n: usize| format!("module M() {}{}", "{".repeat(n), "}".repeat(n));
    assert_eq!(first_error(&blocks(64)), None);
    // The 65th `{` is at column 12 + 64.
    assert_eq!(first_error(&blocks(65)), Some((Code::S001, 1, 76)));
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

proptest! {
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
    // would need more than 10^9 steps. The bound is generous, and the check is a
    // count of errors with a coarse time limit.
    let input = "$ ".repeat(50_000);
    let start = std::time::Instant::now();
    let parsed = parse(&input);
    assert_eq!(parsed.errors.len(), 50_000);
    assert_eq!(parsed.errors[49_999].pos, pos(1, 99_999));
    assert!(start.elapsed() < std::time::Duration::from_secs(5));
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
        let start = std::time::Instant::now();
        let parsed = parse(&input);
        assert!(!parsed.errors.is_empty());
        assert_eq!(parsed.syntax().text().to_string(), input);
        assert!(
            start.elapsed() < std::time::Duration::from_secs(5),
            "{unit:?}"
        );
    }
}
