-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Syntax

/-!
The AST dump of section 11.1 of the front-end design, and a source printer.

The Rust front end copies the dump byte for byte, so these rules fix each byte:

- A node prints as `(<constructor> <field> ...)`: the constructor name of `Source.Syntax` in
  lowercase, then each field in declaration order. One space separates two parts. A node with
  no fields cannot occur, so `(` is always followed by a name.
- The structure `Param` prints as `(param <comptime> <name> <ty>)`.
- A `pos` field does not print. An `Ident` prints as its name, as a string.
- A `String` prints in double quotes. It escapes `"`, `\`, LF, CR, and tab as `\"`, `\\`,
  `\n`, `\r`, and `\t`, the escapes of the grammar. Each other character prints as itself.
- A `Nat` prints in decimal without leading zeros. A `Bool` prints as `true` or `false`.
- A `UnOp` or a `BinOp` prints as its constructor name, for example `addw` for `+%`.
- A `List` prints as `(<element> ...)` with one space between two elements, and `()` if it is
  empty.
- An `Option` prints as `none`, or as `(some <value>)`.
- Each item prints on one line, and LF ends each line. The dump of no items is empty.
-/
namespace Silicon.Source.Print

/-! A string literal with the escapes of the grammar. The printer uses it too. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map escape) ++ "\""
where
  escape : Char → String
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | c => String.singleton c

def node (name : String) (fields : List String) : String :=
  "(" ++ " ".intercalate (name :: fields) ++ ")"

def list (xs : List String) : String := "(" ++ " ".intercalate xs ++ ")"

def option : Option String → String
  | none => "none"
  | some x => node "some" [x]

def boolean (b : Bool) : String := if b then "true" else "false"

def ident (i : Ident) : String := quote i.name

def args (xs : List String) : String := ", ".intercalate xs

def indent (depth : Nat) : String := "".pushn ' ' (4 * depth)

def unaryLevel : Nat := 10
def postfixLevel : Nat := 11

end Print

open Print

def UnOp.name : UnOp → String
  | .not => "not" | .inv => "inv" | .neg => "neg"

def BinOp.name : BinOp → String
  | .lor => "lor" | .land => "land" | .or => "or" | .xor => "xor" | .and => "and"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .shl => "shl" | .shr => "shr"
  | .add => "add" | .sub => "sub" | .addw => "addw" | .subw => "subw"
  | .mul => "mul" | .div => "div" | .rem => "rem" | .mulw => "mulw"

def Expr.dump : Expr → String
  | .num _ v => node "num" [toString v]
  | .bool _ v => node "bool" [boolean v]
  | .str _ v => node "str" [quote v]
  | .name _ n => node "name" [quote n]
  | .unary _ op a => node "unary" [op.name, a.dump]
  | .binary _ op l r => node "binary" [op.name, l.dump, r.dump]
  | .cond _ c y n => node "cond" [c.dump, y.dump, n.dump]
  | .call _ f args => node "call" [f.dump, list (args.map Expr.dump)]
  | .index _ b args => node "index" [b.dump, list (args.map Expr.dump)]
  | .field _ b f => node "field" [b.dump, ident f]

def TypeExpr.dump : TypeExpr → String
  | .name _ n => node "name" [quote n]
  | .index _ b args => node "index" [b.dump, list (args.map Expr.dump)]

def Stmt.dump : Stmt → String
  | .local _ m n ty v => node "local" [boolean m, ident n, option (ty.map TypeExpr.dump), v.dump]
  | .assign _ t v => node "assign" [t.dump, v.dump]
  | .connect _ t v => node "connect" [t.dump, v.dump]
  | .reg _ n ty i => node "reg" [ident n, ty.dump, i.dump]
  | .wire _ n ty => node "wire" [ident n, ty.dump]
  | .input _ n ty => node "input" [ident n, ty.dump]
  | .output _ n ty => node "output" [ident n, ty.dump]
  | .inst _ n m args => node "inst" [ident n, ident m, list (args.map Expr.dump)]
  | .ret _ v => node "ret" [option (v.map Expr.dump)]
  | .ctIf _ c y none => node "ctif" [c.dump, list (y.map Stmt.dump), option none]
  | .ctIf _ c y (some n) =>
    node "ctif" [c.dump, list (y.map Stmt.dump), option (some (list (n.map Stmt.dump)))]
  | .ctFor _ i lo hi b => node "ctfor" [ident i, lo.dump, hi.dump, list (b.map Stmt.dump)]
  | .block _ b => node "block" [list (b.map Stmt.dump)]
  | .expr _ v => node "expr" [v.dump]

def Param.dump (p : Param) : String :=
  node "param" [boolean p.comptime, ident p.name, p.ty.dump]

def Item.dump : Item → String
  | .const _ n ty v => node "const" [ident n, ty.dump, v.dump]
  | .fn _ c n ps r b =>
    node "fn" [boolean c, ident n, list (ps.map Param.dump), r.dump, list (b.map Stmt.dump)]
  | .module _ n ps ds b =>
    node "module" [ident n, list (ps.map Param.dump), option (ds.map (list ∘ List.map ident)),
      list (b.map Stmt.dump)]

/-! The AST dump of a source file. -/
def Print.dump (items : List Item) : String :=
  String.join (items.map fun i => i.dump ++ "\n")

/-!
The source printer. Its text parses back to the same AST up to positions, if the parser can
give that AST. Thus each name is a valid identifier, each `index` has an argument, and each
module parameter has `comptime`. The printer does not keep comments.

The binding power of an expression follows the levels of the grammar, from 0 for `if` to 11
for a postfix form or a primary. A form prints in parentheses where its context needs a
higher level. A `field` prints in parentheses also as the callee of a `call`.
-/

def BinOp.text : BinOp → String
  | .lor => "||" | .land => "&&" | .or => "|" | .xor => "^" | .and => "&"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .shl => "<<" | .shr => ">>"
  | .add => "+" | .sub => "-" | .addw => "+%" | .subw => "-%"
  | .mul => "*" | .div => "/" | .rem => "%" | .mulw => "*%"

def BinOp.level : BinOp → Nat
  | .lor => 1 | .land => 2 | .or => 3 | .xor => 4 | .and => 5
  | .eq | .ne | .lt | .le | .gt | .ge => 6
  | .shl | .shr => 7
  | .add | .sub | .addw | .subw => 8
  | .mul | .div | .rem | .mulw => 9

/-! A comparison is not associative, so neither of its operands can be a comparison. -/
def BinOp.associative (op : BinOp) : Bool := op.level != 6

def UnOp.text : UnOp → String
  | .not => "!" | .inv => "~" | .neg => "-"

def Expr.level : Expr → Nat
  | .cond .. => 0
  | .binary _ op .. => op.level
  | .unary .. => unaryLevel
  | _ => postfixLevel

/-! The text of `e` in a context that needs at least the level `ctx`. -/
def Expr.print (ctx : Nat) (e : Expr) : String :=
  let text := match e with
    | .num _ v => toString v
    | .bool _ v => boolean v
    | .str _ v => quote v
    | .name _ n => n
    | .unary _ op a => op.text ++ a.print unaryLevel
    | .binary _ op l r =>
      let lhs := if op.associative then op.level else op.level + 1
      l.print lhs ++ " " ++ op.text ++ " " ++ r.print (op.level + 1)
    | .cond _ c y n =>
      "if (" ++ c.print 0 ++ ") { " ++ y.print 0 ++ " } else { " ++ n.print 0 ++ " }"
    | .call _ f xs =>
      -- The parser reads `a.f(x)` as a receiver call, so a field callee needs parentheses.
      let callee := if f matches .field .. then "(" ++ f.print 0 ++ ")" else f.print postfixLevel
      callee ++ "(" ++ args (xs.map (Expr.print 0)) ++ ")"
    | .index _ b xs => b.print postfixLevel ++ "[" ++ args (xs.map (Expr.print 0)) ++ "]"
    | .field _ b f => b.print postfixLevel ++ "." ++ f.name
  if e.level < ctx then "(" ++ text ++ ")" else text

def TypeExpr.print : TypeExpr → String
  | .name _ n => n
  | .index _ b xs => b.print ++ "[" ++ args (xs.map (Expr.print 0)) ++ "]"

mutual
  /-- The lines of a statement at the nesting depth `d`. Each line ends with LF. -/
  def Stmt.print (d : Nat) : Stmt → String
    | .local _ m n ty v =>
      let mut_ := if m then "mut " else ""
      let ty := (ty.map fun t => ": " ++ t.print).getD ""
      indent d ++ "let " ++ mut_ ++ n.name ++ ty ++ " = " ++ v.print 0 ++ ";\n"
    | .assign _ t v => indent d ++ t.print 0 ++ " = " ++ v.print 0 ++ ";\n"
    | .connect _ t v => indent d ++ t.print 0 ++ " := " ++ v.print 0 ++ ";\n"
    | .reg _ n ty i => indent d ++ "reg " ++ n.name ++ ": " ++ ty.print ++ " = " ++ i.print 0
      ++ ";\n"
    | .wire _ n ty => indent d ++ "wire " ++ n.name ++ ": " ++ ty.print ++ ";\n"
    | .input _ n ty => indent d ++ "input " ++ n.name ++ ": " ++ ty.print ++ ";\n"
    | .output _ n ty => indent d ++ "output " ++ n.name ++ ": " ++ ty.print ++ ";\n"
    | .inst _ n m xs => indent d ++ "instance " ++ n.name ++ " = " ++ m.name ++ "("
      ++ args (xs.map (Expr.print 0)) ++ ");\n"
    | .ret _ none => indent d ++ "return;\n"
    | .ret _ (some v) => indent d ++ "return " ++ v.print 0 ++ ";\n"
    | .ctIf _ c y none => indent d ++ "comptime if (" ++ c.print 0 ++ ") " ++ Stmt.body d y
      ++ "\n"
    | .ctIf _ c y (some n) => indent d ++ "comptime if (" ++ c.print 0 ++ ") "
      ++ Stmt.body d y ++ " else " ++ Stmt.body d n ++ "\n"
    | .ctFor _ i lo hi b => indent d ++ "comptime for " ++ i.name ++ " in " ++ lo.print 0
      ++ " .. " ++ hi.print 0 ++ " " ++ Stmt.body d b ++ "\n"
    | .block _ b => indent d ++ Stmt.body d b ++ "\n"
    | .expr _ v => indent d ++ v.print 0 ++ ";\n"

  /-- A block at depth `d`: its statements one level deeper, and the `}` at depth `d`. -/
  def Stmt.body (d : Nat) : List Stmt → String
    | [] => "{}"
    | b => "{\n" ++ Stmt.lines (d + 1) b ++ indent d ++ "}"

  def Stmt.lines (d : Nat) : List Stmt → String
    | [] => ""
    | s :: ss => s.print d ++ Stmt.lines d ss
end

def Param.print (p : Param) : String :=
  (if p.comptime then "comptime " else "") ++ p.name.name ++ ": " ++ p.ty.print

def Item.print : Item → String
  | .const _ n ty v => "const " ++ n.name ++ ": " ++ ty.print ++ " = " ++ v.print 0 ++ ";\n"
  | .fn _ c n ps r b => (if c then "comptime " else "") ++ "fn " ++ n.name ++ "("
    ++ args (ps.map Param.print) ++ ") -> " ++ r.print ++ " " ++ Stmt.body 0 b ++ "\n"
  | .module _ n ps ds b =>
    let domains := match ds with
      | none => ""
      | some ds => " domains(" ++ args (ds.map (·.name)) ++ ")"
    "module " ++ n.name ++ "(" ++ args (ps.map Param.print) ++ ")" ++ domains ++ " "
      ++ Stmt.body 0 b ++ "\n"

/-! The source text of a file. A blank line separates two items. -/
def Print.print (items : List Item) : String :=
  "\n".intercalate (items.map Item.print)

end Silicon.Source
