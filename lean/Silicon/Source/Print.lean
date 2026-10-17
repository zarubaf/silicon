-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Syntax

/-!
The AST dump of section 11.1 of the front-end design, and a source printer.

The Rust front end copies the dump byte for byte, so these rules fix each byte:

- A node prints as `(<constructor> <field> ...)`: the constructor name of `Source.Syntax` in
  lowercase, then each field in declaration order. One space separates two parts. A node with
  no fields prints as `(<constructor>)`, for example `(unit)`. Thus `(` is followed by a name,
  except in an empty list.
- The structure `Param` prints as `(param <mode> <name> <ty>)`. The structure `StructField`
  prints as `(structfield <name> <ty>)`. The structure `Variant` prints as
  `(variant <name> <payload> <tag>)`. A `FnParam` prints as `(fnparam <mutable> <ty>)`. An
  `Arm` prints as `(arm <pat> <value>)`.
- A `ParamMode` prints as its constructor name: `none`, `comptime`, or `mut`.
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

def boolean (b : Bool) : String := if b then "true" else "false"

def ident (i : Ident) : String := quote i.name

def args (xs : List String) : String := ", ".intercalate xs

def indent (depth : Nat) : String := "".pushn ' ' (4 * depth)

/-! The end of a tuple of `n` elements. A tuple of one element ends with `,)`. -/
def tupleEnd (n : Nat) : String := if n == 1 then ",)" else ")"

/-! The text of a function type from the texts of its parameter types and its result type. -/
def fnText (params : List String) (ret : String) : String :=
  "fn (" ++ args params ++ ") -> " ++ ret

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

/-!
The dump appends to an accumulator, so its work is linear in the size of its output. The
elements of a list append in a loop, so no recursion grows with the length of a list.
-/

/-- `acc`, then the elements of `xs` as `f` writes them, with one space between two. -/
def Print.sepTo (f : String → α → String) (acc : String) : List α → String
  | [] => acc
  | [x] => f acc x
  | x :: xs => sepTo f (f acc x ++ " ") xs

def Print.listTo (f : String → α → String) (acc : String) (xs : List α) : String :=
  sepTo f (acc ++ "(") xs ++ ")"

def Print.optionTo (f : String → α → String) (acc : String) : Option α → String
  | none => acc ++ "none"
  | some x => f (acc ++ "(some ") x ++ ")"

def Pattern.dumpTo (acc : String) : Pattern → String
  | .wild _ => acc ++ "(wild)"
  | .int _ neg v => acc ++ "(int " ++ boolean neg ++ " " ++ toString v ++ ")"
  | .bool _ v => acc ++ "(bool " ++ boolean v ++ ")"
  | .variant _ t v bs =>
    listTo (optionTo fun acc i => acc ++ ident i)
      (acc ++ "(variant " ++ ident t ++ " " ++ ident v ++ " ") bs ++ ")"

mutual
  def Expr.dumpTo (acc : String) : Expr → String
    | .num _ v => acc ++ "(num " ++ toString v ++ ")"
    | .bool _ v => acc ++ "(bool " ++ boolean v ++ ")"
    | .str _ v => acc ++ "(str " ++ quote v ++ ")"
    | .name _ n => acc ++ "(name " ++ quote n ++ ")"
    | .unary _ op a => a.dumpTo (acc ++ "(unary " ++ op.name ++ " ") ++ ")"
    | .binary _ op l r => r.dumpTo (l.dumpTo (acc ++ "(binary " ++ op.name ++ " ") ++ " ") ++ ")"
    | .cond _ c y n => n.dumpTo (y.dumpTo (c.dumpTo (acc ++ "(cond ") ++ " ") ++ " ") ++ ")"
    | .call _ f xs => Expr.dumpsTo (f.dumpTo (acc ++ "(call ") ++ " (") xs ++ "))"
    | .index _ b xs => Expr.dumpsTo (b.dumpTo (acc ++ "(index ") ++ " (") xs ++ "))"
    | .field _ b f => b.dumpTo (acc ++ "(field ") ++ " " ++ ident f ++ ")"
    | .unit _ => acc ++ "(unit)"
    | .tuple _ xs => Expr.dumpsTo (acc ++ "(tuple (") xs ++ "))"
    | .array _ xs => Expr.dumpsTo (acc ++ "(array (") xs ++ "))"
    | .select _ b _ i => b.dumpTo (acc ++ "(select ") ++ " " ++ toString i ++ ")"
    | .arrayType _ t n => n.dumpTo (t.dumpTo (acc ++ "(arraytype ") ++ " ") ++ ")"
    | .method _ r m xs =>
      Expr.dumpsTo (r.dumpTo (acc ++ "(method ") ++ " " ++ ident m ++ " (") xs ++ "))"
    | .fnType _ ps r => r.dumpTo (FnParam.dumpsTo (acc ++ "(fntype (") ps ++ ") ") ++ ")"
    | .path _ t v => acc ++ "(path " ++ ident t ++ " " ++ ident v ++ ")"
    | .«match» _ s arms => Arm.dumpsTo (s.dumpTo (acc ++ "(match ") ++ " (") arms ++ "))"

  /-- `sepTo Expr.dumpTo`, which the recursion over `Expr` needs as its own function. -/
  def Expr.dumpsTo (acc : String) : List Expr → String
    | [] => acc
    | [e] => e.dumpTo acc
    | e :: es => Expr.dumpsTo (e.dumpTo acc ++ " ") es

  def TypeExpr.dumpTo (acc : String) : TypeExpr → String
    | .name _ n => acc ++ "(name " ++ quote n ++ ")"
    | .index _ b xs => Expr.dumpsTo (b.dumpTo (acc ++ "(index ") ++ " (") xs ++ "))"
    | .unit _ => acc ++ "(unit)"
    | .tuple _ ts => TypeExpr.dumpsTo (acc ++ "(tuple (") ts ++ "))"
    | .array _ t n => n.dumpTo (t.dumpTo (acc ++ "(array ") ++ " ") ++ ")"
    | .fn _ ps r => r.dumpTo (FnParam.dumpsTo (acc ++ "(fn (") ps ++ ") ") ++ ")"

  /-- `sepTo TypeExpr.dumpTo`, which the recursion over `TypeExpr` needs as its own function. -/
  def TypeExpr.dumpsTo (acc : String) : List TypeExpr → String
    | [] => acc
    | [t] => t.dumpTo acc
    | t :: ts => TypeExpr.dumpsTo (t.dumpTo acc ++ " ") ts

  def FnParam.dumpTo (acc : String) : FnParam → String
    | .mk m t => t.dumpTo (acc ++ "(fnparam " ++ boolean m ++ " ") ++ ")"

  /-- `sepTo FnParam.dumpTo`, which the recursion over `FnParam` needs as its own function. -/
  def FnParam.dumpsTo (acc : String) : List FnParam → String
    | [] => acc
    | [p] => p.dumpTo acc
    | p :: ps => FnParam.dumpsTo (p.dumpTo acc ++ " ") ps

  def Arm.dumpTo (acc : String) : Arm → String
    | .mk p v => v.dumpTo (p.dumpTo (acc ++ "(arm ") ++ " ") ++ ")"

  /-- `sepTo Arm.dumpTo`, which the recursion over `Arm` needs as its own function. -/
  def Arm.dumpsTo (acc : String) : List Arm → String
    | [] => acc
    | [a] => a.dumpTo acc
    | a :: as => Arm.dumpsTo (a.dumpTo acc ++ " ") as
end

mutual
  def Stmt.dumpTo (acc : String) : Stmt → String
    | .local _ m n ty v =>
      let acc := acc ++ "(local " ++ boolean m ++ " " ++ ident n ++ " "
      v.dumpTo (optionTo TypeExpr.dumpTo acc ty ++ " ") ++ ")"
    | .assign _ t v => v.dumpTo (t.dumpTo (acc ++ "(assign ") ++ " ") ++ ")"
    | .connect _ t v => v.dumpTo (t.dumpTo (acc ++ "(connect ") ++ " ") ++ ")"
    | .reg _ n ty i => i.dumpTo (ty.dumpTo (acc ++ "(reg " ++ ident n ++ " ") ++ " ") ++ ")"
    | .wire _ n ty => ty.dumpTo (acc ++ "(wire " ++ ident n ++ " ") ++ ")"
    | .mem _ n ty d => d.dumpTo (ty.dumpTo (acc ++ "(mem " ++ ident n ++ " ") ++ " ") ++ ")"
    | .input _ n ty => ty.dumpTo (acc ++ "(input " ++ ident n ++ " ") ++ ")"
    | .output _ n ty => ty.dumpTo (acc ++ "(output " ++ ident n ++ " ") ++ ")"
    | .inst _ n m xs =>
      listTo Expr.dumpTo (acc ++ "(inst " ++ ident n ++ " " ++ ident m ++ " ") xs ++ ")"
    | .ret _ v => optionTo Expr.dumpTo (acc ++ "(ret ") v ++ ")"
    | .ctIf _ c y none => Stmt.dumpsTo (c.dumpTo (acc ++ "(ctif ") ++ " (") y ++ ") none)"
    | .ctIf _ c y (some n) =>
      let acc := Stmt.dumpsTo (c.dumpTo (acc ++ "(ctif ") ++ " (") y ++ ") (some ("
      Stmt.dumpsTo acc n ++ ")))"
    | .ctFor _ i lo hi b =>
      let acc := hi.dumpTo (lo.dumpTo (acc ++ "(ctfor " ++ ident i ++ " ") ++ " ") ++ " ("
      Stmt.dumpsTo acc b ++ "))"
    | .block _ b => Stmt.dumpsTo (acc ++ "(block (") b ++ "))"
    | .expr _ v => v.dumpTo (acc ++ "(expr ") ++ ")"
    | .alias _ n ty => ty.dumpTo (acc ++ "(alias " ++ ident n ++ " ") ++ ")"

  /-- `sepTo Stmt.dumpTo`, which the recursion over `Stmt` needs as its own function. -/
  def Stmt.dumpsTo (acc : String) : List Stmt → String
    | [] => acc
    | [s] => s.dumpTo acc
    | s :: ss => Stmt.dumpsTo (s.dumpTo acc ++ " ") ss
end

def ParamMode.name : ParamMode → String
  | .none => "none" | .comptime => "comptime" | .mut => "mut"

def Param.dumpTo (acc : String) (p : Param) : String :=
  p.ty.dumpTo (acc ++ "(param " ++ p.mode.name ++ " " ++ ident p.name ++ " ") ++ ")"

def StructField.dumpTo (acc : String) (f : StructField) : String :=
  f.ty.dumpTo (acc ++ "(structfield " ++ ident f.name ++ " ") ++ ")"

def Variant.dumpTo (acc : String) (v : Variant) : String :=
  let acc := listTo TypeExpr.dumpTo (acc ++ "(variant " ++ ident v.name ++ " ") v.payload
  v.tag.dumpTo (acc ++ " ") ++ ")"

def Item.dumpTo (acc : String) : Item → String
  | .const _ n ty v => v.dumpTo (ty.dumpTo (acc ++ "(const " ++ ident n ++ " ") ++ " ") ++ ")"
  | .fn _ c n ps r b =>
    let acc := listTo Param.dumpTo (acc ++ "(fn " ++ boolean c ++ " " ++ ident n ++ " ") ps
    Stmt.dumpsTo (r.dumpTo (acc ++ " ") ++ " (") b ++ "))"
  | .module _ n ps ds b =>
    let acc := listTo Param.dumpTo (acc ++ "(module " ++ ident n ++ " ") ps ++ " "
    let acc := optionTo (listTo fun acc i => acc ++ ident i) acc ds
    Stmt.dumpsTo (acc ++ " (") b ++ "))"
  | .struct _ n ps fs =>
    let acc := listTo Param.dumpTo (acc ++ "(struct " ++ ident n ++ " ") ps ++ " "
    listTo StructField.dumpTo acc fs ++ ")"
  | .alias _ n ty => ty.dumpTo (acc ++ "(alias " ++ ident n ++ " ") ++ ")"
  | .enum _ n ty vs =>
    listTo Variant.dumpTo (ty.dumpTo (acc ++ "(enum " ++ ident n ++ " ") ++ " ") vs ++ ")"

def Expr.dump (e : Expr) : String := e.dumpTo ""
def TypeExpr.dump (t : TypeExpr) : String := t.dumpTo ""
def Stmt.dump (s : Stmt) : String := s.dumpTo ""
def Item.dump (i : Item) : String := i.dumpTo ""

/-! The AST dump of a source file. -/
def Print.dump (items : List Item) : String :=
  items.foldl (fun acc i => i.dumpTo acc ++ "\n") ""

/-!
The source printer. Its text parses back to the same AST up to positions, if the parser can
give that AST. Thus each name is a valid identifier, each `index` has an argument, and each
module parameter and each struct parameter has `comptime`. The printer does not keep comments.

The binding power of an expression follows the levels of the grammar, from 0 for `if` to 11
for a postfix form or a primary. A form prints in parentheses where its context needs a
higher level. A `field` prints in parentheses also as the callee of a `call`.

A `tuple` of one element prints as `(a,)`, so that it differs from `a` in parentheses. A
`select` is a postfix form, and its selector prints in decimal. An array type `[T; N]` in an
expression is a primary. A receiver call `x.m(a)` is a postfix form.

A function type in an expression is a unary operand, because its result type takes each postfix
after it. Thus it prints in parentheses as the base of a postfix form. A function type as the
base of a type family index prints in parentheses for the same reason.

A struct without parameters prints without parentheses. Each field of a struct prints on its own
line and ends with `,`. Each variant of an enum prints on its own line and ends with `,` too. A
variant without payload types prints without parentheses. A variant path `E::V` is a primary.

A `match` has the level of `if`. It prints on one line, and each arm ends with `,`. A variant
pattern without binders prints without parentheses. A binder `none` prints as `_`.
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
  | .cond .. | .«match» .. => 0
  | .binary _ op .. => op.level
  | .unary .. | .fnType .. => unaryLevel
  | _ => postfixLevel

def Pattern.binderText : Option Ident → String
  | none => "_"
  | some i => i.name

def Pattern.print : Pattern → String
  | .wild _ => "_"
  | .int _ neg v => (if neg then "-" else "") ++ toString v
  | .bool _ v => boolean v
  | .variant _ t v bs =>
    let binders := if bs.isEmpty then "" else "(" ++ args (bs.map Pattern.binderText) ++ ")"
    t.name ++ "::" ++ v.name ++ binders

/-! The text of the arms of a `match` from the text of each arm. -/
def Print.armsText (arms : List String) : String := String.join (arms.map (" " ++ · ++ ","))

mutual
  /-- The text of `e` in a context that needs at least the level `ctx`. -/
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
      | .unit _ => "()"
      | .tuple _ xs => "(" ++ args (xs.map (Expr.print 0)) ++ tupleEnd xs.length
      | .array _ xs => "[" ++ args (xs.map (Expr.print 0)) ++ "]"
      | .select _ b _ i => b.print postfixLevel ++ "." ++ toString i
      | .arrayType _ t n => "[" ++ t.print ++ "; " ++ n.print 0 ++ "]"
      | .method _ r m xs =>
        r.print postfixLevel ++ "." ++ m.name ++ "(" ++ args (xs.map (Expr.print 0)) ++ ")"
      | .fnType _ ps r => fnText (ps.map FnParam.print) r.print
      | .path _ t v => t.name ++ "::" ++ v.name
      | .«match» _ s arms =>
        "match (" ++ s.print 0 ++ ") {" ++ armsText (arms.map Arm.print) ++ " }"
    if e.level < ctx then "(" ++ text ++ ")" else text

  def TypeExpr.print : TypeExpr → String
    | .name _ n => n
    | .index _ b xs =>
      let base := if b matches .fn .. then "(" ++ b.print ++ ")" else b.print
      base ++ "[" ++ args (xs.map (Expr.print 0)) ++ "]"
    | .unit _ => "()"
    | .tuple _ ts => "(" ++ args (ts.map TypeExpr.print) ++ tupleEnd ts.length
    | .array _ t n => "[" ++ t.print ++ "; " ++ n.print 0 ++ "]"
    | .fn _ ps r => fnText (ps.map FnParam.print) r.print

  def FnParam.print : FnParam → String
    | .mk m t => (if m then "mut " else "") ++ t.print

  def Arm.print : Arm → String
    | .mk p v => p.print ++ " => " ++ v.print 0
end

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
    | .mem _ n ty e => indent d ++ "mem " ++ n.name ++ ": [" ++ ty.print ++ "; " ++ e.print 0
      ++ "];\n"
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
    | .alias _ n ty => indent d ++ "type " ++ n.name ++ " = " ++ ty.print ++ ";\n"

  /-- A block at depth `d`: its statements one level deeper, and the `}` at depth `d`. -/
  def Stmt.body (d : Nat) : List Stmt → String
    | [] => "{}"
    | b => "{\n" ++ Stmt.lines (d + 1) b ++ indent d ++ "}"

  def Stmt.lines (d : Nat) : List Stmt → String
    | [] => ""
    | s :: ss => s.print d ++ Stmt.lines d ss
end

/-! The mark of a parameter mode, with its space. -/
def ParamMode.mark : ParamMode → String
  | .none => "" | .comptime => "comptime " | .mut => "mut "

def Param.print (p : Param) : String := p.mode.mark ++ p.name.name ++ ": " ++ p.ty.print

def StructField.print (f : StructField) : String := f.name.name ++ ": " ++ f.ty.print

def Variant.print (v : Variant) : String :=
  let payload :=
    if v.payload.isEmpty then "" else "(" ++ args (v.payload.map TypeExpr.print) ++ ")"
  v.name.name ++ payload ++ " = " ++ v.tag.print 0

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
  | .struct _ n ps fs =>
    let params := if ps.isEmpty then "" else "(" ++ args (ps.map Param.print) ++ ")"
    let fields := if fs.isEmpty then "{}"
      else "{\n" ++ String.join (fs.map fun f => indent 1 ++ f.print ++ ",\n") ++ "}"
    "struct " ++ n.name ++ params ++ " " ++ fields ++ "\n"
  | .alias _ n ty => "type " ++ n.name ++ " = " ++ ty.print ++ ";\n"
  | .enum _ n ty vs =>
    let variants := if vs.isEmpty then "{}"
      else "{\n" ++ String.join (vs.map fun v => indent 1 ++ v.print ++ ",\n") ++ "}"
    "enum " ++ n.name ++ ": " ++ ty.print ++ " " ++ variants ++ "\n"

/-! The source text of a file. A blank line separates two items. -/
def Print.print (items : List Item) : String :=
  "\n".intercalate (items.map Item.print)

end Silicon.Source
