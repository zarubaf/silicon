-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Print
import Silicon.Source.Lex

/-!
The token kinds of the printed text of each AST node, for `parse_print`. Each function follows
the printer of `Source.Print` part by part. Whitespace gives no token. An identifier gives an
`ident` token, a fixed word gives a `keyword` token. The lexer lemma shows that the lexer gives
these kinds for the printed text of a `Printable` AST.
-/
namespace Silicon.Source

open Lex Print

/-! The kinds of a list of arguments, with a `,` between two arguments. -/
def Print.argToks (xs : List (List Kind)) : List Kind := List.intercalate [.symbol ","] xs

mutual
  /-- The kinds of `e.print ctx`. -/
  def Expr.toks (ctx : Nat) (e : Expr) : List Kind :=
    let body := match e with
      | .num _ v => [.number v]
      | .bool _ v => [.keyword (boolean v)]
      | .str _ v => [.string v]
      | .name _ n => [.ident n]
      | .unary _ op a => .symbol op.text :: a.toks unaryLevel
      | .binary _ op l r =>
        let lhs := if op.associative then op.level else op.level + 1
        l.toks lhs ++ .symbol op.text :: r.toks (op.level + 1)
      | .cond _ c y n =>
        [.keyword "if", .symbol "("] ++ c.toks 0 ++ [.symbol ")", .symbol "{"] ++ y.toks 0
          ++ [.symbol "}", .keyword "else", .symbol "{"] ++ n.toks 0 ++ [.symbol "}"]
      | .call _ f xs =>
        let callee :=
          if f matches .field .. then .symbol "(" :: f.toks 0 ++ [.symbol ")"]
          else f.toks postfixLevel
        callee ++ .symbol "(" :: argToks (xs.map (Expr.toks 0)) ++ [.symbol ")"]
      | .index _ b xs =>
        b.toks postfixLevel ++ .symbol "[" :: argToks (xs.map (Expr.toks 0)) ++ [.symbol "]"]
      | .field _ b f => b.toks postfixLevel ++ [.symbol ".", .ident f.name]
      | .unit _ => [.symbol "(", .symbol ")"]
      | .tuple _ xs =>
        .symbol "(" :: argToks (xs.map (Expr.toks 0))
          ++ (if xs.length == 1 then [.symbol ",", .symbol ")"] else [.symbol ")"])
      | .array _ xs => .symbol "[" :: argToks (xs.map (Expr.toks 0)) ++ [.symbol "]"]
      | .select _ b _ i => b.toks postfixLevel ++ [.symbol ".", .number i]
      | .arrayType _ t n => .symbol "[" :: t.toks ++ .symbol ";" :: n.toks 0 ++ [.symbol "]"]
    if e.level < ctx then .symbol "(" :: body ++ [.symbol ")"] else body

  def TypeExpr.toks : TypeExpr → List Kind
    | .name _ n => [.ident n]
    | .index _ b xs => b.toks ++ .symbol "[" :: argToks (xs.map (Expr.toks 0)) ++ [.symbol "]"]
    | .unit _ => [.symbol "(", .symbol ")"]
    | .tuple _ ts =>
      .symbol "(" :: argToks (ts.map TypeExpr.toks)
        ++ (if ts.length == 1 then [.symbol ",", .symbol ")"] else [.symbol ")"])
    | .array _ t n => .symbol "[" :: t.toks ++ .symbol ";" :: n.toks 0 ++ [.symbol "]"]
end

mutual
  /-- The kinds of `s.print d`, for each depth `d`. -/
  def Stmt.toks : Stmt → List Kind
    | .local _ m n ty v =>
      [.keyword "let"] ++ (if m then [.keyword "mut"] else []) ++ [.ident n.name]
        ++ ((ty.map fun t => .symbol ":" :: t.toks).getD []) ++ .symbol "=" :: v.toks 0
        ++ [.symbol ";"]
    | .assign _ t v => t.toks 0 ++ .symbol "=" :: v.toks 0 ++ [.symbol ";"]
    | .connect _ t v => t.toks 0 ++ .symbol ":=" :: v.toks 0 ++ [.symbol ";"]
    | .reg _ n ty i =>
      [.keyword "reg", .ident n.name, .symbol ":"] ++ ty.toks ++ .symbol "=" :: i.toks 0
        ++ [.symbol ";"]
    | .wire _ n ty => [.keyword "wire", .ident n.name, .symbol ":"] ++ ty.toks ++ [.symbol ";"]
    | .input _ n ty => [.keyword "input", .ident n.name, .symbol ":"] ++ ty.toks ++ [.symbol ";"]
    | .output _ n ty =>
      [.keyword "output", .ident n.name, .symbol ":"] ++ ty.toks ++ [.symbol ";"]
    | .inst _ n m xs =>
      [.keyword "instance", .ident n.name, .symbol "=", .ident m.name, .symbol "("]
        ++ argToks (xs.map (Expr.toks 0)) ++ [.symbol ")", .symbol ";"]
    | .ret _ none => [.keyword "return", .symbol ";"]
    | .ret _ (some v) => .keyword "return" :: v.toks 0 ++ [.symbol ";"]
    | .ctIf _ c y none =>
      [.keyword "comptime", .keyword "if", .symbol "("] ++ c.toks 0
        ++ .symbol ")" :: Stmt.bodyToks y
    | .ctIf _ c y (some n) =>
      [.keyword "comptime", .keyword "if", .symbol "("] ++ c.toks 0
        ++ .symbol ")" :: Stmt.bodyToks y ++ .keyword "else" :: Stmt.bodyToks n
    | .ctFor _ i lo hi b =>
      [.keyword "comptime", .keyword "for", .ident i.name, .keyword "in"] ++ lo.toks 0
        ++ .symbol ".." :: hi.toks 0 ++ Stmt.bodyToks b
    | .block _ b => Stmt.bodyToks b
    | .expr _ v => v.toks 0 ++ [.symbol ";"]
    | .alias _ n ty => [.keyword "type", .ident n.name, .symbol "="] ++ ty.toks ++ [.symbol ";"]

  /-- The kinds of `Stmt.body d b`. An empty body prints as `{}`, which is two tokens. -/
  def Stmt.bodyToks (b : List Stmt) : List Kind :=
    .symbol "{" :: Stmt.linesToks b ++ [.symbol "}"]

  def Stmt.linesToks : List Stmt → List Kind
    | [] => []
    | s :: ss => s.toks ++ Stmt.linesToks ss
end

def Param.toks (p : Param) : List Kind :=
  (if p.comptime then [.keyword "comptime"] else []) ++ [.ident p.name.name, .symbol ":"]
    ++ p.ty.toks

def StructField.toks (f : StructField) : List Kind :=
  [.ident f.name.name, .symbol ":"] ++ f.ty.toks ++ [.symbol ","]

def Item.toks : Item → List Kind
  | .const _ n ty v =>
    [.keyword "const", .ident n.name, .symbol ":"] ++ ty.toks ++ .symbol "=" :: v.toks 0
      ++ [.symbol ";"]
  | .fn _ c n ps r b =>
    (if c then [.keyword "comptime"] else []) ++ [.keyword "fn", .ident n.name, .symbol "("]
      ++ argToks (ps.map Param.toks) ++ [.symbol ")", .symbol "->"] ++ r.toks ++ Stmt.bodyToks b
  | .module _ n ps ds b =>
    let domains := match ds with
      | none => []
      | some ds =>
        [.keyword "domains", .symbol "("] ++ argToks (ds.map fun d => [.ident d.name])
          ++ [.symbol ")"]
    [.keyword "module", .ident n.name, .symbol "("] ++ argToks (ps.map Param.toks)
      ++ .symbol ")" :: domains ++ Stmt.bodyToks b
  | .struct _ n ps fs =>
    let params :=
      if ps.isEmpty then [] else .symbol "(" :: argToks (ps.map Param.toks) ++ [.symbol ")"]
    [.keyword "struct", .ident n.name] ++ params ++ .symbol "{" :: fs.flatMap StructField.toks
      ++ [.symbol "}"]
  | .alias _ n ty => [.keyword "type", .ident n.name, .symbol "="] ++ ty.toks ++ [.symbol ";"]

/-! The kinds of `Print.print items`: the lexer gives these, then `eof`. -/
def Print.toks (items : List Item) : List Kind := items.flatMap Item.toks

end Silicon.Source
