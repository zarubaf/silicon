import Silicon.Source.Lex
import Silicon.Source.Print

/-!
The parser of slice 1. It reads the tokens of `Source.Lex`. It gives the items of the file,
or the first error in position order. `S001` is a token that the grammar does not accept.
`S004` is the syntax of a later slice.

The parser reads the tokens from left to right. It stops at the first token that the slice 1
grammar does not accept, or at the first token of a later construct. It thus finds the errors
in position order, and it reports the first. This rule also orders a lexical error after an
`S004`. The lexer ends the tokens with an `error` token. The parser reports that token only
if it gets to it. `S004` is at these tokens:

- The keyword: `import`, `pub`, `type`, `struct`, and `extern` at an item. `type` and `mem`
  at a statement. `in`, `as`, `with`, and `conforms` after their forms. `mut` at a function
  parameter. `fn` of a function type.
- The opening token: `(` of `()` and of a tuple, and `[` of an array value or type. `(` of a
  unit, tuple, or grouped type. `@` of one of the five builtins.
- A later token of the construct: the `::` of a path, and the number after `.`. The `(` after
  `.name`, which is a receiver call. The `(` after a type, which is a type function call. The
  second name in a `domains` clause.
- The first name of an assignment or connection target with a `[` or a `.` and a number, for
  example `a[i] = x;`. Slice 1 has no arrays and no tuples, so a place is `x` or `x.f`.

Two constructs need a look ahead. At `(`, the parser looks for a `,` before the matching
bracket. At a statement that starts with a name, it skips `.` with a name or a number. It
also skips a `[` up to its matching bracket. Then it looks for `=` or `:=`. Both scans count
brackets of the three kinds as one depth.

`@` followed by another name than a builtin is `S001` at that name: no slice has that syntax.
A module parameter without `comptime` is `S001` at its name, and with `mut` it is `S001` at
`mut`: the v0.1 grammar has only `comptime` module parameters. At the end of the file, the
position is the end of the text of the lexer: the line after a final LF.

These rules settle the open points of the grammar:

- A statement that starts with `if` is an expression statement. The grammar has no `if`
  statement, so the conditional needs its `;`, and its arms hold only expressions.
- A comparison does not chain. `a < b < c` is `S001` at the second `<`. Parentheses group:
  `(a < b) < c`.
- Slice 1 has no packages, so a path is one identifier: a `name` expression, a `name` type, or
  the module of an `inst`. A `::` after it is `S004`.
- The `domains` of a module are `none` without a clause and `some` with a clause.
- Parentheses make no node. A node keeps the position of its first token, also if that token
  is a `(`: the `binary` node of `(a + b) * c` is at the `(`.
- A number has no upper limit. The lexer gives the value of a hexadecimal or binary number.

The nesting limit of section 6.1 is a limit on the height of each expression and each type.
A name, a number, a string, and `true` or `false` have height 1. Each other node, and each
pair of parentheses, has the height 1 plus the largest height of its parts. A type has the
same rule: a type name has height 1. Height 65 is `S001` at the first token of the first form
that has it. That form is the first such form to end, because two forms of height 65 do not
overlap. Thus `a + a + ... + a` with 65 operands fails at the first `a`. The limit bounds each
recursive pass over the AST.

Blocks nest at most 64 levels deep. The body of an item is at depth 1, and each block in a
block adds 1. A block at depth 65 is `S001` at its `{`.
-/
namespace Silicon.Source.Parse

open Lex

/-! The parser reads the token array and keeps the index of the next token. -/
abbrev P := ReaderT (Array Token) (StateT Nat (Except Error))

def maxDepth : Nat := 64

def builtins : List String := ["TypeOf", "typeInfo", "field", "Struct", "ports"]

def allBinOps : List BinOp :=
  [.lor, .land, .or, .xor, .and, .eq, .ne, .lt, .le, .gt, .ge, .shl, .shr,
   .add, .sub, .addw, .subw, .mul, .div, .rem, .mulw]

/-! The lexer ends the tokens with `eof` or `error`. The parser never reads past that token. -/
def peekAt (k : Nat) : P Token := do
  let ts ← read
  return ts.getD ((← get) + k) (ts.getD (ts.size - 1) ⟨⟨1, 1⟩, .eof⟩)

def peek : P Token := peekAt 0

def bump : P Unit := modify (· + 1)

def isSym (s : String) (t : Token) : Bool := t.kind == .symbol s

def isKw (w : String) (t : Token) : Bool := t.kind == .keyword w

/-! `S001` at `t`. A lexical error keeps the message of the lexer. -/
def unexpected (t : Token) (what : String) : P α :=
  match t.kind with
  | .error msg => throw ⟨.S001, t.pos, msg⟩
  | _ => throw ⟨.S001, t.pos, "expected " ++ what⟩

def later (t : Token) (what : String) : P α :=
  throw ⟨.S004, t.pos, what ++ " is not in slice 1"⟩

def sym (s : String) : P Unit := do
  let t ← peek
  if isSym s t then bump else unexpected t s!"`{s}`"

def kw (w : String) : P Unit := do
  let t ← peek
  if isKw w t then bump else unexpected t s!"`{w}`"

def acceptSym (s : String) : P Bool := do
  if isSym s (← peek) then bump; return true else return false

def acceptKw (w : String) : P Bool := do
  if isKw w (← peek) then bump; return true else return false

def ident : P Ident := do
  let t ← peek
  match t.kind with
  | .ident n => bump; return ⟨t.pos, n⟩
  | _ => unexpected t "a name"

/-! A path of slice 1 is one identifier. -/
def path : P Ident := do
  let n ← ident
  let t ← peek
  if isSym "::" t then later t "a package path" else return n

/-! `@` at `t`: `S004` for a builtin, else `S001` at the name. -/
def builtin (t : Token) : P α := do
  let u ← peekAt 1
  match u.kind with
  | .ident n => if builtins.contains n then later t "a builtin" else unexpected u "a builtin name"
  | _ => unexpected u "a builtin name"

def noDomain : P Unit := do
  let t ← peek
  if isKw "in" t then later t "a domain annotation" else pure ()

def opAt (level : Nat) (t : Token) : Option BinOp :=
  allBinOps.find? fun op => op.level == level && isSym op.text t

def unOp (t : Token) : Option UnOp :=
  [UnOp.not, .inv, .neg].find? fun op => isSym op.text t

/-! Fuel exhaustion cannot occur with the fuel of `parse`. -/
def exhausted : P α := do
  throw ⟨.S001, (← peek).pos, "parser fuel exhausted"⟩

/-! The height of a node from the heights of its children. Height 65 is `S001` at `start`. -/
def height (start : Pos) (children : List Nat) : P Nat := do
  let h := children.foldl max 0 + 1
  if h > maxDepth then
    throw ⟨.S001, start, s!"expression nests deeper than {maxDepth} levels"⟩
  return h

/-! An expression with its height. -/
structure Node where
  expr : Expr
  height : Nat

def leaf (e : Expr) : Node := ⟨e, 1⟩

def opening (t : Token) : Bool := isSym "(" t || isSym "[" t || isSym "{" t

def closing (t : Token) : Bool := isSym ")" t || isSym "]" t || isSym "}" t

/-! True if a `,` comes before the bracket that closes the open bracket at depth `d + 1`. -/
def commaAhead : List Token → Nat → Bool
  | [], _ => false
  | t :: ts, d =>
    if opening t then commaAhead ts (d + 1)
    else if closing t then d != 0 && commaAhead ts (d - 1)
    else if isSym "," t then d == 0 || commaAhead ts d
    else commaAhead ts d

/-!
True if the tokens after a name continue a place of a later slice up to `=` or `:=`: they
hold a `[` or a `.` with a number. Inside brackets the scan counts brackets of each kind.
-/
def laterPlace : List Token → Nat → Bool → Bool
  | [], _, _ => false
  | t :: ts, d + 1, seen =>
    if opening t then laterPlace ts (d + 2) seen
    else if closing t then laterPlace ts d seen
    else laterPlace ts (d + 1) seen
  | t :: ts, 0, seen =>
    if isSym "=" t || isSym ":=" t then seen
    else if isSym "[" t then laterPlace ts 1 true
    else if isSym "." t then
      match ts with
      | ⟨_, .ident _⟩ :: rest => laterPlace rest 0 seen
      | ⟨_, .number _⟩ :: rest => laterPlace rest 0 true
      | _ => false
    else false

/-! The tokens after the next token. -/
def rest : P (List Token) := do
  let ts ← read
  return (ts.extract ((← get) + 1) ts.size).toList

/-!
Each function takes one unit of fuel from its caller. The argument `l` is the binding level of
`Print`: 1 for `||` to 9 for `*`, and 10 for a prefix operator.
-/
mutual
  def expr : Nat → P Node
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      if isKw "if" t then
        bump
        sym "("
        let c ← expr f
        sym ")"
        sym "{"
        let y ← expr f
        sym "}"
        kw "else"
        sym "{"
        let n ← expr f
        sym "}"
        let h ← height t.pos [c.height, y.height, n.height]
        return ⟨.cond t.pos c.expr y.expr n.expr, h⟩
      else operand f 1

  /-- An expression of binding level `l` or higher. -/
  def operand : Nat → Nat → P Node
    | 0, _ => exhausted
    | f + 1, l => do
      let start := (← peek).pos
      let e ← unary f
      climb f l start e

  /-- The infix operators after `e`, from the highest level down to `l`. -/
  def climb : Nat → Nat → Pos → Node → P Node
    | 0, _, _, _ => exhausted
    | f + 1, l, start, e =>
      ((List.range (Print.unaryLevel - l)).map (Print.unaryLevel - 1 - ·)).foldlM
        (fun e k => infixOps f k start e) e

  /-- The operators of level `l` after `lhs`. A comparison takes one operator only. -/
  def infixOps : Nat → Nat → Pos → Node → P Node
    | 0, _, _, _ => exhausted
    | f + 1, l, start, lhs => do
      match opAt l (← peek) with
      | none => return lhs
      | some op =>
        bump
        let rhs ← operand f (l + 1)
        let e := ⟨.binary start op lhs.expr rhs.expr, ← height start [lhs.height, rhs.height]⟩
        if op.associative then infixOps f l start e
        else
          let t ← peek
          if (opAt l t).isSome then
            throw ⟨.S001, t.pos, "a comparison does not chain; use parentheses"⟩
          return e

  def unary : Nat → P Node
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      match unOp t with
      | some op =>
        bump
        let a ← unary f
        return ⟨.unary t.pos op a.expr, ← height t.pos [a.height]⟩
      | none =>
        if isKw "fn" t then later t "a function type"
        else return (← postfixExpr f).1

  /-- A postfix form, and whether it is a place of slice 1: a name or a field of a place. -/
  def postfixExpr : Nat → P (Node × Bool)
    | 0 => exhausted
    | f + 1 => do
      let start := (← peek).pos
      let (e, place) ← primary f
      suffixes f start e place

  def suffixes : Nat → Pos → Node → Bool → P (Node × Bool)
    | 0, _, _, _ => exhausted
    | f + 1, start, e, place => do
      let t ← peek
      if isSym "(" t then
        bump
        let xs ← args f ")" true
        let h ← height start (e.height :: xs.map (·.height))
        suffixes f start ⟨.call start e.expr (xs.map (·.expr)), h⟩ false
      else if isSym "[" t then
        bump
        let xs ← args f "]" false
        let h ← height start (e.height :: xs.map (·.height))
        suffixes f start ⟨.index start e.expr (xs.map (·.expr)), h⟩ false
      else if isSym "." t then
        bump
        let s ← peek
        match s.kind with
        | .ident n =>
          bump
          let u ← peek
          if isSym "(" u then later u "a receiver call"
          let h ← height start [e.height]
          suffixes f start ⟨.field start e.expr ⟨s.pos, n⟩, h⟩ place
        | .number _ => later s "a tuple selector"
        | _ => unexpected s "a field name"
      else return (e, place)

  def primary : Nat → P (Node × Bool)
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      match t.kind with
      | .ident n =>
        let _ ← path
        return (leaf (.name t.pos n), true)
      | .number v => bump; return (leaf (.num t.pos v), false)
      | .string s => bump; return (leaf (.str t.pos s), false)
      | .keyword "true" => bump; return (leaf (.bool t.pos true), false)
      | .keyword "false" => bump; return (leaf (.bool t.pos false), false)
      | .symbol "(" =>
        let ts ← rest
        if ts.head?.any (isSym ")") || commaAhead ts 0 then later t "a unit or tuple value"
        bump
        let e ← expr f
        sym ")"
        return (⟨e.expr, ← height t.pos [e.height]⟩, false)
      | .symbol "[" => later t "an array"
      | .symbol "@" => builtin t
      | _ => unexpected t "an expression"

  /-- A list of expressions up to `close`. A `,` can end the list. -/
  def args : Nat → String → Bool → P (List Node)
    | 0, _, _ => exhausted
    | f + 1, close, allowEmpty => do
      if allowEmpty then
        if ← acceptSym close then return []
      let e ← expr f
      argsRest f close [e]

  def argsRest : Nat → String → List Node → P (List Node)
    | 0, _, _ => exhausted
    | f + 1, close, acc => do
      if ← acceptSym close then return acc.reverse
      let t ← peek
      if isSym "," t then
        bump
        if ← acceptSym close then return acc.reverse
        let e ← expr f
        argsRest f close (e :: acc)
      else unexpected t s!"`,` or `{close}`"
end

/-! A type with its height. The limit of expressions also holds for types. -/
mutual
  def typeExpr : Nat → P (TypeExpr × Nat)
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      match t.kind with
      | .ident n =>
        let _ ← path
        typeSuffix f t.pos (.name t.pos n, 1)
      | .keyword "fn" => later t "a function type"
      | .symbol "(" => later t "a unit, tuple, or grouped type"
      | .symbol "[" => later t "an array type"
      | .symbol "@" => builtin t
      | _ => unexpected t "a type"

  def typeSuffix : Nat → Pos → TypeExpr × Nat → P (TypeExpr × Nat)
    | 0, _, _ => exhausted
    | f + 1, start, (ty, h) => do
      let t ← peek
      if isSym "[" t then
        bump
        let xs ← args f "]" false
        let h ← height start (h :: xs.map (·.height))
        typeSuffix f start (.index start ty (xs.map (·.expr)), h)
      else if isSym "(" t then later t "a type function call"
      else return (ty, h)
end

def typeAnnotation (f : Nat) : P TypeExpr := do
  sym ":"
  return (← typeExpr f).1

/-! An expression directly in a statement or an item. -/
def value (f : Nat) : P Expr := return (← expr f).expr

/-! `x = v;` or `x := v;` after the postfix form `e`, or else an expression statement. -/
def placeStmt (f : Nat) (start : Pos) (e : Node) (place : Bool) : P Stmt := do
  let t ← peek
  if isSym "=" t || isSym ":=" t then
    if !place then unexpected t "`;`"
    bump
    let v ← value f
    sym ";"
    return if isSym "=" t then .assign start e.expr v else .connect start e.expr v
  else
    let e ← climb f 1 start e
    sym ";"
    return .expr start e.expr

mutual
  /-- A statement in a block at the depth `b`. -/
  def stmt : Nat → Nat → P Stmt
    | 0, _ => exhausted
    | f + 1, b => do
      let t ← peek
      match t.kind with
      | .keyword "let" =>
        bump
        let m ← acceptKw "mut"
        let n ← ident
        let ty ← if isSym ":" (← peek) then some <$> typeAnnotation f else pure none
        sym "="
        let v ← value f
        sym ";"
        return .local t.pos m n ty v
      | .keyword "reg" =>
        bump
        let n ← ident
        let ty ← typeAnnotation f
        noDomain
        sym "="
        let v ← value f
        sym ";"
        return .reg t.pos n ty v
      | .keyword "wire" =>
        bump
        let n ← ident
        let ty ← typeAnnotation f
        noDomain
        sym ";"
        return .wire t.pos n ty
      | .keyword "input" => port f t .input
      | .keyword "output" => port f t .output
      | .keyword "instance" =>
        bump
        let n ← ident
        sym "="
        let m ← path
        sym "("
        let xs := (← args f ")" true).map (·.expr)
        let u ← peek
        if isKw "with" u then later u "a domain map"
        sym ";"
        return .inst t.pos n m xs
      | .keyword "return" =>
        bump
        if ← acceptSym ";" then return .ret t.pos none
        let v ← value f
        sym ";"
        return .ret t.pos (some v)
      | .keyword "comptime" =>
        bump
        let u ← peek
        if isKw "if" u then
          bump
          sym "("
          let c ← value f
          sym ")"
          let y ← block f (b + 1)
          let n ← if ← acceptKw "else" then some <$> block f (b + 1) else pure none
          return .ctIf t.pos c y n
        else if isKw "for" u then
          bump
          let i ← ident
          kw "in"
          let lo ← value f
          sym ".."
          let hi ← value f
          return .ctFor t.pos i lo hi (← block f (b + 1))
        else unexpected u "`if` or `for`"
      | .keyword "mem" => later t "a memory"
      | .keyword "type" => later t "a type alias"
      | .symbol "{" => return .block t.pos (← block f (b + 1))
      | .ident _ =>
        if laterPlace (← rest) 0 false then later t "a place with an index or a tuple selector"
        let (e, place) ← postfixExpr f
        placeStmt f t.pos e place
      | _ =>
        let e ← value f
        sym ";"
        return .expr t.pos e

  def port : Nat → Token → (Pos → Ident → TypeExpr → Stmt) → P Stmt
    | 0, _, _ => exhausted
    | f + 1, t, make => do
      bump
      let n ← ident
      let u ← peek
      if isSym "[" u then later u "a port family"
      let ty ← typeAnnotation f
      noDomain
      let u ← peek
      if isKw "as" u then later u "a port key"
      sym ";"
      return make t.pos n ty

  /-- A block at the depth `b`. The body of an item is at depth 1. -/
  def block : Nat → Nat → P (List Stmt)
    | 0, _ => exhausted
    | f + 1, b => do
      let t ← peek
      sym "{"
      if b > maxDepth then
        throw ⟨.S001, t.pos, s!"blocks nest deeper than {maxDepth} levels"⟩
      stmts f b []

  def stmts : Nat → Nat → List Stmt → P (List Stmt)
    | 0, _, _ => exhausted
    | f + 1, b, acc => do
      let t ← peek
      if isSym "}" t then bump; return acc.reverse
      if t.kind == .eof then unexpected t "`}`"
      let s ← stmt f b
      stmts f b (s :: acc)
end

/-!
A parameter. A module parameter needs `comptime`, and a function parameter can have it.
`mut` is a later slice at a function parameter and no syntax at a module parameter.
-/
def param (f : Nat) (static : Bool) : P Param := do
  let t ← peek
  if isKw "mut" t && !static then later t "a `mut` formal"
  let c ← if static then kw "comptime" *> pure true else acceptKw "comptime"
  let n ← ident
  return ⟨t.pos, c, n, ← typeAnnotation f⟩

def params : Nat → Bool → List Param → P (List Param)
  | 0, _, _ => exhausted
  | f + 1, static, acc => do
    if ← acceptSym ")" then return acc.reverse
    let p ← param f static
    if ← acceptSym ")" then return (p :: acc).reverse
    sym ","
    params f static (p :: acc)

/-! The names of a `domains` clause after its `(`. A second name is a later slice. -/
def domainNames : P (List Ident) := do
  if ← acceptSym ")" then return []
  let n ← ident
  if ← acceptSym ")" then return [n]
  sym ","
  let t ← peek
  if t.kind matches .ident _ then later t "more than one domain"
  sym ")"
  return [n]

def fnRest (f : Nat) (start : Pos) (comptime : Bool) : P Item := do
  kw "fn"
  let n ← ident
  sym "("
  let ps ← params f false []
  sym "->"
  let r := (← typeExpr f).1
  return .fn start comptime n ps r (← block f 1)

def moduleItem (f : Nat) (start : Pos) : P Item := do
  kw "module"
  let n ← ident
  sym "("
  let ps ← params f true []
  let ds ← if ← acceptKw "domains" then sym "(" *> some <$> domainNames else pure none
  let t ← peek
  if isKw "conforms" t then later t "a contract attachment"
  return .module start n ps ds (← block f 1)

def laterItems : List (String × String) :=
  [("import", "an import"), ("pub", "`pub`"), ("type", "a type alias"),
   ("struct", "a struct"), ("extern", "an extern module")]

def item (f : Nat) : P Item := do
  let t ← peek
  match t.kind with
  | .keyword "const" =>
    bump
    let n ← ident
    let ty ← typeAnnotation f
    sym "="
    let v ← value f
    sym ";"
    return .const t.pos n ty v
  | .keyword "comptime" => bump; fnRest f t.pos true
  | .keyword "fn" => fnRest f t.pos false
  | .keyword "module" => moduleItem f t.pos
  | .keyword w =>
    match laterItems.lookup w with
    | some what => later t what
    | none => unexpected t "an item"
  | _ => unexpected t "an item"

def items : Nat → List Item → P (List Item)
  | 0, _ => exhausted
  | f + 1, acc => do
    if (← peek).kind == .eof then return acc.reverse
    let i ← item f
    items f (i :: acc)

/-!
The items of a token list, or the first error. The fuel bounds the depth of the calls, not
their number. On a chain of active calls the token index never decreases. A loop step starts
after its previous step took a token. Fewer than 32 calls on a chain start at one index. The
longest such run goes from `items` through `stmt` and `expr` to `primary`. Thus
`32 * (n + 1)` fuel for `n` tokens never runs out.
-/
def parse (tokens : List Token) : Except Error (List Item) :=
  let ts := tokens.toArray
  ((items (32 * (ts.size + 1)) []).run ts).run' 0

/-! The items of a source text. -/
def parseSource (s : String) : Except Error (List Item) := parse (lex s)

end Silicon.Source.Parse
