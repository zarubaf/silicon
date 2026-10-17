-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Lex
import Silicon.Source.Print

/-!
The parser of slices 1 to 3. It reads the tokens of `Source.Lex`. It gives the items of the
file, or the first error in position order. `S001` is a token that the grammar does not accept.
`S004` is the syntax of a later slice or of a later phase of slice 3.

The parser reads the tokens from left to right. It stops at the first token that the grammar
does not accept, or at the first token of a later construct. It thus finds the errors in
position order, and it reports the first. This rule also orders a lexical error after an
`S004`. The lexer ends the tokens with an `error` token. The parser reports that token only
if it gets to it. `S004` is at these tokens:

- The keyword: `import`, `pub`, and `extern` at an item.
  `in`, `as`, `with`, and `conforms` after their forms. `input`, `output`, `reg`, `wire`,
  `mem`, and `instance` in the body of a `fn` without `comptime`: a helper that declares
  resources is slice 3.
- The opening token: `@` of one of the five builtins.
- A later token of the construct: the `::` of a package path. The `(` after a type, which is a
  type function call. The second name in a `domains` clause. The `(` after the name of an enum,
  which is an enum with parameters.

Two constructs need a look ahead. At `(`, the parser looks for `)` as the next token, or for
a `,` directly in the bracket: these give `()` or a tuple, else the bracket groups. At `[` in an
expression, it looks for a `;` directly in the bracket: this is an array type `[T; N]`. Both
scans count brackets of the three kinds as one depth.

The flag of the bracket pass decides the form at `[` in an expression, and the parser never
reads a token again. With a `;` directly in the bracket, the element `T` of `[T; N]` is a type.
The first token that is not part of a type is `S001`: `[0; 4]` is `S001` at the `0`, and
`[a, b; c]` is `S001` at the `,`.

The parse is linear in the number of tokens. Before the parse, one pass finds the matching
bracket of each opening bracket. It also records if a `,` or a `;` comes directly in that
bracket. Thus each look ahead takes constant time.

`@` followed by another name than a builtin is `S001` at that name: no slice has that syntax.
A module parameter or a struct parameter without `comptime` is `S001` at its name. With `mut`,
it is `S001` at `mut`. The v0.1 grammar has only `comptime` module parameters, and the front-end
spec keeps this rule for a struct (section 5.6). A function parameter has at most one mark,
`comptime` or `mut`. A second mark is `S001` at that mark, because the parser expects the name
there. At the end of the file, the position is the
end of the text of the lexer: the line after a final LF.

These rules settle the open points of the grammar:

- A statement that starts with `if` is an expression statement. The grammar has no `if`
  statement, so the conditional needs its `;`, and its arms hold only expressions.
- A comparison does not chain. `a < b < c` is `S001` at the second `<`. Parentheses group:
  `(a < b) < c`.
- Slice 3 has no packages. A path in an expression is a name, or a variant path `E::V` of two
  names. A path in a type and the module of an `instance` are one name. A package path is `S004`
  with one text: the second `::` of an expression path, and the `::` of a type or of a module.
- A `match` is an expression at the level of `if`: `match (x) { p => e, ... }`. Its scrutinee
  is in parentheses. Each arm has a pattern, `=>`, and one expression. A `,` separates two arms,
  and a `,` can end the arms. A `match` can have zero arms.
- A pattern is a number, `-` and a number, `true`, `false`, `_`, or a variant path `E::V`. A
  variant path can have binders in parentheses: a name or `_` each, and a `,` can end them.
  `E::V` and `E::V()` give the same pattern. Each other token in a pattern is `S001` with the
  text of section 6.2. This rule also holds for the token after the pattern, which must be
  `=>`. Thus a bare name, a nested pattern, an expression, a range, and `|` are `S001`. A third
  part of a path is `S004`, as in an expression.
- An enum has its tag type after `:`. Each variant has a name, the payload types in
  parentheses, and its tag value after `=`. The tag value is not optional: without `=`, the
  variant is `S001`. A `,` can end the variants and the payload types. `Add` and `Add()` give
  the same variant.
- The `domains` of a module are `none` without a clause and `some` with a clause.
- A struct without parentheses and a struct with `()` both have no parameters.
- Parentheses make no node. A node keeps the position of its first token, also if that token
  is a `(`: the `binary` node of `(a + b) * c` is at the `(`.
- `(a)` groups, `(a,)` is a tuple of one element, and `()` is the unit value. The same holds
  for a type: `(T)` groups, `(T,)` is a tuple type, and `()` is the unit type. A type suffix
  can follow each type form.
- A place is a name, or a field, an index, or a selector `.N` of a place. The parser accepts
  an index with more than one argument as a place. The type rules reject it.
- `x.m(args)` is a receiver call: a `method` node at the position of `x`. `t.0(x)` is a call of
  the element `t.0`, not a receiver call: a selector is no method name. `(x.m)(args)` calls the
  field `x.m`.
- A function type `fn (T, mut U) -> V` is a type, and in an expression a unary operand. Its
  result type takes each suffix after it: `fn () -> UInt[8]` indexes `UInt`. A `,` can end the
  parameters. A `comptime` mark on a parameter is `S001` at the mark. `(fn () -> T)[8]` parses
  as an index of a function type: pass 4 rejects it with `S007`.
- The lexer gives the value of a hexadecimal or binary number. A value of 2^65536 or more is a
  lexical error at the literal. A selector `.N` takes each number literal, for example `t.0x1`.

The syntax depth N of section 5.4 bounds the native stack of the parser and of each later
pass over the AST:

- The lexer rejects a bracket at the depth N + 1. Each recursive call of the parser that can
  repeat without limit first reads a bracket. Thus the recursion of the parser stays below a
  constant times N, for each input.
- The parser builds each chain in a loop: binary operators, prefix operators, suffixes, and
  the arrows of function types. It also reads each list in a loop. These are the elements of a
  tuple, an array, or a tuple type, and the parameters of a function type. They are also the
  arms of a `match` and the binders of a pattern. The branches of `if` and the arms of a
  `match` are in brackets.
- The height of each outermost expression or type is at most N. A name, a number, a
  string, `true`, `false`, `()`, and `[]` have height 1. Each other node has the height 1 plus
  the largest height of its parts. Parentheses make no node. A type has the same rule: a type
  name and `()` have height 1. The parts of a function type are its parameter types and its
  result type. A `mut` mark adds no height. Thus a recursive pass over the AST goes at most
  about 2N deep: N for the blocks and N for an expression.

An outermost expression or type is not part of another one. Each argument of an `instance` is
an outermost expression. The parser computes each height when it builds the node, so it needs
no recursion over the AST. A height above N is `S001` at the first token of the first such
outermost expression or type. This check runs only after a parse without another error. Thus
each syntax error wins over a height error, also a later one.
-/
namespace Silicon.Source.Parse

open Lex

def isSym (s : String) (t : Token) : Bool := t.kind == .symbol s

def isKw (w : String) (t : Token) : Bool := t.kind == .keyword w

/-!
The tokens and the result of the bracket pass. `close` holds the index of the matching bracket
of each opening bracket, or the size of the array if no bracket matches. `comma` is true at an
opening bracket if a `,` comes at its depth before its match. `semi` is the same for `;`.
-/
structure Input where
  tokens : Array Token
  close : Array Nat
  comma : Array Bool
  semi : Array Bool

/-! The bracket pass. It counts brackets of the three kinds as one depth. -/
def Input.of (ts : Array Token) : Input := Id.run do
  let mut close := Array.replicate ts.size ts.size
  let mut comma := Array.replicate ts.size false
  let mut semi := Array.replicate ts.size false
  let mut open_ : List Nat := []
  for h : i in [0:ts.size] do
    let t := ts[i]
    if opening t then open_ := i :: open_
    else if closing t then
      if let j :: rest := open_ then
        close := close.set! j i
        open_ := rest
    else if isSym "," t then
      if let j :: _ := open_ then comma := comma.set! j true
    else if isSym ";" t then
      if let j :: _ := open_ then semi := semi.set! j true
  return ⟨ts, close, comma, semi⟩

/-!
The context of the parser: the tokens, the syntax depth, and whether the parser is in the body
of a function without `comptime`.
-/
structure Ctx where
  input : Input
  depth : Nat
  plainFn : Bool

/-!
The state of the parser. `next` is the index of the next token. `high` is the first token of
the first outermost expression or type that is too high.
-/
structure St where
  next : Nat
  high : Option Pos

abbrev P := ReaderT Ctx (StateT St (Except Error))

def builtins : List String := ["TypeOf", "typeInfo", "field", "Struct", "ports"]

def allBinOps : List BinOp :=
  [.lor, .land, .or, .xor, .and, .eq, .ne, .lt, .le, .gt, .ge, .shl, .shr,
   .add, .sub, .addw, .subw, .mul, .div, .rem, .mulw]

/-! The lexer ends the tokens with `eof` or `error`. The parser never reads past that token. -/
def tokenAt (inp : Input) (i : Nat) : Token :=
  inp.tokens.getD i (inp.tokens.getD (inp.tokens.size - 1) ⟨⟨1, 1⟩, .eof⟩)

def peekAt (k : Nat) : P Token := return tokenAt (← read).input ((← get).next + k)

def peek : P Token := peekAt 0

def bump : P Unit := modify fun s => { s with next := s.next + 1 }

/-! `S001` at `t`. A lexical error keeps the message of the lexer. -/
def unexpected (t : Token) (what : String) : P α :=
  match t.kind with
  | .error msg => throw ⟨.S001, t.pos, msg⟩
  | _ => throw ⟨.S001, t.pos, "expected " ++ what⟩

def later (t : Token) (what : String) : P α :=
  throw ⟨.S004, t.pos, what ++ " is not supported yet"⟩

/-! The `S004` texts of section 6.2 with their fix. -/
def packagePathText : String :=
  "a package path is not supported yet; in this slice, a path is a variant `E::V` of an enum " ++
    "`E`, in an expression or a pattern"

def enumParamsText : String :=
  "an enum with parameters is not supported yet; remove the parameters, and give each payload " ++
    "a fixed type"

def packagePath (t : Token) : P α := throw ⟨.S004, t.pos, packagePathText⟩

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

/-! The path of a type or of a module is one identifier. -/
def path : P Ident := do
  let n ← ident
  let t ← peek
  if isSym "::" t then packagePath t else return n

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

/-! The `S001` text of a token that is not valid in a pattern (section 6.2). -/
def patternText : String :=
  "expected a pattern: an integer, `true`, `false`, `E::V(..)`, or `_`; compare with a " ++
    "constant in an `if`"

/-! `S001` at `t` in a pattern. A lexical error keeps the message of the lexer. -/
def badPattern (t : Token) : P α :=
  match t.kind with
  | .error msg => throw ⟨.S001, t.pos, msg⟩
  | _ => throw ⟨.S001, t.pos, patternText⟩

/-! A binder of a variant pattern: a name, or `_` for no name. -/
def binder : P (Option Ident) := do
  let t ← peek
  match t.kind with
  | .ident n => bump; return if n == "_" then none else some ⟨t.pos, n⟩
  | _ => badPattern t

/-! Fuel exhaustion cannot occur with the fuel of `parse`. -/
def exhausted : P α := do
  throw ⟨.S001, (← peek).pos, "parser fuel exhausted"⟩

/-! The binders of a variant pattern after its `(`, up to `)`. A `,` can end the list. -/
def binders : Nat → List (Option Ident) → P (List (Option Ident))
  | 0, _ => exhausted
  | f + 1, acc => do
    if ← acceptSym ")" then return acc.reverse
    let acc := (← binder) :: acc
    if ← acceptSym ")" then return acc.reverse
    let t ← peek
    if isSym "," t then bump; binders f acc else badPattern t

/-! A variant pattern after its first name `ty`: `::`, the variant name, and the binders. -/
def variantPattern (f : Nat) (start : Pos) (ty : Ident) : P Pattern := do
  let c ← peek
  unless isSym "::" c do badPattern c
  bump
  let u ← peek
  let .ident v := u.kind | badPattern u
  bump
  let w ← peek
  if isSym "::" w then packagePath w
  let bs ← if ← acceptSym "(" then binders f [] else pure []
  return .variant start ty ⟨u.pos, v⟩ bs

/-! A pattern, then the `=>` of its arm. -/
def pattern (f : Nat) : P Pattern := do
  let t ← peek
  let p ← match t.kind with
    | .number v => bump; pure (.int t.pos false v)
    | .symbol "-" => do
      bump
      let u ← peek
      let .number v := u.kind | badPattern u
      bump
      pure (.int t.pos true v)
    | .keyword "true" => bump; pure (.bool t.pos true)
    | .keyword "false" => bump; pure (.bool t.pos false)
    | .ident n =>
      bump
      if n == "_" then pure (.wild t.pos) else variantPattern f t.pos ⟨t.pos, n⟩
    | _ => badPattern t
  let a ← peek
  if isSym "=>" a then bump; return p else badPattern a

/-! The height of a node from the heights of its children. -/
def height (children : List Nat) : Nat := children.foldl max 0 + 1

/-!
Records the outermost expression or type at `start` with the height `h` if it is too high and
no earlier one is. Outermost forms do not overlap, so they end in the order of their start.
-/
def checkHeight (start : Pos) (h : Nat) : P Unit := do
  let d := (← read).depth
  modify fun s => if s.high.isNone && h > d then { s with high := some start } else s

/-!
The function types `acc` around the result type `r`, each with its height. `acc` holds the
position and the parameters of each function type, the innermost first.
-/
def fnFold (acc : List (Pos × List (FnParam × Nat))) (r : TypeExpr × Nat) : TypeExpr × Nat :=
  acc.foldl (fun r q => (.fn q.1 (q.2.map (·.1)) r.1, height (r.2 :: q.2.map (·.2)))) r

/-! An expression with its height. -/
structure Node where
  expr : Expr
  height : Nat

def leaf (e : Expr) : Node := ⟨e, 1⟩

/-! True at `(` if `()` follows, or if a `,` comes before the matching bracket. -/
def tupleAhead : P Bool := do
  let inp := (← read).input
  return isSym ")" (← peekAt 1) || inp.comma.getD (← get).next false

/-! True at `[` if a `;` comes before the matching bracket: an array type `[T; N]`. -/
def arrayTypeAhead : P Bool := do
  return (← read).input.semi.getD (← get).next false

/-!
Each function takes one unit of fuel from its caller. The argument `l` is the binding level of
`Print`: 1 for `||` to 9 for `*`, and 10 for a prefix operator.
-/
mutual
  def expr : Nat → P Node
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      if isKw "match" t then
        bump
        sym "("
        let s ← expr f
        sym ")"
        sym "{"
        let ms ← arms f []
        return ⟨.«match» t.pos s.expr (ms.map (·.1)), height (s.height :: ms.map (·.2))⟩
      else if isKw "if" t then
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
        return ⟨.cond t.pos c.expr y.expr n.expr, height [c.height, y.height, n.height]⟩
      else operand f 1

  /--
  The arms of a `match` after its `{`, up to `}`, each with the height of its expression. A `,`
  can end the list.
  -/
  def arms : Nat → List (Arm × Nat) → P (List (Arm × Nat))
    | 0, _ => exhausted
    | f + 1, acc => do
      if ← acceptSym "}" then return acc.reverse
      let p ← pattern f
      let e ← expr f
      let acc := (.mk p e.expr, e.height) :: acc
      if ← acceptSym "}" then return acc.reverse
      let t ← peek
      if isSym "," t then bump; arms f acc else unexpected t "`,` or `}`"

  /-- An expression of binding level `l` or higher. -/
  def operand : Nat → Nat → P Node
    | 0, _ => exhausted
    | f + 1, l => do
      let start := (← peek).pos
      let e ← unary f []
      climb f l start e

  /-- The infix operators after `e`, from the highest level down to `l`. -/
  def climb : Nat → Nat → Pos → Node → P Node
    | 0, _, _, _ => exhausted
    | f + 1, l, start, e =>
      ((List.range (Print.unaryLevel - l)).map (Print.unaryLevel - 1 - ·)).foldlM
        (fun e k => infixOps f k start e) e

  /--
  The operators of level `l` after `lhs`, in a loop. The right operand binds tighter, so its
  recursion goes at most `Print.unaryLevel` levels deeper. A comparison takes one operator.
  -/
  def infixOps : Nat → Nat → Pos → Node → P Node
    | 0, _, _, _ => exhausted
    | f + 1, l, start, lhs => do
      match opAt l (← peek) with
      | none => return lhs
      | some op =>
        bump
        let rhs ← operand f (l + 1)
        let e := ⟨.binary start op lhs.expr rhs.expr, height [lhs.height, rhs.height]⟩
        if op.associative then infixOps f l start e
        else
          let t ← peek
          if (opAt l t).isSome then
            throw ⟨.S001, t.pos, "a comparison does not chain; use parentheses"⟩
          return e

  /-- The prefix operators in a loop, then their operand. `ops` holds them in reverse order. -/
  def unary : Nat → List (Pos × UnOp) → P Node
    | 0, _ => exhausted
    | f + 1, ops => do
      let t ← peek
      match unOp t with
      | some op =>
        bump
        unary f ((t.pos, op) :: ops)
      | none =>
        let a ← if isKw "fn" t then do
            let ps ← fnHead f
            let (r, h) ← fnTypes f []
            pure ⟨.fnType t.pos (ps.map (·.1)) r, height (h :: ps.map (·.2))⟩
          else do
            let (a, _) ← postfixExpr f
            pure a
        return ops.foldl (fun a (p, op) => ⟨.unary p op a.expr, a.height + 1⟩) a

  /--
  A postfix form, and whether it is a place: a name, or a field, an index, or a selector of a
  place.
  -/
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
        let xs ← args f ")" true false
        let h := height (e.height :: xs.map (·.height))
        suffixes f start ⟨.call start e.expr (xs.map (·.expr)), h⟩ false
      else if isSym "[" t then
        bump
        let xs ← args f "]" false false
        let h := height (e.height :: xs.map (·.height))
        suffixes f start ⟨.index start e.expr (xs.map (·.expr)), h⟩ place
      else if isSym "." t then
        bump
        let s ← peek
        match s.kind with
        | .ident n =>
          bump
          if ← acceptSym "(" then
            let xs ← args f ")" true false
            let h := height (e.height :: xs.map (·.height))
            suffixes f start ⟨.method start e.expr ⟨s.pos, n⟩ (xs.map (·.expr)), h⟩ false
          else suffixes f start ⟨.field start e.expr ⟨s.pos, n⟩, e.height + 1⟩ place
        | .number v =>
          bump
          suffixes f start ⟨.select start e.expr s.pos v, e.height + 1⟩ place
        | _ => unexpected s "a field name"
      else return (e, place)

  def primary : Nat → P (Node × Bool)
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      match t.kind with
      | .ident n =>
        bump
        if isSym "::" (← peek) then
          bump
          let v ← ident
          let w ← peek
          if isSym "::" w then packagePath w
          else return (leaf (.path t.pos ⟨t.pos, n⟩ v), false)
        else return (leaf (.name t.pos n), true)
      | .number v => bump; return (leaf (.num t.pos v), false)
      | .string s => bump; return (leaf (.str t.pos s), false)
      | .keyword "true" => bump; return (leaf (.bool t.pos true), false)
      | .keyword "false" => bump; return (leaf (.bool t.pos false), false)
      | .symbol "(" =>
        if ← tupleAhead then
          bump
          let xs ← args f ")" true false
          let e : Node := match xs with
            | [] => leaf (.unit t.pos)
            | _ => ⟨.tuple t.pos (xs.map (·.expr)), height (xs.map (·.height))⟩
          return (e, false)
        bump
        let e ← expr f
        sym ")"
        return (e, false)
      | .symbol "[" =>
        if ← arrayTypeAhead then
          bump
          let (ty, h) ← typeExpr f
          sym ";"
          let n ← expr f
          sym "]"
          return (⟨.arrayType t.pos ty n.expr, height [h, n.height]⟩, false)
        else
          bump
          let xs ← args f "]" true false
          return (⟨.array t.pos (xs.map (·.expr)), height (xs.map (·.height))⟩, false)
      | .symbol "@" => builtin t
      | _ => unexpected t "an expression"

  /--
  A list of expressions up to `close`. A `,` can end the list. Each is an outermost expression
  if `top`.
  -/
  def args : Nat → String → Bool → Bool → P (List Node)
    | 0, _, _, _ => exhausted
    | f + 1, close, allowEmpty, top => do
      if allowEmpty then
        if ← acceptSym close then return []
      let e ← argument f top
      argsRest f close top [e]

  def argsRest : Nat → String → Bool → List Node → P (List Node)
    | 0, _, _, _ => exhausted
    | f + 1, close, top, acc => do
      if ← acceptSym close then return acc.reverse
      let t ← peek
      if isSym "," t then
        bump
        if ← acceptSym close then return acc.reverse
        let e ← argument f top
        argsRest f close top (e :: acc)
      else unexpected t s!"`,` or `{close}`"

  /-- An argument. It is an outermost expression if `top`. -/
  def argument : Nat → Bool → P Node
    | 0, _ => exhausted
    | f + 1, top => do
      let start := (← peek).pos
      let e ← expr f
      if top then checkHeight start e.height
      return e

  /-- A type with its height. The limit of expressions also holds for types. -/
  def typeExpr : Nat → P (TypeExpr × Nat)
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      match t.kind with
      | .ident n =>
        let _ ← path
        typeSuffix f t.pos (.name t.pos n, 1)
      | .keyword "fn" => fnTypes f []
      | .symbol "(" =>
        if ← tupleAhead then
          bump
          if ← acceptSym ")" then typeSuffix f t.pos (.unit t.pos, 1)
          else
            let ts ← typeElems f []
            typeSuffix f t.pos (.tuple t.pos (ts.map (·.1)), height (ts.map (·.2)))
        else
          bump
          let ty ← typeExpr f
          sym ")"
          typeSuffix f t.pos ty
      | .symbol "[" =>
        bump
        let (ty, h) ← typeExpr f
        sym ";"
        let n ← expr f
        sym "]"
        typeSuffix f t.pos (.array t.pos ty n.expr, height [h, n.height])
      | .symbol "@" => builtin t
      | _ => unexpected t "a type"

  /-- The element types of a tuple type up to `)`. A `,` can end the list. -/
  def typeElems : Nat → List (TypeExpr × Nat) → P (List (TypeExpr × Nat))
    | 0, _ => exhausted
    | f + 1, acc => do
      let acc := (← typeExpr f) :: acc
      if ← acceptSym ")" then return acc.reverse
      let t ← peek
      if isSym "," t then
        bump
        if ← acceptSym ")" then return acc.reverse
        typeElems f acc
      else unexpected t "`,` or `)`"

  def typeSuffix : Nat → Pos → TypeExpr × Nat → P (TypeExpr × Nat)
    | 0, _, _ => exhausted
    | f + 1, start, (ty, h) => do
      let t ← peek
      if isSym "[" t then
        bump
        let xs ← args f "]" false false
        typeSuffix f start (.index start ty (xs.map (·.expr)), height (h :: xs.map (·.height)))
      else if isSym "(" t then later t "a type function call"
      else return (ty, h)

  /-- `fn (params) ->`: the parameters with their heights. -/
  def fnHead : Nat → P (List (FnParam × Nat))
    | 0 => exhausted
    | f + 1 => do
      kw "fn"
      sym "("
      let ps ← fnParams f []
      sym "->"
      return ps

  /--
  The parameters of a function type up to `)`, with their heights. A `,` can end the list. A
  `comptime` mark is `S001` at the mark.
  -/
  def fnParams : Nat → List (FnParam × Nat) → P (List (FnParam × Nat))
    | 0, _ => exhausted
    | f + 1, acc => do
      if ← acceptSym ")" then return acc.reverse
      let t ← peek
      if isKw "comptime" t then
        throw ⟨.S001, t.pos, "a parameter of a function type has no `comptime` mark"⟩
      let m ← acceptKw "mut"
      let (ty, h) ← typeExpr f
      let acc := (.mk m ty, h) :: acc
      if ← acceptSym ")" then return acc.reverse
      sym ","
      fnParams f acc

  /--
  A chain of function types `fn (A) -> fn (B) -> T` in a loop, then the result type `T` of the
  last. Arrows bind right. `acc` holds the position and the parameters of each `fn` before, in
  reverse order.
  -/
  def fnTypes : Nat → List (Pos × List (FnParam × Nat)) → P (TypeExpr × Nat)
    | 0, _ => exhausted
    | f + 1, acc => do
      let t ← peek
      if isKw "fn" t then
        let ps ← fnHead f
        fnTypes f ((t.pos, ps) :: acc)
      else return fnFold acc (← typeExpr f)
end

/-! An outermost type. -/
def typeTop (f : Nat) : P TypeExpr := do
  let start := (← peek).pos
  let (ty, h) ← typeExpr f
  checkHeight start h
  return ty

def typeAnnotation (f : Nat) : P TypeExpr := do
  sym ":"
  typeTop f

/-! An outermost expression, directly in a statement or an item. -/
def value (f : Nat) : P Expr := do
  let start := (← peek).pos
  let e ← expr f
  checkHeight start e.height
  return e.expr

/-! `x = v;` or `x := v;` after the postfix form `e`, or else an expression statement. -/
def placeStmt (f : Nat) (start : Pos) (e : Node) (place : Bool) : P Stmt := do
  let t ← peek
  if isSym "=" t || isSym ":=" t then
    if !place then unexpected t "`;`"
    checkHeight start e.height
    bump
    let v ← value f
    sym ";"
    return if isSym "=" t then .assign start e.expr v else .connect start e.expr v
  else
    let e ← climb f 1 start e
    checkHeight start e.height
    sym ";"
    return .expr start e.expr

/-! `type N = T;` at an item or a statement. -/
def aliasDecl (f : Nat) (start : Pos) (make : Pos → Ident → TypeExpr → α) : P α := do
  kw "type"
  let n ← ident
  sym "="
  let ty ← typeTop f
  sym ";"
  return make start n ty

/-! The statements that declare a port, a resource, or an instance. -/
def resourceKeywords : List String := ["input", "output", "reg", "wire", "mem", "instance"]

mutual
  def stmt : Nat → P Stmt
    | 0 => exhausted
    | f + 1 => do
      let t ← peek
      if (← read).plainFn && resourceKeywords.any (isKw · t) then
        later t "a port, a resource, or an instance in a `fn` without `comptime`"
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
      | .keyword "mem" =>
        bump
        let n ← ident
        sym ":"
        sym "["
        let ty ← typeTop f
        sym ";"
        let d ← value f
        sym "]"
        noDomain
        sym ";"
        return .mem t.pos n ty d
      | .keyword "input" => port f t .input
      | .keyword "output" => port f t .output
      | .keyword "instance" =>
        bump
        let n ← ident
        sym "="
        let m ← path
        sym "("
        let xs := (← args f ")" true true).map (·.expr)
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
          let y ← block f
          let n ← if ← acceptKw "else" then some <$> block f else pure none
          return .ctIf t.pos c y n
        else if isKw "for" u then
          bump
          let i ← ident
          kw "in"
          let lo ← value f
          sym ".."
          let hi ← value f
          return .ctFor t.pos i lo hi (← block f)
        else unexpected u "`if` or `for`"
      | .keyword "type" => aliasDecl f t.pos .alias
      | .symbol "{" => return .block t.pos (← block f)
      | .ident _ =>
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

  def block : Nat → P (List Stmt)
    | 0 => exhausted
    | f + 1 => do
      sym "{"
      stmts f []

  def stmts : Nat → List Stmt → P (List Stmt)
    | 0, _ => exhausted
    | f + 1, acc => do
      let t ← peek
      if isSym "}" t then bump; return acc.reverse
      if t.kind == .eof then unexpected t "`}`"
      let s ← stmt f
      stmts f (s :: acc)
end

/-!
The mode of a parameter. A module parameter and a struct parameter need `comptime`. A function
parameter can have `comptime` or `mut`.
-/
def paramMode : Bool → P ParamMode
  | true => kw "comptime" *> pure .comptime
  | false => do
    if ← acceptKw "comptime" then return .comptime
    if ← acceptKw "mut" then return .mut
    return .none

def param (f : Nat) (static : Bool) : P Param := do
  let t ← peek
  let m ← paramMode static
  let n ← ident
  return ⟨t.pos, m, n, ← typeAnnotation f⟩

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
  let r ← typeTop f
  let b ← withReader (fun c => { c with plainFn := !comptime }) (block f)
  return .fn start comptime n ps r b

def moduleItem (f : Nat) (start : Pos) : P Item := do
  kw "module"
  let n ← ident
  sym "("
  let ps ← params f true []
  let ds ← if ← acceptKw "domains" then sym "(" *> some <$> domainNames else pure none
  let t ← peek
  if isKw "conforms" t then later t "a contract attachment"
  return .module start n ps ds (← block f)

/-! The fields of a struct after its `{`, up to `}`. A `,` can end the list. -/
def fields : Nat → List StructField → P (List StructField)
  | 0, _ => exhausted
  | f + 1, acc => do
    if ← acceptSym "}" then return acc.reverse
    let n ← ident
    let acc := ⟨n, ← typeAnnotation f⟩ :: acc
    if ← acceptSym "}" then return acc.reverse
    sym ","
    fields f acc

/-! A struct. Without parentheses and with `()`, it has no parameters. -/
def structItem (f : Nat) (start : Pos) : P Item := do
  kw "struct"
  let n ← ident
  let ps ← if ← acceptSym "(" then params f true [] else pure []
  sym "{"
  return .struct start n ps (← fields f [])

/-! The payload types of a variant after its `(`, up to `)`. A `,` can end the list. -/
def payload : Nat → List TypeExpr → P (List TypeExpr)
  | 0, _ => exhausted
  | f + 1, acc => do
    if ← acceptSym ")" then return acc.reverse
    let acc := (← typeTop f) :: acc
    if ← acceptSym ")" then return acc.reverse
    sym ","
    payload f acc

/-! A variant: its name, its payload types in parentheses, `=`, and its tag value. -/
def variant (f : Nat) : P Variant := do
  let n ← ident
  let ps ← if ← acceptSym "(" then payload f [] else pure []
  sym "="
  return ⟨n, ps, ← value f⟩

/-! The variants of an enum after its `{`, up to `}`. A `,` can end the list. -/
def variants : Nat → List Variant → P (List Variant)
  | 0, _ => exhausted
  | f + 1, acc => do
    if ← acceptSym "}" then return acc.reverse
    let acc := (← variant f) :: acc
    if ← acceptSym "}" then return acc.reverse
    sym ","
    variants f acc

/-! An enum. A `(` after its name is an enum with parameters, a later slice. -/
def enumItem (f : Nat) (start : Pos) : P Item := do
  kw "enum"
  let n ← ident
  let t ← peek
  if isSym "(" t then throw ⟨.S004, t.pos, enumParamsText⟩
  let ty ← typeAnnotation f
  sym "{"
  return .enum start n ty (← variants f [])

def laterItems : List (String × String) :=
  [("import", "an import"), ("pub", "`pub`"), ("extern", "an extern module")]

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
  | .keyword "struct" => structItem f t.pos
  | .keyword "type" => aliasDecl f t.pos .alias
  | .keyword "enum" => enumItem f t.pos
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

/-! The message of an expression or a type higher than the syntax depth `depth`. -/
def heightText (depth : Nat) : String :=
  s!"an expression or a type is higher than {depth} levels; raise --syntax-depth"

/-!
The items of a token list, or the first error. The fuel bounds the depth of the calls, not
their number. On a chain of active calls the token index never decreases. A loop step starts
after its previous step took a token. Fewer than 32 calls on a chain start at one index. The
longest such run goes from `items` through `stmt` and `expr` to `primary`. Thus
`32 * (n + 1)` fuel for `n` tokens never runs out. `depth` is the syntax depth. A height
error comes only after a parse without another error.
-/
def parse (depth : Nat) (tokens : List Token) : Except Error (List Item) := do
  let ts := tokens.toArray
  let (items, s) ← ((items (32 * (ts.size + 1)) []).run ⟨Input.of ts, depth, false⟩).run ⟨0, none⟩
  match s.high with
  | some p => throw ⟨.S001, p, heightText depth⟩
  | none => return items

/-!
An expression of the command line, such as the `EXPR` of `eval`, with the syntax depth `depth`.
The positions are in the text of the expression. A token after the expression is `S001`.
-/
def parseExpr (depth : Nat) (s : String) : Except Error Expr := do
  let ts := (lex depth s).toArray
  let act : P Expr := do
    let e ← value (32 * (ts.size + 1))
    let t ← peek
    unless t.kind == .eof do unexpected t "the end of the expression"
    return e
  let (e, st) ← (act.run ⟨Input.of ts, depth, false⟩).run ⟨0, none⟩
  match st.high with
  | some p => throw ⟨.S001, p, heightText depth⟩
  | none => return e

/-! The items of a source text, with the syntax depth `depth`. -/
def parseSource (depth : Nat) (s : String) : Except Error (List Item) :=
  parse depth (lex depth s)

end Silicon.Source.Parse
