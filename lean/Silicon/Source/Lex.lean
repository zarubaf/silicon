import Silicon.Source.Syntax

/-!
The lexer of the full v0.1 token set. It covers the keywords of later slices, so the parser
can reject their syntax with `S004` instead of `S001`. Each token takes the longest match.
The lexer checks no rule between tokens: `12ab` is a number and an identifier. `@` is a
symbol, so the parser checks the builtin name after it.

The input is a `String`, so it is valid UTF-8. The command line rejects other bytes as a
usage error before it calls the lexer.

The lexer also bounds the brackets. `(`, `[`, and `{` together nest at most the syntax depth N
of section 5.4. The first opening bracket at the depth N + 1 is an error token. Thus the
recursion of the parser stays bounded for each input. A closing bracket at the depth 0 keeps
the depth at 0, so an extra closing bracket cannot hide a later excess. The parser reports
that closing bracket, because it comes first.
-/
namespace Silicon.Source.Lex

/-! The keywords of the v0.1 grammar. No slice adds a keyword. -/
def keywords : List String :=
  ["import", "as", "pub", "const", "type", "struct", "comptime", "fn", "module", "extern",
   "let", "mut", "return", "if", "else", "for", "in", "conforms", "using", "true", "false",
   "reg", "wire", "mem", "input", "output", "instance", "domains", "with"]

/-! The two-character operators. Longest match prefers them to the one-character ones. -/
def longSymbols : List String :=
  [":=", "::", "->", "..", "+%", "-%", "*%", "==", "!=", "<=", ">=", "<<", ">>", "&&", "||"]

def shortSymbols : List Char :=
  ['(', ')', '[', ']', '{', '}', ',', ';', ':', '.', '=', '+', '-', '*', '/', '%', '<', '>',
   '!', '~', '&', '|', '^', '@']

/-! A token kind. A lexical error ends the token list with `error` at its position. -/
inductive Kind where
  | ident (name : String)
  | keyword (word : String)
  | symbol (text : String)
  | number (value : Nat)
  | string (value : String)
  | eof
  | error (msg : String)
  deriving Repr, DecidableEq, BEq, Inhabited

structure Token where
  pos : Pos
  kind : Kind
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The lexer state between two characters. -/
inductive Mode where
  | top
  /-- The next character is the second character of a token that `top` already read. -/
  | skip (next : Mode)
  | word (start : Pos) (acc : List Char)
  | number (start : Pos) (radix : Nat) (acc : List Char)
  | string (start : Pos) (acc : List Char) (escape : Bool)
  | lineComment
  | blockComment (start : Pos) (star : Bool)
  deriving Repr, Inhabited

/-! LF ends a line. Each other character counts as one column, also CR and tab. -/
def advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then ⟨p.line + 1, 1⟩ else ⟨p.line, p.col + 1⟩

def whitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

def identStart (c : Char) : Bool := c.isAlpha || c == '_'

def identChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-! The Unicode control characters, which a string must write as an escape. -/
def control (c : Char) : Bool := c.toNat < 0x20 || (0x7F ≤ c.toNat && c.toNat < 0xA0)

def digitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def isDigitOf (radix : Nat) (c : Char) : Bool :=
  (c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) && digitValue c < radix

/-! The accumulators hold their characters in reverse order. -/
def numberValue (radix : Nat) (digits : List Char) : Nat :=
  digits.foldl (fun n c => n * radix + digitValue c) 0

def escaped : Char → Option Char
  | '"' => some '"' | '\\' => some '\\' | 'n' => some '\n' | 'r' => some '\r'
  | 't' => some '\t' | _ => none

def wordToken (start : Pos) (acc : List Char) : Token :=
  let s := String.ofList acc.reverse
  ⟨start, if keywords.contains s then .keyword s else .ident s⟩

/-! The most significant digits of 2^65536 in each radix. Leading zeros do not count. -/
def maxDigits : Nat → Nat
  | 2 => 65536 | 16 => 16384 | _ => 19729

/-!
A number literal is below 2^65536. The lexer counts the digits before it converts them. Thus a
long literal fails in linear time, at the position of the literal.
-/
def numberToken (start : Pos) (radix : Nat) (acc : List Char) : Token :=
  let digits := acc.reverse.dropWhile (· == '0')
  let tooLarge : Token := ⟨start, .error "number literal is not below 2^65536"⟩
  if digits.length > maxDigits radix then tooLarge
  else
    let v := numberValue radix digits
    if v < 2 ^ 65536 then ⟨start, .number v⟩ else tooLarge

/-! A prefix `0x` or `0b` needs a digit after it. Else the `0` is a decimal number. -/
def radixAfter (c : Char) : List Char → Option Nat
  | 'x' :: d :: _ => if c == '0' && isDigitOf 16 d then some 16 else none
  | 'b' :: d :: _ => if c == '0' && isDigitOf 2 d then some 2 else none
  | _ => none

/-! The token that starts at `c`. A token of two characters sets `skip`. -/
def begin (p : Pos) (c : Char) (rest : List Char) : Mode × Option Token :=
  let pair := rest.head?.map fun d => String.ofList [c, d]
  if whitespace c then (.top, none)
  else if pair == some "//" then (.skip .lineComment, none)
  else if pair == some "/*" then (.skip (.blockComment p false), none)
  else if c == '"' then (.string p [] false, none)
  else if identStart c then (.word p [c], none)
  else if let some r := radixAfter c rest then (.skip (.number p r []), none)
  else if c.isDigit then (.number p 10 [c], none)
  else match pair with
    | some s => if longSymbols.contains s then (.skip .top, some ⟨p, .symbol s⟩) else short
    | none => short
where
  short : Mode × Option Token :=
    if shortSymbols.contains c then (.top, some ⟨p, .symbol (String.singleton c)⟩)
    else (.top, some ⟨p, .error "unexpected character"⟩)

/-! The token list ends with the first error token. -/
def push (tokens : List Token) : Option Token → Except (List Token) (List Token)
  | none => .ok tokens
  | some t@⟨_, .error _⟩ => .error (t :: tokens)
  | some t => .ok (t :: tokens)

/-! The default of the syntax depth. -/
def defaultSyntaxDepth : Nat := 4096

/-! The largest syntax depth. The runtime stack of the executable is tested up to it. -/
def maxSyntaxDepth : Nat := 65536

/-! The three kinds of brackets count as one depth, in the lexer and in the parser. -/
def opening (t : Token) : Bool :=
  t.kind == .symbol "(" || t.kind == .symbol "[" || t.kind == .symbol "{"

def closing (t : Token) : Bool :=
  t.kind == .symbol ")" || t.kind == .symbol "]" || t.kind == .symbol "}"

/-!
The token `t` at the bracket depth `d`, and the depth after it. An opening bracket at the depth
`depth + 1` becomes an error token. A closing bracket at the depth 0 keeps the depth at 0.
-/
def nest (depth d : Nat) : Option Token → Option Token × Nat
  | none => (none, d)
  | some t =>
    if opening t then
      if d < depth then (some t, d + 1)
      else (some ⟨t.pos, .error s!"brackets nest deeper than {depth} levels"⟩, d)
    else if closing t then (some t, d - 1)
    else (some t, d)

/-!
One step per character keeps the recursion structural. The tokens are in reverse order. `d` is
the bracket depth before the character.
-/
def run (depth : Nat) : Nat → Mode → Pos → List Token → List Char → List Token
  | _, mode, p, tokens, [] =>
    let last : Option Token := match mode with
      | .word s acc => some (wordToken s acc)
      | .number s r acc => some (numberToken s r acc)
      | .string s .. => some ⟨s, .error "unterminated string"⟩
      | .blockComment s _ => some ⟨s, .error "unterminated comment"⟩
      | _ => none
    match push tokens last with
    | .ok tokens => ⟨p, .eof⟩ :: tokens
    | .error tokens => tokens
  | d, mode, p, tokens, c :: cs =>
    let q := advance p c
    let start (tokens : List Token) (first : Option Token) : List Token :=
      match push tokens first with
      | .error tokens => tokens
      | .ok tokens =>
        let (mode, t) := begin p c cs
        let (t, e) := nest depth d t
        match push tokens t with
        | .error tokens => tokens
        | .ok tokens => run depth e mode q tokens cs
    match mode with
    | .top => start tokens none
    | .skip next => run depth d next q tokens cs
    | .word s acc =>
      if identChar c then run depth d (.word s (c :: acc)) q tokens cs
      else start tokens (some (wordToken s acc))
    | .number s r acc =>
      if isDigitOf r c then run depth d (.number s r (c :: acc)) q tokens cs
      else start tokens (some (numberToken s r acc))
    | .string s acc true => match escaped c with
      | some e => run depth d (.string s (e :: acc) false) q tokens cs
      | none => ⟨s, .error "invalid escape"⟩ :: tokens
    | .string s acc false =>
      if c == '"' then
        run depth d .top q (⟨s, .string (String.ofList acc.reverse)⟩ :: tokens) cs
      else if c == '\\' then run depth d (.string s acc true) q tokens cs
      else if control c then
        ⟨s, .error (if c == '\n' then "unterminated string" else "control character")⟩
          :: tokens
      else run depth d (.string s (c :: acc) false) q tokens cs
    | .lineComment => run depth d (if c == '\n' then .top else .lineComment) q tokens cs
    | .blockComment s star =>
      if star && c == '/' then run depth d .top q tokens cs
      else run depth d (.blockComment s (c == '*')) q tokens cs

/-!
The tokens of a source text with the syntax depth `depth`. The last token is `eof`, or `error`
for `S001`. The lexer stops at its first error, so that error is the first in position order.
-/
def lex (depth : Nat) (s : String) : List Token := (run depth 0 .top ⟨1, 1⟩ [] s.toList).reverse

/-! The `S001` error of a token list, if the lexer stopped at an error. -/
def error? (tokens : List Token) : Option Error :=
  match tokens.getLast? with
  | some ⟨p, .error msg⟩ => some ⟨.S001, p, msg⟩
  | _ => none

end Silicon.Source.Lex
