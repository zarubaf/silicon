import Silicon.Core.Syntax
import Std

/-!
The text format uses named S-expression forms.
The reader preserves source positions. The printer preserves input order.
-/
namespace Silicon.Core

/-! Keywords cannot be names. Names use ASCII letters, digits, underscores, and dollar signs. -/
def keywords : List String :=
  ["design", "module", "extern", "input", "output", "clock", "bits", "deps", "let", "reg",
   "next", "mem", "write", "inst", "assign", "reset", "sync", "const", "not", "add", "sub",
   "mul", "and", "or", "xor", "shl", "shru", "shrs", "concat", "icmp", "mux", "extract",
   "replicate", "read", "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"]

def nameStart (c : Char) : Bool := c.isAlpha || c == '_'

def nameRest (c : Char) : Bool := nameStart c || c.isDigit || c == '$'

def validName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => nameStart c && cs.all nameRest && !keywords.contains s

/-! Name collection gives one lexical condition for every name in a design. -/
def Expr.names : Expr → List String
  | .ref _ n => [n]
  | .port _ i n => [i, n]
  | .const .. => []
  | .un _ _ a | .extract _ a _ _ | .replicate _ a _ => a.names
  | .bin _ _ a b | .icmp _ _ a b => a.names ++ b.names
  | .mux _ a b c => a.names ++ b.names ++ c.names
  | .read _ n a => n :: a.names

def Reset.names (r : Reset) : List String := r.signal.names ++ r.value.names

def Stmt.names : Stmt → List String
  | .let_ _ n _ v | .next _ n v | .assign _ n v => n :: v.names
  | .reg _ n _ c r => n :: c :: (r.toList.flatMap Reset.names)
  | .mem _ n _ _ c => [n, c]
  | .write _ n _ a d e => n :: (a.names ++ d.names ++ e.names)
  | .inst _ n m xs => n :: m :: xs.flatMap (fun (k, v) => k :: v.names)

def Item.names : Item → List String
  | .module m => m.name :: (m.ports.map Port.name ++ m.body.flatMap Stmt.names)
  | .extern e => e.name :: (e.ports.map Port.name ++
      e.deps.flatMap (fun d => d.output :: d.inputs))

def Design.ValidNames (d : Design) : Prop :=
  ∀ n ∈ d.top :: d.items.flatMap Item.names, validName n = true

/-! Parser limits concern expression depth and all numbers except constant values. -/
structure TextLimit where
  pos : Pos
  path : List Nat
  value : Nat
  bound : Nat
  deriving Repr

def TextLimit.ok (l : TextLimit) : Bool := l.value ≤ l.bound

def numberLimit (p : Pos) (path : List Nat) (n : Nat) : TextLimit :=
  ⟨p, path, n, 4294967295⟩

/-! A name has depth zero. Each compound expression adds one level. -/
def Expr.textLimits (depth : Nat) : Expr → List TextLimit
  | .ref .. | .port .. => []
  | .const p w _ => [⟨p, [], depth + 1, 256⟩, numberLimit p [1] w]
  | .un p _ a => ⟨p, [], depth + 1, 256⟩ :: a.textLimits (depth + 1)
  | .bin p _ a b | .icmp p _ a b =>
    ⟨p, [], depth + 1, 256⟩ :: (a.textLimits (depth + 1) ++ b.textLimits (depth + 1))
  | .mux p a b c => ⟨p, [], depth + 1, 256⟩ ::
    (a.textLimits (depth + 1) ++ b.textLimits (depth + 1) ++ c.textLimits (depth + 1))
  | .extract p a l w => ⟨p, [], depth + 1, 256⟩ ::
    (a.textLimits (depth + 1) ++ [numberLimit p [2] l, numberLimit p [3] w])
  | .replicate p a n => ⟨p, [], depth + 1, 256⟩ ::
    (a.textLimits (depth + 1) ++ [numberLimit p [2] n])
  | .read p _ a => ⟨p, [], depth + 1, 256⟩ :: a.textLimits (depth + 1)

def Reset.textLimits (r : Reset) : List TextLimit :=
  r.signal.textLimits 0 ++ r.value.textLimits 0

def Stmt.textLimits : Stmt → List TextLimit
  | .let_ p _ w v => numberLimit p [2, 1] w :: v.textLimits 0
  | .reg p _ w _ r => numberLimit p [2, 1] w :: r.toList.flatMap Reset.textLimits
  | .mem p _ w d _ => [numberLimit p [2, 1] w, numberLimit p [3] d]
  | .next _ _ v | .assign _ _ v => v.textLimits 0
  | .write p _ i a d e => numberLimit p [2] i ::
    (a.textLimits 0 ++ d.textLimits 0 ++ e.textLimits 0)
  | .inst _ _ _ xs => xs.flatMap (fun x => x.2.textLimits 0)

def Port.textLimits (p : Port) : List TextLimit :=
  match p.ty with
  | .clock => []
  | .bits n => [numberLimit p.pos [2, 1] n]

def Item.textLimits : Item → List TextLimit
  | .module m => m.ports.flatMap Port.textLimits ++ m.body.flatMap Stmt.textLimits
  | .extern e => e.ports.flatMap Port.textLimits

def Design.textLimits (d : Design) : List TextLimit := d.items.flatMap Item.textLimits

def Design.WithinLimits (d : Design) : Prop := d.textLimits.all TextLimit.ok = true

/-! Source erasure leaves the values of all parser limits unchanged. -/
@[simp] theorem Expr.textLimits_erase (e : Expr) (depth : Nat) :
    (e.erasePos.textLimits depth).map TextLimit.ok = (e.textLimits depth).map TextLimit.ok := by
  induction e generalizing depth <;>
    simp_all [Expr.erasePos, Expr.textLimits, numberLimit, TextLimit.ok]

@[simp] theorem Reset.textLimits_erase (r : Reset) :
    r.erasePos.textLimits.map TextLimit.ok = r.textLimits.map TextLimit.ok := by
  simp [Reset.erasePos, Reset.textLimits]

@[simp] theorem Stmt.textLimits_erase (s : Stmt) :
    s.erasePos.textLimits.map TextLimit.ok = s.textLimits.map TextLimit.ok := by
  cases s <;> simp [Stmt.erasePos, Stmt.textLimits, numberLimit, TextLimit.ok,
    List.map_flatMap, List.flatMap_map]
  rename_i r
  cases r <;> simp

@[simp] theorem Port.textLimits_erase (p : Port) :
    p.erasePos.textLimits.map TextLimit.ok = p.textLimits.map TextLimit.ok := by
  cases p with
  | mk pos dir name ty => cases ty <;> rfl

@[simp] theorem Item.textLimits_erase (i : Item) :
    i.erasePos.textLimits.map TextLimit.ok = i.textLimits.map TextLimit.ok := by
  cases i <;> simp [Item.erasePos, Item.textLimits, List.map_flatMap, List.flatMap_map]

@[simp] theorem Design.textLimits_erase (d : Design) :
    d.erasePos.textLimits.map TextLimit.ok = d.textLimits.map TextLimit.ok := by
  simp [Design.erasePos, Design.textLimits, List.map_flatMap, List.flatMap_map]


/-! Tokens retain their first character position. The final position marks the end of the file. -/
namespace Text

structure Token where
  pos : Pos
  text : String
  deriving Repr, DecidableEq, Inhabited

def advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then ⟨p.line + 1, 1, []⟩ else ⟨p.line, p.col + 1, []⟩

def delimiter (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '(' || c == ')' || c == ';'

def flush (start : Pos) (word : List Char) (tokens : List Token) : List Token :=
  if word.isEmpty then tokens else ⟨start, String.ofList word.reverse⟩ :: tokens

def lexLoop : List Char → Pos → Pos → List Char → Bool → List Token → List Token × Pos
  | [], p, start, word, _, tokens => ((flush start word tokens).reverse, p)
  | c :: cs, p, start, word, comment, tokens =>
    if comment then
      lexLoop cs (advance p c) start word (c != '\n') tokens
    else if delimiter c then
      let tokens := flush start word tokens
      let tokens := if c == '(' || c == ')' then ⟨p, String.singleton c⟩ :: tokens else tokens
      lexLoop cs (advance p c) (advance p c) [] (c == ';') tokens
    else
      lexLoop cs (advance p c) (if word.isEmpty then p else start) (c :: word) false tokens

def lex (s : String) : List Token × Pos := lexLoop s.toList ⟨1, 1, []⟩ ⟨1, 1, []⟩ [] false []

/-! A malformed atom reports its first bad character rather than the atom's start. -/
def tokenCharacter (c : Char) : Bool := nameRest c || c == '.'

def badTokenCharacter (t : Token) : Option Error :=
  if t.text == "(" || t.text == ")" then none else
    let chars := t.text.toList
    let offset := chars.findIdx (!tokenCharacter ·)
    if offset < chars.length then
      some ⟨.E001, ⟨t.pos.line, t.pos.col + offset, []⟩, "invalid character"⟩
    else none

def badCharacter : List Token → Option Error
  | [] => none
  | t :: ts => (badTokenCharacter t).orElse (fun _ => badCharacter ts)

def correctTokenError (tokens : List Token) (error : Error) : Error :=
  match tokens.find? (·.pos == error.pos) with
  | none => error
  | some t => (badTokenCharacter t).getD error

/-! A missing closing token stays in the tree so earlier grammar errors take priority. -/
inductive Form where
  | atom (token : Token)
  | list (pos : Pos) (children : List Form) (close : Option Pos)
  | bad (pos : Pos)
  deriving Repr, Inhabited

def Form.pos : Form → Pos
  | .atom t => t.pos
  | .list p .. | .bad p => p

def forms : Nat → List Token → List Form × List Token
  | 0, ts => ([], ts)
  | _ + 1, [] => ([], [])
  | fuel + 1, t :: ts =>
    if t.text == ")" then ([], t :: ts)
    else if t.text == "(" then
      let (inside, rest) := forms fuel ts
      let (close, rest) := match rest with
        | r :: rs => (some r.pos, rs)
        | [] => (none, [])
      let (after, rest) := forms fuel rest
      (.list t.pos inside close :: after, rest)
    else
      let (after, rest) := forms fuel ts
      (.atom t :: after, rest)

/-! The grammar reader reports the next token or the enclosing end position. -/
def failure (p : Pos) (msg : String := "unexpected token") : Except Error α :=
  .error ⟨.E001, p, msg⟩

structure Cursor where
  forms : List Form
  stop : Pos
  closed : Bool

def Cursor.pos (c : Cursor) : Pos := c.forms.head?.map Form.pos |>.getD c.stop

abbrev Reader (α : Type) := Cursor → Except Error (α × Cursor)

instance : Monad Reader where
  pure a c := .ok (a, c)
  bind f g c := do
    let (a, c) ← f c
    g a c

def take : Reader Form := fun c =>
  match c.forms with
  | [] => failure c.stop
  | f :: fs => .ok (f, { c with forms := fs })

def atom : Reader Token := fun c => do
  let (f, c') ← take c
  match f with
  | .atom t => .ok (t, c')
  | _ => failure f.pos

def word (s : String) : Reader Unit := fun c => do
  let (t, c') ← atom c
  if t.text == s then .ok ((), c') else failure t.pos ("expected " ++ s)

def name : Reader String := fun c => do
  let (t, c') ← atom c
  if validName t.text then .ok (t.text, c') else failure t.pos "expected name"

def number : Reader Nat := fun c => do
  let (t, c') ← atom c
  if !t.text.toList.isEmpty && t.text.toList.all Char.isDigit then
    .ok (Nat.ofDigitChars 10 t.text.toList 0, c')
  else failure t.pos "expected decimal natural number"

def finish : Reader Unit := fun c =>
  if c.forms.isEmpty && c.closed then .ok ((), c) else failure c.pos

def inside (eof : Pos) (f : Form) (r : Reader α) : Except Error α := do
  match f with
  | .list _ fs close =>
    let (a, c) ← r ⟨fs, close.getD eof, close.isSome⟩
    let _ ← finish c
    pure a
  | _ => failure f.pos "expected opening parenthesis"

def form (eof : Pos) (r : Pos → Reader α) : Reader α := fun c => do
  let (f, c') ← take c
  let a ← inside eof f (r f.pos)
  pure (a, c')

def peekWord (c : Cursor) : Option String :=
  match c.forms with
  | .atom t :: _ => some t.text
  | _ => none

def peekHead (c : Cursor) : Option String :=
  match c.forms with
  | .list _ (.atom t :: _) _ :: _ => some t.text
  | _ => none

/-! Repeated fields consume at most one source form per step. -/
def many (r : Reader α) : Nat → Reader (List α)
  | 0 => fun c => if c.forms.isEmpty then .ok ([], c) else failure c.pos
  | fuel + 1 => fun c =>
    if c.forms.isEmpty then .ok ([], c) else do
      let (a, c) ← r c
      let (as, c) ← many r fuel c
      pure (a :: as, c)

def remaining (r : Reader α) : Reader (List α) := fun c => many r c.forms.length c

/-! The reader and the printer share operation spellings. -/
def _root_.Silicon.Core.UnOp.text : UnOp → String | .not => "not"

def _root_.Silicon.Core.BinOp.text : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .and => "and" | .or => "or"
  | .xor => "xor" | .shl => "shl" | .shru => "shru" | .shrs => "shrs" | .concat => "concat"

def _root_.Silicon.Core.Pred.text : Pred → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .ugt => "ugt"
  | .uge => "uge" | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

def readBin (s : String) : Option BinOp :=
  [.add, .sub, .mul, .and, .or, .xor, .shl, .shru, .shrs, .concat].find? (·.text == s)

def readPred : Reader Pred := fun c => do
  let (t, c') ← atom c
  match [.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge].find?
      (fun p : Pred => p.text == t.text) with
  | some p => pure (p, c')
  | none => failure t.pos "expected comparison predicate"

/-! The token count bounds expression recursion. -/
def expr (eof : Pos) : Nat → Reader Expr
  | 0 => fun c => failure c.pos
  | fuel + 1 => fun c => do
    let (f, c') ← take c
    let result ← match f with
      | .atom t =>
        match (t.text.toList.splitOn '.').map String.ofList with
        | [n] => if validName n then pure (.ref t.pos n) else failure t.pos
        | [i, n] =>
          if validName i && validName n then pure (.port t.pos i n) else failure t.pos
        | _ => failure t.pos
      | _ => inside eof f do
        let tag ← atom
        let p := f.pos
        match tag.text with
        | "const" => return .const p (← number) (← number)
        | "not" => return .un p .not (← expr eof fuel)
        | "icmp" => return .icmp p (← readPred) (← expr eof fuel) (← expr eof fuel)
        | "mux" => return .mux p (← expr eof fuel) (← expr eof fuel) (← expr eof fuel)
        | "extract" => return .extract p (← expr eof fuel) (← number) (← number)
        | "replicate" => return .replicate p (← expr eof fuel) (← number)
        | "read" => return .read p (← name) (← expr eof fuel)
        | s => match readBin s with
          | some op => return .bin p op (← expr eof fuel) (← expr eof fuel)
          | none => fun _ => failure tag.pos
    pure (result, c')

/-! Type readers keep the grammar's distinction between widths and port types. -/
def bits (eof : Pos) : Reader Nat := form eof fun _ => do
  word "bits"
  number

def ty (eof : Pos) : Reader Ty := fun c =>
  if peekWord c == some "clock" then do
    let (_, c') ← word "clock" c
    pure (.clock, c')
  else do
    let (n, c') ← bits eof c
    pure (.bits n, c')

/-! Reset and statement readers retain positions from the start of each form. -/
def reset (eof : Pos) (fuel : Nat) : Reader Reset := form eof fun _ => do
  word "reset"
  word "sync"
  return ⟨.sync, ← expr eof fuel, ← expr eof fuel⟩

def optionalReset (eof : Pos) (fuel : Nat) : Reader (Option Reset) := fun c =>
  if c.forms.isEmpty then pure (none, c) else do
    let (r, c') ← reset eof fuel c
    pure (some r, c')

def stmt (eof : Pos) (fuel : Nat) : Reader Stmt := form eof fun p => do
  let tag ← atom
  match tag.text with
  | "let" => return .let_ p (← name) (← bits eof) (← expr eof fuel)
  | "reg" => return .reg p (← name) (← bits eof) (← name) (← optionalReset eof fuel)
  | "next" => return .next p (← name) (← expr eof fuel)
  | "mem" => return .mem p (← name) (← bits eof) (← number) (← name)
  | "write" =>
    return .write p (← name) (← number) (← expr eof fuel) (← expr eof fuel) (← expr eof fuel)
  | "inst" =>
    return .inst p (← name) (← name)
      (← remaining (form eof fun _ => do return (← name, ← expr eof fuel)))
  | "assign" => return .assign p (← name) (← expr eof fuel)
  | _ => fun _ => failure tag.pos

/-! Ports precede statements or dependency entries in each item. -/
def port (eof : Pos) : Reader Port := form eof fun p => do
  let tag ← atom
  let dir ← match tag.text with
    | "input" => pure PortDir.input
    | "output" => pure PortDir.output
    | _ => fun _ => failure tag.pos
  return ⟨p, dir, ← name, ← ty eof⟩

def ports (eof : Pos) : Nat → Reader (List Port)
  | 0 => pure []
  | fuel + 1 => fun c =>
    if peekHead c == some "input" || peekHead c == some "output" then do
      let (p, c) ← port eof c
      let (ps, c) ← ports eof fuel c
      pure (p :: ps, c)
    else pure ([], c)

def dep (eof : Pos) : Reader Dep := form eof fun p => do
  word "deps"
  return ⟨p, ← name, ← form eof (fun _ => remaining name)⟩

def item (eof : Pos) (fuel : Nat) : Reader Item := form eof fun p => do
  let tag ← atom
  match tag.text with
  | "module" => return .module ⟨p, ← name, ← ports eof fuel, ← remaining (stmt eof fuel)⟩
  | "extern" => return .extern ⟨p, ← name, ← ports eof fuel, ← remaining (dep eof)⟩
  | _ => fun _ => failure tag.pos

end Text

/-! Parsing uses the token count as a structural recursion bound. -/
def Text.parseRaw (s : String) : Except Error Design := do
  let (ts, eof) := Text.lex s
  let fuel := ts.length + 1
  let (fs, rest) := Text.forms fuel ts
  let fs := fs ++ rest.map (fun t => Text.Form.bad t.pos)
  let (d, c) ← Text.form eof (fun _ => do
    Text.word "design"
    return ⟨← Text.name, ← Text.remaining (Text.item eof fuel), ⟨0, 0, []⟩⟩) ⟨fs, eof, true⟩
  let _ ← Text.finish c
  pure d

/-! Limits retain the position of the field that violates them. -/
namespace Text

def Form.atPath : Form → List Nat → Pos
  | f, [] => f.pos
  | .list p fs _, i :: path =>
    match fs[i]? with
    | some f => f.atPath path
    | none => p
  | f, _ => f.pos

mutual
  def Form.findPos (p : Pos) : Form → Option Form
    | f@(.atom _) | f@(.bad _) => if f.pos == p then some f else none
    | f@(.list _ fs _) =>
      if f.pos == p then some f else Form.findPosMany p fs
  def Form.findPosMany (p : Pos) : List Form → Option Form
    | [] => none
    | f :: fs => (f.findPos p).or (Form.findPosMany p fs)
end

/-!
The position index stores paths at most two levels below each form.
A caller must use a path within this depth to obtain a field position.
-/
private def fieldPositions (depth : Nat) (f : Form) : List (List Nat × Nat × Nat) :=
  ([], f.pos.line, f.pos.col) :: match depth, f with
    | depth + 1, .list _ fs _ => fs.zipIdx.flatMap fun (child, index) =>
      (fieldPositions depth child).map fun (path, line, col) => (index :: path, line, col)
    | _, _ => []

private abbrev PositionIndex := Std.HashMap (Nat × Nat) Pos

mutual
  private def indexForm (f : Form) (index : PositionIndex) : PositionIndex :=
    let p := { f.pos with atoms := fieldPositions 2 f }
    let index := index.insert (p.line, p.col) p
    match f with
    | .list _ fs _ => indexForms fs index
    | _ => index
  private def indexForms (fs : List Form) (index : PositionIndex) : PositionIndex :=
    match fs with
    | [] => index
    | f :: fs => indexForms fs (indexForm f index)
end

private def indexedPosition (index : PositionIndex) (p : Pos) : Pos :=
  (index[(p.line, p.col)]?).getD p

def attachPositions (fs : List Form) (d : Design) : Design :=
  let index := indexForms fs {}
  let top := match fs with | f :: _ => f.atPath [1] | [] => d.topPos
  { d.mapPos (indexedPosition index) with topPos := top }

@[simp] theorem attachPositions_erase (fs : List Form) (d : Design) :
    (attachPositions fs d).erasePos = d.erasePos := by
  simpa only [attachPositions, Design.erasePos] using
    Design.mapPos_erase (indexedPosition (indexForms fs {})) d

def locateLimit (fs : List Form) (l : TextLimit) : Pos :=
  match fs.findSome? (fun f => f.findPos l.pos) with
  | some f => f.atPath l.path
  | none => l.pos

def limitFailure (p : Pos) : Error := ⟨.E001, p, "parser limit exceeded"⟩

def earlier (a b : Error) : Error :=
  if a.pos.line < b.pos.line || (a.pos.line == b.pos.line && a.pos.col ≤ b.pos.col)
  then a else b

def firstError (a b : Option Error) : Option Error :=
  match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => some (earlier a b)

/-! The source pass also finds limits before an incomplete grammar form. -/
inductive LimitContext where
  | syntax
  | expr (depth : Nat)
  | connection
  | number
  deriving DecidableEq

def childContext (ctx : LimitContext) (tag : String) (i : Nat) : LimitContext :=
  match ctx with
  | .expr depth =>
    if tag == "const" then (if i == 1 then .number else .syntax)
    else if tag == "extract" && (i == 2 || i == 3) || tag == "replicate" && i == 2
      then .number
    else if i == 0 then .syntax else .expr (depth + 1)
  | .connection => if i == 1 then .expr 0 else .syntax
  | _ =>
    if tag == "bits" && i == 1 || tag == "mem" && i == 3 || tag == "write" && i == 2
      then .number
    else if tag == "let" && i == 3 || (tag == "next" || tag == "assign") && i == 2 ||
        tag == "write" && i ≥ 3 || tag == "reset" && i ≥ 2 then .expr 0
    else if tag == "inst" && i ≥ 3 then .connection
    else .syntax

mutual
  def sourceLimit (ctx : LimitContext) : Form → Option Error
    | .atom t =>
      if ctx == .number && t.text.toList.all Char.isDigit &&
          Nat.ofDigitChars 10 t.text.toList 0 > 4294967295
      then some (limitFailure t.pos) else none
    | .bad _ => none
    | .list p fs _ =>
      let depthError := match ctx with
        | .expr depth => if depth ≥ 256 then some (limitFailure p) else none
        | _ => none
      let tag := match fs with | .atom t :: _ => t.text | _ => ""
      firstError depthError (sourceLimits ctx tag 0 fs)
  def sourceLimits (ctx : LimitContext) (tag : String) (i : Nat) : List Form → Option Error
    | [] => none
    | f :: fs => firstError (sourceLimit (childContext ctx tag i) f)
        (sourceLimits ctx tag (i + 1) fs)
end

end Text

/-! Grammar, character, and limit errors compete by their source position. -/
def parse (s : String) : Except Error Design :=
  let (ts, _) := Text.lex s
  let fs := (Text.forms (ts.length + 1) ts).1
  match Text.parseRaw s with
  | .ok d =>
    match d.textLimits.find? (fun l => !l.ok) with
    | none => .ok (Text.attachPositions fs d)
    | some l => .error (Text.limitFailure (Text.locateLimit fs l))
  | .error e =>
    let e := Text.correctTokenError ts e
    let other := Text.firstError (Text.badCharacter ts)
      (Text.sourceLimits .syntax "" 0 fs)
    .error (match other with | none => e | some other => Text.earlier e other)

/-! Printing uses a single space between fields and never reorders them. -/
namespace Text

def list (xs : List String) : String := "(" ++ String.intercalate " " xs ++ ")"

def printTy : Ty → String
  | .clock => "clock"
  | .bits n => list ["bits", toString n]

def printExpr : Expr → String
  | .ref _ n => n
  | .port _ i n => i ++ "." ++ n
  | .const _ w v => list ["const", toString w, toString v]
  | .un _ o a => list [o.text, printExpr a]
  | .bin _ o a b => list [o.text, printExpr a, printExpr b]
  | .icmp _ o a b => list ["icmp", o.text, printExpr a, printExpr b]
  | .mux _ a b c => list ["mux", printExpr a, printExpr b, printExpr c]
  | .extract _ a l w => list ["extract", printExpr a, toString l, toString w]
  | .replicate _ a n => list ["replicate", printExpr a, toString n]
  | .read _ n a => list ["read", n, printExpr a]

def printReset (r : Reset) : String :=
  list ["reset", "sync", printExpr r.signal, printExpr r.value]

def printStmt : Stmt → String
  | .let_ _ n w v => list ["let", n, printTy (.bits w), printExpr v]
  | .reg _ n w c r => list (["reg", n, printTy (.bits w), c] ++ r.toList.map printReset)
  | .next _ n v => list ["next", n, printExpr v]
  | .mem _ n w d c => list ["mem", n, printTy (.bits w), toString d, c]
  | .write _ n i a d e =>
    list ["write", n, toString i, printExpr a, printExpr d, printExpr e]
  | .inst _ n m xs => list (["inst", n, m] ++ xs.map fun (k, v) => list [k, printExpr v])
  | .assign _ n v => list ["assign", n, printExpr v]

def printPort (p : Port) : String :=
  list [match p.dir with | .input => "input" | .output => "output", p.name, printTy p.ty]

def printDep (d : Dep) : String := list ["deps", d.output, list d.inputs]

def block (header : List String) (entries : List String) (indent : String) : String :=
  "(" ++ String.intercalate " " header ++
    String.join (entries.map (fun entry => "\n" ++ indent ++ entry)) ++ ")"

def printItem : Item → String
  | .module m => block ["module", m.name] (m.ports.map printPort ++ m.body.map printStmt) "    "
  | .extern e => block ["extern", e.name] (e.ports.map printPort ++ e.deps.map printDep) "    "

end Text

def print (d : Design) : String :=
  Text.block ["design", d.top] (d.items.map Text.printItem) "  " ++ "\n"

/-! Canonical order sorts items by name and statements by kind, name, then write port. -/
def Stmt.sortKey : Stmt → Nat × String × Nat
  | .reg _ n .. => (0, n, 0)
  | .mem _ n .. => (1, n, 0)
  | .inst _ n .. => (2, n, 0)
  | .let_ _ n .. => (3, n, 0)
  | .next _ n .. => (4, n, 0)
  | .write _ n p .. => (5, n, p)
  | .assign _ n .. => (6, n, 0)

def Item.name : Item → String
  | .module m => m.name
  | .extern e => e.name

def Stmt.before (a b : Stmt) : Bool :=
  let (ka, na, pa) := a.sortKey
  let (kb, nb, pb) := b.sortKey
  ka < kb || (ka == kb && (na < nb || (na == nb && pa ≤ pb)))

def Item.ports : Item → List Port
  | .module m => m.ports
  | .extern e => e.ports

private def portIndex (ports : List Port) (name : String) : Nat :=
  ports.findIdx (·.name == name)

def canonicalStmt (items : List Item) : Stmt → Stmt
  | .inst p n child connections =>
    match items.find? (·.name == child) with
    | none => .inst p n child connections
    | some item => .inst p n child (connections.mergeSort fun a b =>
        portIndex item.ports a.1 ≤ portIndex item.ports b.1)
  | stmt => stmt

def canonicalize (d : Design) : Design :=
  let items := d.items.map fun
    | .module m => .module { m with
        body := (m.body.map (canonicalStmt d.items)).mergeSort Stmt.before }
    | .extern e => .extern { e with deps := e.deps.mergeSort (fun a b =>
        portIndex e.ports a.output ≤ portIndex e.ports b.output) }
  { d with items := items.mergeSort (fun a b => a.name ≤ b.name) }

/-! Canonical order preserves the top module and each ordered port interface. -/
@[simp] theorem canonicalize_top (d : Design) : (canonicalize d).top = d.top := rfl

theorem canonicalize_interfaces (d : Design) :
    ((canonicalize d).items.map fun i => (i.name, i.ports)).Perm
      (d.items.map fun i => (i.name, i.ports)) := by
  unfold canonicalize
  dsimp only
  refine (List.Perm.map _ (List.mergeSort_perm _ _)).trans ?_
  simp only [List.map_map]
  apply List.Perm.of_eq
  apply List.map_congr_left
  intro i _
  cases i <;> rfl

namespace Text

/-! The scanner preserves each legal atom and each token boundary. -/
theorem lexLoop_word_append (chars rest : List Char) (p start : Pos)
    (word : List Char) (tokens : List Token) (hne : word ≠ [])
    (hchars : ∀ c ∈ chars, delimiter c = false) :
    lexLoop (chars ++ rest) p start word false tokens =
      lexLoop rest (chars.foldl advance p) start (chars.reverse ++ word) false tokens := by
  induction chars generalizing p word with
  | nil => simp
  | cons c cs ih =>
    have hc := hchars c (by simp)
    have hcs : ∀ d ∈ cs, delimiter d = false := fun d hd => hchars d (by simp [hd])
    simp only [List.cons_append, lexLoop, Bool.false_eq_true, ↓reduceIte, hc]
    have he : word.isEmpty = false := by cases word <;> simp_all
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    rw [ih _ _ (by simp) hcs]
    simp [List.reverse_cons, List.append_assoc]

theorem lexLoop_word (c : Char) (cs rest : List Char) (p start : Pos)
    (tokens : List Token) (hc : delimiter c = false)
    (hcs : ∀ d ∈ cs, delimiter d = false) :
    lexLoop ((c :: cs) ++ rest) p start [] false tokens =
      lexLoop rest ((c :: cs).foldl advance p) p (c :: cs).reverse false tokens := by
  simp only [List.cons_append, lexLoop, Bool.false_eq_true, ↓reduceIte, hc]
  simp only [List.isEmpty_nil, ↓reduceIte]
  rw [lexLoop_word_append cs rest (advance p c) p [c] tokens (by simp) hcs]
  simp

theorem lexLoop_space (rest : List Char) (p start : Pos)
    (word : List Char) (tokens : List Token) :
    lexLoop (' ' :: rest) p start word false tokens =
      lexLoop rest (advance p ' ') (advance p ' ') [] false (flush start word tokens) := by
  simp [lexLoop, delimiter]

theorem lexLoop_lparen (rest : List Char) (p start : Pos)
    (word : List Char) (tokens : List Token) :
    lexLoop ('(' :: rest) p start word false tokens =
      lexLoop rest (advance p '(') (advance p '(') [] false
        (⟨p, "("⟩ :: flush start word tokens) := by
  simp [lexLoop, delimiter]

theorem lexLoop_rparen (rest : List Char) (p start : Pos)
    (word : List Char) (tokens : List Token) :
    lexLoop (')' :: rest) p start word false tokens =
      lexLoop rest (advance p ')') (advance p ')') [] false
        (⟨p, ")"⟩ :: flush start word tokens) := by
  simp [lexLoop, delimiter]

/-! Legal name characters cannot end an atom or start a comment. -/
theorem nameRest_delimiter (c : Char) (h : nameRest c = true) : delimiter c = false := by
  cases hd : delimiter c with
  | false => rfl
  | true =>
    simp only [delimiter, Bool.or_eq_true,
      beq_iff_eq] at hd
    rcases hd with ((((((hc | hc) | hc) | hc) | hc) | hc) | hc) <;>
      subst c <;> contradiction

theorem validName_nonempty (s : String) (h : validName s = true) : s.toList ≠ [] := by
  intro he
  simp [validName, he] at h

theorem validName_delimiter (s : String) (h : validName s = true) :
    ∀ c ∈ s.toList, delimiter c = false := by
  unfold validName at h
  cases hs : s.toList with
  | nil => simp [hs] at h
  | cons d ds =>
    simp only [hs, Bool.and_eq_true] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · apply nameRest_delimiter
      simp [nameRest, h.1.1]
    · exact nameRest_delimiter c (List.all_eq_true.mp h.1.2 c hc)

/-! Token accumulation does not change the text or order of an atom. -/
theorem flush_reverse (chars : List Char) (p : Pos) (tokens : List Token)
    (h : chars ≠ []) :
    flush p chars.reverse tokens = ⟨p, String.ofList chars⟩ :: tokens := by
  have he : chars.reverse.isEmpty = false := by cases chars <;> simp_all
  simp [flush, he]

theorem lexLoop_atom_space (s : String) (rest : List Char) (p start : Pos)
    (tokens : List Token) (hne : s.toList ≠ [])
    (hchars : ∀ c ∈ s.toList, delimiter c = false) :
    lexLoop (s.toList ++ ' ' :: rest) p start [] false tokens =
      lexLoop rest (advance (s.toList.foldl advance p) ' ')
        (advance (s.toList.foldl advance p) ' ') [] false (⟨p, s⟩ :: tokens) := by
  cases hs : s.toList with
  | nil => exact False.elim (hne hs)
  | cons c cs =>
    have hc : delimiter c = false := hchars c (by simp [hs])
    have hcs : ∀ d ∈ cs, delimiter d = false := fun d hd => hchars d (by simp [hs, hd])
    rw [lexLoop_word c cs _ p start tokens hc hcs, lexLoop_space, flush_reverse]
    · simp [← hs]
    · simp

theorem flush_append (p : Pos) (word : List Char) (tokens extra : List Token) :
    flush p word (tokens ++ extra) = flush p word tokens ++ extra := by
  simp only [flush]
  split <;> simp

theorem lexLoop_tokens_append (chars : List Char) (p start : Pos)
    (word : List Char) (comment : Bool) (tokens extra : List Token) :
    lexLoop chars p start word comment (tokens ++ extra) =
      let result := lexLoop chars p start word comment tokens
      (extra.reverse ++ result.1, result.2) := by
  induction chars generalizing p start word comment tokens with
  | nil => simp [lexLoop, flush_append]
  | cons c cs ih =>
    simp only [lexLoop]
    split
    · apply ih
    · split
      · rw [flush_append]
        split
        · simpa only [List.cons_append] using
            ih (advance p c) (advance p c) [] (c == ';')
              (⟨p, String.singleton c⟩ :: flush start word tokens)
        · exact ih _ _ _ _ _
      · exact ih _ _ _ _ _

theorem lexLoop_atom_boundary (s : String) (c : Char) (rest : List Char)
    (p start : Pos) (tokens : List Token) (hne : s.toList ≠ [])
    (hchars : ∀ d ∈ s.toList, delimiter d = false) (hc : delimiter c = true) :
    lexLoop (s.toList ++ c :: rest) p start [] false tokens =
      let stop := s.toList.foldl advance p
      let tokens := ⟨p, s⟩ :: tokens
      let tokens := if c == '(' || c == ')' then ⟨stop, String.singleton c⟩ :: tokens
        else tokens
      lexLoop rest (advance stop c) (advance stop c) [] (c == ';') tokens := by
  cases hs : s.toList with
  | nil => exact False.elim (hne hs)
  | cons d ds =>
    have hd : delimiter d = false := hchars d (by simp [hs])
    have hds : ∀ e ∈ ds, delimiter e = false := fun e he => hchars e (by simp [hs, he])
    rw [lexLoop_word d ds _ p start tokens hd hds]
    simp only [lexLoop, Bool.false_eq_true, ↓reduceIte, hc]
    rw [flush_reverse _ _ _ (by simp)]
    simp [← hs]

/-! Text trees connect character scanning to structured grammar forms. -/
inductive Tree where
  | atom (text : String)
  | list (children : List Tree)
  deriving Repr

def Tree.separator (depth : Nat) (first : Bool) : List Char :=
  if first then [' '] else
    match depth with
    | 0 => [' ']
    | 1 => ['\n', ' ', ' ', ' ', ' ']
    | _ => ['\n', ' ', ' ']

mutual
  def Tree.chars : Tree → Nat → List Char
    | .atom s, _ => s.toList
    | .list xs, depth => '(' :: Tree.forestChars xs depth true ++ [')']
  def Tree.forestChars : List Tree → Nat → Bool → List Char
    | [], _, _ => []
    | [x], depth, _ => x.chars (depth - 1)
    | x :: y :: xs, depth, first =>
      x.chars (depth - 1) ++ Tree.separator depth first ++
        Tree.forestChars (y :: xs) depth false
end

def Tree.render (t : Tree) (depth : Nat := 0) : String := String.ofList (t.chars depth)

def Tree.after (t : Tree) (p : Pos) (depth : Nat := 0) : Pos :=
  (t.chars depth).foldl advance p

/-! Placement assigns the positions that scanning the rendered tree will produce. -/
mutual
  def Tree.place (t : Tree) (p : Pos) (depth : Nat := 0) : Form :=
    match t with
    | .atom s => .atom ⟨p, s⟩
    | .list xs =>
      let inner := advance p '('
      .list p (Tree.placeMany xs inner depth true)
        (some ((Tree.forestChars xs depth true).foldl advance inner))
  def Tree.placeMany : List Tree → Pos → Nat → Bool → List Form
    | [], _, _, _ => []
    | x :: xs, p, depth, first =>
      x.place p (depth - 1) :: Tree.placeMany xs
        ((Tree.separator depth first).foldl advance (x.after p (depth - 1))) depth false
end

/-! A legal tree has nonempty atoms without token delimiters. -/
mutual
  def Tree.Legal : Tree → Prop
    | .atom s => s.toList ≠ [] ∧ ∀ c ∈ s.toList, delimiter c = false
    | .list xs => Tree.LegalMany xs
  def Tree.LegalMany : List Tree → Prop
    | [] => True
    | x :: xs => x.Legal ∧ Tree.LegalMany xs
end

/-! Tree weight counts tokens and bounds every recursive grammar call. -/
mutual
  def Tree.weight : Tree → Nat
    | .atom _ => 1
    | .list xs => 2 + Tree.weightMany xs
  def Tree.weightMany : List Tree → Nat
    | [] => 0
    | x :: xs => x.weight + Tree.weightMany xs
end
/-! Matching ignores positions but requires every list to have a closing token. -/
mutual
inductive Tree.Matches : Tree → Form → Prop where
  | atom (p : Pos) : Matches (.atom s) (.atom ⟨p, s⟩)
  | list (p close : Pos) (h : Tree.MatchesMany xs fs) :
      Matches (.list xs) (.list p fs (some close))
inductive Tree.MatchesMany : List Tree → List Form → Prop where
  | nil : MatchesMany [] []
  | cons (h : Tree.Matches t f) (hs : MatchesMany ts fs) : MatchesMany (t :: ts) (f :: fs)
end

theorem Tree.place_matches (t : Tree) (p : Pos) (depth : Nat := 0) :
    t.Matches (t.place p depth) := by
  induction t using Tree.rec (motive_2 := fun xs =>
      ∀ p depth first, Tree.MatchesMany xs (Tree.placeMany xs p depth first))
      generalizing p depth with
  | atom s => exact .atom p
  | list xs ih => exact .list _ _ (ih _ _ _)
  | nil => exact .nil
  | cons x xs ih ihs => exact .cons (ih _ _) (ihs _ _ _)

/-! Flattening a positioned form recovers its token sequence. -/
mutual
  def Form.tokens : Form → List Token
    | .atom t => [t]
    | .list p xs close => ⟨p, "("⟩ :: Form.tokensMany xs ++
        close.toList.map (fun q => ⟨q, ")"⟩)
    | .bad _ => []
  def Form.tokensMany : List Form → List Token
    | [] => []
    | f :: fs => f.tokens ++ Form.tokensMany fs
end

theorem lexLoop_whitespace (chars rest : List Char) (p : Pos) (tokens : List Token)
    (h : ∀ c ∈ chars, c = ' ' ∨ c = '\n') :
    lexLoop (chars ++ rest) p p [] false tokens =
      lexLoop rest (chars.foldl advance p) (chars.foldl advance p) [] false tokens := by
  induction chars generalizing p with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht : ∀ d ∈ cs, d = ' ' ∨ d = '\n' := fun d hd => h d (by simp [hd])
    rcases hc with rfl | rfl <;>
      simpa [lexLoop, delimiter, flush] using ih (advance p _) ht

theorem Tree.separator_chars (depth : Nat) (first : Bool) :
    ∀ c ∈ Tree.separator depth first, c = ' ' ∨ c = '\n' := by
  cases first <;> cases depth with
  | zero => simp [Tree.separator]
  | succ n => cases n <;> simp [Tree.separator]

theorem Tree.separator_ne (depth : Nat) (first : Bool) :
    Tree.separator depth first ≠ [] := by
  cases first <;> cases depth with
  | zero => simp [Tree.separator]
  | succ n => cases n <;> simp [Tree.separator]

/-! Scanning a legal tree produces exactly its positioned tokens. -/
theorem Tree.lex_chars (t : Tree) (legal : t.Legal) (p : Pos)
    (c : Char) (rest : List Char) (tokens : List Token) (hc : delimiter c = true)
    (depth : Nat := 0) :
    lexLoop (t.chars depth ++ c :: rest) p p [] false tokens =
      lexLoop (c :: rest) (t.after p depth) (t.after p depth) [] false
        ((t.place p depth).tokens.reverse ++ tokens) := by
  induction t using Tree.rec (motive_2 := fun xs =>
      ∀ (legal : Tree.LegalMany xs) (p : Pos) (c : Char) (rest : List Char)
        (tokens : List Token), delimiter c = true → ∀ depth first,
        lexLoop (Tree.forestChars xs depth first ++ c :: rest) p p [] false tokens =
          lexLoop (c :: rest) ((Tree.forestChars xs depth first).foldl advance p)
            ((Tree.forestChars xs depth first).foldl advance p) [] false
            ((Form.tokensMany (Tree.placeMany xs p depth first)).reverse ++ tokens))
      generalizing p c rest tokens depth with
  | atom s =>
    rw [Tree.chars, lexLoop_atom_boundary s c rest p p tokens legal.1 legal.2 hc]
    simp [Tree.place, Form.tokens, Tree.after, Tree.chars, lexLoop, hc, flush]
  | list xs ih =>
    simp only [Tree.chars, List.cons_append, List.append_assoc]
    rw [lexLoop_lparen]
    simp only [flush, List.isEmpty_nil, ↓reduceIte, List.nil_append]
    rw [ih legal (advance p '(') ')' (c :: rest) (⟨p, "("⟩ :: tokens) (by decide)]
    rw [lexLoop_rparen]
    simp [Tree.place, Form.tokens, Tree.after, Tree.chars, List.foldl_append,
      List.reverse_append, flush, List.append_assoc]
  | nil => rfl
  | cons x xs ih ihs =>
    rename_i legal p c rest tokens hc depth first
    cases xs with
    | nil =>
      simpa [Tree.forestChars, Tree.placeMany, Form.tokensMany, Tree.after] using
        ih legal.1 p c rest tokens hc (depth - 1)
    | cons y ys =>
      have hg := Tree.separator_chars depth first
      have hn := Tree.separator_ne depth first
      cases he : Tree.separator depth first with
      | nil => exact False.elim (hn he)
      | cons gap gaps =>
        have hgap : delimiter gap = true := by
          have h := hg gap (by simp [he])
          rcases h with rfl | rfl <;> decide
        simp only [Tree.forestChars, he, List.append_assoc, List.cons_append]
        rw [ih legal.1 p gap (gaps ++ (Tree.forestChars (y :: ys) depth false ++ c :: rest))
          tokens hgap (depth - 1)]
        rw [show gap :: (gaps ++ (Tree.forestChars (y :: ys) depth false ++ c :: rest)) =
          (gap :: gaps) ++ (Tree.forestChars (y :: ys) depth false ++ c :: rest) by simp]
        rw [lexLoop_whitespace _ _ _ _ (by simpa [he] using hg)]
        rw [ihs legal.2 _ c rest ((x.place p (depth - 1)).tokens.reverse ++ tokens)
          hc depth false]
        simp [Tree.placeMany, Form.tokensMany, List.foldl_append, Tree.after,
          List.reverse_append, List.append_assoc, he]

theorem lexLoop_append_space_fst (chars : List Char) (p start : Pos)
    (word : List Char) (comment : Bool) (tokens : List Token) :
    (lexLoop (chars ++ [' ']) p start word comment tokens).1 =
      (lexLoop chars p start word comment tokens).1 := by
  induction chars generalizing p start word comment tokens with
  | nil => cases comment <;> simp [lexLoop, delimiter, flush]
  | cons c cs ih =>
    simp only [List.cons_append, lexLoop]
    split
    · apply ih
    · split
      · apply ih
      · apply ih

theorem lexLoop_append_lf_fst (chars : List Char) (p start : Pos)
    (word : List Char) (comment : Bool) (tokens : List Token) :
    (lexLoop (chars ++ ['\n']) p start word comment tokens).1 =
      (lexLoop chars p start word comment tokens).1 := by
  induction chars generalizing p start word comment tokens with
  | nil => cases comment <;> simp [lexLoop, delimiter, flush]
  | cons c cs ih =>
    simp only [List.cons_append, lexLoop]
    split
    · apply ih
    · split
      · apply ih
      · apply ih

theorem lex_append_lf (s : String) : (lex (s ++ "\n")).1 = (lex s).1 := by
  simp only [lex, String.toList_append]
  exact lexLoop_append_lf_fst _ _ _ _ _ _

theorem Tree.lex_render (t : Tree) (legal : t.Legal) (depth : Nat := 0) :
    (lex (t.render depth)).1 = (t.place ⟨1, 1, []⟩ depth).tokens := by
  change (lexLoop (String.ofList (t.chars depth)).toList ⟨1, 1, []⟩ ⟨1, 1, []⟩ [] false []).1 = _
  simp only [String.toList_ofList]
  rw [← lexLoop_append_space_fst]
  rw [t.lex_chars legal ⟨1, 1, []⟩ ' ' [] [] (by decide) depth]
  simp [lexLoop, delimiter, flush]

theorem legal_atom_ne (s : String) (h : (Tree.atom s).Legal) : s ≠ "(" ∧ s ≠ ")" := by
  constructor
  · intro he
    subst s
    have hh := h.2 '(' (by decide)
    contradiction
  · intro he
    subst s
    have hh := h.2 ')' (by decide)
    contradiction

/-! The form reader reconstructs each legal tree within its token bound. -/
theorem Tree.forms_tokens (t : Tree) (legal : t.Legal) (p : Pos)
    (n : Nat) (hn : t.weight ≤ n) (rest : List Token) (depth : Nat := 0) :
    forms (n + 1) ((t.place p depth).tokens ++ rest) =
      let after := forms n rest
      (t.place p depth :: after.1, after.2) := by
  induction t using Tree.rec (motive_2 := fun xs =>
      ∀ (legal : Tree.LegalMany xs) (p : Pos) (n : Nat), Tree.weightMany xs ≤ n →
        ∀ (close : Pos) (rest : List Token) (depth : Nat) (first : Bool),
        forms (n + 1) (Form.tokensMany (Tree.placeMany xs p depth first) ++ ⟨close, ")"⟩ :: rest) =
          (Tree.placeMany xs p depth first, ⟨close, ")"⟩ :: rest)) generalizing p n rest depth with
  | atom s =>
    have hs := legal_atom_ne s legal
    simp [Tree.place, Form.tokens, forms, hs]
  | list xs ih =>
    cases n with
    | zero => simp [Tree.weight] at hn
    | succ n =>
      have hb : Tree.weightMany xs ≤ n := by simp only [Tree.weight] at hn; omega
      simp only [Tree.place, Form.tokens, Option.toList_some, List.map_cons, List.map_nil,
        List.cons_append, List.append_assoc, List.nil_append]
      rw [forms]
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [ih legal (advance p '(') n hb]
      rfl
  | nil => simp [Tree.placeMany, Form.tokensMany, forms]
  | cons x xs ih ihs =>
    rename_i legal p n hn close rest depth first
    cases n with
    | zero =>
      have hx : 0 < x.weight := by cases x <;> simp [Tree.weight] <;> omega
      simp only [Tree.weightMany] at hn
      omega
    | succ n =>
      have hx : x.weight ≤ n + 1 := by simp only [Tree.weightMany] at hn; omega
      have hxs : Tree.weightMany xs ≤ n := by
        have hw : 0 < x.weight := by cases x <;> simp [Tree.weight] <;> omega
        simp only [Tree.weightMany] at hn
        omega
      simp only [Tree.placeMany, Form.tokensMany, List.append_assoc]
      rw [ih legal.1 p (n + 1) hx _ (depth - 1)]
      rw [ihs legal.2 _ n hxs]

theorem Tree.tokens_length (t : Tree) (p : Pos) (depth : Nat := 0) :
    (t.place p depth).tokens.length = t.weight := by
  induction t using Tree.rec (motive_2 := fun xs => ∀ p depth first,
      (Form.tokensMany (Tree.placeMany xs p depth first)).length = Tree.weightMany xs)
      generalizing p depth with
  | atom s => rfl
  | list xs ih => simp [Tree.place, Form.tokens, Tree.weight, ih, Nat.add_comm]; omega
  | nil => rfl
  | cons x xs ih ihs => simp [Tree.placeMany, Form.tokensMany, Tree.weightMany, ih, ihs]

theorem Tree.forms_lex_render (t : Tree) (legal : t.Legal) (n : Nat)
    (hn : t.weight ≤ n) (depth : Nat := 0) :
    ∃ f, t.Matches f ∧ forms (n + 1) (lex (t.render depth)).1 = ([f], []) := by
  refine ⟨t.place ⟨1, 1, []⟩ depth, t.place_matches _ depth, ?_⟩
  rw [t.lex_render legal depth]
  have h := t.forms_tokens legal ⟨1, 1, []⟩ n hn [] depth
  have hn0 : 0 < n := by
    have hw : 0 < t.weight := by cases t <;> simp [Tree.weight] <;> omega
    omega
  cases n with
  | zero => omega
  | succ n => simpa [forms] using h

theorem Tree.forms_lex_render_length (t : Tree) (legal : t.Legal) (depth : Nat := 0) :
    ∃ f, t.Matches f ∧
      forms ((lex (t.render depth)).1.length + 1) (lex (t.render depth)).1 = ([f], []) := by
  apply t.forms_lex_render legal _ _ depth
  rw [t.lex_render legal depth, t.tokens_length _ depth]
  exact Nat.le_refl _

@[simp] theorem Tree.render_atom (s : String) (depth : Nat := 0) :
    (Tree.atom s).render depth = s := by
  simp [Tree.render, Tree.chars]

/-! Tree rendering uses the same spacing as the public printer. -/
theorem Tree.forestChars_render (xs : List Tree) :
    ∀ first, String.ofList (Tree.forestChars xs 0 first) =
      String.intercalate " " (xs.map Tree.render) := by
  induction xs with
  | nil => simp [Tree.forestChars]
  | cons x xs ih =>
    intro first
    cases xs with
    | nil => simp [Tree.forestChars, Tree.render]
    | cons y ys =>
      have hsep : Tree.separator 0 first = [' '] := by cases first <;> rfl
      simp [Tree.forestChars, hsep, String.ofList_append, ih,
        String.intercalate_cons_cons, Tree.render, String.append_assoc]

@[simp] theorem Tree.render_list (xs : List Tree) :
    (Tree.list xs).render = Text.list (xs.map Tree.render) := by
  unfold Tree.render
  rw [Tree.chars]
  change String.ofList (['('] ++ (Tree.forestChars xs 0 true ++ [')'])) = _
  rw [String.ofList_append, String.ofList_append, Tree.forestChars_render]
  simp only [Text.list, String.append_assoc]; rfl

theorem Tree.forestChars_prefixed (x : Tree) (xs : List Tree) (depth : Nat) :
    String.ofList (Tree.forestChars (x :: xs) depth false) =
      x.render (depth - 1) ++ String.join (xs.map fun t =>
        String.ofList (Tree.separator depth false) ++ t.render (depth - 1)) := by
  induction xs generalizing x with
  | nil => simp [Tree.forestChars, Tree.render]
  | cons y ys ih =>
    simp [Tree.forestChars, String.ofList_append, ih, Tree.render, String.append_assoc]

theorem Tree.render_block (a b : String) (xs : List Tree) (depth : Nat)
    (hdepth : depth > 0 := by omega) :
    (Tree.list (.atom a :: .atom b :: xs)).render depth =
      Text.block [a, b] (xs.map fun t => t.render (depth - 1))
        (if depth = 1 then "    " else "  ") := by
  cases depth with
  | zero => omega
  | succ depth =>
    simp only [Tree.render, Tree.chars, Tree.forestChars, Tree.separator,
      List.cons_append, String.ofList_cons, String.ofList_append]
    rw [Tree.forestChars_prefixed]
    simp [Tree.render, Tree.chars, Text.block, String.append_assoc]
    cases depth <;> simp only [Tree.separator, Bool.false_eq_true, ↓reduceIte,
      Nat.succ_ne_zero, Function.comp_def, ← String.append_assoc] <;> rfl

/-! The encoder gives each syntax node its grammar tree. -/
def encodeTy : Ty → Tree
  | .clock => .atom "clock"
  | .bits n => .list [.atom "bits", .atom (toString n)]

def encodeExpr : Expr → Tree
  | .ref _ n => .atom n
  | .port _ i n => .atom (i ++ "." ++ n)
  | .const _ w v => .list [.atom "const", .atom (toString w), .atom (toString v)]
  | .un _ o a => .list [.atom o.text, encodeExpr a]
  | .bin _ o a b => .list [.atom o.text, encodeExpr a, encodeExpr b]
  | .icmp _ o a b => .list [.atom "icmp", .atom o.text, encodeExpr a, encodeExpr b]
  | .mux _ a b c => .list [.atom "mux", encodeExpr a, encodeExpr b, encodeExpr c]
  | .extract _ a l w => .list [.atom "extract", encodeExpr a, .atom (toString l),
      .atom (toString w)]
  | .replicate _ a n => .list [.atom "replicate", encodeExpr a, .atom (toString n)]
  | .read _ n a => .list [.atom "read", .atom n, encodeExpr a]

def encodeReset (r : Reset) : Tree :=
  .list [.atom "reset", .atom "sync", encodeExpr r.signal, encodeExpr r.value]

def encodeStmt : Stmt → Tree
  | .let_ _ n w v => .list [.atom "let", .atom n, encodeTy (.bits w), encodeExpr v]
  | .reg _ n w c r =>
    .list ([.atom "reg", .atom n, encodeTy (.bits w), .atom c] ++ r.toList.map encodeReset)
  | .next _ n v => .list [.atom "next", .atom n, encodeExpr v]
  | .mem _ n w d c =>
    .list [.atom "mem", .atom n, encodeTy (.bits w), .atom (toString d), .atom c]
  | .write _ n i a d e => .list [.atom "write", .atom n, .atom (toString i),
      encodeExpr a, encodeExpr d, encodeExpr e]
  | .inst _ n m xs =>
    .list ([.atom "inst", .atom n, .atom m] ++ xs.map fun (k, v) =>
      .list [.atom k, encodeExpr v])
  | .assign _ n v => .list [.atom "assign", .atom n, encodeExpr v]

def encodePort (p : Port) : Tree :=
  .list [.atom (match p.dir with | .input => "input" | .output => "output"),
    .atom p.name, encodeTy p.ty]

def encodeDep (d : Dep) : Tree := .list [.atom "deps", .atom d.output,
  .list (d.inputs.map Tree.atom)]

def encodeItem : Item → Tree
  | .module m =>
    .list ([.atom "module", .atom m.name] ++ m.ports.map encodePort ++ m.body.map encodeStmt)
  | .extern e =>
    .list ([.atom "extern", .atom e.name] ++ e.ports.map encodePort ++ e.deps.map encodeDep)

def encode (d : Design) : Tree := .list ([.atom "design", .atom d.top] ++ d.items.map encodeItem)

/-! A dot separates two names and cannot occur within either name. -/
theorem validName_no_dot (s : String) (h : validName s = true) : '.' ∉ s.toList := by
  unfold validName at h
  cases hs : s.toList with
  | nil => simp
  | cons c cs =>
    simp only [hs, Bool.and_eq_true] at h
    simp only [List.mem_cons, not_or]
    constructor
    · intro hc
      subst c
      have : nameStart '.' = false := rfl
      simp [this] at h
    · intro hc
      have := List.all_eq_true.mp h.1.2 '.' hc
      contradiction

theorem split_name (s : String) (h : validName s = true) :
    (s.toList.splitOn '.').map String.ofList = [s] := by
  simp [List.splitOn_eq_singleton (validName_no_dot s h)]

theorem split_port (i n : String) (hi : validName i = true) (hn : validName n = true) :
    ((i ++ "." ++ n).toList.splitOn '.').map String.ofList = [i, n] := by
  simp only [String.toList_append, List.append_assoc]
  change ((i.toList ++ '.' :: n.toList).splitOn '.').map String.ofList = [i, n]
  rw [List.splitOn_append_cons_self_of_not_mem (validName_no_dot i hi)]
  simp [List.splitOn_eq_singleton (validName_no_dot n hn)]

/-! Decimal reading recovers arbitrary natural numbers without a machine-width limit. -/
@[simp] theorem number_print (n : Nat) (p stop : Pos) (fs : List Form) (closed : Bool) :
    number ⟨.atom ⟨p, n.repr⟩ :: fs, stop, closed⟩ =
      .ok (n, ⟨fs, stop, closed⟩) := by
  have hn : (Nat.toDigits 10 n).isEmpty = false := by
    cases h : Nat.toDigits 10 n with
    | nil => exact False.elim (Nat.toDigits_ne_nil h)
    | cons _ _ => rfl
  have hd : (Nat.toDigits 10 n).all Char.isDigit = true := by
    apply List.all_eq_true.mpr
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp [number, atom, take, Bind.bind, Except.bind, Nat.repr_eq_ofList_toDigits, hn, hd,
    Nat.ofDigitChars_ten_toDigits]

@[simp] theorem name_read (n : String) (h : validName n = true)
    (p stop : Pos) (fs : List Form) (closed : Bool) :
    name ⟨.atom ⟨p, n⟩ :: fs, stop, closed⟩ = .ok (n, ⟨fs, stop, closed⟩) := by
  simp [name, atom, take, Bind.bind, Except.bind, h]

/-! Expression leaves recover names, instance ports, and constants. -/
theorem expr_ref_read (n : String) (hn : validName n = true)
    (fuel : Nat) (p eof : Pos) (c : Cursor) :
    expr eof (fuel + 1) { c with forms := .atom ⟨p, n⟩ :: c.forms } =
      .ok (.ref p n, c) := by
  cases c
  simp [expr, take, Bind.bind, Except.bind, Pure.pure, Except.pure, split_name n hn, hn]

theorem expr_port_read (i n : String) (hi : validName i = true) (hn : validName n = true)
    (fuel : Nat) (p eof : Pos) (c : Cursor) :
    expr eof (fuel + 1) { c with forms := .atom ⟨p, i ++ "." ++ n⟩ :: c.forms } =
      .ok (.port p i n, c) := by
  cases c
  simp only [expr, take, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [split_port i n hi hn]
  simp [hi, hn]

theorem expr_const_read (w v : Nat) (fuel : Nat) (p close a b k eof : Pos) (c : Cursor) :
    expr eof (fuel + 1)
      { c with forms := (Form.list p [.atom ⟨k, "const"⟩,
          .atom ⟨a, toString w⟩, .atom ⟨b, toString v⟩] (some close)) :: c.forms } =
      .ok (.const p w v, c) := by
  cases c
  simp [expr, take, inside, atom, finish, Form.pos, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-! Expression reading preserves every field except source positions. -/
macro "unpack_matches" : tactic => `(tactic|
  repeat first
    | cases ‹Tree.Matches (.atom _) _›
    | cases ‹Tree.MatchesMany [] _›
    | cases ‹Tree.MatchesMany (_ :: _) _›)

theorem expr_roundtrip (e : Expr) (fuel : Nat) (f : Form)
    (hn : ∀ n ∈ e.names, validName n = true)
    (hb : (encodeExpr e).weight < fuel) (hm : (encodeExpr e).Matches f)
    (eof : Pos) (c : Cursor) :
    ∃ a, expr eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = e.erasePos := by
  induction e generalizing fuel f c with
  | ref p n =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | atom q =>
        exact ⟨.ref q n, expr_ref_read n (hn n (by simp [Expr.names])) k q eof c, rfl⟩
  | port p i n =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | atom q =>
        exact ⟨.port q i n, expr_port_read i n (hn i (by simp [Expr.names]))
          (hn n (by simp [Expr.names])) k q eof c, rfl⟩
  | const p w v =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        exact ⟨.const q w v, expr_const_read w v k _ _ _ _ _ _ _, rfl⟩
  | un p o a ih =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i opPos fa hfa
        have hba : (encodeExpr a).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        obtain ⟨a', ha, hea⟩ := ih k fa hn hba hfa ⟨[], close, true⟩
        refine ⟨.un q o a', ?_, ?_⟩
        · cases o
          cases c
          rw [expr]
          simp [take, inside, atom, finish, Form.pos, Bind.bind, Except.bind,
            Pure.pure, Except.pure, UnOp.text, ha]
        · simp [Expr.erasePos, hea]
  | bin p o a b iha ihb =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i opPos fa hfa fb hfb
        have hba : (encodeExpr a).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        have hbb : (encodeExpr b).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        obtain ⟨a', ha, hea⟩ := iha k fa
          (fun n h => hn n (by simp [Expr.names, h])) hba hfa ⟨[fb], close, true⟩
        obtain ⟨b', hb', heb⟩ := ihb k fb
          (fun n h => hn n (by simp [Expr.names, h])) hbb hfb ⟨[], close, true⟩
        refine ⟨.bin q o a' b', ?_, ?_⟩
        · cases o <;> cases c <;> rw [expr] <;>
            simp [take, inside, atom, finish, Form.pos, Bind.bind, Except.bind,
              Pure.pure, Except.pure, BinOp.text, readBin, ha, hb']
        · simp [Expr.erasePos, hea, heb]
  | icmp p o a b iha ihb =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i tagPos opPos fa hfa fb hfb
        have hba : (encodeExpr a).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        have hbb : (encodeExpr b).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        obtain ⟨a', ha, hea⟩ := iha k fa
          (fun n h => hn n (by simp [Expr.names, h])) hba hfa ⟨[fb], close, true⟩
        obtain ⟨b', hb', heb⟩ := ihb k fb
          (fun n h => hn n (by simp [Expr.names, h])) hbb hfb ⟨[], close, true⟩
        refine ⟨.icmp q o a' b', ?_, ?_⟩
        · cases o <;> cases c <;> rw [expr] <;>
            simp [take, inside, atom, finish, Form.pos, Bind.bind, Except.bind,
              Pure.pure, Except.pure, Pred.text, readPred, ha, hb']
        · simp [Expr.erasePos, hea, heb]
  | mux p a b d iha ihb ihd =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i tagPos fa hfa fb hfb fd hfd
        have hba : (encodeExpr a).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        have hbb : (encodeExpr b).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        have hbd : (encodeExpr d).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        obtain ⟨a', ha, hea⟩ := iha k fa
          (fun n h => hn n (by simp [Expr.names, h])) hba hfa ⟨[fb, fd], close, true⟩
        obtain ⟨b', hb', heb⟩ := ihb k fb
          (fun n h => hn n (by simp [Expr.names, h])) hbb hfb ⟨[fd], close, true⟩
        obtain ⟨d', hd, hed⟩ := ihd k fd
          (fun n h => hn n (by simp [Expr.names, h])) hbd hfd ⟨[], close, true⟩
        refine ⟨.mux q a' b' d', ?_, ?_⟩
        · cases c
          rw [expr]
          simp [take, inside, atom, finish, Form.pos, Bind.bind, Except.bind,
            Pure.pure, Except.pure, ha, hb', hd]
        · simp [Expr.erasePos, hea, heb, hed]
  | extract p a l w ih =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i tagPos fa hfa loPos widthPos
        have hba : (encodeExpr a).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        obtain ⟨a', ha, hea⟩ := ih k fa hn hba hfa
          ⟨[.atom ⟨loPos, toString l⟩, .atom ⟨widthPos, toString w⟩], close, true⟩
        simp at ha
        refine ⟨.extract q a' l w, ?_, ?_⟩
        · cases c
          rw [expr]
          simp [take, inside, atom, finish, Form.pos, Bind.bind, Except.bind,
            Pure.pure, Except.pure, ha]
        · simp [Expr.erasePos, hea]
  | replicate p a n ih =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i tagPos fa hfa countPos
        have hba : (encodeExpr a).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        obtain ⟨a', ha, hea⟩ := ih k fa hn hba hfa
          ⟨[.atom ⟨countPos, toString n⟩], close, true⟩
        simp at ha
        refine ⟨.replicate q a' n, ?_, ?_⟩
        · cases c
          rw [expr]
          simp [take, inside, atom, finish, Form.pos, Bind.bind, Except.bind,
            Pure.pure, Except.pure, ha]
        · simp [Expr.erasePos, hea]
  | read p n a ih =>
    cases fuel with
    | zero => omega
    | succ k =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i tagPos namePos fa hfa
        have hba : (encodeExpr a).weight < k := by
          simp only [encodeExpr, Tree.weight, Tree.weightMany] at hb
          omega
        have hname := hn n (by simp [Expr.names])
        obtain ⟨a', ha, hea⟩ := ih k fa
          (fun n h => hn n (by simp [Expr.names, h])) hba hfa ⟨[], close, true⟩
        refine ⟨.read q n a', ?_, ?_⟩
        · cases c
          rw [expr]
          simp [take, inside, atom, finish, Form.pos, Bind.bind, Except.bind,
            Pure.pure, Except.pure, hname, ha]
        · simp [Expr.erasePos, hea]

/-! Field readers recover types, ports, and external dependencies. -/
theorem bits_read (n : Nat) (f : Form) (h : (encodeTy (.bits n)).Matches f)
    (eof : Pos) (c : Cursor) :
    bits eof { c with forms := f :: c.forms } = .ok (n, c) := by
  cases h with
  | list p close hs =>
    cases hs with
    | cons ha hs =>
      cases ha
      cases hs with
      | cons hn hs =>
        cases hn
        cases hs
        cases c
        simp [bits, form, take, inside, word, atom, finish,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem ty_read (t : Ty) (f : Form) (h : (encodeTy t).Matches f)
    (eof : Pos) (c : Cursor) :
    ty eof { c with forms := f :: c.forms } = .ok (t, c) := by
  cases t with
  | clock =>
    cases h
    cases c
    simp [ty, peekWord, word, atom, take, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | bits n =>
    have hb := bits_read n f h eof c
    cases h
    simp [ty, peekWord, Bind.bind, Except.bind, Pure.pure, Except.pure, hb]

theorem port_read (v : Port) (f : Form) (h : (encodePort v).Matches f)
    (hn : validName v.name = true) (eof : Pos) (c : Cursor) :
    ∃ a, port eof { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = v.erasePos := by
  cases h with
  | list p close hs =>
    cases hs with
    | cons hd hs =>
      cases hd
      cases hs with
      | cons hname hs =>
        cases hname
        cases hs with
        | cons ht hs =>
          cases hs
          rename_i pd pn ft
          refine ⟨{ v with pos := p }, ?_, rfl⟩
          have htt := ty_read v.ty ft ht eof ⟨[], close, true⟩
          cases v with
          | mk vp dir vn vt =>
            cases dir <;> cases c <;>
              simp [port, form, take, inside, atom, name_read _ hn, finish, Form.pos,
                Bind.bind, Except.bind, Pure.pure, Except.pure, htt]

/-! Matched lists have equal lengths, so repeated readers use sufficient fuel. -/
theorem matchesMany_length (ts : List Tree) (fs : List Form) (h : Tree.MatchesMany ts fs) :
    ts.length = fs.length := by
  induction ts generalizing fs with
  | nil => cases h; rfl
  | cons t ts ih => cases h with
    | cons hh hs => simp [ih _ hs]

theorem many_names_read (ns : List String) (fs : List Form)
    (h : Tree.MatchesMany (ns.map Tree.atom) fs)
    (hn : ∀ n ∈ ns, validName n = true) (fuel : Nat) (hf : ns.length ≤ fuel)
    (stop : Pos) (closed : Bool) :
    many name fuel ⟨fs, stop, closed⟩ = .ok (ns, ⟨[], stop, closed⟩) := by
  induction ns generalizing fs fuel with
  | nil =>
    cases h
    cases fuel <;> simp [many]
  | cons n ns ih =>
    cases h with
    | cons hh hs =>
      cases hh
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
        have hn0 := hn n (by simp)
        have hns : ∀ m ∈ ns, validName m = true := fun m hm => hn m (by simp [hm])
        have hnf : ns.length ≤ fuel := by simpa using hf
        simp [many, name_read _ hn0, Bind.bind, Except.bind, Pure.pure, Except.pure,
          ih _ hs hns fuel hnf]

theorem remaining_names_read (ns : List String) (fs : List Form)
    (h : Tree.MatchesMany (ns.map Tree.atom) fs)
    (hn : ∀ n ∈ ns, validName n = true) (stop : Pos) (closed : Bool) :
    remaining name ⟨fs, stop, closed⟩ = .ok (ns, ⟨[], stop, closed⟩) := by
  apply many_names_read ns fs h hn
  have hl := matchesMany_length _ _ h
  simp only [List.length_map] at hl
  change ns.length ≤ fs.length
  omega

/-! Dependency and port readers preserve the order of interface fields. -/
theorem dep_read (v : Dep) (f : Form) (h : (encodeDep v).Matches f)
    (hn : validName v.output = true) (hi : ∀ n ∈ v.inputs, validName n = true)
    (eof : Pos) (c : Cursor) :
    ∃ a, dep eof { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = v.erasePos := by
  cases h with
  | list p close hs =>
    cases hs with
    | cons hd hs =>
      cases hd
      cases hs with
      | cons hname hs =>
        cases hname
        cases hs with
        | cons hinputs hs =>
          cases hs
          cases hinputs with
          | list pi ci hi' =>
            rename_i pd pn fi
            refine ⟨{ v with pos := p }, ?_, rfl⟩
            have hir := remaining_names_read v.inputs fi hi' hi ci true
            cases v
            cases c
            simp [dep, form, take, inside, word, atom, name_read _ hn, finish, Form.pos,
              Bind.bind, Except.bind, Pure.pure, Except.pure, hir]

theorem port_peek (v : Port) (f : Form) (h : (encodePort v).Matches f) (c : Cursor) :
    (peekHead { c with forms := f :: c.forms } == some "input" ||
      peekHead { c with forms := f :: c.forms } == some "output") = true := by
  cases h with
  | list p close hs =>
    cases hs with
    | cons hd hs =>
      cases hd
      cases v.dir <;> rfl

theorem ports_read (vs : List Port) (fs : List Form)
    (h : Tree.MatchesMany (vs.map encodePort) fs)
    (hn : ∀ v ∈ vs, validName v.name = true) (fuel : Nat) (hf : vs.length ≤ fuel)
    (eof : Pos) (c : Cursor)
    (hc : (peekHead c == some "input" || peekHead c == some "output") = false) :
    ∃ ps, ports eof fuel { c with forms := fs ++ c.forms } = .ok (ps, c) ∧
      ps.map Port.erasePos = vs.map Port.erasePos := by
  induction vs generalizing fs fuel with
  | nil =>
    cases h
    refine ⟨[], ?_, rfl⟩
    cases fuel <;> cases c <;>
      simp_all [ports, Pure.pure, Except.pure]
  | cons v vs ih =>
    cases h with
    | cons hv hvs =>
      rename_i f fs
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
        have hvn := hn v (by simp)
        have hvns : ∀ v ∈ vs, validName v.name = true := fun v hv => hn v (by simp [hv])
        have hvf : vs.length ≤ fuel := by simpa using hf
        obtain ⟨p, hp, hpe⟩ := port_read v f hv hvn eof { c with forms := fs ++ c.forms }
        obtain ⟨ps, hps, hpse⟩ := ih fs hvs hvns fuel hvf
        refine ⟨p :: ps, ?_, by simp [hpe, hpse]⟩
        have hh := port_peek v f hv { c with forms := fs ++ c.forms }
        simp only [List.cons_append, ports, hh, ↓reduceIte,
          Bind.bind, Except.bind, Pure.pure, Except.pure, hp, hps]

/-! List and design readers compose the individual grammar proofs. -/
theorem many_roundtrip {α : Type} (r : Reader α) (encode : α → Tree) (erase : α → α)
    (xs : List α) (fs : List Form) (hm : Tree.MatchesMany (xs.map encode) fs)
    (hr : ∀ x ∈ xs, ∀ f, (encode x).Matches f → ∀ c : Cursor,
      ∃ a, r { c with forms := f :: c.forms } = .ok (a, c) ∧ erase a = erase x)
    (fuel : Nat) (hf : xs.length ≤ fuel) (stop : Pos) (closed : Bool) :
    ∃ ys, many r fuel ⟨fs, stop, closed⟩ = .ok (ys, ⟨[], stop, closed⟩) ∧
      ys.map erase = xs.map erase := by
  induction xs generalizing fs fuel with
  | nil =>
    cases hm
    refine ⟨[], ?_, rfl⟩
    cases fuel <;> simp [many]
  | cons x xs ih =>
    cases hm with
    | cons hx hxs =>
      rename_i f fs
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
        obtain ⟨a, ha, hae⟩ := hr x (by simp) f hx ⟨fs, stop, closed⟩
        have hrt : ∀ x ∈ xs, ∀ f, (encode x).Matches f → ∀ c : Cursor,
            ∃ a, r { c with forms := f :: c.forms } = .ok (a, c) ∧ erase a = erase x :=
          fun x hx => hr x (by simp [hx])
        obtain ⟨ys, hys, hyse⟩ := ih fs hxs hrt fuel (by simpa using hf)
        refine ⟨a :: ys, ?_, by simp [hae, hyse]⟩
        simp [many, Bind.bind, Except.bind, Pure.pure, Except.pure, ha, hys]

theorem remaining_roundtrip {α : Type} (r : Reader α) (encode : α → Tree) (erase : α → α)
    (xs : List α) (fs : List Form) (hm : Tree.MatchesMany (xs.map encode) fs)
    (hr : ∀ x ∈ xs, ∀ f, (encode x).Matches f → ∀ c : Cursor,
      ∃ a, r { c with forms := f :: c.forms } = .ok (a, c) ∧ erase a = erase x)
    (stop : Pos) (closed : Bool) :
    ∃ ys, remaining r ⟨fs, stop, closed⟩ = .ok (ys, ⟨[], stop, closed⟩) ∧
      ys.map erase = xs.map erase := by
  apply many_roundtrip r encode erase xs fs hm hr
  have hl := matchesMany_length _ _ hm
  simp only [List.length_map] at hl
  change xs.length ≤ fs.length
  omega

/-! Splitting matched lists preserves the boundary between ports and body forms. -/
theorem matchesMany_append (xs ys : List Tree) (fs : List Form)
    (h : Tree.MatchesMany (xs ++ ys) fs) :
    ∃ as bs, fs = as ++ bs ∧ Tree.MatchesMany xs as ∧ Tree.MatchesMany ys bs := by
  induction xs generalizing fs with
  | nil => exact ⟨[], fs, rfl, .nil, h⟩
  | cons x xs ih =>
    cases h with
    | cons hx hs =>
      obtain ⟨as, bs, rfl, ha, hb⟩ := ih _ hs
      exact ⟨_ :: as, bs, rfl, .cons hx ha, hb⟩

/-! Each child and each list length fit within the enclosing token count. -/
theorem Tree.weightMany_append (xs ys : List Tree) :
    Tree.weightMany (xs ++ ys) = Tree.weightMany xs + Tree.weightMany ys := by
  induction xs with
  | nil => simp [Tree.weightMany]
  | cons x xs ih => simp [Tree.weightMany, ih, Nat.add_assoc]

theorem Tree.weight_pos (t : Tree) : 0 < t.weight := by
  cases t <;> simp [Tree.weight] <;> omega

theorem Tree.weight_le_weightMany (t : Tree) (ts : List Tree) (h : t ∈ ts) :
    t.weight ≤ Tree.weightMany ts := by
  induction ts with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [Tree.weightMany]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem Tree.length_le_weightMany (ts : List Tree) : ts.length ≤ Tree.weightMany ts := by
  induction ts with
  | nil => simp [Tree.weightMany]
  | cons x xs ih =>
    have := x.weight_pos
    simp only [List.length_cons, Tree.weightMany]
    omega

/-! Statement and dependency heads stop the preceding port reader. -/
theorem stmt_peek (v : Stmt) (f : Form) (h : (encodeStmt v).Matches f) (c : Cursor) :
    (peekHead { c with forms := f :: c.forms } == some "input" ||
      peekHead { c with forms := f :: c.forms } == some "output") = false := by
  cases v <;> cases h with
  | list p close hs =>
    cases hs with
    | cons ht hs => cases ht; rfl

theorem dep_peek (v : Dep) (f : Form) (h : (encodeDep v).Matches f) (c : Cursor) :
    (peekHead { c with forms := f :: c.forms } == some "input" ||
      peekHead { c with forms := f :: c.forms } == some "output") = false := by
  cases h with
  | list p close hs =>
    cases hs with
    | cons ht hs => cases ht; rfl

theorem matched_stop {α : Type} (enc : α → Tree) (xs : List α) (fs : List Form)
    (h : Tree.MatchesMany (xs.map enc) fs)
    (hh : ∀ x ∈ xs, ∀ f, (enc x).Matches f → ∀ c : Cursor,
      (peekHead { c with forms := f :: c.forms } == some "input" ||
        peekHead { c with forms := f :: c.forms } == some "output") = false)
    (stop : Pos) (closed : Bool) :
    (peekHead ⟨fs, stop, closed⟩ == some "input" ||
      peekHead ⟨fs, stop, closed⟩ == some "output") = false := by
  cases xs with
  | nil => cases h; rfl
  | cons x xs =>
    cases h with
    | cons hx hs => exact hh x (by simp) _ hx ⟨_, stop, closed⟩

/-! Module and extern readers combine interface fields with their remaining forms. -/
theorem module_read (m : Module) (f : Form) (hm : (encodeItem (.module m)).Matches f)
    (hn : validName m.name = true) (hp : ∀ p ∈ m.ports, validName p.name = true)
    (fuel : Nat) (hf : m.ports.length ≤ fuel)
    (hr : ∀ s ∈ m.body, ∀ f, (encodeStmt s).Matches f → ∀ c : Cursor,
      ∃ a, stmt eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
        a.erasePos = s.erasePos) (c : Cursor) :
    ∃ a, item eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = (Item.module m).erasePos := by
  cases hm with
  | list p close hs =>
    cases hs with
    | cons htag hs =>
      cases htag
      cases hs with
      | cons hname hs =>
        cases hname
        obtain ⟨pf, sf, rfl, hpf, hsf⟩ := matchesMany_append
          (m.ports.map encodePort) (m.body.map encodeStmt) _ hs
        have hstop := matched_stop encodeStmt m.body sf hsf
          (fun s _ f h c => stmt_peek s f h c) close true
        obtain ⟨ps, hps, hpse⟩ := ports_read m.ports pf hpf hp fuel hf eof
          ⟨sf, close, true⟩ hstop
        obtain ⟨ss, hss, hsse⟩ := remaining_roundtrip (stmt eof fuel) encodeStmt Stmt.erasePos
          m.body sf hsf hr close true
        refine ⟨.module { m with pos := p, ports := ps, body := ss }, ?_, ?_⟩
        · cases c
          simp [item, form, take, inside, atom, name_read _ hn, finish, Form.pos,
            Bind.bind, Except.bind, Pure.pure, Except.pure, hps, hss]
        · simp [Item.erasePos, hpse, hsse]

theorem extern_read (e : Extern) (f : Form) (hm : (encodeItem (.extern e)).Matches f)
    (hn : validName e.name = true) (hp : ∀ p ∈ e.ports, validName p.name = true)
    (hd : ∀ d ∈ e.deps, validName d.output = true ∧ ∀ n ∈ d.inputs, validName n = true)
    (fuel : Nat) (hf : e.ports.length ≤ fuel) (eof : Pos) (c : Cursor) :
    ∃ a, item eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = (Item.extern e).erasePos := by
  cases hm with
  | list p close hs =>
    cases hs with
    | cons htag hs =>
      cases htag
      cases hs with
      | cons hname hs =>
        cases hname
        obtain ⟨pf, df, rfl, hpf, hdf⟩ := matchesMany_append
          (e.ports.map encodePort) (e.deps.map encodeDep) _ hs
        have hstop := matched_stop encodeDep e.deps df hdf
          (fun d _ f h c => dep_peek d f h c) close true
        obtain ⟨ps, hps, hpse⟩ := ports_read e.ports pf hpf hp fuel hf eof
          ⟨df, close, true⟩ hstop
        have hrd : ∀ d ∈ e.deps, ∀ f, (encodeDep d).Matches f → ∀ c : Cursor,
            ∃ a, dep eof { c with forms := f :: c.forms } = .ok (a, c) ∧
              a.erasePos = d.erasePos := fun d hm f h c =>
          dep_read d f h (hd d hm).1 (hd d hm).2 eof c
        obtain ⟨ds, hds, hdse⟩ := remaining_roundtrip (dep eof) encodeDep Dep.erasePos
          e.deps df hdf hrd close true
        refine ⟨.extern { e with pos := p, ports := ps, deps := ds }, ?_, ?_⟩
        · cases c
          simp [item, form, take, inside, atom, name_read _ hn, finish, Form.pos,
            Bind.bind, Except.bind, Pure.pure, Except.pure, hps, hds]
        · simp [Item.erasePos, hpse, hdse]

/-! Item reading composes the statement proof with the module and extern proofs. -/
theorem item_roundtrip
    (hs : ∀ (s : Stmt) (fuel : Nat) (f : Form),
      (∀ n ∈ s.names, validName n = true) → (encodeStmt s).weight < fuel →
      (encodeStmt s).Matches f → ∀ (eof : Pos) (c : Cursor),
      ∃ a, stmt eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
        a.erasePos = s.erasePos)
    (v : Item) (fuel : Nat) (f : Form) (hn : ∀ n ∈ v.names, validName n = true)
    (hb : (encodeItem v).weight < fuel) (hm : (encodeItem v).Matches f)
    (eof : Pos) (c : Cursor) :
    ∃ a, item eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = v.erasePos := by
  cases v with
  | module m =>
    apply module_read m f hm (hn m.name (by simp [Item.names]))
    · intro p hp
      apply hn
      simp only [Item.names, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩))
    · have hl := Tree.length_le_weightMany (m.ports.map encodePort)
      simp only [List.length_map] at hl
      simp only [encodeItem, Tree.weight, Tree.weightMany_append, Tree.weightMany] at hb
      omega
    · intro s hmem f hmatch c
      apply hs s fuel f
      · intro n hname
        apply hn
        simp only [Item.names, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨s, hmem, hname⟩))
      · have hw := Tree.weight_le_weightMany (encodeStmt s) (m.body.map encodeStmt)
          (List.mem_map.mpr ⟨s, hmem, rfl⟩)
        simp only [encodeItem, Tree.weight, Tree.weightMany_append, Tree.weightMany] at hb
        omega
      · exact hmatch
  | extern e =>
    apply extern_read e f hm (hn e.name (by simp [Item.names]))
    · intro p hp
      apply hn
      simp only [Item.names, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩))
    · intro d hd
      constructor
      · apply hn
        simp only [Item.names, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨d, hd, by simp⟩))
      · intro n hname
        apply hn
        simp only [Item.names, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨d, hd, by simp [hname]⟩))
    · have hl := Tree.length_le_weightMany (e.ports.map encodePort)
      simp only [List.length_map] at hl
      simp only [encodeItem, Tree.weight, Tree.weightMany_append, Tree.weightMany] at hb
      omega

/-! Design reading preserves the top name and item order. -/
theorem design_read
    (hs : ∀ (s : Stmt) (fuel : Nat) (f : Form),
      (∀ n ∈ s.names, validName n = true) → (encodeStmt s).weight < fuel →
      (encodeStmt s).Matches f → ∀ (eof : Pos) (c : Cursor),
      ∃ a, stmt eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
        a.erasePos = s.erasePos)
    (d : Design) (fuel : Nat) (f : Form) (hn : d.ValidNames)
    (hb : (encode d).weight < fuel) (hm : (encode d).Matches f)
    (eof : Pos) (c : Cursor) :
    ∃ a, (form eof (fun _ => do
      word "design"
      return (⟨← name, ← remaining (item eof fuel), ⟨0, 0, []⟩⟩ : Design)))
        { c with forms := f :: c.forms } = .ok (a, c) ∧ a.erasePos = d.erasePos := by
  cases hm with
  | list p close hm =>
    cases hm with
    | cons ht hm =>
      cases ht
      cases hm with
      | cons hn' hm =>
        cases hn'
        rename_i pt fs pn
        have htop := hn d.top (by simp)
        have hir : ∀ i ∈ d.items, ∀ f, (encodeItem i).Matches f → ∀ c : Cursor,
            ∃ a, item eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
              a.erasePos = i.erasePos := by
          intro i hi f hmatch c
          apply item_roundtrip hs i fuel f
          · intro n hn'
            exact hn n (List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr ⟨i, hi, hn'⟩)))
          · have hw := Tree.weight_le_weightMany (encodeItem i) (d.items.map encodeItem)
              (List.mem_map.mpr ⟨i, hi, rfl⟩)
            simp only [encode, Tree.weight, Tree.weightMany, Tree.weightMany_append] at hb
            omega
          · exact hmatch
        obtain ⟨is, his, hise⟩ := remaining_roundtrip (item eof fuel) encodeItem Item.erasePos
          d.items fs hm hir close true
        refine ⟨⟨d.top, is, ⟨0, 0, []⟩⟩, ?_, ?_⟩
        · cases c
          simp [form, take, inside, word, atom, name_read _ htop, finish,
            Bind.bind, Except.bind, Pure.pure, Except.pure, his]
        · simp [Design.erasePos, hise]

/-! The token count supplies enough fuel for the complete encoded design. -/
theorem parse_encode
    (hs : ∀ (s : Stmt) (fuel : Nat) (f : Form),
      (∀ n ∈ s.names, validName n = true) → (encodeStmt s).weight < fuel →
      (encodeStmt s).Matches f → ∀ (eof : Pos) (c : Cursor),
      ∃ a, stmt eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
        a.erasePos = s.erasePos)
    (d : Design) (hn : d.ValidNames) (hl : (encode d).Legal) :
    (parseRaw ((encode d).render 2 ++ "\n")).map Design.erasePos = .ok d.erasePos := by
  obtain ⟨f, hm, hf⟩ := (encode d).forms_lex_render_length hl 2
  have hf' : forms ((lex ((encode d).render 2 ++ "\n")).1.length + 1)
      (lex ((encode d).render 2 ++ "\n")).1 = ([f], []) := by
    simpa only [lex_append_lf] using hf
  have hb : (encode d).weight < (lex ((encode d).render 2 ++ "\n")).1.length + 1 := by
    rw [lex_append_lf, (encode d).lex_render hl 2, Tree.tokens_length _ _ 2]
    omega
  obtain ⟨a, ha, hae⟩ := design_read hs d _ f hn hb hm
    (lex ((encode d).render 2 ++ "\n")).2
    ⟨[], (lex ((encode d).render 2 ++ "\n")).2, true⟩
  simp only [parseRaw, hf', List.map_nil, List.append_nil]
  rw [ha]
  simp [finish, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, hae]

/-! Statement reading preserves equations, updates, and instance connections. -/
theorem reset_roundtrip (r : Reset) (fuel : Nat) (f : Form)
    (hn : ∀ n ∈ r.names, validName n = true)
    (hb : (encodeReset r).weight < fuel) (hm : (encodeReset r).Matches f)
    (eof : Pos) (c : Cursor) :
    ∃ a, reset eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = r.erasePos := by
  cases hm with
  | list q close hs =>
    unpack_matches
    rename_i tagPos kindPos fa hfa fb hfb
    have hba : (encodeExpr r.signal).weight < fuel := by
      simp only [encodeReset, Tree.weight, Tree.weightMany] at hb
      omega
    have hbb : (encodeExpr r.value).weight < fuel := by
      simp only [encodeReset, Tree.weight, Tree.weightMany] at hb
      omega
    obtain ⟨a, ha, hea⟩ := expr_roundtrip r.signal fuel fa
      (fun n h => hn n (by simp [Reset.names, h])) hba hfa eof ⟨[fb], close, true⟩
    obtain ⟨b, hb', heb⟩ := expr_roundtrip r.value fuel fb
      (fun n h => hn n (by simp [Reset.names, h])) hbb hfb eof ⟨[], close, true⟩
    refine ⟨⟨.sync, a, b⟩, ?_, ?_⟩
    · cases c
      simp [reset, form, take, inside, word, atom, finish, Bind.bind,
        Except.bind, Pure.pure, Except.pure, ha, hb']
    · cases r with
      | mk kind signal value => cases kind; simp_all [Reset.erasePos]

/-! An instance connection keeps its port name and expression. -/
theorem input_roundtrip (x : String × Expr) (fuel : Nat) (f : Form)
    (hn : validName x.1 = true) (he : ∀ n ∈ x.2.names, validName n = true)
    (hb : (encodeExpr x.2).weight < fuel)
    (hm : (Tree.list [.atom x.1, encodeExpr x.2]).Matches f)
    (eof : Pos) (c : Cursor) :
    ∃ a, (form eof fun _ => do return (← name, ← expr eof fuel))
      { c with forms := f :: c.forms } = .ok (a, c) ∧
      (a.1, a.2.erasePos) = (x.1, x.2.erasePos) := by
  cases hm with
  | list q close hs =>
    unpack_matches
    rename_i namePos fe hfe
    obtain ⟨e, he', hee⟩ := expr_roundtrip x.2 fuel fe he hb hfe eof ⟨[], close, true⟩
    refine ⟨(x.1, e), ?_, by simp [hee]⟩
    cases c
    simp [form, take, inside, name_read _ hn, finish, Bind.bind,
      Except.bind, Pure.pure, Except.pure, he']

/-! Every statement constructor satisfies the same grammar round-trip contract. -/
theorem stmt_roundtrip (s : Stmt) (fuel : Nat) (f : Form)
    (hn : ∀ n ∈ s.names, validName n = true)
    (hb : (encodeStmt s).weight < fuel) (hm : (encodeStmt s).Matches f)
    (eof : Pos) (c : Cursor) :
    ∃ a, stmt eof fuel { c with forms := f :: c.forms } = .ok (a, c) ∧
      a.erasePos = s.erasePos := by
  cases s with
  | let_ p n w e =>
    cases hm with
    | list q close hs =>
      unpack_matches
      rename_i tagPos namePos ft ht fe he
      have hname := hn n (by simp [Stmt.names])
      have hew : (encodeExpr e).weight < fuel := by
        simp only [encodeStmt, Tree.weight, Tree.weightMany] at hb
        omega
      obtain ⟨e', he', hee⟩ := expr_roundtrip e fuel fe
        (fun n h => hn n (by simp [Stmt.names, h])) hew he eof ⟨[], close, true⟩
      have hty := bits_read w ft ht eof ⟨[fe], close, true⟩
      refine ⟨.let_ q n w e', ?_, by simp [Stmt.erasePos, hee]⟩
      cases c
      simp [stmt, form, take, inside, atom, finish, Form.pos, Bind.bind,
        Except.bind, Pure.pure, Except.pure, hname, hty, he']
  | reg p n w clock resetValue =>
    cases resetValue with
    | none =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i tagPos namePos ft ht clockPos
        have hname := hn n (by simp [Stmt.names])
        have hclock := hn clock (by simp [Stmt.names])
        have hty := bits_read w ft ht eof ⟨[.atom ⟨clockPos, clock⟩], close, true⟩
        refine ⟨.reg q n w clock none, ?_, rfl⟩
        cases c
        simp [stmt, form, take, inside, atom, finish, Form.pos, optionalReset, Bind.bind,
          Except.bind, Pure.pure, Except.pure, hname, hclock, hty]
    | some r =>
      cases hm with
      | list q close hs =>
        unpack_matches
        rename_i tagPos namePos ft ht clockPos fr hr
        have hname := hn n (by simp [Stmt.names])
        have hclock := hn clock (by simp [Stmt.names])
        have hrw : (encodeReset r).weight < fuel := by
          simp only [encodeStmt, Option.toList, List.map, List.cons_append, List.nil_append,
            Tree.weight, Tree.weightMany] at hb
          omega
        obtain ⟨r', hr', hre⟩ := reset_roundtrip r fuel fr
          (fun n h => hn n (by simp [Stmt.names, h])) hrw hr eof ⟨[], close, true⟩
        have hty := bits_read w ft ht eof ⟨[.atom ⟨clockPos, clock⟩, fr], close, true⟩
        refine ⟨.reg q n w clock (some r'), ?_, by simp [Stmt.erasePos, hre]⟩
        cases c
        simp [stmt, form, take, inside, atom, finish, Form.pos, optionalReset, Bind.bind,
          Except.bind, Pure.pure, Except.pure, hname, hclock, hty, hr']
  | next p n e =>
    cases hm with
    | list q close hs =>
      unpack_matches
      rename_i tagPos namePos fe he
      have hname := hn n (by simp [Stmt.names])
      have hew : (encodeExpr e).weight < fuel := by
        simp only [encodeStmt, Tree.weight, Tree.weightMany] at hb
        omega
      obtain ⟨e', he', hee⟩ := expr_roundtrip e fuel fe
        (fun n h => hn n (by simp [Stmt.names, h])) hew he eof ⟨[], close, true⟩
      refine ⟨.next q n e', ?_, by simp [Stmt.erasePos, hee]⟩
      cases c
      simp [stmt, form, take, inside, atom, finish, Form.pos, Bind.bind,
        Except.bind, Pure.pure, Except.pure, hname, he']
  | mem p n w d clock =>
    cases hm with
    | list q close hs =>
      unpack_matches
      rename_i tagPos namePos ft ht depthPos clockPos
      have hname := hn n (by simp [Stmt.names])
      have hclock := hn clock (by simp [Stmt.names])
      have hty := bits_read w ft ht eof
        ⟨[.atom ⟨depthPos, toString d⟩, .atom ⟨clockPos, clock⟩], close, true⟩
      simp at hty
      refine ⟨.mem q n w d clock, ?_, rfl⟩
      cases c
      simp [stmt, form, take, inside, atom, finish, Form.pos, Bind.bind,
        Except.bind, Pure.pure, Except.pure, hname, hclock, hty]
  | write p n i a d e =>
    cases hm with
    | list q close hs =>
      unpack_matches
      rename_i tagPos namePos indexPos fa hfa fd hfd fe hfe
      have hname := hn n (by simp [Stmt.names])
      have haw : (encodeExpr a).weight < fuel := by
        simp only [encodeStmt, Tree.weight, Tree.weightMany] at hb
        omega
      have hdw : (encodeExpr d).weight < fuel := by
        simp only [encodeStmt, Tree.weight, Tree.weightMany] at hb
        omega
      have hew : (encodeExpr e).weight < fuel := by
        simp only [encodeStmt, Tree.weight, Tree.weightMany] at hb
        omega
      obtain ⟨a', ha, hea⟩ := expr_roundtrip a fuel fa
        (fun n h => hn n (by simp [Stmt.names, h])) haw hfa eof ⟨[fd, fe], close, true⟩
      obtain ⟨d', hd, hed⟩ := expr_roundtrip d fuel fd
        (fun n h => hn n (by simp [Stmt.names, h])) hdw hfd eof ⟨[fe], close, true⟩
      obtain ⟨e', he, hee⟩ := expr_roundtrip e fuel fe
        (fun n h => hn n (by simp [Stmt.names, h])) hew hfe eof ⟨[], close, true⟩
      refine ⟨.write q n i a' d' e', ?_, by simp [Stmt.erasePos, hea, hed, hee]⟩
      cases c
      simp [stmt, form, take, inside, atom, finish, Form.pos, Bind.bind,
        Except.bind, Pure.pure, Except.pure, hname, ha, hd, he]
  | inst p n m xs =>
    cases hm with
    | list q close hs =>
      unpack_matches
      rename_i tagPos namePos fs hfs modulePos
      have hname := hn n (by simp [Stmt.names])
      have hmodule := hn m (by simp [Stmt.names])
      have hr : ∀ x ∈ xs, ∀ f,
          (Tree.list [.atom x.1, encodeExpr x.2]).Matches f → ∀ c : Cursor,
          ∃ a, (form eof fun _ => do return (← name, ← expr eof fuel))
            { c with forms := f :: c.forms } = .ok (a, c) ∧
            (a.1, a.2.erasePos) = (x.1, x.2.erasePos) := by
        intro x hx f hf c
        have hxn : validName x.1 = true := by
          apply hn x.1
          have hmem : x.1 ∈ xs.flatMap (fun y => y.1 :: y.2.names) :=
            List.mem_flatMap.mpr ⟨x, hx, by simp⟩
          simp [Stmt.names, hmem]
        have hxe : ∀ k ∈ x.2.names, validName k = true := by
          intro k hk
          apply hn k
          have hmem : k ∈ xs.flatMap (fun y => y.1 :: y.2.names) :=
            List.mem_flatMap.mpr ⟨x, hx, by simp [hk]⟩
          simp [Stmt.names, hmem]
        have hxw : (encodeExpr x.2).weight < fuel := by
          have hw := Tree.weight_le_weightMany
            (.list [.atom x.1, encodeExpr x.2])
            (xs.map fun y => Tree.list [.atom y.1, encodeExpr y.2])
            (List.mem_map.mpr ⟨x, hx, rfl⟩)
          simp only [encodeStmt, Tree.weight, Tree.weightMany_append,
            Tree.weightMany] at hb
          simp only [Tree.weight, Tree.weightMany] at hw
          omega
        exact input_roundtrip x fuel f hxn hxe hxw hf eof c
      obtain ⟨ys, hys, heys⟩ := remaining_roundtrip
        (form eof fun _ => do return (← name, ← expr eof fuel))
        (fun x : String × Expr => .list [.atom x.1, encodeExpr x.2])
        (fun x => (x.1, x.2.erasePos)) xs fs hfs hr close true
      simp only [Bind.bind, Except.bind, Pure.pure] at hys
      refine ⟨.inst q n m ys, ?_, by simpa [Stmt.erasePos] using heys⟩
      cases c
      simp [stmt, form, take, inside, atom, finish, Form.pos, Bind.bind,
        Except.bind, Pure.pure, Except.pure, hname, hmodule, hys]
  | assign p n e =>
    cases hm with
    | list q close hs =>
      unpack_matches
      rename_i tagPos namePos fe he
      have hname := hn n (by simp [Stmt.names])
      have hew : (encodeExpr e).weight < fuel := by
        simp only [encodeStmt, Tree.weight, Tree.weightMany] at hb
        omega
      obtain ⟨e', he', hee⟩ := expr_roundtrip e fuel fe
        (fun n h => hn n (by simp [Stmt.names, h])) hew he eof ⟨[], close, true⟩
      refine ⟨.assign q n e', ?_, by simp [Stmt.erasePos, hee]⟩
      cases c
      simp [stmt, form, take, inside, atom, finish, Form.pos, Bind.bind,
        Except.bind, Pure.pure, Except.pure, hname, he']

/-! Valid names make every encoded atom legal. Rendering agrees with the public printer. -/
@[simp] theorem encodeTy_render (t : Ty) : (encodeTy t).render = printTy t := by
  cases t <;> simp [encodeTy, printTy]

@[simp] theorem encodeExpr_render (e : Expr) : (encodeExpr e).render = printExpr e := by
  induction e <;> simp_all [encodeExpr, printExpr]

@[simp] theorem encodeReset_render (r : Reset) : (encodeReset r).render = printReset r := by
  simp [encodeReset, printReset]

@[simp] theorem encodeStmt_render (s : Stmt) : (encodeStmt s).render = printStmt s := by
  cases s <;> simp [encodeStmt, printStmt, List.map_map, Function.comp_def]

@[simp] theorem encodePort_render (p : Port) : (encodePort p).render = printPort p := by
  cases h : p.dir <;> simp [encodePort, printPort, h]

@[simp] theorem encodeDep_render (d : Dep) : (encodeDep d).render = printDep d := by
  simp [encodeDep, printDep, List.map_map, Function.comp_def]

@[simp] theorem encodeItem_render (i : Item) : (encodeItem i).render 1 = printItem i := by
  cases i <;> simp [encodeItem, printItem, Tree.render_block, List.map_map, Function.comp_def]

theorem render_encode (d : Design) : (encode d).render 2 ++ "\n" = print d := by
  simp [encode, print, Tree.render_block, List.map_map, Function.comp_def]

@[simp] theorem legalMany_iff (xs : List Tree) :
    Tree.LegalMany xs ↔ ∀ x ∈ xs, x.Legal := by
  induction xs <;> simp_all [Tree.LegalMany]

@[simp] theorem legal_list (xs : List Tree) :
    (Tree.list xs).Legal ↔ ∀ x ∈ xs, x.Legal := legalMany_iff xs

/-! Lexical name validity supplies the tree's atom conditions. -/
theorem legal_name (n : String) (h : validName n = true) : (Tree.atom n).Legal :=
  ⟨validName_nonempty n h, validName_delimiter n h⟩

@[simp] theorem legal_number (n : Nat) : (Tree.atom n.repr).Legal := by
  simp only [Tree.Legal, Nat.repr_eq_ofList_toDigits, String.toList_ofList]
  refine ⟨Nat.toDigits_ne_nil, ?_⟩
  intro c hc
  apply nameRest_delimiter
  simp [nameRest, Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc]

theorem legal_port_name (i n : String) (hi : validName i = true)
    (hn : validName n = true) : (Tree.atom (i ++ "." ++ n)).Legal := by
  constructor
  · simp
  · intro c hc
    simp only [String.toList_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact validName_delimiter i hi c hc
    · have : c = '.' := by simpa using hc
      subst c
      rfl
    · exact validName_delimiter n hn c hc

@[simp] theorem legal_keyword (s : String) (h : s ∈ keywords) : (Tree.atom s).Legal := by
  simp only [keywords, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h <;> subst s <;> unfold Tree.Legal <;> decide

@[simp] theorem encodeTy_legal (t : Ty) : (encodeTy t).Legal := by
  cases t <;> simp [encodeTy] <;> apply legal_keyword <;> decide

@[simp] theorem unOp_legal (o : UnOp) : (Tree.atom o.text).Legal := by
  cases o <;> apply legal_keyword <;> decide

@[simp] theorem binOp_legal (o : BinOp) : (Tree.atom o.text).Legal := by
  cases o <;> apply legal_keyword <;> decide

@[simp] theorem pred_legal (o : Pred) : (Tree.atom o.text).Legal := by
  cases o <;> apply legal_keyword <;> decide

/-! Syntax encoders preserve the lexical conditions of every field. -/
theorem encodeExpr_legal (e : Expr) (hn : ∀ n ∈ e.names, validName n = true) :
    (encodeExpr e).Legal := by
  induction e <;> simp_all [Expr.names, encodeExpr, legal_name, legal_port_name] <;>
    apply legal_keyword <;> decide

theorem encodeReset_legal (r : Reset) (hn : ∀ n ∈ r.names, validName n = true) :
    (encodeReset r).Legal := by
  simp only [Reset.names, List.mem_append] at hn
  have hs : (encodeExpr r.signal).Legal := encodeExpr_legal _ (fun n h => hn n (Or.inl h))
  have hv : (encodeExpr r.value).Legal := encodeExpr_legal _ (fun n h => hn n (Or.inr h))
  simp [encodeReset, hs, hv]
  constructor <;> apply legal_keyword <;> decide

theorem encodeStmt_legal (s : Stmt) (hn : ∀ n ∈ s.names, validName n = true) :
    (encodeStmt s).Legal := by
  cases s <;> simp_all [Stmt.names, encodeStmt, legal_name, encodeExpr_legal,
    encodeReset_legal] <;> try (apply legal_keyword; decide)
  constructor
  · apply legal_keyword; decide
  · intro a n v hm ha
    subst a
    have hname := legal_name n (hn.2.2 n n v hm (Or.inl rfl))
    have hv := encodeExpr_legal v (fun x hx => hn.2.2 x n v hm (Or.inr hx))
    simp [hname, hv]

theorem encodePort_legal (p : Port) (hn : validName p.name = true) :
    (encodePort p).Legal := by
  cases h : p.dir <;> simp [encodePort, h, legal_name p.name hn] <;>
    apply legal_keyword <;> decide

theorem encodeDep_legal (d : Dep)
    (hn : ∀ n ∈ d.output :: d.inputs, validName n = true) : (encodeDep d).Legal := by
  simp only [List.mem_cons, forall_eq_or_imp] at hn
  simp [encodeDep, legal_name d.output hn.1]
  constructor
  · apply legal_keyword; decide
  · intro n hm
    exact legal_name n (hn.2 n hm)

theorem encodeItem_legal (i : Item) (hn : ∀ n ∈ i.names, validName n = true) :
    (encodeItem i).Legal := by
  cases i with
  | module m =>
    simp_all [Item.names, encodeItem, legal_name]
    constructor
    · apply legal_keyword; decide
    · intro a ha
      rcases ha with ⟨p, hp, rfl⟩ | ⟨s, hs, rfl⟩
      · exact encodePort_legal p (hn.2 p.name (Or.inl ⟨p, hp, rfl⟩))
      · exact encodeStmt_legal s (fun n h => hn.2 n (Or.inr ⟨s, hs, h⟩))
  | extern e =>
    simp_all [Item.names, encodeItem, legal_name]
    constructor
    · apply legal_keyword; decide
    · intro a ha
      rcases ha with ⟨p, hp, rfl⟩ | ⟨d, hd, rfl⟩
      · exact encodePort_legal p (hn.2 p.name (Or.inl ⟨p, hp, rfl⟩))
      · apply encodeDep_legal d
        intro n h
        exact hn.2 n (Or.inr ⟨d, hd, List.mem_cons.mp h⟩)

theorem encode_legal (d : Design) (hn : d.ValidNames) : (encode d).Legal := by
  simp_all [Design.ValidNames, encode, legal_name]
  constructor
  · apply legal_keyword; decide
  · intro i hi
    exact encodeItem_legal i (fun n h => hn.2 n i hi h)

end Text

/-! Printing and parsing preserve a valid design up to source positions. -/
theorem parse_print (d : Design) (h : d.ValidNames) (limits : d.WithinLimits) :
    (parse (print d)).map Design.erasePos = .ok d.erasePos := by
  have raw : (Text.parseRaw (print d)).map Design.erasePos = .ok d.erasePos := by
    rw [← Text.render_encode]
    exact Text.parse_encode Text.stmt_roundtrip d h (Text.encode_legal d h)
  cases hr : Text.parseRaw (print d) with
  | error e => simp [hr, Except.map] at raw
  | ok a =>
    have he : a.erasePos = d.erasePos := by simpa [hr, Except.map, Except.bind] using raw
    have hl : a.textLimits.map TextLimit.ok = d.textLimits.map TextLimit.ok := by
      rw [← Design.textLimits_erase a, he, Design.textLimits_erase]
    have ha : a.textLimits.all TextLimit.ok = true := by
      have hmap := congrArg (fun xs : List Bool => xs.all id) hl
      simp only [List.all_map, Function.comp_def, id_eq] at hmap
      exact hmap.trans limits
    have hn : a.textLimits.find? (fun l => !l.ok) = none := by
      simp only [List.find?_eq_none]
      intro l hm
      have := List.all_eq_true.mp ha l hm
      simp [this]
    simpa [parse, hr, hn, Except.map] using he

end Silicon.Core
