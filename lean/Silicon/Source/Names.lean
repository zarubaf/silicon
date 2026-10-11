-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Text
import Silicon.Source.Value
import Silicon.Source.Sha256

/-!
The names of section 7 of the front-end spec: the core name of a structural path, and the
emitted module name of an `InstantiationId`.

A name is a list of fields. The first field is a user field: a source name unchanged. Each
other field is a user field or a made field. `encode` joins the fields with one `$`. A made field
starts with a digit, so it never equals a user field. `decode` splits at each `$` and reads the
kind of each field from its first character. Thus `decode (encode p) = some p` for each valid
name `p`, and `encode` is injective.

These rules settle the open points of the spec:

- An integer, a call site, a version, and a temporary print in decimal without leading zeros.
  `decode` accepts only this form, so each field has one text.
- A digest is `0h` and at least one lowercase hexadecimal digit.
- `encode` adds the field `0k` to a name with only one field that equals a core keyword. The
  name structure has no field for it. `decode` removes it, and it accepts `0k` only there.
- The readable module name needs each argument to be an integer or a Boolean, and at most 64
  bytes for the full name. The rule also holds for a module without arguments.
- The digest form hashes the serialization of the `InstantiationId`. The digest function is a
  parameter, so a test can make two identities share a digest.
-/
namespace Silicon.Source.Names

/-! The roles of section 7.2: clock, reset, call result, memory response, and memory request. -/
inductive Role where
  | clk | rst | ret | rdata | rvalid | ren | raddr
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

def Role.text : Role → String
  | .clk => "0clk" | .rst => "0rst" | .ret => "0ret" | .rdata => "0rdata"
  | .rvalid => "0rvalid" | .ren => "0ren" | .raddr => "0raddr"

def roles : List Role := [.clk, .rst, .ret, .rdata, .rvalid, .ren, .raddr]

/-! A field of a name. Each constructor except `user` is a made field. -/
inductive Field where
  | user (name : String)
  | int (value : Int)
  | call (site : Nat)
  | version (index : Nat)
  | bool (value : Bool)
  | digest (hex : String)
  | temp (index : Nat)
  | role (role : Role)
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-! A name: a first user field, then the other fields in order. -/
structure Name where
  head : String
  rest : List Field
  deriving Repr, DecidableEq, BEq, Inhabited

/-! A user field is a source identifier: `[A-Za-z_][A-Za-z0-9_]*`. -/
def userField (s : String) : Bool :=
  match s.toList with
  | c :: cs => Core.nameStart c && cs.all Core.fieldChar
  | [] => false

def hexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

def Field.valid : Field → Bool
  | .user s => userField s
  | .digest h => !h.isEmpty && h.all hexDigit
  | _ => true

/-! A valid name has only valid fields. Only a valid name has the round trip. -/
def Name.valid (p : Name) : Bool := userField p.head && p.rest.all Field.valid

def Field.encode : Field → String
  | .user s => s
  | .int n => if n < 0 then s!"{n.natAbs}n" else toString n.natAbs
  | .call k => s!"{k}c"
  | .version k => s!"{k}v"
  | .bool b => if b then "1b" else "0b"
  | .digest h => "0h" ++ h
  | .temp k => s!"{k}t"
  | .role r => r.text

/-! True for a name with one field that equals a core keyword. It gets the field `0k`. -/
def keyword (p : Name) : Bool := p.rest.isEmpty && Core.keywords.contains p.head

def encode (p : Name) : String :=
  "$".intercalate (p.head :: if keyword p then ["0k"] else p.rest.map Field.encode)

/-! A decimal number without leading zeros. -/
def decimal (ds : List Char) : Option Nat :=
  match ds with
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | _ => if ds.all Char.isDigit then String.toNat? (String.ofList ds) else none

/-! A made field: digits and one suffix letter, a role, or a digest. -/
def madeField (s : String) : Option Field :=
  match roles.find? (·.text == s) with
  | some r => some (.role r)
  | none =>
    match s.toList with
    | '0' :: 'h' :: h =>
      let f := Field.digest (String.ofList h)
      if f.valid then some f else none
    | cs =>
      let ds := cs.takeWhile Char.isDigit
      let n := decimal ds
      match cs.drop ds.length with
      | [] => n.map (.int ·)
      | ['n'] => n.bind fun k => if k == 0 then none else some (.int (-k))
      | ['c'] => n.map .call
      | ['v'] => n.map .version
      | ['t'] => n.map .temp
      | ['b'] => n.bind fun k => if k ≤ 1 then some (.bool (k == 1)) else none
      | _ => none

def decodeField (s : String) : Option Field :=
  if userField s then some (.user s) else madeField s

/-! The inverse of `encode` on valid names. Any other text gives `none`. -/
def decode (s : String) : Option Name :=
  match s.splitOn "$" with
  | [h, "0k"] => if Core.keywords.contains h then some ⟨h, []⟩ else none
  | h :: rest => do
    let p : Name := ⟨h, ← rest.mapM decodeField⟩
    if userField h && !keyword p then some p else none
  | [] => none

/-!
A structural path. `outer` is its first user field. `inner` holds its other fields, the last
field first. A frame and each name inside it thus share their fields, so a new name costs one
step and no copy.
-/
structure Path where
  outer : String
  inner : List Field
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

def Path.push (p : Path) (f : Field) : Path := { p with inner := f :: p.inner }

/-! The path of the user field `u` in the frame `p`. The root frame is `none`. -/
def Path.child : Option Path → String → Path
  | none, u => ⟨u, []⟩
  | some p, u => p.push (.user u)

/-! The name of a path. It reverses the inner fields, so the lowering charges its fields. -/
def Path.name (p : Path) : Name := ⟨p.outer, p.inner.reverse⟩

/-! The first 16 hexadecimal digits of the SHA-256 of `s`: the digest of section 7.1. -/
def sha16 (s : String) : String := (Sha256.hex (Sha256.hash s.toUTF8)).take 16 |>.toString

/-! The readable token of an argument. An integer above 256 bits has more than 64 digits. -/
def readable : Value → Option Field
  | .int n => if n.natAbs.log2 < 256 then some (.int n) else none
  | .bool b => some (.bool b)
  | _ => none

/-! The byte length of `encode p` for a name with a field after its first one. -/
def multiSize (p : Name) : Nat :=
  p.rest.foldl (fun n f => n + 1 + (f.encode).utf8ByteSize) p.head.utf8ByteSize

/-! The byte length of `encode p`, known in time linear in the number of fields. -/
def byteSize (p : Name) : Nat := if keyword p then p.head.utf8ByteSize + 3 else multiSize p

/-!
The emitted module name of section 7.1 with the digest function `digest`. `serial` is the
serialization of `id`. The size test reads the module name only for its byte length, so a
long name costs no work here.
-/
def moduleName (digest : String → String) (id : InstantiationId)
    (serial : String := id.serialize) : Name :=
  let hashed : Name := ⟨id.module, [.digest (digest serial)]⟩
  match id.args.mapM readable with
  | some fs =>
    let p : Name := ⟨id.module, fs⟩
    if byteSize p ≤ 64 then p else hashed
  | none => hashed

end Silicon.Source.Names
