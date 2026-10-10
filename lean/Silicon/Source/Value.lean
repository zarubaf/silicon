import Silicon.Core.Semantics.Value
import Silicon.Source.Print

/-!
The static values of slice 1, their canonical serialization, and their recursive size. Section
7.1 of the front-end spec uses the serialization in an `InstantiationId`. Section 5.4 uses the
recursive size in the cost model. The Rust front end copies both byte for byte.

These rules settle the open points of the spec:

- A static value of type `Nat` or `Int` is an `int`. The type check keeps a `Nat` at zero or
  more. Thus the argument `8` of a `Nat` parameter serializes as `(int 8)`.
- A finite static value holds the `BitVec` of the core semantics, with the width of its type.
- A serialization is a node `(<form> <field> ...)`. One space separates two parts.
- An integer prints in decimal without leading zeros, with `-` before a negative value.
- A string prints with the escapes of the grammar, as in the AST dump. Thus the serialization
  is injective.
- A `UInt[W]` value prints its unsigned value, and an `SInt[W]` value prints its signed value.
- An integer has the size 1 for each 64-bit word of its magnitude, and at least 1.
- A finite value has the size 1 for each 64-bit word of its width, and at least 1. The width,
  not the value, sets the work of a finite operation.
- A type has the size 1 for its node, plus the size of its width as an integer.
-/
namespace Silicon.Source

/-! A type as a static value: the scalar types of slice 1 with a static width. -/
inductive Ty where
  | bool | nat | int
  | uint (width : Nat)
  | sint (width : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! A static value of slice 1. -/
inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  | str (value : String)
  | uint (width : Nat) (bits : Core.Semantics.Value width)
  | sint (width : Nat) (bits : Core.Semantics.Value width)
  | type (ty : Ty)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The size of an integer: 1 for each 64-bit word of its magnitude, and at least 1. -/
def intSize (n : Int) : Nat := n.natAbs.log2 / 64 + 1

/-! The size of a finite value: 1 for each 64-bit word of its width, and at least 1. -/
def widthSize (width : Nat) : Nat := max 1 ((width + 63) / 64)

/-! A finite type: `UInt[W]` or `SInt[W]`. -/
def Ty.finite : Ty → Bool
  | .uint _ | .sint _ => true
  | _ => false

def Ty.serialize : Ty → String
  | .bool => "bool"
  | .nat => "nat"
  | .int => "int"
  | .uint w => Print.node "uint" [toString w]
  | .sint w => Print.node "sint" [toString w]

/-! The number of nodes of the type term. A width counts as an integer payload. -/
def Ty.size : Ty → Nat
  | .bool | .nat | .int => 1
  | .uint w | .sint w => 1 + intSize w

def Ty.text : Ty → String
  | .bool => "Bool" | .nat => "Nat" | .int => "Int"
  | .uint w => s!"UInt[{w}]" | .sint w => s!"SInt[{w}]"

/-! The type of a value. A string and a type have no `Ty` in slice 1. -/
def Value.ty? : Value → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .uint w _ => some (.uint w)
  | .sint w _ => some (.sint w)
  | .str _ | .type _ => none

def Value.text : Value → String
  | .str _ => "a string"
  | .type _ => "a type"
  | v => (v.ty?.map Ty.text).getD ""

def Value.finiteTy? : Value → Option Ty
  | .uint w _ => some (.uint w)
  | .sint w _ => some (.sint w)
  | _ => none

/-! The canonical serialization of section 7.1. -/
def Value.serialize : Value → String
  | .int n => Print.node "int" [toString n]
  | .bool b => Print.node "bool" [Print.boolean b]
  | .str s => Print.node "string" [Print.quote s]
  | .uint w v => Print.node "uint" [toString w, toString v.toNat]
  | .sint w v => Print.node "sint" [toString w, toString v.toInt]
  | .type t => Print.node "type" [t.serialize]

/-! The recursive size of section 5.4. -/
def Value.size : Value → Nat
  | .int n => intSize n
  | .bool _ => 1
  | .str s => 1 + s.length
  | .uint w _ | .sint w _ => widthSize w
  | .type t => t.size

/-!
The charge of the decimal forms in the serialization of a value. An integer and a finite value
charge the square of their size (section 5.4). A naive decimal conversion takes this time.
-/
def Value.decimalCharge (v : Value) : Nat :=
  match v with
  | .int _ | .uint .. | .sint .. => v.size * v.size
  | _ => 0

/-!
An `InstantiationId`: a module and its static arguments in order. Up to slice 5, the package of
each module is the root package `root`.
-/
structure InstantiationId where
  module : String
  args : List Value
  deriving Repr, DecidableEq, BEq, Inhabited

/-! The serialization of an `InstantiationId` from the serializations of its arguments. -/
def InstantiationId.render (module : String) (args : List String) : String :=
  Print.node "instantiation" ["root", module, Print.list args]

/-! The byte length of `render module args`, known before the text exists. -/
def InstantiationId.renderSize (module : String) (args : List String) : Nat :=
  24 + module.utf8ByteSize + (args.map String.utf8ByteSize).sum + (args.length - 1)

def InstantiationId.serialize (id : InstantiationId) : String :=
  InstantiationId.render id.module (id.args.map Value.serialize)

end Silicon.Source
