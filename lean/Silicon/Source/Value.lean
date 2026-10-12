-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Value
import Silicon.Source.Print

/-!
The static values of slice 1 and the static containers of slice 2, their canonical
serialization, their recursive size, and their depth. Section 7.1 of the front-end spec uses the
serialization in an `InstantiationId`. Section 5.4 uses the recursive size in the cost model, and
section 5.5 bounds the depth. The Rust front end copies all three byte for byte.

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
- A type has the size 1 for its node, plus the size of each integer in it.
- An array value keeps its element type, so an empty array serializes and has a type. Its size
  does not count the element type (section 5.4).
- The depth of an array value counts its element type, and the depth of a type value is the
  depth of the type. Thus the depth bounds each walk over the value, also over an empty array.
-/
namespace Silicon.Source

/-!
A type as a static value. Its forms are the scalar types of slice 1 with a static width and
the types of the static containers of slice 2. A tuple type has at least one element type:
`()` is `unit`.
-/
inductive Ty where
  | bool | nat | int
  | uint (width : Nat)
  | sint (width : Nat)
  | unit
  | array (elem : Ty) (len : Nat)
  | tuple (elems : Array Ty)
  deriving Repr, Inhabited

/-!
A static value of slice 1, or a static container of slice 2. An array keeps its element type. A
tuple has at least one element: `()` is `unit`.
-/
inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  | str (value : String)
  | uint (width : Nat) (bits : Core.Semantics.Value width)
  | sint (width : Nat) (bits : Core.Semantics.Value width)
  | type (ty : Ty)
  | unit
  | array (elem : Ty) (elems : Array Value)
  | tuple (elems : Array Value)
  deriving Repr, Inhabited

/-! A nested type has no derived `DecidableEq`. This structural test gives it. -/
mutual
  def Ty.beq : Ty → Ty → Bool
    | .bool, .bool | .nat, .nat | .int, .int | .unit, .unit => true
    | .uint a, .uint b | .sint a, .sint b => a == b
    | .array s n, .array t m => Ty.beq s t && n == m
    | .tuple ⟨xs⟩, .tuple ⟨ys⟩ => Ty.beqs xs ys
    | _, _ => false

  def Ty.beqs : List Ty → List Ty → Bool
    | [], [] => true
    | x :: xs, y :: ys => Ty.beq x y && Ty.beqs xs ys
    | _, _ => false
end

mutual
  theorem Ty.eq_of_beq : ∀ a b : Ty, a.beq b = true → a = b
    | .bool, b, h | .nat, b, h | .int, b, h | .unit, b, h | .uint _, b, h | .sint _, b, h => by
      cases b <;> simp_all [Ty.beq]
    | .array s n, b, h => by
      cases b <;> simp [Ty.beq] at h ⊢
      exact ⟨Ty.eq_of_beq _ _ h.1, h.2⟩
    | .tuple ⟨xs⟩, b, h => by
      cases b <;> simp [Ty.beq] at h ⊢
      rw [Ty.eqs_of_beqs _ _ h]

  theorem Ty.eqs_of_beqs : ∀ xs ys : List Ty, Ty.beqs xs ys = true → xs = ys
    | [], ys, h => by cases ys <;> simp_all [Ty.beqs]
    | x :: xs, ys, h => by
      cases ys <;> simp [Ty.beqs] at h ⊢
      exact ⟨Ty.eq_of_beq _ _ h.1, Ty.eqs_of_beqs _ _ h.2⟩
end

mutual
  theorem Ty.beq_self : ∀ a : Ty, a.beq a = true
    | .bool | .nat | .int | .unit | .uint _ | .sint _ => by simp [Ty.beq]
    | .array s _ => by simp [Ty.beq, Ty.beq_self s]
    | .tuple ⟨xs⟩ => by simp [Ty.beq, Ty.beqs_self xs]

  theorem Ty.beqs_self : ∀ xs : List Ty, Ty.beqs xs xs = true
    | [] => by simp [Ty.beqs]
    | x :: xs => by simp [Ty.beqs, Ty.beq_self x, Ty.beqs_self xs]
end

instance : DecidableEq Ty := fun a b =>
  if h : a.beq b then isTrue (Ty.eq_of_beq a b h)
  else isFalse fun e => h (e ▸ Ty.beq_self a)

mutual
  def Value.beq : Value → Value → Bool
    | .int a, .int b => a == b
    | .bool a, .bool b => a == b
    | .str a, .str b => a == b
    | .uint w x, .uint v y | .sint w x, .sint v y => w == v && x.toNat == y.toNat
    | .type s, .type t => decide (s = t)
    | .unit, .unit => true
    | .array s ⟨xs⟩, .array t ⟨ys⟩ => decide (s = t) && Value.beqs xs ys
    | .tuple ⟨xs⟩, .tuple ⟨ys⟩ => Value.beqs xs ys
    | _, _ => false

  def Value.beqs : List Value → List Value → Bool
    | [], [] => true
    | x :: xs, y :: ys => Value.beq x y && Value.beqs xs ys
    | _, _ => false
end

mutual
  theorem Value.eq_of_beq : ∀ a b : Value, a.beq b = true → a = b
    | .int _, b, h | .bool _, b, h | .str _, b, h | .type _, b, h | .unit, b, h => by
      cases b <;> simp_all [Value.beq]
    | .uint _ x, b, h | .sint _ x, b, h => by
      cases b <;> simp [Value.beq] at h ⊢
      obtain ⟨rfl, h⟩ := h
      exact ⟨rfl, heq_of_eq (BitVec.eq_of_toNat_eq h)⟩
    | .array _ ⟨xs⟩, b, h => by
      cases b <;> simp [Value.beq] at h ⊢
      exact ⟨h.1, by rw [Value.eqs_of_beqs _ _ h.2]⟩
    | .tuple ⟨xs⟩, b, h => by
      cases b <;> simp [Value.beq] at h ⊢
      rw [Value.eqs_of_beqs _ _ h]

  theorem Value.eqs_of_beqs : ∀ xs ys : List Value, Value.beqs xs ys = true → xs = ys
    | [], ys, h => by cases ys <;> simp_all [Value.beqs]
    | x :: xs, ys, h => by
      cases ys <;> simp [Value.beqs] at h ⊢
      exact ⟨Value.eq_of_beq _ _ h.1, Value.eqs_of_beqs _ _ h.2⟩
end

mutual
  theorem Value.beq_self : ∀ a : Value, a.beq a = true
    | .int _ | .bool _ | .str _ | .uint .. | .sint .. | .type _ | .unit => by simp [Value.beq]
    | .array _ ⟨xs⟩ => by simp [Value.beq, Value.beqs_self xs]
    | .tuple ⟨xs⟩ => by simp [Value.beq, Value.beqs_self xs]

  theorem Value.beqs_self : ∀ xs : List Value, Value.beqs xs xs = true
    | [] => by simp [Value.beqs]
    | x :: xs => by simp [Value.beqs, Value.beq_self x, Value.beqs_self xs]
end

instance : DecidableEq Value := fun a b =>
  if h : a.beq b then isTrue (Value.eq_of_beq a b h)
  else isFalse fun e => h (e ▸ Value.beq_self a)

/-! The size of an integer: 1 for each 64-bit word of its magnitude, and at least 1. -/
def intSize (n : Int) : Nat := n.natAbs.log2 / 64 + 1

/-! The size of a finite value: 1 for each 64-bit word of its width, and at least 1. -/
def widthSize (width : Nat) : Nat := max 1 ((width + 63) / 64)

/-! A finite type: `UInt[W]` or `SInt[W]`. -/
def Ty.finite : Ty → Bool
  | .uint _ | .sint _ => true
  | _ => false

mutual
  def Ty.serialize : Ty → String
    | .bool => "bool"
    | .nat => "nat"
    | .int => "int"
    | .uint w => Print.node "uint" [toString w]
    | .sint w => Print.node "sint" [toString w]
    | .unit => "unit"
    | .array t n => Print.node "array" [t.serialize, toString n]
    | .tuple ⟨ts⟩ => Print.node "tuple" [Print.list (Ty.serializeAll ts)]

  def Ty.serializeAll : List Ty → List String
    | [] => []
    | t :: ts => t.serialize :: Ty.serializeAll ts
end

/-! The number of nodes of the type term, plus the size of each integer in it (section 5.4). -/
mutual
  def Ty.size : Ty → Nat
    | .bool | .nat | .int | .unit => 1
    | .uint w | .sint w => 1 + intSize w
    | .array t n => 1 + t.size + intSize n
    | .tuple ⟨ts⟩ => 1 + Ty.sizeAll ts

  def Ty.sizeAll : List Ty → Nat
    | [] => 0
    | t :: ts => t.size + Ty.sizeAll ts
end

/-! The depth of section 5.5: 1 for a scalar type, and 1 more than its deepest part. -/
mutual
  def Ty.depth : Ty → Nat
    | .array t _ => 1 + t.depth
    | .tuple ⟨ts⟩ => 1 + Ty.depthAll ts
    | _ => 1

  def Ty.depthAll : List Ty → Nat
    | [] => 0
    | t :: ts => max t.depth (Ty.depthAll ts)
end

mutual
  def Ty.text : Ty → String
    | .bool => "Bool" | .nat => "Nat" | .int => "Int"
    | .uint w => s!"UInt[{w}]" | .sint w => s!"SInt[{w}]"
    | .unit => "Unit"
    | .array t n => s!"[{t.text}; {n}]"
    | .tuple ⟨[t]⟩ => s!"({t.text},)"
    | .tuple ⟨ts⟩ => "(" ++ ", ".intercalate (Ty.textAll ts) ++ ")"

  def Ty.textAll : List Ty → List String
    | [] => []
    | t :: ts => t.text :: Ty.textAll ts
end

/-! The type of a value. A string, a type, and a tuple that holds them have no `Ty`. -/
mutual
  def Value.ty? : Value → Option Ty
    | .int _ => some .int
    | .bool _ => some .bool
    | .uint w _ => some (.uint w)
    | .sint w _ => some (.sint w)
    | .unit => some .unit
    | .array t xs => some (.array t xs.size)
    | .tuple ⟨xs⟩ => (Value.tyAll? xs).map fun ts => .tuple ts.toArray
    | .str _ | .type _ => none

  def Value.tyAll? : List Value → Option (List Ty)
    | [] => some []
    | x :: xs => do return (← x.ty?) :: (← Value.tyAll? xs)
end

/-! The text of a value in a message. Only a tuple has neither a `Ty` nor its own text. -/
def Value.text : Value → String
  | .str _ => "a string"
  | .type _ => "a type"
  | v => (v.ty?.map Ty.text).getD "a tuple"

def Value.finiteTy? : Value → Option Ty
  | .uint w _ => some (.uint w)
  | .sint w _ => some (.sint w)
  | _ => none

/-! The canonical serialization of section 7.1. -/
mutual
  def Value.serialize : Value → String
    | .int n => Print.node "int" [toString n]
    | .bool b => Print.node "bool" [Print.boolean b]
    | .str s => Print.node "string" [Print.quote s]
    | .uint w v => Print.node "uint" [toString w, toString v.toNat]
    | .sint w v => Print.node "sint" [toString w, toString v.toInt]
    | .type t => Print.node "type" [t.serialize]
    | .unit => "(unit)"
    | .array t ⟨xs⟩ => Print.node "array" [t.serialize, Print.list (Value.serializeAll xs)]
    | .tuple ⟨xs⟩ => Print.node "tuple" [Print.list (Value.serializeAll xs)]

  def Value.serializeAll : List Value → List String
    | [] => []
    | x :: xs => x.serialize :: Value.serializeAll xs
end

/-! The recursive size of section 5.4. -/
mutual
  def Value.size : Value → Nat
    | .int n => intSize n
    | .bool _ | .unit => 1
    | .str s => 1 + s.length
    | .uint w _ | .sint w _ => widthSize w
    | .type t => t.size
    | .array _ ⟨xs⟩ | .tuple ⟨xs⟩ => 1 + Value.sizeAll xs

  def Value.sizeAll : List Value → Nat
    | [] => 0
    | x :: xs => x.size + Value.sizeAll xs
end

/-! The depth of section 5.5: 1 for a scalar value, and 1 more than its deepest part. -/
mutual
  def Value.depth : Value → Nat
    | .type t => t.depth
    | .array t ⟨xs⟩ => 1 + max t.depth (Value.depthAll xs)
    | .tuple ⟨xs⟩ => 1 + Value.depthAll xs
    | _ => 1

  def Value.depthAll : List Value → Nat
    | [] => 0
    | x :: xs => max x.depth (Value.depthAll xs)
end

/-!
The charge of the walk that measures the serialization of a value, before the charge of its
bytes (section 5.4). Each array and each tuple charge 1. Each integer and each finite value
charge the square of their size, because a naive decimal conversion takes this time. A scalar
thus keeps the charge of slice 1.
-/
mutual
  def Value.measureCharge : Value → Nat
    | v@(.int _) | v@(.uint ..) | v@(.sint ..) => v.size * v.size
    | .array _ ⟨xs⟩ | .tuple ⟨xs⟩ => 1 + Value.measureChargeAll xs
    | _ => 0

  def Value.measureChargeAll : List Value → Nat
    | [] => 0
    | x :: xs => x.measureCharge + Value.measureChargeAll xs
end

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
