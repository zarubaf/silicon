-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Value
import Silicon.Source.Print

/-!
The static values of slice 1 and the static containers, types, and records of slice 2, their
canonical serialization, their recursive size, and their depth. Section 7.1 of the front-end spec
uses the serialization in an `InstantiationId`. Section 5.4 uses the recursive size in the cost
model, and section 5.5 bounds the depth. The Rust front end copies all three byte for byte.

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
- A type has the size 1 for its node, plus the size of each integer in it. A struct type has
  the size 1 plus the sizes of its static arguments, because its identity is nominal.
- An array value keeps its element type, so an empty array serializes and has a type. Its size
  does not count the element type (section 5.4). A record keeps its struct type for the same
  reason, and its size does not count the type either.
- A list keeps its element type as an array does, with the same size and depth rules. It
  serializes as `(list <type> (<element> ...))`, and `List[T]` as `(list <type>)`.
- The depth of an array value counts its element type, and the depth of a record counts its
  struct type. The depth of a type value is the depth of the type. Thus the depth bounds each
  walk over the value, also over an empty array and a record without fields.
- A function type keeps the `mut` mark of each parameter type. It serializes as
  `(fn (<param> ...) <type>)`, and a parameter with the mark as `(mut <type>)`. Its size counts
  each `mut` mark as one node.
- A function value is its item and its signature, so it has a type. It serializes as
  `(function root <item>)`, has the size 1 and the depth 1, and is not a container.
- A struct type holds the number of its specialization, and a function value the index of its
  item. These numbers do not serialize, print, or add to the size. A key and an equality of
  types compare them in place of the names (`Ty.cmp`), as the Rust ids do.
-/
namespace Silicon.Source

/-!
The type metadata of section 5.4. It holds the bit width as hardware data, the leaf count, the
recursive size of the zero value, and the depth. It also tells if the type is hardware data.
The function flag tells if a function type is a part of the type at any depth. A struct type
stores it, so no operation walks the field types again. The three numbers of a type that is not
hardware data have no meaning. Both front ends set them equally, so they charge the same.
-/
structure Meta where
  width : Nat
  leaves : Nat
  zeroSize : Nat
  depth : Nat
  data : Bool
  funcs : Bool
  deriving Repr, DecidableEq, BEq, Inhabited

mutual
  /--
  A type as a static value. Its forms are the scalar types of slice 1 with a static width and
  the types of the static containers of slice 2. `Type` and the struct types are forms too. A
  tuple type has at least one element type: `()` is `unit`. A struct type is the number of its
  entry in the table of specializations, its item, its static arguments, and its metadata.
  `String` and `List[T]` are static types only. A function type is its parameter types with
  their `mut` marks, and its result type.
  -/
  inductive Ty where
    | bool | nat | int
    | uint (width : Nat)
    | sint (width : Nat)
    | unit
    | type
    | array (elem : Ty) (len : Nat)
    | tuple (elems : Array Ty)
    | struct (spec : Nat) (item : String) (args : Array Value) (info : Meta)
    | string
    | list (elem : Ty)
    | fn (params : Array TyParam) (ret : Ty)

  /-- A parameter type of a function type, with its `mut` mark. -/
  inductive TyParam where
    | mk (mutable : Bool) (ty : Ty)

  /--
  A static value of slice 1, or a static container of slice 2. An array keeps its element type,
  and a record keeps its struct type. A tuple has at least one element: `()` is `unit`. A list
  keeps its element type, as an array does. A function value is a function item, by its index
  and its name, with its signature.
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
    | record (ty : Ty) (fields : Array Value)
    | list (elem : Ty) (elems : Array Value)
    | function (item : Nat) (name : String) (params : Array TyParam) (ret : Ty)
end

deriving instance Repr for Ty, TyParam, Value

instance : Inhabited Ty := ⟨.unit⟩
instance : Inhabited Value := ⟨.unit⟩

/-! A nested type has no derived `DecidableEq`. This structural test gives it. -/
mutual
  def Ty.beq : Ty → Ty → Bool
    | .bool, .bool | .nat, .nat | .int, .int | .unit, .unit | .type, .type
    | .string, .string => true
    | .uint a, .uint b | .sint a, .sint b => a == b
    | .array s n, .array t m => Ty.beq s t && n == m
    | .list s, .list t => Ty.beq s t
    | .tuple ⟨xs⟩, .tuple ⟨ys⟩ => Ty.beqs xs ys
    | .struct a i ⟨xs⟩ m, .struct b j ⟨ys⟩ n =>
      a == b && i == j && Value.beqs xs ys && decide (m = n)
    | .fn ⟨ps⟩ r, .fn ⟨qs⟩ s => TyParam.beqs ps qs && Ty.beq r s
    | _, _ => false

  def Ty.beqs : List Ty → List Ty → Bool
    | [], [] => true
    | x :: xs, y :: ys => Ty.beq x y && Ty.beqs xs ys
    | _, _ => false

  def TyParam.beqs : List TyParam → List TyParam → Bool
    | [], [] => true
    | .mk m s :: ps, .mk n t :: qs => m == n && Ty.beq s t && TyParam.beqs ps qs
    | _, _ => false

  def Value.beq : Value → Value → Bool
    | .int a, .int b => a == b
    | .bool a, .bool b => a == b
    | .str a, .str b => a == b
    | .uint w x, .uint v y | .sint w x, .sint v y => w == v && x.toNat == y.toNat
    | .type s, .type t => Ty.beq s t
    | .unit, .unit => true
    | .array s ⟨xs⟩, .array t ⟨ys⟩ => Ty.beq s t && Value.beqs xs ys
    | .tuple ⟨xs⟩, .tuple ⟨ys⟩ => Value.beqs xs ys
    | .record s ⟨xs⟩, .record t ⟨ys⟩ | .list s ⟨xs⟩, .list t ⟨ys⟩ =>
      Ty.beq s t && Value.beqs xs ys
    | .function a i ⟨ps⟩ r, .function b j ⟨qs⟩ s =>
      a == b && i == j && TyParam.beqs ps qs && Ty.beq r s
    | _, _ => false

  def Value.beqs : List Value → List Value → Bool
    | [], [] => true
    | x :: xs, y :: ys => Value.beq x y && Value.beqs xs ys
    | _, _ => false
end

mutual
  theorem Ty.eq_of_beq : ∀ a b : Ty, a.beq b = true → a = b
    | .bool, b, h | .nat, b, h | .int, b, h | .unit, b, h | .type, b, h | .uint _, b, h
    | .sint _, b, h | .string, b, h => by
      cases b <;> simp_all [Ty.beq]
    | .array s n, b, h => by
      cases b <;> simp [Ty.beq] at h ⊢
      exact ⟨Ty.eq_of_beq _ _ h.1, h.2⟩
    | .list s, b, h => by
      cases b <;> simp [Ty.beq] at h ⊢
      exact Ty.eq_of_beq _ _ h
    | .tuple ⟨xs⟩, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | ⟨⟨ys⟩⟩ | ⟨_, _, ⟨ys⟩, _⟩ | _ | _ | _ <;>
        simp [Ty.beq] at h ⊢
      rw [Ty.eqs_of_beqs _ _ h]
    | .struct _ _ ⟨xs⟩ _, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | ⟨⟨ys⟩⟩ | ⟨_, _, ⟨ys⟩, _⟩ | _ | _ | _ <;>
        simp [Ty.beq] at h ⊢
      exact ⟨h.1.1.1, h.1.1.2, by rw [Value.eqs_of_beqs _ _ h.1.2], h.2⟩
    | .fn ⟨ps⟩ _, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨⟨qs⟩, _⟩ <;>
        simp [Ty.beq] at h ⊢
      exact ⟨by rw [TyParam.eqs_of_beqs _ _ h.1], Ty.eq_of_beq _ _ h.2⟩

  theorem Ty.eqs_of_beqs : ∀ xs ys : List Ty, Ty.beqs xs ys = true → xs = ys
    | [], ys, h => by cases ys <;> simp_all [Ty.beqs]
    | x :: xs, ys, h => by
      cases ys <;> simp [Ty.beqs] at h ⊢
      exact ⟨Ty.eq_of_beq _ _ h.1, Ty.eqs_of_beqs _ _ h.2⟩

  theorem TyParam.eqs_of_beqs : ∀ ps qs : List TyParam, TyParam.beqs ps qs = true → ps = qs
    | [], qs, h => by cases qs <;> simp_all [TyParam.beqs]
    | .mk _ _ :: ps, qs, h => by
      rcases qs with _ | ⟨⟨_, _⟩, qs⟩ <;> simp [TyParam.beqs] at h ⊢
      exact ⟨⟨h.1.1, Ty.eq_of_beq _ _ h.1.2⟩, TyParam.eqs_of_beqs _ _ h.2⟩

  theorem Value.eq_of_beq : ∀ a b : Value, a.beq b = true → a = b
    | .int _, b, h | .bool _, b, h | .str _, b, h | .unit, b, h => by
      cases b <;> simp_all [Value.beq]
    | .type _, b, h => by
      cases b <;> simp [Value.beq] at h ⊢
      exact Ty.eq_of_beq _ _ h
    | .uint _ x, b, h | .sint _ x, b, h => by
      cases b <;> simp [Value.beq] at h ⊢
      obtain ⟨rfl, h⟩ := h
      exact ⟨rfl, heq_of_eq (BitVec.eq_of_toNat_eq h)⟩
    | .array _ ⟨xs⟩, b, h | .record _ ⟨xs⟩, b, h | .list _ ⟨xs⟩, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | ⟨_, ⟨ys⟩⟩ | ⟨⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | _ <;>
        simp [Value.beq] at h ⊢
      exact ⟨Ty.eq_of_beq _ _ h.1, by rw [Value.eqs_of_beqs _ _ h.2]⟩
    | .tuple ⟨xs⟩, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | ⟨_, ⟨ys⟩⟩ | ⟨⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | _ <;>
        simp [Value.beq] at h ⊢
      rw [Value.eqs_of_beqs _ _ h]
    | .function _ _ ⟨ps⟩ _, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, ⟨qs⟩, _⟩ <;>
        simp [Value.beq] at h ⊢
      exact ⟨h.1.1.1, h.1.1.2, by rw [TyParam.eqs_of_beqs _ _ h.1.2], Ty.eq_of_beq _ _ h.2⟩

  theorem Value.eqs_of_beqs : ∀ xs ys : List Value, Value.beqs xs ys = true → xs = ys
    | [], ys, h => by cases ys <;> simp_all [Value.beqs]
    | x :: xs, ys, h => by
      cases ys <;> simp [Value.beqs] at h ⊢
      exact ⟨Value.eq_of_beq _ _ h.1, Value.eqs_of_beqs _ _ h.2⟩
end

mutual
  theorem Ty.beq_self : ∀ a : Ty, a.beq a = true
    | .bool | .nat | .int | .unit | .type | .uint _ | .sint _ | .string => by simp [Ty.beq]
    | .array s _ | .list s => by simp [Ty.beq, Ty.beq_self s]
    | .tuple ⟨xs⟩ => by simp [Ty.beq, Ty.beqs_self xs]
    | .struct _ _ ⟨xs⟩ _ => by simp [Ty.beq, Value.beqs_self xs]
    | .fn ⟨ps⟩ r => by simp [Ty.beq, TyParam.beqs_self ps, Ty.beq_self r]

  theorem Ty.beqs_self : ∀ xs : List Ty, Ty.beqs xs xs = true
    | [] => by simp [Ty.beqs]
    | x :: xs => by simp [Ty.beqs, Ty.beq_self x, Ty.beqs_self xs]

  theorem TyParam.beqs_self : ∀ ps : List TyParam, TyParam.beqs ps ps = true
    | [] => by simp [TyParam.beqs]
    | .mk _ t :: ps => by simp [TyParam.beqs, Ty.beq_self t, TyParam.beqs_self ps]

  theorem Value.beq_self : ∀ a : Value, a.beq a = true
    | .int _ | .bool _ | .str _ | .uint .. | .sint .. | .unit => by simp [Value.beq]
    | .type t => by simp [Value.beq, Ty.beq_self t]
    | .array t ⟨xs⟩ | .record t ⟨xs⟩ | .list t ⟨xs⟩ => by
      simp [Value.beq, Ty.beq_self t, Value.beqs_self xs]
    | .tuple ⟨xs⟩ => by simp [Value.beq, Value.beqs_self xs]
    | .function _ _ ⟨ps⟩ r => by simp [Value.beq, TyParam.beqs_self ps, Ty.beq_self r]

  theorem Value.beqs_self : ∀ xs : List Value, Value.beqs xs xs = true
    | [] => by simp [Value.beqs]
    | x :: xs => by simp [Value.beqs, Value.beq_self x, Value.beqs_self xs]
end

instance : DecidableEq Ty := fun a b =>
  if h : a.beq b then isTrue (Ty.eq_of_beq a b h)
  else isFalse fun e => h (e ▸ Ty.beq_self a)

instance : DecidableEq Value := fun a b =>
  if h : a.beq b then isTrue (Value.eq_of_beq a b h)
  else isFalse fun e => h (e ▸ Value.beq_self a)

/-! The number of the form of a type and of a value, for an order between two forms. -/
def Ty.form : Ty → Nat
  | .bool => 0 | .nat => 1 | .int => 2 | .uint _ => 3 | .sint _ => 4 | .unit => 5 | .type => 6
  | .array .. => 7 | .tuple _ => 8 | .struct .. => 9 | .string => 10 | .list _ => 11
  | .fn .. => 12

def Value.form : Value → Nat
  | .int _ => 0 | .bool _ => 1 | .str _ => 2 | .uint .. => 3 | .sint .. => 4 | .type _ => 5
  | .unit => 6 | .array .. => 7 | .tuple _ => 8 | .record .. => 9 | .list _ _ => 10
  | .function .. => 11

/-!
An order of types and values by their numbers (section 5.6). A struct type compares by the
number of its specialization, and a function value by the number of its item. Each number fixes
the rest of its term, so the order compares no name. Each other part compares in full, so the
work is at most the smaller size, plus the element types of arrays and lists.
-/
mutual
  def Ty.cmp : Ty → Ty → Ordering
    | .uint a, .uint b | .sint a, .sint b => compare a b
    | .array s n, .array t m => (Ty.cmp s t).then (compare n m)
    | .list s, .list t => Ty.cmp s t
    | .tuple ⟨xs⟩, .tuple ⟨ys⟩ => Ty.cmps xs ys
    | .struct a .., .struct b .. => compare a b
    | .fn ⟨ps⟩ r, .fn ⟨qs⟩ s => (TyParam.cmps ps qs).then (Ty.cmp r s)
    | s, t => compare s.form t.form

  def Ty.cmps : List Ty → List Ty → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | x :: xs, y :: ys => (Ty.cmp x y).then (Ty.cmps xs ys)

  def TyParam.cmps : List TyParam → List TyParam → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | .mk m s :: ps, .mk n t :: qs =>
      (compare m n).then ((Ty.cmp s t).then (TyParam.cmps ps qs))

  def Value.cmp : Value → Value → Ordering
    | .int a, .int b => compare a b
    | .bool a, .bool b => compare a b
    | .str a, .str b => compare a b
    | .uint w x, .uint v y | .sint w x, .sint v y => (compare w v).then (compare x.toNat y.toNat)
    | .type s, .type t => Ty.cmp s t
    | .array s ⟨xs⟩, .array t ⟨ys⟩ | .record s ⟨xs⟩, .record t ⟨ys⟩
    | .list s ⟨xs⟩, .list t ⟨ys⟩ => (Ty.cmp s t).then (Value.cmps xs ys)
    | .tuple ⟨xs⟩, .tuple ⟨ys⟩ => Value.cmps xs ys
    | .function a .., .function b .. => compare a b
    | x, y => compare x.form y.form

  def Value.cmps : List Value → List Value → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | x :: xs, y :: ys => (Value.cmp x y).then (Value.cmps xs ys)
end

/-!
The equality of two types by their numbers. For the types of one evaluation it agrees with `=`,
because a struct type comes only from its entry in the table of specializations.
-/
def Ty.same (s t : Ty) : Bool := Ty.cmp s t == .eq

/-! The size of an integer: 1 for each 64-bit word of its magnitude, and at least 1. -/
def intSize (n : Int) : Nat := n.natAbs.log2 / 64 + 1

/-! The size of a finite value: 1 for each 64-bit word of its width, and at least 1. -/
def widthSize (width : Nat) : Nat := max 1 ((width + 63) / 64)

/-! A finite type: `UInt[W]` or `SInt[W]`. -/
def Ty.finite : Ty → Bool
  | .uint _ | .sint _ => true
  | _ => false

/-!
The metadata of the scalar types. `Bool`, `UInt[W]`, `SInt[W]`, and `Unit` are hardware data.
`Unit` has no bit and no leaf, and its zero `()` has the size 1. `Nat`, `Int`, `Type`, and
`String` are not hardware data, and their three numbers are 0. `List[T]` is not hardware data
either. Its depth is 1 more than the depth of `T`, so its metadata reads only that depth. No
scalar type holds a function type.
-/
def Meta.bool : Meta := ⟨1, 1, 1, 1, true, false⟩
def Meta.finite (width : Nat) : Meta := ⟨width, 1, widthSize width, 1, true, false⟩
def Meta.unit : Meta := ⟨0, 0, 1, 1, true, false⟩
def Meta.static : Meta := ⟨0, 0, 0, 1, false, false⟩

/-!
The metadata of `[T; N]` from the metadata `m` of `T`: the product rule of section 5.4. The zero
value is a node with `N` zeros of `T`.
-/
def Meta.array (m : Meta) (n : Nat) : Meta :=
  ⟨n * m.width, n * m.leaves, 1 + n * m.zeroSize, 1 + m.depth, m.data, m.funcs⟩

/-!
The charge of `Meta.array m n`, at the node of `[T; N]` before the type exists. Each of the three
products charges as a multiplication of static integers: the product of the two sizes.
-/
def Meta.arrayCharge (m : Meta) (n : Nat) : Nat :=
  intSize n * (intSize m.width + intSize m.leaves + intSize m.zeroSize)

/-!
The sums of the parts of a tuple or a record. The zero value is a node with the zero of each
part. The depth is 1 more than the deepest part and each extra depth in `extra`.
-/
def Meta.sum (parts : List Meta) (extra : List Nat) : Meta :=
  ⟨(parts.map (·.width)).sum, (parts.map (·.leaves)).sum, 1 + (parts.map (·.zeroSize)).sum,
   1 + ((parts.map (·.depth)) ++ extra).foldl max 0, parts.all (·.data), parts.any (·.funcs)⟩

/-! The metadata of a tuple type from the metadata of its element types. -/
def Meta.tuple (elems : List Meta) : Meta := Meta.sum elems []

/-!
The metadata of a struct specialization. It is made once, when the specialization completes.
It uses the stored metadata of the field types and the depths of the static arguments (section
5.5). A struct without fields
is hardware data with no bit and no leaf (decision Q4 of issue #178).
-/
def Meta.struct (fields : List Meta) (argDepths : List Nat) : Meta := Meta.sum fields argDepths

/-!
The metadata of a function type from the metadata of its parameter types and its result type.
It is not hardware data, so its three numbers are 0. Its depth is 1 more than the deepest part,
and a `mut` mark adds no depth. It sets the function flag.
-/
def Meta.fn (params : List Meta) (ret : Meta) : Meta :=
  ⟨0, 0, 0, 1 + ((params.map (·.depth)).foldl max ret.depth), false, true⟩

/-! The sizes of the four integers of `m`. A type constructor that makes them charges this. -/
def Meta.intCharge (m : Meta) : Nat :=
  intSize m.width + intSize m.leaves + intSize m.zeroSize + intSize m.depth

/-!
The charge of the reads of `Meta.sum parts _`: the sizes of the four integers of each part. It
bounds the work of the additions, so it comes before them.
-/
def Meta.readCharge (parts : List Meta) : Nat := (parts.map Meta.intCharge).sum

/-!
The metadata of a type. A type constructor computes it from its parts. A struct type stores
it, so this walk never enters the field types of a struct.
-/
mutual
  def Ty.info : Ty → Meta
    | .bool => Meta.bool
    | .uint w | .sint w => Meta.finite w
    | .unit => Meta.unit
    | .nat | .int | .type | .string => Meta.static
    | .list t => { Meta.static with depth := 1 + t.info.depth, funcs := t.info.funcs }
    | .array t n => t.info.array n
    | .tuple ⟨ts⟩ => Meta.tuple (Ty.infoAll ts)
    | .struct _ _ _ m => m
    | .fn ⟨ps⟩ r => Meta.fn (TyParam.infoAll ps) r.info

  def Ty.infoAll : List Ty → List Meta
    | [] => []
    | t :: ts => t.info :: Ty.infoAll ts

  def TyParam.infoAll : List TyParam → List Meta
    | [] => []
    | .mk _ t :: ps => t.info :: TyParam.infoAll ps
end

/-! The canonical serialization of section 7.1. -/
mutual
  def Ty.serialize : Ty → String
    | .bool => "bool"
    | .nat => "nat"
    | .int => "int"
    | .uint w => Print.node "uint" [toString w]
    | .sint w => Print.node "sint" [toString w]
    | .unit => "unit"
    | .type => "type"
    | .array t n => Print.node "array" [t.serialize, toString n]
    | .tuple ⟨ts⟩ => Print.node "tuple" [Print.list (Ty.serializeAll ts)]
    | .struct _ i ⟨xs⟩ _ => Print.node "struct" ["root", i, Print.list (Value.serializeAll xs)]
    | .string => "string"
    | .list t => Print.node "list" [t.serialize]
    | .fn ⟨ps⟩ r => Print.node "fn" [Print.list (TyParam.serializeAll ps), r.serialize]

  def Ty.serializeAll : List Ty → List String
    | [] => []
    | t :: ts => t.serialize :: Ty.serializeAll ts

  def TyParam.serializeAll : List TyParam → List String
    | [] => []
    | .mk m t :: ps =>
      (if m then Print.node "mut" [t.serialize] else t.serialize) :: TyParam.serializeAll ps

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
    | .record t ⟨xs⟩ => Print.node "record" [t.serialize, Print.list (Value.serializeAll xs)]
    | .list t ⟨xs⟩ => Print.node "list" [t.serialize, Print.list (Value.serializeAll xs)]
    | .function _ i _ _ => Print.node "function" ["root", i]

  def Value.serializeAll : List Value → List String
    | [] => []
    | x :: xs => x.serialize :: Value.serializeAll xs
end

/-!
The recursive size of section 5.4. A type has the number of nodes of its term. Each integer and
each static argument in it adds its size. Each `mut` mark of a function type is one more node. A
named function has the size 1.
-/
mutual
  def Ty.size : Ty → Nat
    | .bool | .nat | .int | .unit | .type | .string => 1
    | .uint w | .sint w => 1 + intSize w
    | .array t n => 1 + t.size + intSize n
    | .list t => 1 + t.size
    | .tuple ⟨ts⟩ => 1 + Ty.sizeAll ts
    | .struct _ _ ⟨xs⟩ _ => 1 + Value.sizeAll xs
    | .fn ⟨ps⟩ r => 1 + TyParam.sizeAll ps + r.size

  def Ty.sizeAll : List Ty → Nat
    | [] => 0
    | t :: ts => t.size + Ty.sizeAll ts

  def TyParam.sizeAll : List TyParam → Nat
    | [] => 0
    | .mk m t :: ps => (if m then 1 else 0) + t.size + TyParam.sizeAll ps

  def Value.size : Value → Nat
    | .int n => intSize n
    | .bool _ | .unit | .function .. => 1
    | .str s => 1 + s.length
    | .uint w _ | .sint w _ => widthSize w
    | .type t => t.size
    | .array _ ⟨xs⟩ | .tuple ⟨xs⟩ | .record _ ⟨xs⟩ | .list _ ⟨xs⟩ => 1 + Value.sizeAll xs

  def Value.sizeAll : List Value → Nat
    | [] => 0
    | x :: xs => x.size + Value.sizeAll xs
end

/-!
The depth of section 5.5: 1 for a scalar type, and 1 more than its deepest part. A struct type
has its stored depth, which counts its field types and its static arguments. A `mut` mark adds no
depth.
-/
mutual
  def Ty.depth : Ty → Nat
    | .array t _ | .list t => 1 + t.depth
    | .tuple ⟨ts⟩ => 1 + Ty.depthAll ts
    | .struct _ _ _ m => m.depth
    | .fn ⟨ps⟩ r => 1 + max (TyParam.depthAll ps) r.depth
    | _ => 1

  def Ty.depthAll : List Ty → Nat
    | [] => 0
    | t :: ts => max t.depth (Ty.depthAll ts)

  def TyParam.depthAll : List TyParam → Nat
    | [] => 0
    | .mk _ t :: ps => max t.depth (TyParam.depthAll ps)
end

/-! The depth of section 5.5: 1 for a scalar value, and 1 more than its deepest part. -/
mutual
  def Value.depth : Value → Nat
    | .type t => t.depth
    | .array t ⟨xs⟩ | .record t ⟨xs⟩ | .list t ⟨xs⟩ => 1 + max t.depth (Value.depthAll xs)
    | .tuple ⟨xs⟩ => 1 + Value.depthAll xs
    | _ => 1

  def Value.depthAll : List Value → Nat
    | [] => 0
    | x :: xs => max x.depth (Value.depthAll xs)
end

/-!
The depth of the zero value of a hardware data type, from the type alone. An array of length 0
has the depth of its type, and another array 1 more than the zero of its element. A record is
1 deeper than its struct type, because the depth of a record counts its type. Thus this walk
never enters the field types of a struct. It gives the depth of section 5.5 of `T()`.
-/
mutual
  def Ty.zeroDepth : Ty → Nat
    | .array t 0 => 1 + t.depth
    | .array t _ => 1 + t.zeroDepth
    | .tuple ⟨ts⟩ => 1 + Ty.zeroDepthAll ts
    | t@(.struct ..) => 1 + t.depth
    | _ => 1

  def Ty.zeroDepthAll : List Ty → Nat
    | [] => 0
    | t :: ts => max t.zeroDepth (Ty.zeroDepthAll ts)
end

/-!
The text of a type in a message, and the source text of a static argument in it. A struct type
prints its item, with its arguments in brackets when it has any: `P[8]`. A function type prints
in its source form, and a function value prints its item.
-/
mutual
  def Ty.text : Ty → String
    | .bool => "Bool" | .nat => "Nat" | .int => "Int"
    | .uint w => s!"UInt[{w}]" | .sint w => s!"SInt[{w}]"
    | .unit => "Unit"
    | .type => "Type"
    | .array t n => s!"[{t.text}; {n}]"
    | .tuple ⟨[t]⟩ => s!"({t.text},)"
    | .tuple ⟨ts⟩ => "(" ++ ", ".intercalate (Ty.textAll ts) ++ ")"
    | .struct _ i ⟨[]⟩ _ => i
    | .struct _ i ⟨xs⟩ _ => i ++ "[" ++ ", ".intercalate (Value.literalAll xs) ++ "]"
    | .string => "String"
    | .list t => s!"List[{t.text}]"
    | .fn ⟨ps⟩ r => Print.fnText (TyParam.textAll ps) r.text

  def Ty.textAll : List Ty → List String
    | [] => []
    | t :: ts => t.text :: Ty.textAll ts

  def TyParam.textAll : List TyParam → List String
    | [] => []
    | .mk m t :: ps => ((if m then "mut " else "") ++ t.text) :: TyParam.textAll ps

  def Value.literal : Value → String
    | .int n => toString n
    | .bool b => Print.boolean b
    | .str s => Print.quote s
    | .uint _ v => toString v.toNat
    | .sint _ v => toString v.toInt
    | .type t => t.text
    | .unit => "()"
    | .array _ ⟨xs⟩ => "[" ++ ", ".intercalate (Value.literalAll xs) ++ "]"
    | .tuple ⟨[x]⟩ => s!"({x.literal},)"
    | .tuple ⟨xs⟩ => "(" ++ ", ".intercalate (Value.literalAll xs) ++ ")"
    | .record t ⟨xs⟩ => t.text ++ "(" ++ ", ".intercalate (Value.literalAll xs) ++ ")"
    | .list t ⟨[]⟩ => s!"list({t.text})"
    | .list _ ⟨xs⟩ => "[" ++ ", ".intercalate (Value.literalAll xs) ++ "]"
    | .function _ i _ _ => i

  def Value.literalAll : List Value → List String
    | [] => []
    | x :: xs => x.literal :: Value.literalAll xs
end

/-! The type of a value. A type value has the type `Type`, and a function its signature. -/
mutual
  def Value.ty? : Value → Option Ty
    | .int _ => some .int
    | .bool _ => some .bool
    | .uint w _ => some (.uint w)
    | .sint w _ => some (.sint w)
    | .unit => some .unit
    | .array t xs => some (.array t xs.size)
    | .tuple ⟨xs⟩ => (Value.tyAll? xs).map fun ts => .tuple ts.toArray
    | .record t _ => some t
    | .type _ => some .type
    | .str _ => some .string
    | .list t _ => some (.list t)
    | .function _ _ ps r => some (.fn ps r)

  def Value.tyAll? : List Value → Option (List Ty)
    | [] => some []
    | x :: xs => do return (← x.ty?) :: (← Value.tyAll? xs)
end

/-! The text of a value in a message: its type, or its own text for a string and a type. -/
def Value.text : Value → String
  | .str _ => "a string"
  | .type _ => "a type"
  | v => (v.ty?.map Ty.text).getD "a tuple"

def Value.finiteTy? : Value → Option Ty
  | .uint w _ => some (.uint w)
  | .sint w _ => some (.sint w)
  | _ => none

/-!
The charge of the walk that measures the serialization of a value, before the charge of its
bytes (section 5.4). Each array, tuple, record, and list charges 1. Each integer and each
finite value charge the square of their size, because a naive decimal conversion takes this
time. A scalar thus keeps the charge of slice 1. A type charges nothing: an integer in a type
gets no charge for its decimal form.
-/
mutual
  def Value.measureCharge : Value → Nat
    | v@(.int _) | v@(.uint ..) | v@(.sint ..) => v.size * v.size
    | .array _ ⟨xs⟩ | .tuple ⟨xs⟩ | .record _ ⟨xs⟩ | .list _ ⟨xs⟩ =>
      1 + Value.measureChargeAll xs
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
