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
- A prelude struct has the token `prelude` in the place of `root`:
  `(struct prelude ReadResponse ((type (uint 8))))` or `(struct prelude PortKey ())`. A user
  struct with the same name thus has another serialization.
- A generated record type (origin `gen`) serializes each name and field type in order:
  `(gstruct (("a" (uint 8)) ("b" bool)))`, and `(gstruct ())` without fields. Its identity is
  structural, so its size is 1 plus the size of each name as a string and of each field type.
  Its depth is 1 plus the largest depth of a field type. A message prints it as
  `@Struct { a: UInt[8], b: Bool }`, or `@Struct {}` without fields. Each name has the limit of a
  string in a message (`strText`).
- An enum type holds the index of its item, its name, and its metadata. It serializes as
  `(enum root <name> ())`, has the size 1, and compares by its item. Its metadata is that of a
  record of `UInt[W]` and `UInt[P]`, without the second part when `P` is 0.
- A static enum value holds its type, its tag of `W` bits, and its payload of `P` bits. It is
  the one static form of an enum value (section 5.1). It serializes as
  `(enum <type> <tag> (uint P <payload>))`, without the payload when `P` is 0. Its size and its
  depth are those of a record with the parts `tag` and `payload`. In a message, its tag prints
  as its integer, because the value does not hold the name of a variant.
- A handle type `Reg[T]`, `Wire[T]`, `Input[T]`, or `Mem[T, N]` holds its parts. It
  serializes as `(reg <type>)`, `(wire <type>)`, `(input <type>)`, or `(mem <type> <N>)`.
  `Instance[M, args]` holds the index of the module item, its name, and its converted arguments.
  It serializes as `(instance root <name> (<argument> ...))`, the form of an `InstantiationId`.
  Its size is 1 plus the sizes of its arguments, as for a struct type.
- A text of a type or a value in a message has at most 1024 bytes and then `...`. Each integer
  in it is decimal up to 256 bits (section 5.5).
-/
namespace Silicon.Source

/-!
The type metadata of section 5.4. It holds the bit width as hardware data, the leaf count, the
recursive size of the zero value, and the depth. It also tells if the type is hardware data.
The function flag tells if a function type is a part of the type at any depth. The enum flag
tells the same for an enum type, and the handle flag for a handle type. A value of a type with
the handle flag is never static (section 5.1). A struct type stores the flags, so no operation
walks the field types again. The three numbers of a type that is not hardware data have no
meaning. Both front ends set them equally, so they charge the same.
-/
structure Meta where
  width : Nat
  leaves : Nat
  zeroSize : Nat
  depth : Nat
  data : Bool
  funcs : Bool
  enums : Bool
  handles : Bool
  deriving Repr, DecidableEq, BEq, Inhabited

/-!
The origin of a struct type (section 5.6): a struct item (`user`), a prelude struct
(`prelude`), or a generated record type of `@Struct` (`gen`).
-/
inductive Origin where
  | user
  | prelude
  | gen
  deriving Repr, DecidableEq, Inhabited

mutual
  /--
  A type as a static value. Its forms are the scalar types of slice 1 with a static width and
  the types of the static containers of slice 2. `Type` and the struct types are forms too. A
  tuple type has at least one element type: `()` is `unit`. A struct type is the number of its
  entry in the table of specializations, its item, its static arguments, its metadata, and its
  origin. The origin `prelude` marks a prelude struct (section 7.1). A generated record type
  has the origin `gen`, no item, and the name and the type of each field as its arguments, in
  the order `[name, type, ...]` (`Eval.genArgs`). An enum type is the
  index of its item, its name, and its metadata.
  `String` and `List[T]` are static types only. A function type is its parameter types with
  their `mut` marks, and its result type. The handle types `Reg[T]`, `Wire[T]`, `Input[T]`,
  `Mem[T, N]`, and `Instance[M, args]` are static types too (section 5.1). An instance type is
  the index of its module item, its name, and its converted arguments.
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
        (origin : Origin := .user)
    | string
    | list (elem : Ty)
    | fn (params : Array TyParam) (ret : Ty)
    | enum (item : Nat) (name : String) (info : Meta)
    | reg (data : Ty)
    | wire (data : Ty)
    | input (data : Ty)
    | mem (word : Ty) (depth : Nat)
    | inst (item : Nat) (name : String) (args : Array Value)

  /-- A parameter type of a function type, with its `mut` mark. -/
  inductive TyParam where
    | mk (mutable : Bool) (ty : Ty)

  /--
  A static value of slice 1, or a static container of slice 2. An array keeps its element type,
  and a record keeps its struct type. A tuple has at least one element: `()` is `unit`. A list
  keeps its element type, as an array does. A function value is a function item, by its index
  and its name, with its signature. An enum value holds its type, its tag of `w` bits, and its
  payload of `p` bits.
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
    | enum (ty : Ty) (w : Nat) (tag : Core.Semantics.Value w) (p : Nat)
        (payload : Core.Semantics.Value p)
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
    | .struct a i ⟨xs⟩ m e, .struct b j ⟨ys⟩ n f =>
      a == b && i == j && Value.beqs xs ys && decide (m = n) && e == f
    | .fn ⟨ps⟩ r, .fn ⟨qs⟩ s => TyParam.beqs ps qs && Ty.beq r s
    | .enum a i m, .enum b j n => a == b && i == j && decide (m = n)
    | .reg s, .reg t | .wire s, .wire t | .input s, .input t => Ty.beq s t
    | .mem s n, .mem t m => Ty.beq s t && n == m
    | .inst a i ⟨xs⟩, .inst b j ⟨ys⟩ => a == b && i == j && Value.beqs xs ys
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
    | .enum s w x p y, .enum t v x' q y' =>
      Ty.beq s t && w == v && x.toNat == x'.toNat && p == q && y.toNat == y'.toNat
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
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | ⟨⟨ys⟩⟩ | ⟨_, _, ⟨ys⟩, _, _⟩ | _ | _ | _ | _
        | _ | _ | _ | _ | ⟨_, _, ⟨ys⟩⟩ <;>
        simp [Ty.beq] at h ⊢
      rw [Ty.eqs_of_beqs _ _ h]
    | .struct _ _ ⟨xs⟩ _ _, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | ⟨⟨ys⟩⟩ | ⟨_, _, ⟨ys⟩, _, _⟩ | _ | _ | _ | _
        | _ | _ | _ | _ | ⟨_, _, ⟨ys⟩⟩ <;>
        simp [Ty.beq] at h ⊢
      exact ⟨h.1.1.1.1, h.1.1.1.2, by rw [Value.eqs_of_beqs _ _ h.1.1.2], h.1.2, h.2⟩
    | .fn ⟨ps⟩ _, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨⟨qs⟩, _⟩ | _
        | _ | _ | _ | _ | _ <;>
        simp [Ty.beq] at h ⊢
      exact ⟨by rw [TyParam.eqs_of_beqs _ _ h.1], Ty.eq_of_beq _ _ h.2⟩
    | .enum .., b, h => by
      cases b <;> simp_all [Ty.beq]
    | .reg s, b, h | .wire s, b, h | .input s, b, h => by
      cases b <;> simp [Ty.beq] at h ⊢
      exact Ty.eq_of_beq _ _ h
    | .mem s n, b, h => by
      cases b <;> simp [Ty.beq] at h ⊢
      exact ⟨Ty.eq_of_beq _ _ h.1, h.2⟩
    | .inst _ _ ⟨xs⟩, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
        | _ | _ | _ | _ | ⟨_, _, ⟨ys⟩⟩ <;>
        simp [Ty.beq] at h ⊢
      exact ⟨h.1.1, h.1.2, by rw [Value.eqs_of_beqs _ _ h.2]⟩

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
      rcases b with _ | _ | _ | _ | _ | _ | _ | ⟨_, ⟨ys⟩⟩ | ⟨⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | _
        | _ <;>
        simp [Value.beq] at h ⊢
      exact ⟨Ty.eq_of_beq _ _ h.1, by rw [Value.eqs_of_beqs _ _ h.2]⟩
    | .tuple ⟨xs⟩, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | ⟨_, ⟨ys⟩⟩ | ⟨⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | ⟨_, ⟨ys⟩⟩ | _
        | _ <;>
        simp [Value.beq] at h ⊢
      rw [Value.eqs_of_beqs _ _ h]
    | .function _ _ ⟨ps⟩ _, b, h => by
      rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_, _, ⟨qs⟩, _⟩ | _ <;>
        simp [Value.beq] at h ⊢
      exact ⟨h.1.1.1, h.1.1.2, by rw [TyParam.eqs_of_beqs _ _ h.1.2], Ty.eq_of_beq _ _ h.2⟩
    | .enum _ _ x _ y, b, h => by
      cases b <;> simp [Value.beq] at h ⊢
      obtain ⟨⟨⟨⟨h1, rfl⟩, h2⟩, rfl⟩, h3⟩ := h
      exact ⟨Ty.eq_of_beq _ _ h1, rfl, heq_of_eq (BitVec.eq_of_toNat_eq h2), rfl,
        heq_of_eq (BitVec.eq_of_toNat_eq h3)⟩

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
    | .struct _ _ ⟨xs⟩ _ _ => by simp [Ty.beq, Value.beqs_self xs]
    | .fn ⟨ps⟩ r => by simp [Ty.beq, TyParam.beqs_self ps, Ty.beq_self r]
    | .enum .. => by simp [Ty.beq]
    | .reg s | .wire s | .input s | .mem s _ => by simp [Ty.beq, Ty.beq_self s]
    | .inst _ _ ⟨xs⟩ => by simp [Ty.beq, Value.beqs_self xs]

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
    | .enum t .. => by simp [Value.beq, Ty.beq_self t]

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
  | .fn .. => 12 | .enum .. => 13 | .reg _ => 14 | .wire _ => 15 | .input _ => 16
  | .mem .. => 17 | .inst .. => 18

def Value.form : Value → Nat
  | .int _ => 0 | .bool _ => 1 | .str _ => 2 | .uint .. => 3 | .sint .. => 4 | .type _ => 5
  | .unit => 6 | .array .. => 7 | .tuple _ => 8 | .record .. => 9 | .list _ _ => 10
  | .function .. => 11 | .enum .. => 12

/-!
An order of types and values by their numbers (section 5.6). A struct type compares by the
number of its specialization, and a function value by the number of its item. Each number fixes
the rest of its term, so the order compares no name. Each other part compares in full, so the
work is at most the smaller size, plus the element types of arrays and lists. An enum type
compares by its item, and an enum value by its type, its tag, and its payload. A handle type
compares its parts, and an instance type its module item and then its arguments.
-/
mutual
  def Ty.cmp : Ty → Ty → Ordering
    | .uint a, .uint b | .sint a, .sint b => compare a b
    | .array s n, .array t m => (Ty.cmp s t).then (compare n m)
    | .list s, .list t => Ty.cmp s t
    | .tuple ⟨xs⟩, .tuple ⟨ys⟩ => Ty.cmps xs ys
    | .struct a .., .struct b .. => compare a b
    | .fn ⟨ps⟩ r, .fn ⟨qs⟩ s => (TyParam.cmps ps qs).then (Ty.cmp r s)
    | .enum a .., .enum b .. => compare a b
    | .reg s, .reg t | .wire s, .wire t | .input s, .input t => Ty.cmp s t
    | .mem s n, .mem t m => (Ty.cmp s t).then (compare n m)
    | .inst a _ ⟨xs⟩, .inst b _ ⟨ys⟩ => (compare a b).then (Value.cmps xs ys)
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
    | .enum s _ x _ y, .enum t _ x' _ y' =>
      (Ty.cmp s t).then ((compare x.toNat x'.toNat).then (compare y.toNat y'.toNat))
    | x, y => compare x.form y.form

  def Value.cmps : List Value → List Value → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | x :: xs, y :: ys => (Value.cmp x y).then (Value.cmps xs ys)
end

/-!
The equality of two types by their numbers. For the types of one evaluation it agrees with `=`,
because a struct type comes only from its entry in the table of specializations. The name of an
instance type follows from its module item in the same way.
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
scalar type holds a function type, an enum type, or a handle type.
-/
def Meta.bool : Meta := ⟨1, 1, 1, 1, true, false, false, false⟩
def Meta.finite (width : Nat) : Meta := ⟨width, 1, widthSize width, 1, true, false, false, false⟩
def Meta.unit : Meta := ⟨0, 0, 1, 1, true, false, false, false⟩
def Meta.static : Meta := ⟨0, 0, 0, 1, false, false, false, false⟩

/-!
The metadata of `[T; N]` from the metadata `m` of `T`: the product rule of section 5.4. The zero
value is a node with `N` zeros of `T`.
-/
def Meta.array (m : Meta) (n : Nat) : Meta :=
  ⟨n * m.width, n * m.leaves, 1 + n * m.zeroSize, 1 + m.depth, m.data, m.funcs, m.enums,
   m.handles⟩

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
   1 + ((parts.map (·.depth)) ++ extra).foldl max 0, parts.all (·.data), parts.any (·.funcs),
   parts.any (·.enums), parts.any (·.handles)⟩

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
and a `mut` mark adds no depth. It sets the function flag, and it takes the enum flag of its
parts. It never takes the handle flag, because a function value holds no handle (section 5.4).
-/
def Meta.fn (params : List Meta) (ret : Meta) : Meta :=
  ⟨0, 0, 0, 1 + ((params.map (·.depth)).foldl max ret.depth), false, true,
   params.any (·.enums) || ret.enums, false⟩

/-!
The metadata of an enum with the tag width `w` and the payload width `p` (section 5.4). It is
the sums of a record of `UInt[w]` and `UInt[p]`, without the second part when `p` is 0.
`enumParts` gives the parts. An enum is hardware data, and it sets the enum flag.
-/
def Meta.enumParts (w p : Nat) : List Meta :=
  Meta.finite w :: if p = 0 then [] else [Meta.finite p]

def Meta.enum (w p : Nat) : Meta := { Meta.sum (Meta.enumParts w p) [] with enums := true }

/-! The sizes of the four integers of `m`. A type constructor that makes them charges this. -/
def Meta.intCharge (m : Meta) : Nat :=
  intSize m.width + intSize m.leaves + intSize m.zeroSize + intSize m.depth

/-!
The charge of the reads of `Meta.sum parts _`: the sizes of the four integers of each part. It
bounds the work of the additions, so it comes before them.
-/
def Meta.readCharge (parts : List Meta) : Nat := (parts.map Meta.intCharge).sum

/-!
The depth of section 5.5: 1 for a scalar type or value, and 1 more than its deepest part. A
struct type has its stored depth, which counts its field types and its static arguments. An enum
type has the stored depth of its metadata. A `mut` mark adds no depth. A handle type is 1 deeper
than its deepest part, and the depth `N` of `Mem[T, N]` is an integer of the depth 1. An enum
value counts its type, as a record does, and its two parts have the depth 1.
-/
mutual
  def Ty.depth : Ty → Nat
    | .array t _ | .list t | .reg t | .wire t | .input t | .mem t _ => 1 + t.depth
    | .tuple ⟨ts⟩ => 1 + Ty.depthAll ts
    | .struct _ _ _ m _ | .enum _ _ m => m.depth
    | .fn ⟨ps⟩ r => 1 + max (TyParam.depthAll ps) r.depth
    | .inst _ _ ⟨xs⟩ => 1 + Value.depthAll xs
    | _ => 1

  def Ty.depthAll : List Ty → Nat
    | [] => 0
    | t :: ts => max t.depth (Ty.depthAll ts)

  def TyParam.depthAll : List TyParam → Nat
    | [] => 0
    | .mk _ t :: ps => max t.depth (TyParam.depthAll ps)

  def Value.depth : Value → Nat
    | .type t => t.depth
    | .array t ⟨xs⟩ | .record t ⟨xs⟩ | .list t ⟨xs⟩ => 1 + max t.depth (Value.depthAll xs)
    | .tuple ⟨xs⟩ => 1 + Value.depthAll xs
    | .enum t .. => 1 + max t.depth 1
    | _ => 1

  def Value.depthAll : List Value → Nat
    | [] => 0
    | x :: xs => max x.depth (Value.depthAll xs)
end

/-!
The metadata of a type. A type constructor computes it from its parts. A struct type stores
it, so this walk never enters the field types of a struct. A handle type has the metadata of
`List[T]` (section 5.4). It is not hardware data, and it takes the function flag and the enum
flag of `T`. An instance type has neither flag, and its depth counts its arguments. Each handle
type has the handle flag, and `List[T]` takes it from `T`. `Type` does not have it.
-/
mutual
  def Ty.info : Ty → Meta
    | .bool => Meta.bool
    | .uint w | .sint w => Meta.finite w
    | .unit => Meta.unit
    | .nat | .int | .type | .string => Meta.static
    | .list t =>
      { Meta.static with
        depth := 1 + t.info.depth, funcs := t.info.funcs, enums := t.info.enums
        handles := t.info.handles }
    | .reg t | .wire t | .input t | .mem t _ =>
      { Meta.static with
        depth := 1 + t.info.depth, funcs := t.info.funcs, enums := t.info.enums, handles := true }
    | .array t n => t.info.array n
    | .tuple ⟨ts⟩ => Meta.tuple (Ty.infoAll ts)
    | .struct _ _ _ m _ => m
    | .fn ⟨ps⟩ r => Meta.fn (TyParam.infoAll ps) r.info
    | .enum _ _ m => m
    | .inst _ _ ⟨xs⟩ => { Meta.static with depth := 1 + Value.depthAll xs, handles := true }

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
    | .struct _ i ⟨xs⟩ _ .user =>
      Print.node "struct" ["root", i, Print.list (Value.serializeAll xs)]
    | .struct _ i ⟨xs⟩ _ .prelude =>
      Print.node "struct" ["prelude", i, Print.list (Value.serializeAll xs)]
    | .struct _ _ ⟨xs⟩ _ .gen => Print.node "gstruct" [Print.list (Value.serializeGen xs)]
    | .string => "string"
    | .list t => Print.node "list" [t.serialize]
    | .fn ⟨ps⟩ r => Print.node "fn" [Print.list (TyParam.serializeAll ps), r.serialize]
    | .enum _ x _ => Print.node "enum" ["root", x, Print.list []]
    | .reg t => Print.node "reg" [t.serialize]
    | .wire t => Print.node "wire" [t.serialize]
    | .input t => Print.node "input" [t.serialize]
    | .mem t n => Print.node "mem" [t.serialize, toString n]
    | .inst _ x ⟨xs⟩ => Print.node "instance" ["root", x, Print.list (Value.serializeAll xs)]

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
    | .enum t _ x p y =>
      Print.node "enum" ([t.serialize, toString x.toNat] ++
        if p = 0 then [] else [Print.node "uint" [toString p, toString y.toNat]])

  def Value.serializeAll : List Value → List String
    | [] => []
    | x :: xs => x.serialize :: Value.serializeAll xs

  /--
  The fields of a generated record type from its arguments: `("a" (uint 8))` for each name and
  field type. Its arguments are always such pairs.
  -/
  def Value.serializeGen : List Value → List String
    | .str x :: .type t :: xs => Print.list [Print.quote x, t.serialize] :: Value.serializeGen xs
    | _ => []
end

/-!
The recursive size of section 5.4. A type has the number of nodes of its term. Each integer and
each static argument in it adds its size. Each `mut` mark of a function type is one more node. A
named function has the size 1. An enum type has the size 1, and an enum value the size of a
record of its tag and its payload. An empty payload adds nothing. A handle type has the size 1
plus its parts, and `Instance[M, args]` adds its arguments as a struct type does (section 5.4).

This size is the fifth metadata number of section 5.4. The Rust front end stores it with each
type, so a read costs constant work. Lean does not store it: `Ty.size` walks the term. Both give
the same number, and each read of it goes into a charge, so the charges agree.
-/
mutual
  def Ty.size : Ty → Nat
    | .bool | .nat | .int | .unit | .type | .string => 1
    | .uint w | .sint w => 1 + intSize w
    | .array t n => 1 + t.size + intSize n
    | .list t => 1 + t.size
    | .tuple ⟨ts⟩ => 1 + Ty.sizeAll ts
    | .struct _ _ ⟨xs⟩ _ _ => 1 + Value.sizeAll xs
    | .fn ⟨ps⟩ r => 1 + TyParam.sizeAll ps + r.size
    | .enum .. => 1
    | .reg t | .wire t | .input t => 1 + t.size
    | .mem t n => 1 + t.size + intSize n
    | .inst _ _ ⟨xs⟩ => 1 + Value.sizeAll xs

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
    | .enum _ w _ p _ => 1 + widthSize w + if p = 0 then 0 else widthSize p

  def Value.sizeAll : List Value → Nat
    | [] => 0
    | x :: xs => x.size + Value.sizeAll xs
end

/-!
The depth of the zero value of a hardware data type, from the type alone. An array of length 0
has the depth of its type, and another array 1 more than the zero of its element. A record is
1 deeper than its struct type, because the depth of a record counts its type. An enum is
1 deeper than its type in the same way. Thus this walk
never enters the field types of a struct. It gives the depth of section 5.5 of `T()`.
-/
mutual
  def Ty.zeroDepth : Ty → Nat
    | .array t 0 => 1 + t.depth
    | .array t _ => 1 + t.zeroDepth
    | .tuple ⟨ts⟩ => 1 + Ty.zeroDepthAll ts
    | t@(.struct ..) | t@(.enum ..) => 1 + t.depth
    | _ => 1

  def Ty.zeroDepthAll : List Ty → Nat
    | [] => 0
    | t :: ts => max t.zeroDepth (Ty.zeroDepthAll ts)
end

/-!
An integer in a message: decimal up to 256 bits, else its bit length. The bit length needs no
decimal conversion, so a message stays small and cheap for any computed integer.
-/
def intText (n : Int) : String :=
  let bits := n.natAbs.log2 + 1
  if bits ≤ 256 then toString n
  else s!"{if n < 0 then "a negative" else "an"} integer of {bits} bits"

/-! The longest text of a type or a value in a message, before `...` (section 5.5). -/
def textLimit : Nat := 1024

/-! The longest prefix of `cs` with at most `n` bytes in UTF-8. -/
def takeBytes : List Char → Nat → List Char
  | [], _ => []
  | c :: cs, n => if c.utf8Size ≤ n then c :: takeBytes cs (n - c.utf8Size) else []

/-!
The text `s` in a message: `s` when it has at most `textLimit` bytes, else its longest prefix
of at most `textLimit` bytes that ends at a character, then `...`.
-/
def boundText (s : String) : String :=
  if s.utf8ByteSize ≤ textLimit then s
  else String.ofList (takeBytes s.toList textLimit) ++ "..."

/-!
The name of a struct or an enum item in a message. A user item with a prelude type name has the
prefix `crate::` (section 5.6), so it never prints as the prelude type. A prelude struct
(`prelude`) keeps its source form.
-/
def itemText (prelude : Bool) (x : String) : String :=
  if !prelude && preludeTypeNames.contains x then "crate::" ++ x else x

/-!
The text of a type in a message, and the source text of a static argument in it. A struct type
prints its item (`itemText`), with its arguments in brackets when it has any: `P[8]`. A function
type prints in its source form, and a function value prints its item. An enum type prints its
name (`itemText`), and an enum value its tag, because the value does not hold the name of its
variant. A handle type prints in its source form: `Reg[UInt[8]]`, `Mem[UInt[8], 16]`, or
`Instance[Counter, 8]`. Each integer prints as `intText` does.

Each walk appends to the text `o` so far. Each step, of a part and of a list of parts, first
checks the bound: it returns `o` at once when `o` has more than `textLimit` bytes. Each piece
that it appends is short: a string argument appends at most `textLimit + 1` characters. Thus the
walk of a huge type, also of a tuple with `2^20` parts, stops soon after the bound. Each open
step then adds its closing piece in constant work, and `boundText` cuts the text (section 5.5).
-/
mutual
  def Ty.put (o : String) (t : Ty) : String :=
    if textLimit < o.utf8ByteSize then o
    else match t with
    | .bool => o ++ "Bool" | .nat => o ++ "Nat" | .int => o ++ "Int"
    | .uint w => o ++ s!"UInt[{w}]" | .sint w => o ++ s!"SInt[{w}]"
    | .unit => o ++ "Unit"
    | .type => o ++ "Type"
    | .array t n => t.put (o ++ "[") ++ s!"; {intText n}]"
    | .tuple ⟨[t]⟩ => t.put (o ++ "(") ++ ",)"
    | .tuple ⟨ts⟩ => Ty.putAll (o ++ "(") ts ++ ")"
    | .struct _ _ ⟨[]⟩ _ .gen => o ++ "@Struct {}"
    | .struct _ _ ⟨xs⟩ _ .gen => Value.putGen (o ++ "@Struct { ") xs ++ " }"
    | .struct _ i ⟨[]⟩ _ p => o ++ itemText (p == .prelude) i
    | .struct _ i ⟨xs⟩ _ p => Value.putAll (o ++ itemText (p == .prelude) i ++ "[") xs ++ "]"
    | .string => o ++ "String"
    | .list t => t.put (o ++ "List[") ++ "]"
    | .fn ⟨ps⟩ r => r.put (TyParam.putAll (o ++ "fn (") ps ++ ") -> ")
    | .enum _ x _ => o ++ itemText false x
    | .reg t => t.put (o ++ "Reg[") ++ "]"
    | .wire t => t.put (o ++ "Wire[") ++ "]"
    | .input t => t.put (o ++ "Input[") ++ "]"
    | .mem t n => t.put (o ++ "Mem[") ++ s!", {intText n}]"
    | .inst _ x ⟨[]⟩ => o ++ "Instance[" ++ x ++ "]"
    | .inst _ x ⟨xs⟩ => Value.putAll (o ++ "Instance[" ++ x ++ ", ") xs ++ "]"

  /-- The types `ts` with `, ` between them. -/
  def Ty.putAll (o : String) (ts : List Ty) : String :=
    if textLimit < o.utf8ByteSize then o
    else match ts with
    | [] => o
    | [t] => t.put o
    | t :: ts => Ty.putAll (t.put o ++ ", ") ts

  def TyParam.putAll (o : String) (ps : List TyParam) : String :=
    if textLimit < o.utf8ByteSize then o
    else match ps with
    | [] => o
    | [.mk m t] => t.put (if m then o ++ "mut " else o)
    | .mk m t :: ps => TyParam.putAll (t.put (if m then o ++ "mut " else o) ++ ", ") ps

  def Value.put (o : String) (v : Value) : String :=
    if textLimit < o.utf8ByteSize then o
    else match v with
    | .int n => o ++ intText n
    | .bool b => o ++ Print.boolean b
    | .str s => o ++ Print.quote (s.take (textLimit + 1)).toString
    | .uint _ v => o ++ intText v.toNat
    | .sint _ v => o ++ intText v.toInt
    | .type t => t.put o
    | .unit => o ++ "()"
    | .array _ ⟨xs⟩ => Value.putAll (o ++ "[") xs ++ "]"
    | .tuple ⟨[x]⟩ => x.put (o ++ "(") ++ ",)"
    | .tuple ⟨xs⟩ => Value.putAll (o ++ "(") xs ++ ")"
    | .record t ⟨xs⟩ => Value.putAll (t.put o ++ "(") xs ++ ")"
    | .list t ⟨[]⟩ => t.put (o ++ "list(") ++ ")"
    | .list _ ⟨xs⟩ => Value.putAll (o ++ "[") xs ++ "]"
    | .function _ i _ _ => o ++ i
    | .enum _ _ x _ _ => o ++ intText x.toNat

  /-- The literals `xs` with `, ` between them. -/
  def Value.putAll (o : String) (xs : List Value) : String :=
    if textLimit < o.utf8ByteSize then o
    else match xs with
    | [] => o
    | [x] => x.put o
    | x :: xs => Value.putAll (x.put o ++ ", ") xs

  /--
  The fields of a generated record type from its arguments: `a: UInt[8]` for each name and
  field type, with `, ` between them. A name has the limit of a string (`strText`).
  -/
  def Value.putGen (o : String) (xs : List Value) : String :=
    if textLimit < o.utf8ByteSize then o
    else match xs with
    | [.str x, .type t] => t.put (o ++ strText x ++ ": ")
    | .str x :: .type t :: xs => Value.putGen (t.put (o ++ strText x ++ ": ") ++ ", ") xs
    | _ => o
end

/-! The text of a type in a message, at most `textLimit` bytes and `...`. -/
def Ty.text (t : Ty) : String := boundText (t.put "")

/-! The source text of a static argument in a message, at most `textLimit` bytes and `...`. -/
def Value.literal (v : Value) : String := boundText (v.put "")

/-!
The type of a value. A type value has the type `Type`, and a function its signature. A tuple
walks its elements, because it stores no type.
-/
mutual
  def Value.ty : Value → Ty
    | .int _ => .int
    | .bool _ => .bool
    | .uint w _ => .uint w
    | .sint w _ => .sint w
    | .unit => .unit
    | .array t xs => .array t xs.size
    | .tuple ⟨xs⟩ => .tuple (Value.tyAll xs).toArray
    | .record t _ => t
    | .type _ => .type
    | .str _ => .string
    | .list t _ => .list t
    | .function _ _ ps r => .fn ps r
    | .enum t .. => t

  def Value.tyAll : List Value → List Ty
    | [] => []
    | x :: xs => x.ty :: Value.tyAll xs
end

/-! The type of a value as an option, for the callers that join it with the type of a part. -/
def Value.ty? (v : Value) : Option Ty := some v.ty

/-!
The text of the type of a value, appended to `o`. A tuple walks its elements, so it builds no
type. Each other value has its type in one step.
-/
mutual
  def Value.putTy (o : String) (v : Value) : String :=
    if textLimit < o.utf8ByteSize then o
    else match v with
    | .tuple ⟨[x]⟩ => x.putTy (o ++ "(") ++ ",)"
    | .tuple ⟨xs⟩ => Value.putTyAll (o ++ "(") xs ++ ")"
    | v => (v.ty?.map (·.put o)).getD o

  def Value.putTyAll (o : String) (xs : List Value) : String :=
    if textLimit < o.utf8ByteSize then o
    else match xs with
    | [] => o
    | [x] => x.putTy o
    | x :: xs => Value.putTyAll (x.putTy o ++ ", ") xs
end

/-! The text of a value in a message: its type, or its own text for a string and a type. -/
def Value.text : Value → String
  | .str _ => "a string"
  | .type _ => "a type"
  | v => boundText (v.putTy "")

def Value.finiteTy? : Value → Option Ty
  | .uint w _ => some (.uint w)
  | .sint w _ => some (.sint w)
  | _ => none

/-!
The charge of the walk that measures the serialization of a value, before the charge of its
bytes (section 5.4). Each array, tuple, record, and list charges 1. Each integer and each
finite value charge the square of their size, because a naive decimal conversion takes this
time. A scalar thus keeps the charge of slice 1. A type charges nothing: an integer in a type
gets no charge for its decimal form. An enum value is one container node, so it charges 1 and
the squares of the sizes of its tag and its payload.
-/
mutual
  def Value.measureCharge : Value → Nat
    | v@(.int _) | v@(.uint ..) | v@(.sint ..) => v.size * v.size
    | .array _ ⟨xs⟩ | .tuple ⟨xs⟩ | .record _ ⟨xs⟩ | .list _ ⟨xs⟩ =>
      1 + Value.measureChargeAll xs
    | .enum _ w _ p _ =>
      1 + widthSize w * widthSize w + if p = 0 then 0 else widthSize p * widthSize p
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
