-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Eval.Inst

/-!
The kind checks of `@field(x, k)` (sections 6.2 and 9.3), steps 5 to 7 of the **`@field`
order**. The base gives the key type that it takes (`FieldBase`). The key then gets its typed use
at this type. A `String` key and the name of a `PortKey` key charge their size before a look-up
reads them. The result is the ordinary selection that the key names (`FieldKey`): a field, an
index, or a public port of a child. `Eval` then runs the look-up and the selection in the context
of the `@field`: an expression, a place, or a query operand.
-/
namespace Silicon.Source.Eval

open Resolve Names

/-!
The kind of a base of `@field`: a record, an enum, an array, a list, or a tuple (`seq`), or an
`Instance` handle. The handle keeps its child number, its path, its interface, and its type.
-/
inductive FieldBase where
  | record
  | enum (t : Ty)
  | seq
  | inst (id : Nat) (path : Path) (iface : Iface) (ty : Ty)

/-! The kind of a base of the data type `t`, if `@field` selects in it. -/
def Ty.fieldBase? : Ty → Option FieldBase
  | .struct .. => some .record
  | t@(.enum ..) => some (.enum t)
  | .array .. | .tuple _ | .list _ => some .seq
  | _ => none

/-!
The kind of the base `v`, if `@field` selects in it. A static tuple stores no type, so its form
gives its kind with no walk. Another value gives its kind by its stored type.
-/
def Val.fieldBase? : Val → Option FieldBase
  | .handle (.inst id path iface ty) => some (.inst id path iface ty)
  | .static (.record ..) => some .record
  | .static (.array ..) | .static (.tuple _) | .static (.list ..) => some .seq
  | v => v.ty?.bind Ty.fieldBase?

/-! The key type `{w}` that a base takes, in the text "Key of `@field`" of section 6.2. -/
def FieldBase.want : FieldBase → String
  | .record | .enum _ => "`String`"
  | .seq => "`Nat`"
  | .inst .. => "`String` or `PortKey`"

/-! The value `{a}` of a part of the data type `t` that a query keeps only by its type. -/
def Ty.about (t : Ty) : String := s!"a value of `{t.text}`"

/-! The `S010` text "Key of `@field`" of section 6.2: base `a`, key type `w`, and key `b`. -/
def fieldKeyText (a w b : String) : String :=
  s!"`@field` on {a} takes {w}, not {b}; give a static {w}"

/-! The `S010` text "Base of `@field`" of section 6.2, for the base `a`. -/
def fieldBaseText (a : String) : String :=
  s!"`@field` selects in a record, an array, a list, a tuple, or an instance, not {a}; select " ++
    "from such a value"

/-!
The selection that a key of `@field` names. It is the field with the symbol `y` and the name
`name`, or the index `k`. It can also be the port of the name `name` with the symbol `y` of the
child number `id`, with the path `path`, the interface `iface`, and the type `ty`. An entry of a
family has its `key`.
-/
inductive FieldKey where
  | field (y : Option Nat) (name : String)
  | index (k : Value)
  | port (id : Nat) (path : Path) (iface : Iface) (ty : Ty) (y : Option Nat) (name : String)
      (key : Option Nat)

/-!
Steps 6 and 7 of the **`@field` order** for the static key `k` at `kp` on a base of the kind
`base` (section 6.2). `a` gives the text of the base, only in an error. A record takes a
`String`, and an enum too, but a `String` on an enum is "Field of an enum". An array, a list, and
a tuple take a `Nat` by its typed use: a negative key is `S012`. An `Instance` handle takes a
`String` or a value of the prelude struct `PortKey` (`Elab.portKey?`), with the checks of its
index (`S022`, `S012`). Each other key is "Key of `@field`". A `String` key and the name of a
`PortKey` charge their size, then the look-up of the symbol adds no name (`symbolFind`).
-/
def fieldKeyOf (kp : Pos) (base : FieldBase) (a : Unit → String) (k : Value) : M FieldKey :=
  match base, k with
  | .record, .str s => do
    charge kp (Value.str s).size
    return .field (← symbolFind s) s
  | .enum t, .str s => fail .S010 kp (enumFieldText t (strText s))
  | .seq, .int i => do
    if i < 0 then fail .S012 kp (fitText .nat i)
    return .index k
  | .inst id path iface ty, k =>
    match Elab.portKey? k with
    | some r => do
      let (x, key) ← lift kp r
      charge kp (Value.str x).size
      return .port id path iface ty (← symbolFind x) x key
    | none => fail .S010 kp (fieldKeyText (a ()) base.want (Val.static k).about)
  | b, k => fail .S010 kp (fieldKeyText (a ()) b.want (Val.static k).about)

end Silicon.Source.Eval
