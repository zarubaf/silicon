-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Value

/-!
These tests fix the bytes of the canonical serialization, which the Rust front end must copy,
and the recursive size at the word limits.
-/

namespace Silicon.Source.Test.Value

open Silicon.Source

/-! The forms of section 7.1. -/
#guard (Value.int (-5)).serialize == "(int -5)"
#guard (Value.int 0).serialize == "(int 0)"
#guard (Value.int 18446744073709551616).serialize == "(int 18446744073709551616)"
#guard (Value.bool true).serialize == "(bool true)"
#guard (Value.bool false).serialize == "(bool false)"
#guard (Value.str "a\"b").serialize == "(string \"a\\\"b\")"
#guard (Value.str "\\\n\r\t").serialize == "(string \"\\\\\\n\\r\\t\")"
#guard (Value.str "").serialize == "(string \"\")"
#guard ({ module := "Counter", args := [.int 8] } : InstantiationId).serialize ==
  "(instantiation root Counter ((int 8)))"
#guard ({ module := "Fifo", args := [.int 16, .bool true] } : InstantiationId).serialize ==
  "(instantiation root Fifo ((int 16) (bool true)))"
#guard ({ module := "Top", args := [] } : InstantiationId).serialize ==
  "(instantiation root Top ())"

/-! Finite values and types. -/
#guard (Value.uint 8 255).serialize == "(uint 8 255)"
#guard (Value.sint 8 255).serialize == "(sint 8 -1)"
#guard (Value.sint 8 127).serialize == "(sint 8 127)"
#guard (Value.type .bool).serialize == "(type bool)"
#guard (Value.type .nat).serialize == "(type nat)"
#guard (Value.type .int).serialize == "(type int)"
#guard (Value.type (.uint 8)).serialize == "(type (uint 8))"
#guard (Value.type (.sint 16)).serialize == "(type (sint 16))"

/-! The size of an integer at the 64-bit word limits, for both signs. -/
#guard (Value.int 0).size == 1
#guard (Value.int 1).size == 1
#guard (Value.int 18446744073709551615).size == 1
#guard (Value.int 18446744073709551616).size == 2
#guard (Value.int (-18446744073709551615)).size == 1
#guard (Value.int (-18446744073709551616)).size == 2
#guard (Value.int (2 ^ 128 - 1)).size == 2
#guard (Value.int (2 ^ 128)).size == 3

/-! The other sizes. A string counts characters, not bytes. -/
#guard (Value.bool true).size == 1
#guard (Value.str "").size == 1
#guard (Value.str "abc").size == 4
#guard (Value.str "ä").size == 2
#guard (Value.uint 0 0).size == 1
#guard (Value.uint 64 0).size == 1
#guard (Value.sint 65 0).size == 2
#guard (Value.type .bool).size == 1
#guard (Value.type (.uint 8)).size == 2
#guard (Value.type (.uint 18446744073709551616)).size == 3

/-! The container forms of section 7.1. -/
#guard Value.unit.serialize == "(unit)"
#guard (Value.array (.uint 8) #[.uint 8 1, .uint 8 2]).serialize ==
  "(array (uint 8) ((uint 8 1) (uint 8 2)))"
#guard (Value.array .bool #[]).serialize == "(array bool ())"
#guard (Value.tuple #[.int 1, .bool true]).serialize == "(tuple ((int 1) (bool true)))"
#guard (Value.tuple #[.unit]).serialize == "(tuple ((unit)))"
#guard (Value.type (.array (.uint 8) 4)).serialize == "(type (array (uint 8) 4))"
#guard (Value.type (.tuple #[.bool, .uint 8])).serialize == "(type (tuple (bool (uint 8))))"
#guard (Value.type .unit).serialize == "(type unit)"
#guard (Value.array (.array .bool 2) #[.array .bool #[.bool true, .bool false]]).serialize ==
  "(array (array bool 2) ((array bool ((bool true) (bool false)))))"
#guard ({ module := "Top", args := [.tuple #[.int 1], .unit] } : InstantiationId).serialize ==
  "(instantiation root Top ((tuple ((int 1))) (unit)))"

/-! The text of a type in a message. A tuple with one element keeps its comma. -/
#guard Ty.unit.text == "Unit"
#guard (Ty.array (.uint 8) 4).text == "[UInt[8]; 4]"
#guard (Ty.tuple #[.bool]).text == "(Bool,)"
#guard (Ty.tuple #[.bool, .array .int 2]).text == "(Bool, [Int; 2])"
#guard (Value.tuple #[.int 1, .bool true]).ty? == some (.tuple #[.int, .bool])
#guard (Value.array .bool #[]).ty? == some (.array .bool 0)
#guard (Value.tuple #[.str "a"]).ty? == none
#guard (Value.tuple #[.str "a"]).text == "a tuple"

/-! Equality is structural. An array keeps its element type, also when it is empty. -/
#guard Value.array .bool #[] != Value.array .int #[]
#guard Value.tuple #[.int 1] != Value.array .int #[.int 1]
#guard Value.tuple #[.uint 8 1] == Value.tuple #[.uint 8 1]
#guard Value.uint 8 1 != Value.uint 16 1
#guard Ty.tuple #[.bool] != Ty.array .bool 1

/-! The sizes of the containers and of their types (section 5.4). -/
#guard Value.unit.size == 1
#guard (Value.type .unit).size == 1
#guard (Value.array .bool #[]).size == 1
#guard (Value.array (.uint 8) #[.uint 8 1, .uint 8 2]).size == 3
#guard (Value.tuple #[.int 1, .str "ab"]).size == 5
#guard (Value.type (.array (.uint 8) 4)).size == 4
#guard (Value.type (.tuple #[.bool, .uint 8])).size == 4
#guard (Value.type (.array .bool 18446744073709551616)).size == 4

/-! The nested doubling of section 5.5: `a_k = [a_(k-1), a_(k-1)]`. -/
def doubling : Nat → Value
  | 0 => .array .bool #[.bool true, .bool false]
  | k + 1 => .array ((doubling k).ty?.getD .bool) #[doubling k, doubling k]

#guard (List.range 8).all fun k => (doubling k).size == 2 ^ (k + 2) - 1

/-! The depth of section 5.5. An array value counts its element type. -/
#guard (Value.int 5).depth == 1
#guard Value.unit.depth == 1
#guard (Value.type (.uint 8)).depth == 1
#guard (Value.type (.array (.array .bool 2) 3)).depth == 3
#guard (Value.type (.tuple #[.bool, .tuple #[.int]])).depth == 3
#guard (Value.tuple #[.tuple #[.int 1], .bool true]).depth == 3
#guard (Value.array .bool #[]).depth == 2
#guard (Value.array (.array .bool 0) #[]).depth == 3
#guard (List.range 8).all fun k => (doubling k).depth == k + 2

/-! The charge of the walk that measures a serialization: containers and decimal forms. -/
#guard (Value.int 5).measureCharge == 1
#guard (Value.int 18446744073709551616).measureCharge == 4
#guard (Value.sint 65 0).measureCharge == 4
#guard (Value.bool true).measureCharge == 0
#guard (Value.type (.array (.uint 8) 4)).measureCharge == 0
#guard Value.unit.measureCharge == 0
#guard (Value.array .bool #[]).measureCharge == 1
#guard (Value.array (.uint 8) #[.uint 8 1, .uint 8 2]).measureCharge == 3
#guard (Value.tuple #[.int 18446744073709551616, .tuple #[.bool true]]).measureCharge == 6

/-! A struct type and a record: `struct Packet(comptime W: Nat) { a: UInt[W], b: Bool }`. -/
def packet (w : Nat) : Ty := .struct "Packet" #[.int w] (Meta.struct [Meta.finite w, Meta.bool] [1])

def empty : Ty := .struct "Empty" #[] (Meta.struct [] [])

/-! `struct Wrap(comptime T: Type) {}` at `T = [[Bool; 1]; 1]`. -/
def wrap : Ty := .struct "Wrap" #[.type (.array (.array .bool 1) 1)] (Meta.struct [] [3])

/-! The forms of section 7.1 for types and records. -/
#guard (Value.type .type).serialize == "(type type)"
#guard (Value.type (packet 8)).serialize == "(type (struct root Packet ((int 8))))"
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).serialize ==
  "(record (struct root Packet ((int 8))) ((uint 8 3) (bool false)))"
#guard (Value.record empty #[]).serialize == "(record (struct root Empty ()) ())"
#guard wrap.serialize == "(struct root Wrap ((type (array (array bool 1) 1))))"
#guard (Value.type (.tuple #[.type, .array empty 2])).serialize ==
  "(type (tuple (type (array (struct root Empty ()) 2))))"

/-! The text of a struct type names its item and its arguments. -/
#guard Ty.type.text == "Type"
#guard (packet 8).text == "Packet[8]"
#guard empty.text == "Empty"
#guard wrap.text == "Wrap[[[Bool; 1]; 1]]"
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).text == "Packet[8]"
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).literal == "Packet[8](3, false)"
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).ty? == some (packet 8)

/-! Equality of struct types compares the item and the arguments. -/
#guard packet 8 == packet 8
#guard packet 8 != packet 16
#guard Value.record empty #[] != Value.tuple #[]
#guard Value.type (packet 8) == Value.type (packet 8)

/-! A struct type has the size 1 plus its arguments. A record does not count its type. -/
#guard Ty.type.size == 1
#guard (packet 8).size == 2
#guard empty.size == 1
#guard wrap.size == 6
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).size == 3
#guard (Value.record empty #[]).size == 1

/-! The depth of a struct type counts its fields and its arguments. A record counts its type. -/
#guard Ty.type.depth == 1
#guard (packet 8).depth == 2
#guard empty.depth == 1
#guard wrap.depth == 4
#guard (Value.type wrap).depth == 4
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).depth == 3
#guard (Value.record wrap #[]).depth == 5
#guard (Ty.array (packet 8) 2).depth == 3

/-! The metadata of the scalar types, of a tuple, and of a struct. -/
#guard Ty.bool.info == ⟨1, 1, 1, 1, true⟩
#guard (Ty.uint 65).info == ⟨65, 1, 2, 1, true⟩
#guard Ty.unit.info == ⟨0, 0, 1, 1, true⟩
#guard Ty.type.info == ⟨0, 0, 0, 1, false⟩
#guard (Ty.tuple #[.bool, .int]).info == ⟨1, 1, 2, 2, false⟩
#guard (packet 8).info == ⟨9, 2, 3, 2, true⟩
#guard empty.info == ⟨0, 0, 1, 1, true⟩
#guard wrap.info == ⟨0, 0, 1, 4, true⟩
#guard Meta.structCharge [Meta.finite 8, Meta.bool] (packet 8).info == 6

/-! `[T; N]` multiplies the numbers of `T` by `N`, and each product charges its two sizes. -/
#guard (Ty.array (packet 8) 4).info == ⟨36, 8, 13, 3, true⟩
#guard (Ty.array .bool 0).info == ⟨0, 0, 1, 2, true⟩
#guard Meta.arrayCharge (packet 8).info 4 == 3
#guard (Ty.array (.uint 8) (2 ^ 64)).info.width == 2 ^ 67
#guard Meta.arrayCharge (Ty.uint 8).info (2 ^ 64) == 6

/-!
A chain of structs that doubles at each step: `S(k+1) { a: S(k), b: S(k) }`. The width grows
exponentially, but each struct stores its numbers, so the metadata and the size stay cheap.
-/
def chain : Nat → Ty
  | 0 => .struct "S0" #[] (Meta.struct [Meta.finite 1] [])
  | k + 1 => let t := chain k; .struct s!"S{k + 1}" #[] (Meta.struct [t.info, t.info] [])

#guard (chain 200).info == ⟨2 ^ 200, 2 ^ 200, 3 * 2 ^ 200 - 1, 202, true⟩
#guard (chain 200).size == 1
#guard (chain 200).depth == 202
#guard Meta.structCharge [(chain 199).info, (chain 199).info] (chain 200).info == 15
#guard (Value.type (chain 200)).serialize == "(type (struct root S200 ()))"

/-! The walk that measures a record charges 1 for its node, and nothing for its type. -/
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).measureCharge == 2
#guard (Value.type (packet 8)).measureCharge == 0

end Silicon.Source.Test.Value
