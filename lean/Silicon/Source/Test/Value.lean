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

end Silicon.Source.Test.Value
