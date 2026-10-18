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
def packet (w : Nat) : Ty :=
  .struct w "Packet" #[.int w] (Meta.struct [Meta.finite w, Meta.bool] [1])

def empty : Ty := .struct 100 "Empty" #[] (Meta.struct [] [])

/-! `struct Wrap(comptime T: Type) {}` at `T = [[Bool; 1]; 1]`. -/
def wrap : Ty := .struct 101 "Wrap" #[.type (.array (.array .bool 1) 1)] (Meta.struct [] [3])

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
#guard Ty.bool.info == ⟨1, 1, 1, 1, true, false, false⟩
#guard (Ty.uint 65).info == ⟨65, 1, 2, 1, true, false, false⟩
#guard Ty.unit.info == ⟨0, 0, 1, 1, true, false, false⟩
#guard Ty.type.info == ⟨0, 0, 0, 1, false, false, false⟩
#guard (Ty.tuple #[.bool, .int]).info == ⟨1, 1, 2, 2, false, false, false⟩
#guard (packet 8).info == ⟨9, 2, 3, 2, true, false, false⟩
#guard empty.info == ⟨0, 0, 1, 1, true, false, false⟩
#guard wrap.info == ⟨0, 0, 1, 4, true, false, false⟩
#guard Meta.readCharge [Meta.finite 8, Meta.bool] == 8
#guard (packet 8).info.intCharge == 4

/-! `[T; N]` multiplies the numbers of `T` by `N`, and each product charges its two sizes. -/
#guard (Ty.array (packet 8) 4).info == ⟨36, 8, 13, 3, true, false, false⟩
#guard (Ty.array .bool 0).info == ⟨0, 0, 1, 2, true, false, false⟩
#guard Meta.arrayCharge (packet 8).info 4 == 3
#guard (Ty.array (.uint 8) (2 ^ 64)).info.width == 2 ^ 67
#guard Meta.arrayCharge (Ty.uint 8).info (2 ^ 64) == 6

/-!
A chain of structs that doubles at each step: `S(k+1) { a: S(k), b: S(k) }`. The width grows
exponentially, but each struct stores its numbers, so the metadata and the size stay cheap.
-/
def chain : Nat → Ty
  | 0 => .struct 1000 "S0" #[] (Meta.struct [Meta.finite 1] [])
  | k + 1 => let t := chain k; .struct (1001 + k) s!"S{k + 1}" #[] (Meta.struct [t.info, t.info] [])

#guard (chain 200).info == ⟨2 ^ 200, 2 ^ 200, 3 * 2 ^ 200 - 1, 202, true, false, false⟩
#guard (chain 200).size == 1
#guard (chain 200).depth == 202
#guard Meta.readCharge [(chain 199).info, (chain 199).info] == 26
#guard (chain 200).info.intCharge == 13
#guard (Value.type (chain 200)).serialize == "(type (struct root S200 ()))"

/-! The walk that measures a record charges 1 for its node, and nothing for its type. -/
#guard (Value.record (packet 8) #[.uint 8 3, .bool false]).measureCharge == 2
#guard (Value.type (packet 8)).measureCharge == 0

/-! The forms of section 7.1 for strings and lists. A list keeps its element type. -/
#guard (Value.list .int #[.int 1, .int 2]).serialize == "(list int ((int 1) (int 2)))"
#guard (Value.list .int #[]).serialize == "(list int ())"
#guard (Value.type (.list .int)).serialize == "(type (list int))"
#guard (Value.type .string).serialize == "(type string)"
#guard (Value.list .string #[.str "a"]).serialize == "(list string ((string \"a\")))"
#guard (Value.type (.list (.list (.uint 8)))).serialize == "(type (list (list (uint 8))))"

/-! The type and the text of a string and a list. -/
#guard (Value.str "a").ty? == some .string
#guard (Value.list .int #[]).ty? == some (.list .int)
#guard (Value.tuple #[.str "a"]).ty? == some (.tuple #[.string])
#guard (Value.tuple #[.str "a"]).text == "(String,)"
#guard (Ty.list (.uint 8)).text == "List[UInt[8]]"
#guard Ty.string.text == "String"
#guard (Value.list .int #[]).literal == "list(Int)"
#guard (Value.list .int #[.int 1, .int 2]).literal == "[1, 2]"

/-! Equality of lists compares the element type and the elements. -/
#guard Value.list .int #[] != Value.list .bool #[]
#guard Value.list .int #[] != Value.array .int #[]
#guard Value.list .int #[.int 1] == Value.list .int #[.int 1]
#guard Value.list .int #[.int 1] != Value.list .int #[.int 1, .int 1]
#guard Ty.list .int != Ty.list .nat
#guard Ty.string == Ty.string

/-! A list has the size 1 plus its elements, and `List[T]` the size 1 plus `T`. -/
#guard (Value.list .int #[]).size == 1
#guard (Value.list .int #[.int 1, .int 18446744073709551616]).size == 4
#guard (Value.list .string #[.str "ab"]).size == 4
#guard Ty.string.size == 1
#guard (Ty.list (.uint 8)).size == 3

/-! The depth of a list counts its element type. `String` has the depth 1. -/
#guard Ty.string.depth == 1
#guard (Ty.list .int).depth == 2
#guard (Ty.list (.list .int)).depth == 3
#guard (Value.list .int #[]).depth == 2
#guard (Value.list (.list .int) #[]).depth == 3
#guard (Value.list (.list .int) #[.list .int #[]]).depth == 3

/-! `String` and `List[T]` are not hardware data. The depth of `List[T]` reads only `T`. -/
#guard Ty.string.info == ⟨0, 0, 0, 1, false, false, false⟩
#guard (Ty.list .bool).info == ⟨0, 0, 0, 2, false, false, false⟩
#guard (Ty.list (packet 8)).info == ⟨0, 0, 0, 3, false, false, false⟩
#guard (Ty.list (chain 200)).info.depth == 203

/-! The walk that measures a list charges 1 for its node. A string charges nothing. -/
#guard (Value.list .int #[]).measureCharge == 1
#guard (Value.list .int #[.int 1, .int 2]).measureCharge == 3
#guard (Value.str "abc").measureCharge == 0

/-!
Function types. `inc : fn (mut UInt[8], Bool) -> Unit` is the form of section 7.1. A function
type is a node with each parameter type and the result type. Each `mut` mark is one more node.
-/
def incTy : Ty := .fn #[.mk true (.uint 8), .mk false .bool] .unit
def pred : Ty := .fn #[] .bool
def higher : Ty := .fn #[.mk false pred] (.array (.uint 8) 4)

#guard (Value.type incTy).serialize == "(type (fn ((mut (uint 8)) bool) unit))"
#guard pred.serialize == "(fn () bool)"
#guard higher.serialize == "(fn ((fn () bool)) (array (uint 8) 4))"
#guard incTy.text == "fn (mut UInt[8], Bool) -> Unit"
#guard pred.text == "fn () -> Bool"
#guard higher.text == "fn (fn () -> Bool) -> [UInt[8]; 4]"
#guard (Ty.list pred).text == "List[fn () -> Bool]"
#guard incTy.size == 6
#guard pred.size == 2
#guard higher.size == 7
#guard (Ty.fn #[.mk true .bool] .unit).size == (Ty.fn #[.mk false .bool] .unit).size + 1

/-! The depth of a function type is 1 more than its deepest part. A `mut` mark adds none. -/
#guard incTy.depth == 2
#guard pred.depth == 2
#guard higher.depth == 3
#guard (Ty.fn #[.mk true (.array .bool 1)] .bool).depth == 3
#guard (Ty.fn #[.mk false (.array .bool 1)] .bool).depth == 3
#guard (Value.type higher).depth == 3

/-!
A function type is not hardware data: its three numbers are 0. Its metadata keeps its depth and
sets the function flag.
-/
#guard incTy.info == ⟨0, 0, 0, 2, false, true, false⟩
#guard pred.info == ⟨0, 0, 0, 2, false, true, false⟩
#guard higher.info == ⟨0, 0, 0, 3, false, true, false⟩
#guard (Ty.fn #[.mk true (.array .bool 1)] .bool).info.depth == 3

/-! The function flag holds at any depth of a type, and a constructor takes it from its parts. -/
#guard (Ty.array pred 0).info == ⟨0, 0, 1, 3, false, true, false⟩
#guard (Ty.list pred).info == ⟨0, 0, 0, 3, false, true, false⟩
#guard (Ty.tuple #[.bool, pred]).info.funcs
#guard (Ty.array (.tuple #[.bool, .list pred]) 2).info.funcs
#guard !(Ty.tuple #[.bool, .int]).info.funcs
#guard !(Ty.array (.list .string) 2).info.funcs
#guard !(packet 8).info.funcs
#guard !(chain 200).info.funcs
#guard (Ty.struct 102 "Holder" #[] (Meta.struct [pred.info] [])).info.funcs
#guard (Ty.list (.struct 102 "Holder" #[] (Meta.struct [pred.info] []))).info.funcs

/-! The function flag of a struct comes from its field types, not from its static arguments. -/
#guard !(Ty.struct 103 "Tag" #[.type pred] (Meta.struct [] [pred.depth])).info.funcs

/-! Equality of function types compares the parameter types, the `mut` marks, and the result. -/
#guard incTy == .fn #[.mk true (.uint 8), .mk false .bool] .unit
#guard incTy != .fn #[.mk false (.uint 8), .mk false .bool] .unit
#guard incTy != .fn #[.mk true (.uint 8), .mk false .bool] .bool
#guard incTy != .fn #[.mk true (.uint 8)] .unit
#guard pred != Ty.tuple #[.bool]

/-!
A function value is its item and its signature. It serializes its package and its name, has the
size 1 and the depth 1, and its type is its signature.
-/
def inc : Value := .function 0 "inc" #[.mk true (.uint 8), .mk false .bool] .unit

#guard inc.serialize == "(function root inc)"
#guard inc.size == 1
#guard inc.depth == 1
#guard inc.ty? == some incTy
#guard inc.literal == "inc"
#guard inc.text == "fn (mut UInt[8], Bool) -> Unit"
#guard inc.measureCharge == 0
#guard !(inc.ty?.map (·.info.data)).getD true
#guard inc == .function 0 "inc" #[.mk true (.uint 8), .mk false .bool] .unit
#guard inc != .function 1 "dec" #[.mk true (.uint 8), .mk false .bool] .unit
#guard (Value.tuple #[inc]).ty? == some (.tuple #[incTy])
#guard (Value.tuple #[inc]).serialize == "(tuple ((function root inc)))"
#guard (Value.tuple #[inc]).size == 2
#guard (Value.tuple #[inc]).depth == 2
#guard (Value.list pred #[.function 2 "yes" #[] .bool]).serialize ==
  "(list (fn () bool) ((function root yes)))"
#guard (Value.list pred #[]).depth == 3
#guard ({ module := "Map", args := [inc] } : InstantiationId).serialize ==
  "(instantiation root Map ((function root inc)))"

/-!
The prelude struct `ReadResponse` has the token `prelude` in the place of the package. A user
struct with the same name and arguments serializes with `root`, so the two never share an
identity. A message names both in their source form.
-/
def response (pre : Bool) : Ty :=
  .struct 4 "ReadResponse" #[.type (.uint 8)] (Meta.struct [(Ty.uint 8).info, Ty.bool.info] [2])
    pre
#guard (response true).serialize == "(struct prelude ReadResponse ((type (uint 8))))"
#guard (response false).serialize == "(struct root ReadResponse ((type (uint 8))))"
#guard (response true).text == "ReadResponse[UInt[8]]"
#guard (response false).text == "ReadResponse[UInt[8]]"
#guard (response true) != (response false)
#guard (response true).size == (response false).size
#guard (Value.record (response true) #[.uint 8 3, .bool true]).serialize ==
  "(record (struct prelude ReadResponse ((type (uint 8)))) ((uint 8 3) (bool true)))"

/-!
An enum type (slice 3) is its item, its name, and its metadata. The metadata is the sums of a
record of `UInt[W]` and `UInt[P]`, without the second part when `P` is 0. The type has the size
1, sets the enum flag, and compares by its item. A static enum value has the size and the depth
of a record of its tag and its payload. It serializes as one container node, without the payload
when `P` is 0. Its measure charges 1 and the squares of the sizes of its two parts.
-/
def op : Ty := .enum 7 "Op" (Meta.enum 2 8)
def flag : Ty := .enum 8 "Flag" (Meta.enum 1 0)
#guard Meta.enumParts 2 8 == [Meta.finite 2, Meta.finite 8]
#guard Meta.enumParts 1 0 == [Meta.finite 1]
#guard op.info == ⟨10, 2, 3, 2, true, false, true⟩
#guard flag.info == ⟨1, 1, 2, 2, true, false, true⟩
#guard op.size == 1 && op.depth == 2 && op.zeroDepth == 3
#guard op.serialize == "(enum root Op ())"
#guard op.text == "Op"
#guard op != .enum 7 "Op" (Meta.enum 2 9)
#guard op.same (.enum 7 "Other" (Meta.enum 2 9)) && !op.same flag
#guard (Ty.array op 4).info.enums && (Ty.tuple #[.bool, op]).info.enums
#guard (Ty.list op).info.enums && (Ty.fn #[.mk false op] .bool).info.enums
#guard (Ty.struct 9 "H" #[] (Meta.struct [op.info] [])).info.enums
#guard !(packet 8).info.enums && !(Ty.array (.list .bool) 2).info.enums
#guard (Value.enum op 2 1 8 3).serialize == "(enum (enum root Op ()) 1 (uint 8 3))"
#guard (Value.enum flag 1 0 0 0).serialize == "(enum (enum root Flag ()) 0)"
#guard (Value.enum op 2 1 8 3).size == 3 && (Value.enum flag 1 0 0 0).size == 2
#guard (Value.enum op 2 1 8 3).size == op.info.zeroSize
#guard (Value.enum op 2 1 8 3).depth == 3 && (Value.enum op 2 1 8 3).depth == op.zeroDepth
#guard (Value.enum op 2 1 8 3).measureCharge == 3 && (Value.enum flag 1 0 0 0).measureCharge == 2
#guard (Value.enum op 2 1 8 3).ty? == some op
#guard (Value.enum op 2 1 8 3).text == "Op" && (Value.enum op 2 1 8 3).literal == "1"
#guard Value.enum op 2 1 8 3 == Value.enum op 2 1 8 3
#guard Value.enum op 2 1 8 3 != Value.enum op 2 1 8 4
#guard (Value.enum op 2 1 8 3).cmp (.enum op 2 2 8 0) == .lt
#guard (Value.enum op 2 1 8 3).cmp (.enum op 2 1 8 2) == .gt
#guard (Value.enum op 2 1 8 3).cmp (.enum op 2 1 8 3) == .eq

/-!
The handle types (slice 3, section 5.1). `Reg[T]`, `Wire[T]`, and `Input[T]` are a node with
`T`, `Mem[T, N]` adds the integer `N`, and `Instance[M, args]` holds its converted arguments, as
a struct type does. The metadata is that of `List[T]`: not hardware data, with the flags of `T`.
`Instance` has neither flag. They serialize as in section 7.1, print in their source form, and
compare by their parts. A handle type is never a zero.
-/
def counter : Ty := .inst 3 "Counter" #[.int 8]
#guard (Value.type (.reg (.uint 8))).serialize == "(type (reg (uint 8)))"
#guard (Value.type (.wire .bool)).serialize == "(type (wire bool))"
#guard (Value.type (.mem (.uint 8) 16)).serialize == "(type (mem (uint 8) 16))"
#guard (Value.type (.input (.uint 8))).serialize == "(type (input (uint 8)))"
#guard (Value.type counter).serialize == "(type (instance root Counter ((int 8))))"
#guard (Value.type (.inst 3 "Top" #[])).serialize == "(type (instance root Top ()))"
#guard (Value.type (.reg (packet 8))).serialize == "(type (reg (struct root Packet ((int 8)))))"
#guard (Ty.reg (.uint 8)).size == 3 && (Ty.wire .bool).size == 2 && (Ty.input .bool).size == 2
#guard (Ty.mem (.uint 8) 16).size == 4 && (Ty.mem .bool (2 ^ 64)).size == 4
#guard counter.size == 2 && (Ty.inst 3 "Top" #[]).size == 1
#guard (Ty.inst 3 "C" #[.type (.array .bool 4), .int (2 ^ 64)]).size == 6
#guard (Ty.reg (.uint 8)).depth == 2 && (Ty.mem (.array .bool 4) 16).depth == 3
#guard counter.depth == 2 && (Ty.inst 3 "Top" #[]).depth == 1
#guard (Ty.inst 3 "C" #[.type (.reg (.array .bool 4))]).depth == 4
#guard (Ty.reg (.uint 8)).info == ⟨0, 0, 0, 2, false, false, false⟩
#guard (Ty.mem (.array .bool 4) 16).info == ⟨0, 0, 0, 3, false, false, false⟩
#guard (Ty.wire op).info == ⟨0, 0, 0, 3, false, false, true⟩
#guard (Ty.input (.array op 2)).info.enums && (Ty.mem (.fn #[] .bool) 2).info.funcs
#guard counter.info == ⟨0, 0, 0, 2, false, false, false⟩
#guard (Ty.inst 3 "C" #[.type op]).info == ⟨0, 0, 0, 3, false, false, false⟩
#guard [Ty.reg .bool, .wire .bool, .input .bool, .mem .bool 2, counter].all
  fun t => t.info.depth == t.depth && t.zeroDepth == 1
#guard (Ty.reg (.uint 8)).text == "Reg[UInt[8]]"
#guard (Ty.wire .bool).text == "Wire[Bool]"
#guard (Ty.input (.uint 8)).text == "Input[UInt[8]]"
#guard (Ty.mem (.uint 8) 16).text == "Mem[UInt[8], 16]"
#guard counter.text == "Instance[Counter, 8]"
#guard (Ty.inst 3 "Top" #[]).text == "Instance[Top]"
#guard (Ty.inst 3 "C" #[.type (.reg .bool), .bool true]).text == "Instance[C, Reg[Bool], true]"
#guard (Ty.mem .bool (2 ^ 300)).text == "Mem[Bool, an integer of 301 bits]"
#guard (Value.type (.reg .bool)).literal == "Reg[Bool]"
#guard (Value.type (.reg .bool)).text == "a type"
#guard Ty.reg .bool == Ty.reg .bool && Ty.reg .bool != Ty.wire .bool
#guard Ty.mem .bool 2 != Ty.mem .bool 3 && counter != .inst 3 "Counter" #[.int 9]
#guard counter.same (.inst 3 "Other" #[.int 8]) && !counter.same (.inst 4 "Counter" #[.int 8])
#guard (Ty.reg .bool).cmp (.reg (.uint 1)) == .lt && (Ty.reg .bool).cmp (.wire .bool) == .lt
#guard (Ty.mem .bool 3).cmp (.mem .bool 2) == .gt && counter.cmp (.inst 3 "C" #[.int 9]) == .lt
#guard (Ty.enum 0 "E" (Meta.enum 1 0)).cmp (.reg .bool) == .lt
#guard (Value.type (.reg .bool)).measureCharge == 0

/-!
The text of a type or a value in a message has at most 1024 bytes, cut at a character, and then
`...` (section 5.5). The walk stops soon after the bound, so a type with `2^64` parts prints at
once. An integer above 256 bits prints its bit length.
-/
def tall : Nat → Ty
  | 0 => .bool
  | k + 1 => .list (tall k)
def wide (k : Nat) : Ty := .tuple (Array.replicate k (.uint 8))
def huge : Nat → Ty
  | 0 => .bool
  | k + 1 => let t := huge k; .tuple #[t, t]
#guard (tall 300).text.utf8ByteSize == 1027 && (tall 300).text.endsWith "List[List..."
#guard (tall 170).text.utf8ByteSize == 1024 && (tall 170).text.endsWith "]]]"
#guard (wide 113).text.utf8ByteSize == 1017 && (wide 113).text.endsWith "UInt[8])"
#guard (wide 114).text.utf8ByteSize == 1027 && (wide 114).text.endsWith "UInt[8..."
#guard (wide (2 ^ 20)).text.utf8ByteSize == 1027 && (wide (2 ^ 20)).text.endsWith "UInt[8..."
#guard (Value.tuple (Array.replicate (2 ^ 20) (.uint 8 0))).text.utf8ByteSize == 1027
/-!
Past the bound, each walk returns its text at once and visits no part. Thus a list of `2^20`
parts adds one step after the bound, not one step for each part.
-/
example (o : String) (h : textLimit < o.utf8ByteSize) (t : Ty) : t.put o = o := by
  unfold Ty.put; simp [h]
example (o : String) (h : textLimit < o.utf8ByteSize) (ts : List Ty) : Ty.putAll o ts = o := by
  unfold Ty.putAll; simp [h]
example (o : String) (h : textLimit < o.utf8ByteSize) (ps : List TyParam) :
    TyParam.putAll o ps = o := by
  unfold TyParam.putAll; simp [h]
example (o : String) (h : textLimit < o.utf8ByteSize) (v : Value) : v.put o = o := by
  unfold Value.put; simp [h]
example (o : String) (h : textLimit < o.utf8ByteSize) (xs : List Value) :
    Value.putAll o xs = o := by
  unfold Value.putAll; simp [h]
def named (n : Nat) : Ty := .struct 0 "S" #[.str (String.ofList (List.replicate n 'a'))] Meta.static
#guard (named 1019).text == "S[\"" ++ String.ofList (List.replicate 1019 'a') ++ "\"]"
#guard (named 1020).text == "S[\"" ++ String.ofList (List.replicate 1020 'a') ++ "\"..."
#guard (huge 64).text.utf8ByteSize == 1027 && (huge 64).text.endsWith "(((Bool, Bo..."
#guard (Value.tuple (Array.replicate 1000 (.uint 8 0))).text.utf8ByteSize == 1027
#guard (Value.str (String.ofList (List.replicate 5000 'é'))).literal.utf8ByteSize == 1026
#guard (Ty.struct 0 "S" #[.str (String.ofList (List.replicate 5000 'é'))] Meta.static).text ==
  "S[\"" ++ String.ofList (List.replicate 510 'é') ++ "..."
#guard (Ty.array .bool (2 ^ 256)).text == "[Bool; an integer of 257 bits]"
#guard (Ty.struct 0 "P" #[.int (-(2 ^ 300))] Meta.static).text ==
  "P[a negative integer of 301 bits]"
#guard (Value.enum (.enum 0 "E" (Meta.enum 300 0)) 300 (2 ^ 299) 0 0).literal ==
  "an integer of 300 bits"

end Silicon.Source.Test.Value
