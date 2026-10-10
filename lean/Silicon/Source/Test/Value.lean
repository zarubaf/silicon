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

end Silicon.Source.Test.Value
