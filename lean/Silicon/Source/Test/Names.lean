-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Names

/-!
These tests check the names of section 7 of the front-end spec. The round trip
`decode (encode p) = some p` holds on each name of a generated set. The set has user names equal
to each core keyword, names close to the made fields, and each made field form. Each encoded
name matches the core name pattern and is not a core keyword.
-/

namespace Silicon.Source.Test.Names

open Silicon.Source Silicon.Source.Names

/-! User names: each core keyword, backend kinds, and names close to the made fields. -/
def users : List String :=
  Core.keywords ++ ["clk", "rst", "silicon_reg_r", "x", "_", "_0k", "k0", "n5", "c3", "v2",
    "b1", "h0", "t4", "e2", "ret", "rdata", "A_b9", "Counter"]

/-! Each made field form, with the boundary values of each number. -/
def made : List Field :=
  [.int 0, .int 5, .int (-5), .int 18446744073709551616, .int (-1), .call 0, .call 3,
   .version 1, .version 12, .bool true, .bool false, .digest "3f2a9c0b1d4e5f60", .digest "0",
   .temp 0, .temp 4, .elem 0, .elem 2, .elem 18446744073709551616] ++ roles.map .role

def fields : List Field := made ++ (users.map .user)

/-! Names of one, two, and three fields. -/
def names : List Name :=
  users.map (⟨·, []⟩) ++ users.flatMap (fun u => fields.map (⟨u, [·]⟩)) ++
    ["x", "add", "i"].flatMap fun u => fields.flatMap fun f => made.map (⟨u, [f, ·]⟩)

def roundTrip (p : Name) : Bool := decode (encode p) == some p

def legal (p : Name) : Bool := Core.validName (encode p)

#guard names.length > 1000
#guard names.all Name.valid
#guard names.all roundTrip
#guard names.all legal

/-! A user name alone that equals a core keyword gets `0k`. No other name gets it. -/
#guard encode ⟨"add", []⟩ == "add$0k"
#guard encode ⟨"add", [.version 1]⟩ == "add$1v"
#guard encode ⟨"addx", []⟩ == "addx"
#guard encode ⟨"i", [.int 2, .user "r"]⟩ == "i$2$r"
#guard encode ⟨"f", [.call 0, .user "t"]⟩ == "f$0c$t"
#guard encode ⟨"d", [.role .clk]⟩ == "d$0clk"
#guard encode ⟨"i", [.int (-5)]⟩ == "i$5n"
#guard encode ⟨"Fifo", [.int 16, .bool true]⟩ == "Fifo$16$1b"

/-! The leaf names of section 7.3. An element `<k>e` differs from the loop value `k`. -/
#guard encode ⟨"r", [.elem 2]⟩ == "r$2e"
#guard encode ⟨"q", [.version 1, .user "xs", .elem 0]⟩ == "q$1v$xs$0e"
#guard encode ⟨"f", [.call 0, .role .ret, .elem 0]⟩ == "f$0c$0ret$0e"
#guard decode "r$2e" == some ⟨"r", [.elem 2]⟩
#guard decode "p$0e$x" == some ⟨"p", [.elem 0, .user "x"]⟩
#guard decode "p$0$x" == some ⟨"p", [.int 0, .user "x"]⟩
#guard decode "x$02e" == none
#guard decode "x$2e2" == none
#guard decode "x$2ee" == none

/-! `decode` accepts only the texts that `encode` makes. -/
#guard decode "add" == none
#guard decode "x$0k" == none
#guard decode "add$0k$1v" == none
#guard decode "x$05" == none
#guard decode "x$0n" == none
#guard decode "x$2b" == none
#guard decode "x$0h" == none
#guard decode "x$0hA" == none
#guard decode "x$$y" == none
#guard decode "x$" == none
#guard decode "5$x" == none
#guard decode "" == none
#guard decode "x$0clkx" == none
#guard decode "x$0ret" == some ⟨"x", [.role .ret]⟩

/-! A path shares its frame. Its name lists the fields from the outside in. -/
#guard ((Path.child none "i").push (.int 2) |> some |> (Path.child · "r")).name ==
  ⟨"i", [.int 2, .user "r"]⟩

/-! The readable module name, and the digest form for other arguments. -/
def id (m : String) (args : List Value) : InstantiationId := ⟨m, args⟩

#guard encode (moduleName sha16 (id "Counter" [.int 8])) == "Counter$8"
#guard encode (moduleName sha16 (id "Fifo" [.int 16, .bool true])) == "Fifo$16$1b"
#guard encode (moduleName sha16 (id "M" [.int (-5)])) == "M$5n"
#guard encode (moduleName sha16 (id "Top" [])) == "Top"
#guard encode (moduleName sha16 (id "add" [])) == "add$0k"
#guard encode (moduleName sha16 (id "M" [.str "a"])) ==
  "M$0h" ++ sha16 "(instantiation root M ((string \"a\")))"
#guard encode (moduleName sha16 (id "M" [.type .bool])) ==
  "M$0h" ++ sha16 "(instantiation root M ((type bool)))"

/-! The 64-byte limit: a name of 64 bytes stays readable, and one of 65 bytes takes the digest. -/
def long (n : Nat) : String := String.ofList (List.replicate n 'a')

#guard encode (moduleName sha16 (id (long 62) [.int 5])) == long 62 ++ "$5"
#guard encode (moduleName sha16 (id (long 63) [.int 5])) ==
  long 63 ++ "$0h" ++ sha16 s!"(instantiation root {long 63} ((int 5)))"
#guard encode (moduleName sha16 (id (long 64) [])) == long 64
#guard (encode (moduleName sha16 (id (long 65) []))).startsWith (long 65 ++ "$0h")
#guard encode (moduleName sha16 (id "M" [.int (10 ^ 61)])) == "M$1" ++ String.ofList
  (List.replicate 61 '0')
#guard (encode (moduleName sha16 (id "M" [.int (10 ^ 62)]))).startsWith "M$0h"
#guard (encode (moduleName sha16 (id "M" [.int (2 ^ 300)]))).startsWith "M$0h"

/-! A keyword module without arguments keeps the readable form. -/
#guard (moduleName sha16 (id "add" [])).rest.isEmpty

/-! The sizes that the charges read equal the lengths of the texts. -/
def ids : List InstantiationId :=
  [id "C" [], id "Counter" [.int 8, .bool true], id "M" [.str "a\"b\n", .int (-5)],
   id "M" [.type (.uint 8), .uint 8 3, .sint 4 (-1)]]
#guard ids.all fun i => InstantiationId.renderSize i.module (i.args.map Value.serialize) ==
  i.serialize.utf8ByteSize
#guard ids.all fun i => byteSize (moduleName sha16 i) == (encode (moduleName sha16 i)).utf8ByteSize
#guard names.all fun p => byteSize p == (encode p).utf8ByteSize

/-! Each emitted name is a legal core name. -/
#guard [id "Counter" [.int 8], id "add" [], id "M" [.str "x"], id (long 70) []].all
  fun i => legal (moduleName sha16 i) && roundTrip (moduleName sha16 i)

end Silicon.Source.Test.Names
