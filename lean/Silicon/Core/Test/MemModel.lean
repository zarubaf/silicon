-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.MemModel
import Silicon.Core.Mlir.Print

/-!
These tests check memory port order, array sizes, and write priority.
-/

namespace Silicon.Core.Test.MemModel

open Silicon.Core.Mlir

#guard MemConfig.moduleName ⟨12, 8, 1, 1⟩ == "mem$$12x8_r1w1"
#guard MemConfig.ports ⟨12, 8, 2, 1⟩ =
  [⟨.input, "clk", .clock⟩, ⟨.input, "r0_addr", .int 4⟩,
   ⟨.output, "r0_data", .int 8⟩, ⟨.input, "r1_addr", .int 4⟩,
   ⟨.output, "r1_data", .int 8⟩, ⟨.input, "w0_addr", .int 4⟩,
   ⟨.input, "w0_data", .int 8⟩, ⟨.input, "w0_en", .int 1⟩]

private def registers (c : MemConfig) : List (List String × Op) :=
  (memModel c).body.filter fun (_, op) => match op with
    | .compreg .. => true
    | _ => false

#guard registers ⟨1, 4, 1, 1⟩ =
  [(["reg$$mem"], .compreg "w0_next" "clk" none (.array 2 4))]
#guard registers ⟨12, 8, 1, 1⟩ =
  [(["reg$$mem"], .compreg "w0_next" "clk" none (.array 16 8))]
#guard registers ⟨16, 8, 1, 1⟩ =
  [(["reg$$mem"], .compreg "w0_next" "clk" none (.array 16 8))]
#guard registers ⟨12, 8, 0, 0⟩ =
  [(["reg$$mem"], .compreg "reg$$mem" "clk" none (.array 16 8))]
#guard (memModel ⟨12, 8, 0, 0⟩).outputs = []
#guard (memModel ⟨12, 8, 2, 0⟩).outputs = ["r0_data", "r1_data"]
#guard (memModel ⟨12, 8, 2, 0⟩).body.take 2 =
  [(["r0_data"], .arrayGet "reg$$mem" "r0_addr" 16 8 4),
   (["r1_data"], .arrayGet "reg$$mem" "r1_addr" 16 8 4)]

#guard Mlir.print ⟨[.module (memModel ⟨12, 8, 1, 2⟩)]⟩ ==
  "hw.module @mem$$12x8_r1w2(in %clk : !seq.clock, " ++
  "in %r0_addr : i4, out r0_data : i8, " ++
  "in %w0_addr : i4, in %w0_data : i8, in %w0_en : i1, " ++
  "in %w1_addr : i4, in %w1_data : i8, in %w1_en : i1) {\n" ++
  "  %r0_data = hw.array_get %reg$$mem[%r0_addr] : !hw.array<16xi8>, i4\n" ++
  "  %w0_set = hw.array_inject %reg$$mem[%w0_addr], %w0_data : !hw.array<16xi8>, i4\n" ++
  "  %w0_next = comb.mux %w0_en, %w0_set, %reg$$mem : !hw.array<16xi8>\n" ++
  "  %w1_set = hw.array_inject %w0_next[%w1_addr], %w1_data : !hw.array<16xi8>, i4\n" ++
  "  %w1_next = comb.mux %w1_en, %w1_set, %w0_next : !hw.array<16xi8>\n" ++
  "  %reg$$mem = seq.compreg %w1_next, %clk : !hw.array<16xi8>\n" ++
  "  hw.output %r0_data : i8\n}\n"

end Silicon.Core.Test.MemModel
