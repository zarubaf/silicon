import Silicon.Core.Mlir.Print

namespace Silicon.Core.Test.Mlir

open Silicon.Core.Mlir

def counter : Design := ⟨[.module {
  name := "counter"
  ports := [⟨.input, "clk", .clock⟩, ⟨.input, "rst", .int 1⟩,
    ⟨.input, "en", .int 1⟩, ⟨.output, "q", .int 8⟩]
  body := [(["silicon_t0"], .constant 8 0), (["silicon_t1"], .constant 8 1),
    (["silicon_t2"], .comb "add" ["silicon_reg_r", "silicon_t1"] 8),
    (["silicon_t3"], .mux "en" "silicon_t2" "silicon_reg_r" 8),
    (["silicon_reg_r"], .compreg "silicon_t3" "clk" (some ("rst", "silicon_t0")) (.int 8))]
  outputs := [("silicon_reg_r", .int 8)]
}]⟩

#guard print counter ==
  "hw.module @counter(in %clk : !seq.clock, in %rst : i1, in %en : i1, out q : i8) {\n" ++
  "  %silicon_t0 = hw.constant 0 : i8\n" ++
  "  %silicon_t1 = hw.constant 1 : i8\n" ++
  "  %silicon_t2 = comb.add %silicon_reg_r, %silicon_t1 : i8\n" ++
  "  %silicon_t3 = comb.mux %en, %silicon_t2, %silicon_reg_r : i8\n" ++
  "  %silicon_reg_r = seq.compreg %silicon_t3, %clk reset %rst, %silicon_t0 : i8\n" ++
  "  hw.output %silicon_reg_r : i8\n}\n"

#guard print ⟨[.extern "blk" [⟨.input, "c", .clock⟩, ⟨.input, "a", .int 4⟩,
    ⟨.output, "y", .int 4⟩], .module ⟨"top", [],
    [(["u.y"], .instance "u" "blk" [("c", "clk", .clock), ("a", "a", .int 4)]
      [("y", .int 4)])], []⟩]⟩ ==
  "hw.module.extern @blk(in %c : !seq.clock, in %a : i4, out y : i4)\n" ++
  "hw.module @top() {\n" ++
  "  %u.y = hw.instance \"u\" @blk(c: %clk: !seq.clock, a: %a: i4) -> (y: i4)\n" ++
  "  hw.output\n}\n"

private def line (op : Op) : String := print ⟨[.module ⟨"m", [], [(["v"], op)], []⟩]⟩
private def expected (s : String) : String :=
  "hw.module @m() {\n  %v = " ++ s ++ "\n  hw.output\n}\n"

#guard line (.arrayGet "mem" "idx" 16 8 4) ==
  expected "hw.array_get %mem[%idx] : !hw.array<16xi8>, i4"
#guard line (.arrayInject "mem" "idx" "data" 16 8 4) ==
  expected "hw.array_inject %mem[%idx], %data : !hw.array<16xi8>, i4"
#guard line (.arrayMux "en" "new" "old" 16 8) ==
  expected "comb.mux %en, %new, %old : !hw.array<16xi8>"
#guard line (.extract "a" 2 8 4) == expected "comb.extract %a from 2 : (i8) -> i4"
#guard line (.concat "a" "b" 8 4) == expected "comb.concat %a, %b : i8, i4"
#guard line (.replicate "a" 8 16) == expected "comb.replicate %a : (i8) -> i16"
#guard line (.constant 8 255) == expected "hw.constant 255 : i8"
#guard line (.compreg "next" "clk" none (.int 8)) ==
  expected "seq.compreg %next, %clk : i8"
#guard (["add", "sub", "mul", "and", "or", "xor", "shl", "shru", "shrs"].all fun n =>
  line (.comb n ["a", "b"] 8) == expected ("comb." ++ n ++ " %a, %b : i8"))
#guard ([(Pred.eq, "eq"), (.ne, "ne"), (.ult, "ult"), (.ule, "ule"), (.ugt, "ugt"),
    (.uge, "uge"), (.slt, "slt"), (.sle, "sle"), (.sgt, "sgt"), (.sge, "sge")].all
  fun (p, s) => line (.icmp p "a" "b" 8) == expected ("comb.icmp " ++ s ++ " %a, %b : i8"))
#guard print ⟨[.module ⟨"empty", [], [], []⟩]⟩ ==
  "hw.module @empty() {\n  hw.output\n}\n"
#guard print ⟨[.module ⟨"m", [],
    [([], .instance "u" "sink" [] []),
     (["u.x", "u.y"], .instance "v" "pair" [] [("x", .int 4), ("y", .int 8)])],
    [("u.x", .int 4), ("u.y", .int 8)]⟩]⟩ ==
  "hw.module @m() {\n  hw.instance \"u\" @sink() -> ()\n" ++
  "  %u.x, %u.y = hw.instance \"v\" @pair() -> (x: i4, y: i8)\n" ++
  "  hw.output %u.x, %u.y : i4, i8\n}\n"

end Silicon.Core.Test.Mlir
