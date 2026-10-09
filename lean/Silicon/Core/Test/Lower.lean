import Silicon.Core.Lower
import Silicon.Core.Check
import Silicon.Core.Text
import Silicon.Core.Mlir.Print

namespace Silicon.Core.Test.Lower

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private def checked (source : String) : Except Error Typed.Design := do
  let d ← parse source
  let _ ← check d
  check (canonicalize d)

private def printed (source : String) : String :=
  match checked source with
  | .ok t => Mlir.print (lower t)
  | .error _ => "CHECK FAILED"

private def has (text part : String) : Bool := (text.splitOn part).length > 1

private def occurrences (text part : String) : Nat := (text.splitOn part).length - 1

private def counter : String := "(design counter
  (module counter
    (input clk clock)
    (input rst (bits 1))
    (input en (bits 1))
    (output q (bits 8))
    (reg r (bits 8) clk (reset sync rst (const 8 0)))
    (let inc (bits 8) (add r (const 8 1)))
    (next r (mux en inc r))
    (assign q r)))"

private def memory : String := "(design top
  (module top
    (input clk clock)
    (input x (bits 4))
    (input d (bits 8))
    (input we (bits 1))
    (output p (bits 8))
    (mem m (bits 8) 12 clk)
    (write m 0 x d we)
    (assign p (read m x))))"

private def pow2 : String := "(design top
  (module top
    (input clk clock)
    (input x (bits 4))
    (input y (bits 4))
    (input d (bits 8))
    (input we (bits 1))
    (output p (bits 8))
    (output q (bits 8))
    (mem m (bits 8) 16 clk)
    (write m 0 x d we)
    (write m 1 y d we)
    (assign p (read m x))
    (assign q (read m y))))"

private def counts : String := "(design top
  (module top
    (input clk clock)
    (input a (bits 4))
    (input b (bits 4))
    (input d (bits 8))
    (input e (bits 8))
    (input we (bits 1))
    (output p (bits 8))
    (output q (bits 8))
    (output s (bits 8))
    (mem m (bits 8) 12 clk)
    (mem n (bits 8) 12 clk)
    (write m 0 a d we)
    (write n 0 a d we)
    (write n 1 b e we)
    (assign p (read m a))
    (assign q (read n a))
    (assign s (read n b))))"

private def depth1 : String := "(design top
  (module top
    (input clk clock)
    (input a (bits 1))
    (input d (bits 4))
    (input we (bits 1))
    (output p (bits 4))
    (mem m (bits 4) 1 clk)
    (write m 0 a d we)
    (assign p (read m a))))"

private def external : String := "(design top
  (extern blk
    (input c clock)
    (input a (bits 4))
    (output y (bits 4))
    (deps y (a)))
  (module top
    (input clk clock)
    (input a (bits 4))
    (output q (bits 4))
    (inst u blk (c clk) (a a))
    (assign q u.y)))"

private def operations : String := "(design ops
  (module ops
    (input a (bits 8))
    (input b (bits 8))
    (input s (bits 1))
    (output o_add (bits 8))
    (output o_sub (bits 8))
    (output o_mul (bits 8))
    (output o_and (bits 8))
    (output o_or (bits 8))
    (output o_xor (bits 8))
    (output o_not (bits 8))
    (output o_shl (bits 8))
    (output o_shru (bits 8))
    (output o_shrs (bits 8))
    (output o_cat (bits 16))
    (output o_mux (bits 8))
    (output o_ext (bits 4))
    (output o_rep (bits 16))
    (output o_eq (bits 1))
    (output o_ne (bits 1))
    (output o_ult (bits 1))
    (output o_ule (bits 1))
    (output o_ugt (bits 1))
    (output o_uge (bits 1))
    (output o_slt (bits 1))
    (output o_sle (bits 1))
    (output o_sgt (bits 1))
    (output o_sge (bits 1))
    (output o_out (bits 8))
    (let l (bits 8) (add a b))
    (assign o_add l)
    (assign o_out (not o_add))
    (assign o_sub (sub a b))
    (assign o_mul (mul a b))
    (assign o_and (and a b))
    (assign o_or (or a b))
    (assign o_xor (xor a b))
    (assign o_not (not a))
    (assign o_shl (shl a b))
    (assign o_shru (shru a b))
    (assign o_shrs (shrs a b))
    (assign o_cat (concat a b))
    (assign o_mux (mux s a b))
    (assign o_ext (extract a 2 4))
    (assign o_rep (replicate a 2))
    (assign o_eq (icmp eq a b))
    (assign o_ne (icmp ne a b))
    (assign o_ult (icmp ult a b))
    (assign o_ule (icmp ule a b))
    (assign o_ugt (icmp ugt a b))
    (assign o_uge (icmp uge a b))
    (assign o_slt (icmp slt a b))
    (assign o_sle (icmp sle a b))
    (assign o_sgt (icmp sgt a b))
    (assign o_sge (icmp sge a b))))"

#guard has (printed counter) "%silicon_reg_r = seq.compreg"
#guard has (printed counter) "reset %rst,"
#guard has (printed memory) "@silicon_mem_12x8_r1w1"
#guard occurrences (printed memory) "comb.icmp ult" == 2
#guard has (printed memory) "%p = comb.mux"
#guard has (printed memory) "comb.and %we,"
#guard occurrences (printed pow2) "comb.icmp ult" == 0
#guard has (printed pow2) "@silicon_mem_16x8_r2w2"
#guard occurrences (printed depth1) "comb.icmp ult" == 2
#guard has (printed depth1) "hw.constant 1 : i1"
#guard (match checked counts with
  | .ok t => (memoryConfigs t).map MemConfig.moduleName
  | .error _ => []) == ["silicon_mem_12x8_r1w1", "silicon_mem_12x8_r2w2"]
#guard has (printed external) "hw.module.extern @blk"
#guard has (printed external)
  "%u.y = hw.instance \"u\" @blk(c: %clk: !seq.clock, a: %a: i4) -> (y: i4)"
#guard has (printed operations) "%o_out = comb.xor %o_add,"
#guard has (printed operations) "hw.constant 255 : i8"
#guard has (printed operations) "%o_cat = comb.concat %a, %b : i8, i8"
#guard has (printed operations) "%o_ext = comb.extract %a from 2 : (i8) -> i4"
#guard has (printed operations) "%o_rep = comb.replicate %a : (i8) -> i16"
#guard ["add", "sub", "mul", "and", "or", "xor", "shl", "shru", "shrs"].all
  (fun op => has (printed operations) ("comb." ++ op ++ " "))
#guard ["eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"].all
  (fun p => has (printed operations) ("comb.icmp " ++ p ++ " %a, %b : i8"))
#guard printed "(design top (module top (input a (bits 1)) (input clk clock)))" ==
  "hw.module @top(in %a : i1, in %clk : !seq.clock) {\n  hw.output\n}\n"

private def nested : String := "(design top (module top
  (input clk clock) (input a (bits 1)) (output q (bits 1))
  (mem m (bits 1) 2 clk) (assign q (read m (read m a)))))"

#guard has (printed nested) "r0_addr: %m.r1_data: i1, r1_addr: %a: i1"
#guard has (printed nested) "@silicon_mem_2x1_r2w0"

private def unordered : String := "(design top (module top
  (input clk clock) (input rst (bits 1)) (output q (bits 8))
  (next r (const 8 1)) (assign q r)
  (reg r (bits 8) clk (reset sync rst (const 8 7)))))"

#guard (match parse unordered >>= check with
  | .ok t => has (Mlir.print (lower t)) "reset %rst,"
  | .error _ => false)

private def readOrder : String := "(design top
  (module child (input x (bits 1)))
  (module top (input clk clock) (output q (bits 1))
    (mem m (bits 1) 2 clk)
    (reg r (bits 1) clk (reset sync (read m (const 1 0)) (read m (const 1 1))))
    (inst u child (x (read m (const 1 0))))
    (let l (bits 1) (read m (const 1 1)))
    (next r (read m (const 1 0)))
    (write m 0 (read m (const 1 1)) (read m (const 1 0)) (read m (const 1 1)))
    (assign q (read m (const 1 0)))))"

#guard has (printed readOrder) "@silicon_mem_2x1_r9w1"
#guard has (printed readOrder) "reset %m.r0_data, %m.r1_data"
#guard has (printed readOrder) "@child(x: %m.r2_data: i1)"
#guard has (printed readOrder) "%l = comb.or %m.r3_data, %m.r3_data : i1"
#guard has (printed readOrder) "seq.compreg %m.r4_data, %clk"
#guard has (printed readOrder)
  "w0_addr: %m.r5_data: i1, w0_data: %m.r6_data: i1, w0_en: %m.r7_data: i1"
#guard has (printed readOrder) "%q = comb.or %m.r8_data, %m.r8_data : i1"

private def duplicateConfigs : String := "(design top
  (module z (input clk clock) (mem a (bits 1) 2 clk) (mem b (bits 1) 2 clk))
  (module top (input clk clock) (mem m (bits 1) 2 clk)))"

#guard (match checked duplicateConfigs with
  | .ok t => (memoryConfigs t).map MemConfig.moduleName
  | .error _ => []) == ["silicon_mem_2x1_r0w0"]
#guard occurrences (printed duplicateConfigs) "hw.module.extern @silicon_mem_2x1_r0w0" == 1
#guard (printed duplicateConfigs).startsWith "hw.module.extern @silicon_mem_2x1_r0w0"

private def forwardOutput : String := "(design top (module top
  (input a (bits 8)) (output q (bits 8)) (output z (bits 8))
  (assign q (add z (const 8 1))) (assign z a)))"

#guard has (printed forwardOutput) "%q = comb.add %z,"
#guard has (printed forwardOutput) "%z = comb.or %a, %a : i8"
#guard has (printed forwardOutput) "hw.output %q, %z : i8, i8"

end Silicon.Core.Test.Lower
