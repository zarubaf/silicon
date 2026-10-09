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
#guard has (printed operations) "%o_out = comb.xor %l,"
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
#guard !has (printed readOrder) "%l ="
#guard has (printed readOrder) "seq.compreg %m.r4_data, %clk"
#guard has (printed readOrder)
  "w0_addr: %m.r5_data: i1, w0_data: %m.r6_data: i1, w0_en: %m.r7_data: i1"
#guard has (printed readOrder) "hw.output %m.r8_data : i1"

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

#guard has (printed forwardOutput) "%q = comb.add %a,"
#guard !has (printed forwardOutput) "comb.or"
#guard has (printed forwardOutput) "hw.output %q, %a : i8, i8"

#guard has (printed counter) "hw.output %silicon_reg_r : i8"
#guard !has (printed counter) "comb.or"
#guard has (printed external) "hw.output %u.y : i4"
#guard !has (printed external) "comb.or"
#guard has (printed pow2) "hw.output %m.r0_data, %m.r1_data : i8, i8"
#guard !has (printed pow2) "comb.or"

private def aliasChain : String := "(design top (module top
  (input a (bits 8)) (output q (bits 8))
  (assign q x) (let x (bits 8) y) (let y (bits 8) z) (let z (bits 8) a)))"

private def aliasChainText : String :=
  "hw.module @top(in %a : i8, out q : i8) {\n  hw.output %a : i8\n}\n"

#guard printed aliasChain == aliasChainText
#guard (match parse aliasChain >>= check with
  | .ok t => Mlir.print (lower t) == aliasChainText
  | .error _ => false)

private def aliasConsumers : String := "(design top
  (extern child (input d (bits 8)) (output o (bits 8)) (deps o (d)))
  (module top
    (input clk clock) (input rst (bits 1)) (input a (bits 4)) (input d (bits 8))
    (output q (bits 8))
    (reg r (bits 8) clk (reset sync resetAlias dataAlias))
    (next r resultAlias)
    (inst u child (d dataAlias))
    (mem m (bits 8) 12 clk)
    (write m 0 addrAlias dataAlias resetAlias)
    (assign q (read m addrAlias))
    (let resultAlias (bits 8) u.o)
    (let addrAlias (bits 4) a)
    (let dataAlias (bits 8) d)
    (let resetAlias (bits 1) rst)))"

private def aliasConsumersCorrect (text : String) : Bool :=
  has text "seq.compreg %u.o, %clk reset %rst, %d : i8" &&
  has text "@child(d: %d: i8)" && has text "comb.icmp ult %a," &&
  has text "comb.and %rst," && has text "r0_addr: %a: i4, w0_addr: %a: i4, w0_data: %d: i8" &&
  !has text "Alias" && !has text "comb.or"

#guard aliasConsumersCorrect (printed aliasConsumers)
#guard (match parse aliasConsumers >>= check with
  | .ok t => aliasConsumersCorrect (Mlir.print (lower t))
  | .error _ => false)

private def unorderedExtern : String := "(design top
  (extern blk (input c clock) (output y (bits 4)) (input a (bits 4)) (deps y (a)))
  (module top (input clk clock) (input a (bits 4)) (output q (bits 4))
    (inst u blk (a a) (c clk)) (assign q u.y)))"

private def unorderedModule : String := "(design top
  (module blk (input c clock) (output y (bits 4)) (input a (bits 4)) (assign y a))
  (module top (input clk clock) (input a (bits 4)) (output q (bits 4))
    (inst u blk (a a) (c clk)) (assign q u.y)))"

#guard (match parse unorderedExtern >>= check with
  | .ok t => has (Mlir.print (lower t))
    "%u.y = hw.instance \"u\" @blk(c: %clk: !seq.clock, a: %a: i4) -> (y: i4)"
  | .error _ => false)
#guard (match parse unorderedModule >>= check with
  | .ok t => has (Mlir.print (lower t))
    "%u.y = hw.instance \"u\" @blk(c: %clk: !seq.clock, a: %a: i4) -> (y: i4)"
  | .error _ => false)

private def ownOutput : String := "(design top (module top
  (input a (bits 8)) (output q (bits 8)) (output z (bits 8))
  (assign q (add a a)) (assign z (add q q))))"

#guard has (printed ownOutput) "%q = comb.add %a, %a : i8"
#guard has (printed ownOutput) "%z = comb.add %q, %q : i8"

end Silicon.Core.Test.Lower
