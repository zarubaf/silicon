import Silicon.Core.Interp.Named
import Silicon.Core.Text

/-! Execution tests start from zero and use designs accepted by the checker. -/
namespace Silicon.Core.Test.Interp

open Semantics

private def runRaw (raw : Design) (vectors : List (List (String × Nat))) :
    Except String (List (List Nat)) :=
  match accepted : check raw with
  | .error _ => .error "check"
  | .ok typed =>
    let d := CertifiedDesign.ofCheck raw typed accepted
    if noExterns : typed.externs = [] then
      .ok ((namedRun d vectors noExterns).map (List.map Prod.snd))
    else .error "extern"

private def runText (text : String) (vectors : List (List (String × Nat))) :
    Option (List (List Nat)) :=
  match parse text with
  | .error _ => none
  | .ok raw => (runRaw raw vectors).toOption

private def counter := "(design counter
  (module counter
    (input clk clock) (input rst (bits 1)) (input en (bits 1)) (output q (bits 8))
    (reg r (bits 8) clk (reset sync rst (const 8 0)))
    (let inc (bits 8) (add r (const 8 1)))
    (next r (mux en inc r)) (assign q r)))"

#guard runText counter (List.replicate 4 [("en", 1), ("rst", 0)]) ==
  some [[0], [1], [2], [3]]
#guard runText counter [[("en", 1)], [("rst", 1)], [], [("en", 1)], []] ==
  some [[0], [1], [0], [0], [1]]

private def memory := "(design memtest
  (module memtest
    (input clk clock) (input a (bits 4)) (input d (bits 8)) (input en (bits 1))
    (output q (bits 8)) (mem cells (bits 8) 12 clk)
    (write cells 0 a d en) (assign q (read cells a))))"

#guard runText memory [[("a", 11), ("d", 42), ("en", 1)], [("a", 11)],
  [("a", 13), ("d", 99), ("en", 1)], [("a", 11)], [("a", 13)]] ==
    some [[0], [42], [0], [42], [0]]

/-! An invalid write preserves all twelve cells, not only the last valid cell. -/
#guard runText memory
  ((List.range 12).map (fun a => [("a", a), ("d", a + 1), ("en", 1)]) ++
    (List.range 12).map (fun a => [("a", a)]) ++
    [[("a", 13), ("d", 99), ("en", 1)]] ++
    (List.range 12).map (fun a => [("a", a)])) ==
      some (List.replicate 12 [0] ++ (List.range 12).map (fun a => [a + 1]) ++
        [[0]] ++ (List.range 12).map (fun a => [a + 1]))

private def shifts := "(design shifts
  (module shifts
    (input x (bits 8)) (input n (bits 8))
    (output l (bits 8)) (output u (bits 8)) (output s (bits 8))
    (assign l (shl x n)) (assign u (shru x n)) (assign s (shrs x n))))"

#guard runText shifts [[("x", 128), ("n", 8)], [("x", 128), ("n", 255)],
  [("x", 127), ("n", 8)], [("x", 127), ("n", 255)]] ==
    some [[0, 0, 255], [0, 0, 255], [0, 0, 0], [0, 0, 0]]

private def handshake := "(design top
  (module stage (input x (bits 8)) (input ack (bits 1))
    (output y (bits 8)) (output ready (bits 1))
    (assign y x) (assign ready ack))
  (module top (input x (bits 8)) (input ack (bits 1))
    (output y (bits 8)) (output ready (bits 1))
    (inst a stage (x x) (ack b.ready))
    (inst b stage (x a.y) (ack ack))
    (assign y b.y) (assign ready a.ready)))"

#guard runText handshake [[("x", 42), ("ack", 1)], [("x", 17), ("ack", 0)]] ==
  some [[42, 1], [17, 0]]

/-! A child state update must use connections that become ready after its first output. -/
private def lateState := "(design top
  (module child (input clk clock) (input x (bits 8)) (input later (bits 8))
    (output y (bits 8)) (output q (bits 8))
    (reg r (bits 8) clk) (next r later) (assign y x) (assign q r))
  (module top (input clk clock) (input x (bits 8)) (output y (bits 8)) (output q (bits 8))
    (inst c child (clk clk) (x x) (later late))
    (let base (bits 8) (add x (const 8 1)))
    (let late (bits 8) (add base (const 8 1)))
    (assign y c.y) (assign q c.q)))"

#guard runText lateState [[("x", 10)], [("x", 20)], [("x", 30)]] ==
  some [[10, 0], [20, 12], [30, 22]]

private def wideAdd := "(design wide
  (module wide (input x (bits 1000)) (input y (bits 1000)) (output q (bits 1000))
    (assign q (add x y))))"

#guard runText wideAdd [[("x", 2^1000 - 1), ("y", 1)]] == some [[0]]

/-! These cases also execute after item and statement sorting. -/
private def canonicalRun (text : String) (vectors : List (List (String × Nat))) :
    Option (List (List Nat)) :=
  match parse text with
  | .error _ => none
  | .ok raw => (runRaw (canonicalize raw) vectors).toOption

#guard canonicalRun counter (List.replicate 4 [("en", 1), ("rst", 0)]) ==
  some [[0], [1], [2], [3]]
#guard canonicalRun handshake [[("x", 42), ("ack", 1)], [("x", 17), ("ack", 0)]] ==
  some [[42, 1], [17, 0]]

private def chain (depth : Nat) (wide : Bool) : String :=
  let rows := (List.range depth).map fun i =>
    s!"(let x{i+1} (bits 256) (add x{i} x{i}))" ++
      if wide then s!"(let y{i+1} (bits 256) (add x{i} y{i}))" else ""
  "(design chain (module chain (input x0 (bits 256)) (output q (bits 256))" ++
    (if wide then "(input y0 (bits 256)) (output r (bits 256))" else "") ++
    String.join rows ++ s!"(assign q x{depth})" ++
    (if wide then s!"(assign r y{depth})" else "") ++ "))"

#guard runText (chain 200 false) [[("x0", 1)]] == some [[2^200]]
#guard runText (chain 100 true) [[("x0", 1), ("y0", 3)]] == some [[2^100, 2^100 + 2]]

private def hierarchyChain : String :=
  (((chain 200 false).replace "(design chain" "(design top").dropEnd 1).toString ++
    "(module top (input x (bits 256)) (output q (bits 256))" ++
    "(inst c chain (x0 x)) (assign q c.q)))"

#guard runText hierarchyChain [[("x", 1)]] == some [[2^200]]

private def multiOutputHierarchy (depth outputs : Nat) : String :=
  let ports := String.join ((List.range outputs).map fun i => s!"(output q{i} (bits 32))")
  let modules := (List.range (depth + 1)).map fun level =>
    s!"(module level{level} (input x (bits 32))" ++ ports ++
      (if level == 0 then "" else s!"(inst c level{level - 1} (x x))") ++
      String.join ((List.range outputs).map fun i =>
        s!"(assign q{i} " ++
          (if level == 0 then "x" else s!"(add c.q0 c.q{outputs - 1})") ++ ")") ++ ")"
  s!"(design level{depth} " ++ String.join modules ++ ")"

#guard runText (multiOutputHierarchy 10 2) [[("x", 37)]] == some [[37 * 2^10, 37 * 2^10]]
#guard runText (multiOutputHierarchy 6 4) [[("x", 53)]] == some [List.replicate 4 (53 * 2^6)]

/-! Late connections must not repeat work in nested instances. -/
private def feedbackHierarchy (depth : Nat) : String :=
  let modules := (List.range (depth + 1)).map fun level =>
    s!"(module fb{level} (input clk clock) (input d (bits 32)) (output q (bits 32))" ++
      (if level == 0 then
        "(reg r (bits 32) clk) (next r d) (assign q r)"
      else s!"(inst c fb{level - 1} (clk clk) (d (add c.q d))) (assign q c.q)") ++ ")"
  s!"(design fb{depth} " ++ String.join modules ++ ")"

private def lateHierarchy (depth : Nat) : String :=
  let modules := (List.range (depth + 1)).map fun level =>
    s!"(module late{level} (input clk clock) (input x (bits 32))" ++
      "(input later (bits 32)) (output y (bits 32)) (output q (bits 32))" ++
      (if level == 0 then
        "(reg r (bits 32) clk) (next r later) (assign y x) (assign q r)"
      else s!"(inst c late{level - 1} (clk clk) (x x) (later delayed))" ++
        "(let base (bits 32) (add x (const 32 1)))" ++
        "(let delayed (bits 32) (add base (const 32 1))) (assign y c.y) (assign q c.q)") ++ ")"
  s!"(design late{depth} " ++ String.join modules ++ ")"

private def handshakeHierarchy (depth : Nat) (registers : Bool) : String :=
  let cell := if registers then
    "(module cell (input clk clock) (input d (bits 32)) (output q (bits 32))" ++
      "(reg r (bits 32) clk) (next r d) (assign q r))" else ""
  let modules := (List.range (depth + 1)).map fun level =>
    s!"(module hs{level} (input clk clock) (input x (bits 32)) (input ack (bits 1))" ++
      "(output y (bits 32)) (output ready (bits 1))" ++
      (if registers then "(output q (bits 32))" else "") ++
      (if level == 0 then
        "(assign y x) (assign ready ack)" ++
          (if registers then
            "(inst c cell (clk clk) (d (add c.q x))) (assign q c.q)" else "")
      else s!"(inst a hs{level - 1} (clk clk) (x x) (ack b.ready))" ++
        s!"(inst b hs{level - 1} (clk clk) (x a.y) (ack ack))" ++
        "(assign y b.y) (assign ready a.ready)" ++
        (if registers then "(assign q (add a.q b.q))" else "")) ++ ")"
  s!"(design hs{depth} " ++ cell ++ String.join modules ++ ")"

#guard runText (feedbackHierarchy 12) [[("d", 7)], [("d", 11)]] == some [[0], [7]]
#guard runText (lateHierarchy 12) [[("x", 10)], [("x", 20)]] == some [[10, 0], [20, 12]]
#guard runText (handshakeHierarchy 7 false) [[("x", 42), ("ack", 1)],
  [("x", 17), ("ack", 0)]] == some [[42, 1], [17, 0]]
#guard runText (handshakeHierarchy 8 true) [[("x", 3), ("ack", 1)],
  [("x", 5), ("ack", 0)]] == some [[3, 1, 0], [5, 0, 768]]

/-! Packed parent outputs retain every value without a wide checker interface. -/
private def packExpr : List String → String
  | [] => "(const 32 0)"
  | [name] => name
  | first :: second :: rest =>
    let names := first :: second :: rest
    let half := names.length / 2
    "(concat " ++ packExpr (names.take half) ++ " " ++ packExpr (names.drop half) ++ ")"
termination_by names => names.length
decreasing_by all_goals simp_wf; omega

private def packValues (values : List Nat) : Nat :=
  values.foldl (fun packed value => packed * 2^32 + value) 0

/-! Each child read makes the next connection available in the same cycle. -/
private def zipper (count : Nat) : String :=
  let inputs := String.join ((List.range count).map fun i => s!"(input a{i} (bits 32))")
  let outputs := String.join ((List.range count).map fun i => s!"(output o{i} (bits 32))")
  let assigns := String.join ((List.range count).map fun i => s!"(assign o{i} a{i})")
  let connections := String.join ((List.range count).map fun i =>
    s!"(a{i} " ++ (if i == 0 then "a0" else s!"(add c.o{i-1} a{i})") ++ ")")
  "(design top (module child " ++ inputs ++ outputs ++ assigns ++ ")" ++
    "(module top " ++ inputs ++ s!"(output packed (bits {32 * count}))" ++
    "(inst c child " ++ connections ++ ")" ++
    String.join ((List.range count).map fun i => s!"(let o{i} (bits 32) c.o{i})") ++
    "(assign packed " ++ packExpr ((List.range count).map fun i => s!"o{i}") ++ ")))"

#guard runText (zipper 128)
  [(List.range 128).map (fun i => (s!"a{i}", 1)),
    (List.range 128).map (fun i => (s!"a{i}", 2))] ==
      some [[packValues ((List.range 128).map (· + 1))],
        [packValues ((List.range 128).map (fun i => 2 * (i + 1)))]]

/-! Siblings share a module but keep distinct state. -/
private def siblings (count : Nat) : String :=
  "(design top (module child (input clk clock) (input x (bits 32))" ++
    "(output y (bits 32)) (output q (bits 32))" ++
    "(reg r (bits 32) clk) (next r x) (assign y x) (assign q r))" ++
    "(module top (input clk clock) (input x (bits 32))" ++
    s!"(output y (bits {32 * count})) (output q (bits {32 * count}))" ++
    String.join ((List.range count).map fun i =>
      s!"(inst c{i} child (clk clk) (x (add x (const 32 {i}))))" ++
      s!"(let y{i} (bits 32) c{i}.y) (let q{i} (bits 32) c{i}.q)") ++
    "(assign y " ++ packExpr ((List.range count).map fun i => s!"y{i}") ++ ")" ++
    "(assign q " ++ packExpr ((List.range count).map fun i => s!"q{i}") ++ ")))"

#guard runText (siblings 50) [[("x", 3)], [("x", 5)]] ==
  some [[packValues ((List.range 50).map (3 + ·)), 0],
    [packValues ((List.range 50).map (5 + ·)), packValues ((List.range 50).map (3 + ·))]]

end Silicon.Core.Test.Interp

/-! The counter proofs use its typed equations to avoid reduction through the parser. -/

namespace Silicon.Core.Test.InterpCounter

open Semantics

private def pos : Pos := ⟨1, 1, []⟩
private def counterRaw : Core.Module := ⟨pos, "counter",
  [⟨pos, .input, "clk", .clock⟩, ⟨pos, .input, "rst", .bits 1⟩,
    ⟨pos, .input, "en", .bits 1⟩, ⟨pos, .output, "q", .bits 8⟩],
  [.reg pos "r" 8 "clk" (some ⟨.sync, .ref pos "rst", .const pos 8 0⟩),
    .let_ pos "inc" 8 (.bin pos .add (.ref pos "r") (.const pos 8 1)),
    .next pos "r" (.mux pos (.ref pos "en") (.ref pos "inc") (.ref pos "r")),
    .assign pos "q" (.ref pos "r")]⟩

private def raw : Core.Design := ⟨"counter", [.module counterRaw], pos⟩
private def ctx : Typed.Ctx := Typed.context raw counterRaw
private def reg : Typed.Equation ctx (Typed.portsOf raw) :=
  .reg 0 pos "r" 8 "clk" rfl
    (some ⟨.sync, .ref pos (.name "rst") rfl, .const pos 8 0⟩) 2 pos
    (.mux pos (.ref pos (.name "en") rfl)
      (.ref pos (.name "inc") rfl) (.ref pos (.name "r") rfl))
private def inc : Typed.Equation ctx (Typed.portsOf raw) :=
  .let_ 1 pos "inc" 8
    (.bin pos .add (by intro h; cases h) (.ref pos (.name "r") rfl) (.const pos 8 1))
private def assign : Typed.Equation ctx (Typed.portsOf raw) :=
  .assign 3 pos "q" 8 rfl (.ref pos (.name "r") rfl)

private def counter : Typed.Module where
  pos := pos
  name := "counter"
  ports := counterRaw.ports
  ctx := ctx
  interfaces := Typed.portsOf raw
  body := [reg, inc, assign]
  children := Typed.designDeps raw raw.depsFuel
  ranks := [(.name "inc", 1), (.name "q", 1)]
  acyclic := by
    simp [Typed.equationsErase, reg, inc, assign, List.mergeSort, Typed.Ranked,
      Deps.graph, Deps.equations, Deps.reads, Typed.rank, Typed.Equation.parts,
      Typed.Stmt.erase, Typed.Expr.erase]
    constructor <;> intro _ <;> first | rfl | exact Nat.zero_lt_succ _
  context_eq := by
    simp [Typed.equationsErase, reg, inc, assign, List.mergeSort, Typed.Equation.parts,
      Typed.Stmt.erase, Typed.Expr.erase]
    rfl

private theorem counter_erase : counter.erase = counterRaw := by
  simp [counter, Typed.Module.erase, Typed.equationsErase, reg, inc, assign,
    List.mergeSort, Typed.Equation.parts, Typed.Stmt.erase, Typed.Expr.erase,
    Typed.Reset.erase, counterRaw]

private def counterTyped : Typed.Design where
  top := "counter"
  itemNames := ["counter"]
  externs := []
  bodies := [counter]
  topPos := pos
  hierarchy := by simp [counter_erase, Typed.ordered, Typed.childNames, counterRaw]
  environments := by
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have erased : Typed.assembleDesign "counter" ["counter"] [] [counter] pos = raw := by
        simp [Typed.assembleDesign, counter, Typed.Module.erase, Typed.equationsErase,
          reg, inc, assign, List.mergeSort, Typed.Equation.parts, Typed.Stmt.erase,
          Typed.Expr.erase, Typed.Reset.erase, raw, counterRaw]
      rw [erased]
      exact ⟨rfl, rfl, by rw [counter_erase]; exact List.mem_cons_self ..⟩
    · contradiction

private theorem counter_wf : WellFormed counterTyped.erase := by
  have hn := (Check.e002_spec raw).mp (by cbv)
  have hr := (Check.e003_spec raw).mp (by rfl)
  have erased : counterTyped.erase = raw := by
    change Typed.assembleDesign "counter" ["counter"] [] [counter] pos = raw
    simp only [Typed.assembleDesign, List.filterMap_cons, List.filterMap_nil,
      List.find?_cons, show (counter.name == "counter") = true from rfl,
      counter_erase]
    rfl
  rw [erased]
  refine ⟨hn, hr, (Check.e004_spec raw hn hr
      ((Check.e009_spec raw).mp rfl) ((Check.e011_spec raw).mp rfl)).mp (by rfl),
    (Check.e005_spec raw).mp (by rfl), (Check.e006_spec raw).mp (by rfl),
    (Check.e007_spec raw).mp (by rfl), ?_, (Check.e009_spec raw).mp (by rfl),
    ?_, (Check.e011_spec raw).mp (by rfl), (Check.e012_spec raw).mp (by rfl),
    (Check.e013_spec raw).mp (by rfl)⟩
  · intro m hm
    change m ∈ [counterRaw] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨counter.ranks, ?_⟩
      have h := counter.acyclic
      change Typed.Ranked (Deps.graph counter.erase counter.children) counter.ranks at h
      rw [counter_erase] at h
      exact h
    · contradiction
  · refine ⟨[], ?_⟩
    change ∀ row ∈ ([(Deps.Node.name "counter", [])] : Typed.Graph), ∀ dep ∈ row.2, _
    simp

private def counterDesign : CertifiedDesign := ⟨counterTyped, counter_wf⟩

theorem counter_checked : ∃ typed, check counterTyped.erase = .ok typed :=
  check_complete counterTyped.erase counter_wf

private theorem counter_member : counter ∈ counterDesign.design.bodies := by
  exact List.mem_cons_self ..

private def noExterns : Env counterDesign.design := fun e h => by
  change e ∈ [] at h
  contradiction

private def counterInput (enable reset : BitVec 1) : Input counter := fun p =>
  match p.val.ty with
  | .clock => ()
  | .bits width => BitVec.ofNat width (if p.val.name == "rst" then reset.toNat else enable.toNat)

private def counterQ : PortRef counter.ports .output :=
  ⟨⟨pos, .output, "q", .bits 8⟩, by simp [counter, counterRaw], rfl⟩

private def regRef : EquationRef counter := ⟨reg, List.mem_cons_self ..⟩

private theorem counter_output (state : State counterDesign noExterns counter counter_member)
    (input : Input counter) :
    (step counterDesign noExterns counter counter_member state input).2 counterQ =
      state regRef := by
  obtain ⟨values, hv, unique⟩ :=
    solution_unique counterDesign noExterns counter counter_member state input
  have solved : solution counterDesign noExterns counter counter_member state input = values :=
    unique _ (localSolution_isSolution counterDesign counter counter_member
      (designChildren counterDesign noExterns counter counter_member) state input)
  change solution counterDesign noExterns counter counter_member state input (.name "q") 8 rfl = _
  rw [solved]
  have q := hv (.name "q") 8 rfl
    (.assign 3 pos "q" 8 rfl (.ref pos (.name "r") rfl) (by
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have r := hv (.name "r") 8 rfl
    (.reg 0 pos "r" 8 "clk" rfl
      (some ⟨.sync, .ref pos (.name "rst") rfl, .const pos 8 0⟩) 2 pos
      (.mux pos (.ref pos (.name "en") rfl)
        (.ref pos (.name "inc") rfl) (.ref pos (.name "r") rfl))
      (List.mem_cons_self ..))
  exact q.trans r


private theorem counter_next (state : State counterDesign noExterns counter counter_member)
    (enable reset : BitVec 1) :
    (Core.Interp.step counterDesign noExterns counter counter_member
      state (counterInput enable reset)).1 regRef =
        if reset = 1#1 then 0#8 else
          if enable = 1#1 then (show BitVec 8 from state regRef) + 1#8 else state regRef := by
  rw [Core.Interp.step_eq_values]
  have values := interp_correct counterDesign noExterns counter counter_member
    state (counterInput enable reset)
  have rst := values (.name "rst") 1 rfl
    (.input ⟨pos, .input, "rst", .bits 1⟩
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl rfl)
  have en := values (.name "en") 1 rfl
    (.input ⟨pos, .input, "en", .bits 1⟩
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl rfl)
  have r := values (.name "r") 8 rfl
    (.reg 0 pos "r" 8 "clk" rfl
      (some ⟨.sync, .ref pos (.name "rst") rfl, .const pos 8 0⟩) 2 pos
      (.mux pos (.ref pos (.name "en") rfl)
        (.ref pos (.name "inc") rfl) (.ref pos (.name "r") rfl))
      (List.mem_cons_self ..))
  have incValue := values (.name "inc") 8 rfl
    (.let_ 1 pos "inc" 8
      (.bin pos .add (by intro h; cases h) (.ref pos (.name "r") rfl) (.const pos 8 1))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  change Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "rst") 1 rfl = BitVec.ofNat 1 reset.toNat at rst
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at rst
  change Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "en") 1 rfl = BitVec.ofNat 1 enable.toNat at en
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at en
  change Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "r") 8 rfl = state regRef at r
  change Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "inc") 8 rfl =
    Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "r") 8 rfl + 1#8 at incValue
  change (if Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "rst") 1 rfl = 1#1 then 0#8 else
    if Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "en") 1 rfl = 1#1 then
      Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "inc") 8 rfl else
      Core.Interp.solve counterDesign noExterns counter counter_member
    state (counterInput enable reset) (.name "r") 8 rfl) = _
  rw [rst, en, incValue, r]

private def start := Core.Interp.zeroState counterDesign noExterns rfl counter counter_member
private def tick (state : State counterDesign noExterns counter counter_member)
    (enable reset : BitVec 1) :=
  (Core.Interp.step counterDesign noExterns counter counter_member
    state (counterInput enable reset)).1

private theorem start_reg : start regRef = 0#8 := by
  exact (Core.Interp.zeroState.eq_def counterDesign noExterns rfl counter
    counter_member regRef).trans (by rfl)

private def countState : Nat → State counterDesign noExterns counter counter_member
  | 0 => start
  | n + 1 => tick (countState n) 1#1 0#1

theorem counter_count (n : Nat) : (countState n) regRef = BitVec.ofNat 8 n := by
  induction n with
  | zero => exact start_reg
  | succ n ih =>
    change (tick (countState n) 1#1 0#1) regRef = _
    rw [tick, counter_next]
    simp only [show (0#1 = 1#1) = False from propext (by
      constructor <;> intro h; cases h; contradiction), ite_false, ite_true, ih]
    exact (BitVec.ofNat_add n 1).symm

theorem counter_four_cycles :
    (List.range 4).map (fun n =>
      (Core.Interp.step counterDesign noExterns counter counter_member
        (countState n) (counterInput 1#1 0#1)).2 counterQ) =
      [0#8, 1#8, 2#8, 3#8] := by
  have outputs (n : Nat) :
      (Core.Interp.step counterDesign noExterns counter counter_member
        (countState n) (counterInput 1#1 0#1)).2 counterQ = BitVec.ofNat 8 n := by
    rw [interp_step]
    exact (counter_output _ _).trans (counter_count n)
  simp only [outputs]
  rfl

theorem counter_reset (state : State counterDesign noExterns counter counter_member)
    (enable : BitVec 1) :
    (Core.Interp.step counterDesign noExterns counter counter_member
      (tick state enable 1#1) (counterInput 0#1 0#1)).2 counterQ = 0#8 := by
  rw [interp_step, counter_output, tick, counter_next]
  rfl

end Silicon.Core.Test.InterpCounter
