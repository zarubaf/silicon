import Silicon.Core.MemModel

namespace Silicon.Core
namespace Lower

private def type (ty : Ty) : Mlir.Ty :=
  match ty with
  | .bits w => .int w
  | .clock => .clock

private def port (p : Port) : Mlir.Port :=
  ⟨match p.dir with | .input => .input | .output => .output, p.name, type p.ty⟩

private def predicate : Pred → Mlir.Pred
  | .eq => .eq | .ne => .ne | .ult => .ult | .ule => .ule | .ugt => .ugt
  | .uge => .uge | .slt => .slt | .sle => .sle | .sgt => .sgt | .sge => .sge

private def binary : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .and => "and" | .or => "or"
  | .xor => "xor" | .shl => "shl" | .shru => "shru" | .shrs => "shrs" | .concat => "concat"

private structure ReadPort where
  memory : String
  index : Nat
  addr : String

private structure WritePort where
  memory : String
  index : Nat
  addr : String
  data : String
  enable : String

private structure State where
  nextTemp : Nat := 0
  body : Array (List String × Mlir.Op) := #[]
  readCounts : List (String × Nat) := []
  reads : List ReadPort := []
  writes : List WritePort := []
  nexts : List (String × String) := []
  resets : List (String × Option (String × String)) := []

private abbrev Build := StateM State

private def emit (dest : Option String) (op : Mlir.Op) : Build String := do
  let name ← match dest with
    | some name => pure name
    | none => do
      let n := (← get).nextTemp
      modify fun s => { s with nextTemp := n + 1 }
      pure s!"silicon_t{n}"
  modify fun s => { s with body := s.body.push ([name], op) }
  return name

/-! An identity operation gives each let and assign its own stable name. -/
private def named (dest : Option String) (value : String) (w : Nat) : Build String :=
  match dest with
  | none => pure value
  | some name => emit (some name) (.comb "or" [value, value] w)

private def inRange (depth : Nat) (addr : String) : Build (Option String) := do
  let a := Typed.addressWidth depth
  if depth == 2 ^ a then return none
  let bound ← emit none (.constant a depth)
  return some (← emit none (.icmp .ult addr bound a))

private def valueName (registers : List String) : Deps.Node → String
  | .name n => if registers.contains n then s!"silicon_reg_{n}" else n
  | .port inst p => s!"{inst}.{p}"

/-! Reserve a read port before its address walk, even when the address reads memory. -/
private def expr (registers : List String) : {ty : Ty} → Typed.Expr ctx ty →
    Option String → Build String
  | _, .ref (width := w) _ node _, dest => named dest (valueName registers node) w
  | _, .clock _ name _, _ => pure name
  | _, .const _ w v, dest => emit dest (.constant w v)
  | _, .un (width := w) _ .not a, dest => do
    let a ← expr registers a none
    let ones ← emit none (.constant w (2 ^ w - 1))
    emit dest (.comb "xor" [a, ones] w)
  | _, .bin (width := w) _ op _ a b, dest => do
    let a ← expr registers a none
    let b ← expr registers b none
    emit dest (.comb (binary op) [a, b] w)
  | _, .concat (a := wa) (b := wb) _ a b _, dest => do
    let a ← expr registers a none
    let b ← expr registers b none
    emit dest (.concat a b wa wb)
  | _, .icmp (width := w) _ p a b, dest => do
    let a ← expr registers a none
    let b ← expr registers b none
    emit dest (.icmp (predicate p) a b w)
  | _, .mux (width := w) _ c a b, dest => do
    let c ← expr registers c none
    let a ← expr registers a none
    let b ← expr registers b none
    emit dest (.mux c a b w)
  | _, .extract (width := w) _ a lo count _, dest => do
    let a ← expr registers a none
    emit dest (.extract a lo w count)
  | _, .replicate (width := w) _ a count _, dest => do
    let a ← expr registers a none
    emit dest (.replicate a w (w * count))
  | _, .read (width := w) (depth := depth) _ name _ addr, dest => do
    let n := ((← get).readCounts.lookup name).getD 0
    modify fun s => { s with readCounts := (name, n + 1) :: s.readCounts }
    let addr ← expr registers addr none
    modify fun s => { s with reads := ⟨name, n, addr⟩ :: s.reads }
    let data := s!"{name}.r{n}_data"
    match ← inRange depth addr with
    | none => named dest data w
    | some ok =>
      let zero ← emit none (.constant w 0)
      emit dest (.mux ok data zero w)

private def statement (registers : List String) : Typed.Stmt ctx ports → Build Unit
  | .let_ _ name _ e | .assign _ name _ _ e => do
    let _ ← expr registers e (some name)
  | .reg _ name _ _ reset => do
    let reset ← reset.mapM fun r => do
      let signal ← expr registers r.signal none
      let value ← expr registers r.value none
      return (signal, value)
    modify fun s => { s with resets := (name, reset) :: s.resets }
  | .next _ name _ _ e => do
    let next ← expr registers e none
    modify fun s => { s with nexts := (name, next) :: s.nexts }
  | .mem .. => pure ()
  | .write _ name index _ depth _ addr data enable => do
    let addr ← expr registers addr none
    let data ← expr registers data none
    let enable ← expr registers enable none
    let enable ← match ← inRange depth addr with
      | none => pure enable
      | some ok => emit none (.comb "and" [enable, ok] 1)
    modify fun s => { s with writes := ⟨name, index, addr, data, enable⟩ :: s.writes }
  | .inst _ name child inputs => do
    let args ← inputs.mapM fun input => do
      let value ← expr registers input.2 none
      return (input.1.val.name, value, type input.1.val.ty)
    let results := (ports child).filterMap fun p =>
      if p.dir == .output then some (p.name, type p.ty) else none
    let names := results.map fun p => s!"{name}.{p.1}"
    modify fun s => { s with body := s.body.push (names, .instance name child args results) }

private def memories (m : Typed.Module) : Build (List MemConfig) := do
  let mut configs := []
  for eq in m.body do
    match eq with
    | .mem _ _ name w depth clk _ _ =>
      let reads := ((← get).reads.filter (·.memory == name)).mergeSort (·.index ≤ ·.index)
      let writes := ((← get).writes.filter (·.memory == name)).mergeSort (·.index ≤ ·.index)
      let config : MemConfig := ⟨depth, w, reads.length, writes.length⟩
      let a := Mlir.Ty.int (Typed.addressWidth depth)
      let args := [("clk", clk, Mlir.Ty.clock)] ++
        reads.map (fun r => (s!"r{r.index}_addr", r.addr, a)) ++
        writes.flatMap (fun wr =>
          [(s!"w{wr.index}_addr", wr.addr, a), (s!"w{wr.index}_data", wr.data, .int w),
           (s!"w{wr.index}_en", wr.enable, .int 1)])
      let results := reads.map fun r => (s!"r{r.index}_data", Mlir.Ty.int w)
      let names := reads.map fun r => s!"{name}.r{r.index}_data"
      modify fun s => { s with
        body := s.body.push (names, .instance name config.moduleName args results) }
      configs := config :: configs
    | _ => pure ()
  return configs

/-! Saved indices restore statement order from typed equations. -/
private def module (m : Typed.Module) : Mlir.Module × List MemConfig := Id.run do
  let registers := m.body.filterMap fun eq => match eq with
    | .reg _ _ name _ _ _ _ _ _ _ => some name
    | _ => none
  let statements := ((m.body.flatMap Typed.Equation.parts).mergeSort (·.1 ≤ ·.1)).map Prod.snd
  let build : Build (List MemConfig) := do
    for stmt in statements do statement registers stmt
    memories m
  let (configs, state) := build.run {}
  let regs := m.body.filterMap fun eq => match eq with
    | .reg _ _ name w clk _ _ _ _ _ => do
      let next ← state.nexts.lookup name
      let reset := (state.resets.lookup name).getD none
      some ([s!"silicon_reg_{name}"], Mlir.Op.compreg next clk reset (.int w))
    | _ => none
  let body := state.body.toList ++ regs
  let outputs := m.ports.filterMap fun p =>
    if p.dir == .output then some (p.name, type p.ty) else none
  return (⟨m.name, m.ports.map port, body, outputs⟩, configs)

private def uniqueConfigs (configs : List MemConfig) : List MemConfig :=
  configs.eraseDups.mergeSort (fun a b => a.moduleName ≤ b.moduleName)

private def itemName : Mlir.Item → String
  | .module m => m.name
  | .extern name _ => name

end Lower

def memoryConfigs (t : Typed.Design) : List MemConfig :=
  Lower.uniqueConfigs (t.bodies.flatMap fun m => (Lower.module m).2)

def lower (t : Typed.Design) : Mlir.Design :=
  let modules := t.bodies.map Lower.module
  let configs := Lower.uniqueConfigs (modules.flatMap Prod.snd)
  let items := modules.map (Mlir.Item.module ∘ Prod.fst) ++
    t.externs.map (fun e => Mlir.Item.extern e.name (e.ports.map Lower.port)) ++
    configs.map (fun c => Mlir.Item.extern c.moduleName c.ports)
  ⟨items.mergeSort (fun a b => Lower.itemName a ≤ Lower.itemName b)⟩

end Silicon.Core
