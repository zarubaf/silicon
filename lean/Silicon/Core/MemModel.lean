import Silicon.Core.Mlir.Syntax
import Silicon.Core.Typed

/-!
Memory models use an array register and apply writes in port order.
The parent module guards addresses outside the memory depth.
-/

namespace Silicon.Core

structure MemConfig where
  depth : Nat
  width : Nat
  reads : Nat
  writes : Nat
  deriving DecidableEq

def MemConfig.moduleName (c : MemConfig) : String :=
  s!"silicon_mem_{c.depth}x{c.width}_r{c.reads}w{c.writes}"

def MemConfig.ports (c : MemConfig) : List Mlir.Port :=
  let addr := Mlir.Ty.int (Typed.addressWidth c.depth)
  let data := Mlir.Ty.int c.width
  [⟨.input, "clk", .clock⟩] ++
    (List.range c.reads).flatMap (fun n =>
      [⟨.input, s!"r{n}_addr", addr⟩, ⟨.output, s!"r{n}_data", data⟩]) ++
    (List.range c.writes).flatMap (fun n =>
      [⟨.input, s!"w{n}_addr", addr⟩, ⟨.input, s!"w{n}_data", data⟩,
       ⟨.input, s!"w{n}_en", .int 1⟩])

/-! Each write uses the state from the previous port. The highest port wins. -/
def memModel (c : MemConfig) : Mlir.Module :=
  let a := Typed.addressWidth c.depth
  let n := 2 ^ a
  let reads := (List.range c.reads).map fun r =>
    ([s!"r{r}_data"], Mlir.Op.arrayGet "silicon_reg_mem" s!"r{r}_addr" n c.width a)
  let stateBefore := fun w => if w == 0 then "silicon_reg_mem" else s!"w{w - 1}_next"
  let writes := (List.range c.writes).flatMap fun w =>
    let state := stateBefore w
    [([s!"w{w}_set"], Mlir.Op.arrayInject state s!"w{w}_addr" s!"w{w}_data" n c.width a),
     ([s!"w{w}_next"], Mlir.Op.mux s!"w{w}_en" s!"w{w}_set" state (.array n c.width))]
  { name := c.moduleName
    ports := c.ports
    body := reads ++ writes ++
      [(["silicon_reg_mem"], .compreg (stateBefore c.writes) "clk" none (.array n c.width))]
    outputs := (List.range c.reads).map fun r => s!"r{r}_data" }

/-! Only the exact memory name and signature identify a replaceable external model. -/
def MemConfig.ofModuleName (name : String) : Option MemConfig := do
  let ["silicon", "mem", shape, ports] := name.splitOn "_" | none
  let [depth, width] := shape.splitOn "x" | none
  let [reads, writes] := ports.splitOn "w" | none
  let some reads := reads.dropPrefix? "r" | none
  let c : MemConfig := ⟨← depth.toNat?, ← width.toNat?,
    ← reads.toString.toNat?, ← writes.toNat?⟩
  if c.moduleName = name then some c else none

def Mlir.Design.withModels (d : Mlir.Design) : Mlir.Design :=
  ⟨d.items.map fun item => match item with
    | .extern name ports =>
      match MemConfig.ofModuleName name with
      | some c => if ports = c.ports then .module (memModel c) else item
      | none => item
    | .module _ => item⟩

end Silicon.Core
