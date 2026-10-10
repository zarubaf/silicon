import Silicon.Core.Names
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
  backendName "mem" [s!"{c.depth}x{c.width}_r{c.reads}w{c.writes}"]

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
  let reg := regName "mem"
  let reads := (List.range c.reads).map fun r =>
    ([s!"r{r}_data"], Mlir.Op.arrayGet reg s!"r{r}_addr" n c.width a)
  let stateBefore := fun w => if w == 0 then reg else s!"w{w - 1}_next"
  let writes := (List.range c.writes).flatMap fun w =>
    let state := stateBefore w
    [([s!"w{w}_set"], Mlir.Op.arrayInject state s!"w{w}_addr" s!"w{w}_data" n c.width a),
     ([s!"w{w}_next"], Mlir.Op.mux s!"w{w}_en" s!"w{w}_set" state (.array n c.width))]
  { name := c.moduleName
    ports := c.ports
    body := reads ++ writes ++
      [([reg], .compreg (stateBefore c.writes) "clk" none (.array n c.width))]
    outputs := (List.range c.reads).map fun r => s!"r{r}_data" }

/-! Only a listed memory name with its exact signature identifies a replaceable extern. -/
def Mlir.Item.withModels (configs : List MemConfig) (item : Mlir.Item) : Mlir.Item :=
  match item with
  | .extern name ports =>
    match configs.find? (·.moduleName == name) with
    | some c => if ports = c.ports then .module (memModel c) else item
    | none => item
  | .module _ => item

def Mlir.Design.withModels (configs : List MemConfig) (d : Mlir.Design) : Mlir.Design :=
  ⟨d.items.map (Mlir.Item.withModels configs)⟩

end Silicon.Core
