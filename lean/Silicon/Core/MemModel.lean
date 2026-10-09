import Silicon.Core.Mlir.Syntax
import Silicon.Core.Typed

namespace Silicon.Core

structure MemConfig where
  depth : Nat
  width : Nat
  reads : Nat
  writes : Nat
  deriving DecidableEq, Ord

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
     ([s!"w{w}_next"], Mlir.Op.arrayMux s!"w{w}_en" s!"w{w}_set" state n c.width)]
  { name := c.moduleName
    ports := c.ports
    body := reads ++ writes ++
      [(["silicon_reg_mem"], .compreg (stateBefore c.writes) "clk" none (.array n c.width))]
    outputs := (List.range c.reads).map fun r => (s!"r{r}_data", .int c.width) }

end Silicon.Core
