import Silicon.Core.Lower
import Silicon.Core.Proof.MemModel
import Silicon.Core.Canonical.State

/-!
State paths retain instance names. A memory adds its own instance to the path.
Only the words below the core depth constrain the model array.
-/
namespace Silicon.Core
namespace LowerProof

def extendMemory (c : MemConfig) (memory : Fin c.depth → BitVec c.width)
    (padding : Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width) :
    Fin (2 ^ Typed.addressWidth c.depth) → BitVec c.width :=
  fun i => if h : i.val < c.depth then memory ⟨i.val, h⟩ else padding i

theorem extendMemory_agrees (c : MemConfig) (memory) (padding) :
    MemModelProof.Agrees c (extendMemory c memory padding) memory := by
  intro i
  simp [extendMemory, i.isLt]

def CellCorresponds (σ : Mlir.ModuleState) (path : List String) (name : String) :
    Semantics.NamedCell → Prop
  | .register width value =>
      σ.cells path s!"silicon_reg_{name}" = some (.bits width value)
  | .memory width depth memory =>
      ∃ words : Fin (2 ^ Typed.addressWidth depth) → BitVec width,
        σ.cells (path ++ [name]) "silicon_reg_mem" = some (.array _ _ words) ∧
        MemModelProof.Agrees ⟨depth, width, 0, 0⟩ words memory

theorem cellCorresponds_instance (σ : Mlir.ModuleState) (inst : String)
    (path : List String) (name : String) (cell : Semantics.NamedCell) :
    CellCorresponds (σ.instance inst) path name cell ↔
      CellCorresponds σ (inst :: path) name cell := by
  cases cell <;> rfl

theorem resolve_preserves (aliases : Std.HashMap String String) (env : Mlir.Env)
    (agree : ∀ name next, aliases[name]? = some next → env name = env next)
    (fuel : Nat) (name : String) : env (Lower.resolve aliases fuel name) = env name := by
  induction fuel generalizing name with
  | zero => rfl
  | succ fuel ih =>
    simp only [Lower.resolve]
    cases found : aliases[name]? with
    | none => rfl
    | some next => exact (ih next).trans (agree name next found).symm

@[simp] theorem binary_core (op : BinOp) (ordinary : op ≠ .concat) :
    (Lower.binary op ordinary).core = op := by
  cases op <;> first | rfl | contradiction

@[simp] theorem predicate_core (pred : Pred) : (Lower.predicate pred).core = pred := by
  cases pred <;> rfl

end LowerProof

def Corresponds (d : Semantics.CertifiedDesign) (env : Semantics.Env d.design)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (s : Semantics.State d env m hm) (σ : Mlir.ModuleState) : Prop :=
  ∀ path name cell,
    Semantics.namedState d env noExterns m hm s (path ++ [name]) = some cell →
      LowerProof.CellCorresponds σ path name cell

namespace LowerProof

theorem corresponds_register (d : Semantics.CertifiedDesign) (env)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm)
    (s : Semantics.State d env m hm) (σ : Mlir.ModuleState)
    (h : Corresponds d env noExterns m hm s σ)
    (i : Nat) (p : Pos) (name : String) (width : Nat) (clock : String)
    (target : Typed.valueTy m.ctx name = some (.bits width))
    (reset : Option (Typed.Reset m.ctx width)) (ni : Nat) (np : Pos)
    (next : Typed.Expr m.ctx (.bits width))
    (member : .reg i p name width clock target reset ni np next ∈ m.body) :
    σ.regs s!"silicon_reg_{name}" = some (.bits width
      (s ⟨.reg i p name width clock target reset ni np next, member⟩)) :=
  h [] name _ (Semantics.namedState_register d env noExterns m hm s
    i p name width clock target reset ni np next member)

theorem corresponds_memory (d : Semantics.CertifiedDesign) (env)
    (noExterns : d.design.externs = []) (m : Typed.Module) (hm)
    (s : Semantics.State d env m hm) (σ : Mlir.ModuleState)
    (h : Corresponds d env noExterns m hm s σ) (name : String) (width depth : Nat)
    (found : m.ctx.lookup (.name name) = some (.memory width depth)) :
    ∃ words : Fin (2 ^ Typed.addressWidth depth) → BitVec width,
      (σ.instance name).regs "silicon_reg_mem" = some (.array _ _ words) ∧
      MemModelProof.Agrees ⟨depth, width, 0, 0⟩ words
        (Semantics.stateMemories m (Semantics.designChildren d env m hm) s
          name width depth found) :=
  h [] name _ (Semantics.namedState_memories d env noExterns m hm s name width depth found)

end LowerProof
end Silicon.Core
