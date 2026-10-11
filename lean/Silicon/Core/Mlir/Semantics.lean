-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Mlir.Syntax
import Silicon.Core.Semantics.Value

/-!
A solution assigns values to equations, without an order on SSA names.
Instance paths hold child values, including values absent from output ports.
-/
namespace Silicon.Core.Mlir

private instance : DecidableEq (Fin n → BitVec w) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) ⟨funext, congrFun⟩

inductive Value where
  | bits (w : Nat) (v : BitVec w)
  | array (n w : Nat) (words : Fin n → BitVec w)
  | clock
  deriving DecidableEq

def Value.ty : Value → Ty
  | .bits w _ => .int w
  | .array n w _ => .array n w
  | .clock => .clock

def Value.asBits (w : Nat) : Value → Option (BitVec w)
  | .bits w' v => if h : w' = w then some (h ▸ v) else none
  | _ => none

def Value.asArray (n w : Nat) : Value → Option (Fin n → BitVec w)
  | .array n' w' words =>
    if hn : n' = n then if hw : w' = w then some (hn ▸ hw ▸ words) else none else none
  | _ => none

def CombOp.core : CombOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .and => .and | .or => .or
  | .xor => .xor | .shl => .shl | .shru => .shru | .shrs => .shrs

theorem CombOp.ordinary (op : CombOp) : op.core ≠ .concat := by cases op <;> decide

def Pred.core : Pred → Silicon.Core.Pred
  | .eq => .eq | .ne => .ne | .ult => .ult | .ule => .ule | .ugt => .ugt
  | .uge => .uge | .slt => .slt | .sle => .sle | .sgt => .sgt | .sge => .sge

abbrev Env := String → Option Value

def Env.bits (env : Env) (name : String) (w : Nat) : Option (BitVec w) :=
  env name >>= Value.asBits w

def Env.typed (env : Env) (name : String) (ty : Ty) : Option Value := do
  let v ← env name
  if v.ty = ty then some v else none

/-! Invalid widths and missing operands have no value. State operations have separate equations. -/
def Op.eval (op : Op) (env : Env) : Option Value := do
  match op with
  | .constant w value =>
    if value < 2 ^ w then some (.bits w (BitVec.ofNat w value)) else none
  | .comb op a b w =>
    return .bits w (Semantics.evalOp op.core op.ordinary (← env.bits a w) (← env.bits b w))
  | .icmp p a b w =>
    return .bits 1 (Semantics.evalPred p.core (← env.bits a w) (← env.bits b w))
  | .mux c a b ty =>
    return Semantics.evalMux (← env.bits c 1) (← env.typed a ty) (← env.typed b ty)
  | .extract a lo wi wo =>
    if lo + wo ≤ wi then return .bits wo (Semantics.evalExtract (← env.bits a wi) lo wo)
    else none
  | .concat a b wa wb =>
    return .bits (wa + wb) (Semantics.evalConcat (← env.bits a wa) (← env.bits b wb))
  | .replicate a wi wo =>
    if h : wi * (wo / wi) = wo ∧ 0 < wi then
      return .bits wo (h.1 ▸ Semantics.evalReplicate (← env.bits a wi) (wo / wi))
    else none
  | .arrayGet arr idx n w a =>
    let words ← env arr >>= Value.asArray n w
    let index ← env.bits idx a
    if index.toNat < n then
      return .bits w (Semantics.memoryRead words index.toNat)
    else none
  | .arrayInject arr idx v n w a =>
    let words ← env arr >>= Value.asArray n w
    let index ← env.bits idx a
    let value ← env.bits v w
    if index.toNat < n then
      return .array n w (Semantics.memoryWrite words index.toNat value 1)
    else none
  | .compreg .. | .instance .. => none

abbrev Path := List String
abbrev Valuation := Path → Env

/-! A path names the state of an instance independently of the module body order. -/
structure ModuleState where
  cells : Path → Env

def ModuleState.regs (σ : ModuleState) : Env := σ.cells []
def ModuleState.instance (σ : ModuleState) (name : String) : ModuleState :=
  ⟨fun path => σ.cells (name :: path)⟩

def Module.inputPorts (m : Module) : List Port := m.ports.filter (·.dir == .input)
def Module.outputPorts (m : Module) : List Port := m.ports.filter (·.dir == .output)

def Design.findModule (d : Design) (name : String) : Option Module :=
  d.items.findSome? fun item => match item with
    | .module m => if m.name = name then some m else none
    | .extern .. => none

def Module.findInstance (m : Module) (name : String) :
    Option (String × List (String × String × Ty)) :=
  m.body.findSome? fun (_, op) => match op with
    | .instance inst callee args _ => if inst = name then some (callee, args) else none
    | _ => none

def Module.atPath (d : Design) (m : Module) : Path → Option Module
  | [] => some m
  | name :: path => do
    let (callee, _) ← m.findInstance name
    let child ← d.findModule callee
    child.atPath d path

def instanceInputs (args : List (String × String × Ty)) (env : Env) : Env :=
  fun name => do
    let arg ← args.find? (·.1 == name)
    env.typed arg.2.1 arg.2.2

/-! Every equation requires a value. Two absent values never satisfy an equation. -/
def LocalSolution (d : Design) (m : Module) (state : Env) (inputs : Env)
    (vals : Env) (children : String → Env) : Prop :=
  (∀ p ∈ m.inputPorts, ∃ v, inputs p.name = some v ∧ v.ty = p.ty ∧
    vals p.name = some v) ∧
  (∀ entry ∈ m.body, match entry with
    | (names, .instance inst callee args results) =>
      ∃ child, d.findModule callee = some child ∧
        names.length = results.length ∧ child.outputs.length = results.length ∧
        (∀ p ∈ child.inputPorts,
          children inst p.name = instanceInputs args vals p.name) ∧
        (∀ i : Fin names.length, ∃ v,
          vals names[i] = some v ∧
          (∃ source, child.outputs[i.val]? = some source ∧ children inst source = some v) ∧
          (results[i.val]?.map Prod.snd) = some v.ty)
    | (names, .compreg _ _ _ ty) =>
      ∃ name v, names = [name] ∧ state name = some v ∧ v.ty = ty ∧ vals name = some v
    | (names, op) => ∃ name v, names = [name] ∧ op.eval vals = some v ∧
        vals name = some v) ∧
  m.outputs.length = m.outputPorts.length ∧
  (∀ i : Fin m.outputs.length, ∃ v, vals m.outputs[i] = some v ∧
    (m.outputPorts[i.val]?.map Port.ty) = some v.ty)

/-! Child equations use parent connections without a topological order of SSA values. -/
def IsHierarchySolution (d : Design) (m : Module) (σ : ModuleState) (inputs : Env)
    (vals : Valuation) : Prop :=
  LocalSolution d m σ.regs inputs (vals []) (fun inst => vals [inst]) ∧
  ∀ path parent, m.atPath d path = some parent →
    ∀ inst callee args, parent.findInstance inst = some (callee, args) →
      ∃ child, d.findModule callee = some child ∧
        LocalSolution d child (σ.cells (path ++ [inst]))
          (instanceInputs args (vals path)) (vals (path ++ [inst]))
          (fun name => vals (path ++ [inst, name]))

def Op.nextValue (op : Op) (vals : Env) : Option Value := do
  match op with
  | .compreg next clk reset ty =>
    let _ ← vals.typed clk .clock
    let next ← vals.typed next ty
    match reset with
    | none => some next
    | some (signal, value) =>
      return Semantics.evalMux (← vals.bits signal 1) (← vals.typed value ty) next
  | _ => none

/-! Each cell uses operands at its own instance path and updates at the same edge. -/
def nextHierarchyState (d : Design) (m : Module) (vals : Valuation) : ModuleState :=
  ⟨fun path name => do
    let owner ← m.atPath d path
    let (_, op) ← owner.body.find? (fun entry => entry.1 == [name])
    op.nextValue (vals path)⟩

/-! The public solution exposes local SSA names. Child solutions are witnesses. -/
def IsSolution (d : Design) (m : Module) (σ : ModuleState) (inputs vals : Env) : Prop :=
  ∃ all : Valuation, all [] = vals ∧ IsHierarchySolution d m σ inputs all

theorem IsHierarchySolution.selfInputs
    (h : IsHierarchySolution d m σ inputs vals) :
    IsHierarchySolution d m σ (vals []) vals := by
  refine ⟨⟨?_, h.1.2⟩, h.2⟩
  intro p hp
  obtain ⟨v, _, ty, value⟩ := h.1.1 p hp
  exact ⟨v, value, ty, value⟩

/-!
Internal child values come from a solution with the given local values.
The choice does not impose an order on SSA equations. A design without a solution has no
child values. Local register updates still use the supplied operands.
-/
noncomputable def solutionValues (d : Design) (m : Module) (σ : ModuleState)
    (vals : Env) : Valuation := by
  classical
  exact fun path => match path with
  | [] => vals
  | _ :: _ =>
    if h : IsSolution d m σ vals vals then h.choose path else fun _ => none

theorem solutionValues_spec (h : IsSolution d m σ inputs vals) :
    IsHierarchySolution d m σ vals (solutionValues d m σ vals) := by
  classical
  obtain ⟨all, root, valid⟩ := h
  have existsSelf : IsSolution d m σ vals vals :=
    ⟨all, root, root ▸ valid.selfInputs⟩
  have equal : solutionValues d m σ vals = existsSelf.choose := by
    funext path
    cases path with
    | nil => exact existsSelf.choose_spec.1.symm
    | cons name path => simp [solutionValues, existsSelf]
  rw [equal]
  exact existsSelf.choose_spec.2

noncomputable def nextState (d : Design) (m : Module) (σ : ModuleState)
    (vals : Env) : ModuleState :=
  nextHierarchyState d m (solutionValues d m σ vals)

end Silicon.Core.Mlir
