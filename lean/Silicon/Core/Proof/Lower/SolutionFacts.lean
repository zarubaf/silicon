import Silicon.Core.Proof.Lower.Hierarchy
import Silicon.Core.Proof.Lower.Counts

/-!
An MLIR solution gives each definition a value of its type. A local solution reads its
inputs only at the input ports. Child solutions join a parent solution along instance paths.
-/
namespace Silicon.Core.LowerProof

open Mlir

variable {d d' : Mlir.Design} {m : Mlir.Module} {state inputs inputs' vals : Mlir.Env}
  {children children' : String → Mlir.Env}


theorem eval_type (op : Mlir.Op) (env : Mlir.Env) (v : Mlir.Value) (h : op.eval env = some v) :
    op.resultTypes = [v.ty] := by
  cases op with
  | constant w n =>
    simp only [Mlir.Op.eval] at h
    split at h <;> simp_all [Mlir.Op.resultTypes, Mlir.Value.ty]
    cases h
    rfl
  | mux c a b ty =>
    simp only [Mlir.Op.eval, bind, Option.bind_eq_some_iff, pure] at h
    obtain ⟨x, _, y, hy, z, hz, hv⟩ := h
    cases hv
    simp only [Mlir.Env.typed, bind, Option.bind_eq_some_iff] at hy hz
    obtain ⟨y', _, hy⟩ := hy
    obtain ⟨z', _, hz⟩ := hz
    split at hy <;> split at hz <;> simp_all [Mlir.Op.resultTypes, Semantics.evalMux]
    split <;> simp_all
  | extract a lo wi wo =>
    simp only [Mlir.Op.eval] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨x, _, hv⟩ := h
      cases hv
      rfl
    · cases h
  | replicate a wi wo =>
    simp only [Mlir.Op.eval] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨x, _, hv⟩ := h
      cases hv
      rfl
    · cases h
  | arrayGet arr idx n w a =>
    simp only [Mlir.Op.eval, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, _, y, _, h⟩ := h
    split at h
    · cases h
      rfl
    · cases h
  | arrayInject arr idx val n w a =>
    simp only [Mlir.Op.eval, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, _, y, _, z, _, h⟩ := h
    split at h
    · cases h
      rfl
    · cases h
  | compreg | «instance» => cases h
  | comb | icmp | concat =>
    simp only [Mlir.Op.eval, bind, Option.bind_eq_some_iff, pure] at h
    obtain ⟨x, _, y, _, hv⟩ := h
    cases hv
    rfl

theorem local_types (h : LocalSolution d m state inputs vals children) (y : String)
    (ty : Mlir.Ty) (hy : (y, ty) ∈ m.definitions) : ∃ v, vals y = some v ∧ v.ty = ty := by
  unfold Mlir.Module.definitions at hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨p, hp, same⟩ := List.mem_map.mp hy
    cases same
    obtain ⟨v, _, ty, hv⟩ := h.1 p hp
    exact ⟨v, hv, ty⟩
  · obtain ⟨⟨names, op⟩, he, hz⟩ := List.mem_flatMap.mp hy
    dsimp only at hz
    have equation := h.2.1 _ he
    cases op with
    | «instance» inst callee args results =>
      obtain ⟨child, _, length, _, _, outputs⟩ := equation
      obtain ⟨i, hi, hz⟩ := List.mem_iff_getElem.mp hz
      simp only [List.getElem_zip, Prod.mk.injEq] at hz
      have hn : i < names.length := by simp [List.length_zip] at hi; omega
      obtain ⟨v, hv, _, ht⟩ := outputs ⟨i, hn⟩
      refine ⟨v, hz.1 ▸ hv, ?_⟩
      have hr : i < results.length := by omega
      simp only [Mlir.Op.resultTypes, List.getElem_map] at hz
      rw [← hz.2]
      simp [List.getElem?_eq_getElem hr] at ht
      exact ht.symm
    | compreg next clk reset ty' =>
      obtain ⟨name, v, rfl, _, ht, hv⟩ := equation
      simp only [Mlir.Op.resultTypes, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
        Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨v, hv, ht⟩
    | _ =>
      obtain ⟨name, v, rfl, hop, hv⟩ := equation
      rw [eval_type _ _ _ hop] at hz
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton,
        Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact ⟨v, hv, rfl⟩

theorem localSolution_inputs (agree : ∀ p ∈ m.inputPorts, inputs p.name = inputs' p.name)
    (h : LocalSolution d m state inputs vals children) :
    LocalSolution d m state inputs' vals children := by
  refine ⟨fun p hp => ?_, h.2⟩
  obtain ⟨v, hi, ht, hv⟩ := h.1 p hp
  exact ⟨v, (agree p hp).symm.trans hi, ht, hv⟩

theorem localSolution_design (plain : ∀ entry ∈ m.body, isInstance entry.2 = false)
    (h : LocalSolution d m state inputs vals children) :
    LocalSolution d' m state inputs vals children' := by
  refine ⟨h.1, fun entry he => ?_, h.2.2⟩
  have equation := h.2.1 entry he
  have := plain entry he
  obtain ⟨names, op⟩ := entry
  cases op <;> first | exact equation | cases this

theorem findModule_mem (d : Mlir.Design) (unique : (d.items.map Mlir.Item.name).Nodup)
    (M : Mlir.Module)
    (hm : Mlir.Item.module M ∈ d.items) : d.findModule M.name = some M := by
  unfold Mlir.Design.findModule
  obtain ⟨items⟩ := d
  induction items with
  | nil => cases hm
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp
    · have ne : Mlir.Item.name first ≠ M.name := fun eq =>
        unique.1 (eq ▸ List.mem_map_of_mem (f := Mlir.Item.name) hm')
      rw [List.findSome?_cons]
      cases first with
      | module other =>
        have : other.name ≠ M.name := ne
        simp only [this, ↓reduceIte]
        exact ih unique.2 hm'
      | extern => exact ih unique.2 hm'

def instNames (m : Mlir.Module) : List String :=
  m.body.filterMap (fun (_, op) => match op with | .instance name .. => some name | _ => none)

theorem findInstance_mem (m : Mlir.Module) (unique : (instNames m).Nodup) (names : List String)
    (inst callee : String) (args : List (String × String × Mlir.Ty))
    (results : List (String × Mlir.Ty))
    (he : (names, Mlir.Op.instance inst callee args results) ∈ m.body) :
    m.findInstance inst = some (callee, args) := by
  unfold Mlir.Module.findInstance
  unfold instNames at unique
  obtain ⟨name, ports, body, outputs⟩ := m
  dsimp only at he unique ⊢
  induction body with
  | nil => cases he
  | cons first rest ih =>
    rw [List.findSome?_cons]
    rw [List.filterMap_cons] at unique
    obtain ⟨n₁, op₁⟩ := first
    rcases List.mem_cons.mp he with same | he'
    · cases same
      simp
    · cases op₁ with
      | «instance» other c a r =>
        simp only [List.nodup_cons] at unique
        have ne : other ≠ inst := by
          rintro rfl
          exact unique.1 (List.mem_filterMap.mpr ⟨_, he', by rfl⟩)
        simp only [ne, ↓reduceIte]
        exact ih unique.2 he'
      | _ => exact ih unique he'

/-- Child hierarchy solutions extend a local parent solution along instance paths. -/
theorem hierarchy_compose (d : Mlir.Design) (m : Mlir.Module) (σ : Mlir.ModuleState)
    (inputs vals : Mlir.Env)
    (children : String → Mlir.Valuation)
    (root : LocalSolution d m σ.regs inputs vals (fun inst => children inst []))
    (kids : ∀ inst callee args, m.findInstance inst = some (callee, args) →
      ∃ child, d.findModule callee = some child ∧
        IsHierarchySolution d child (σ.instance inst) (instanceInputs args vals)
          (children inst)) :
    IsHierarchySolution d m σ inputs (fun path => match path with
      | [] => vals
      | inst :: rest => children inst rest) := by
  refine ⟨root, ?_⟩
  intro path parent found inst callee args member
  cases path with
  | nil =>
    simp only [Mlir.Module.atPath, Option.some.injEq] at found
    subst parent
    obtain ⟨child, hc, solved⟩ := kids inst callee args member
    exact ⟨child, hc, solved.1⟩
  | cons first rest =>
    simp only [Mlir.Module.atPath, bind, Option.bind_eq_some_iff] at found
    obtain ⟨⟨callee', args'⟩, hf, child', hc', hp⟩ := found
    obtain ⟨child, hc, solved⟩ := kids first callee' args' hf
    rw [hc] at hc'
    cases hc'
    exact solved.2 rest parent hp inst callee args member

end Silicon.Core.LowerProof
