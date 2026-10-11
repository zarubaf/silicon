-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleRead

/-!
An instance op passes each child input the value of its source connection. Its results follow
the output ports of the child, as the outputs of the lowered child do.
-/
namespace Silicon.Core.LowerProof

open Semantics

theorem instArgs_find (ports : String → List Port) (child : String)
    (unique : ((ports child).map Port.name).Nodup) (args : List (String × String × Mlir.Ty))
    (q : Port) (hq : q ∈ ports child) (input : q.dir = .input)
    (a : String × String × Mlir.Ty) (found : args.find? (fun x => x.1 == q.name) = some a) :
    (instArgs ports child args).find? (fun x => x.1 == q.name) = some a := by
  unfold instArgs
  generalize ports child = l at unique hq
  induction l with
  | nil => cases hq
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp hq with rfl | hq
    · have named : a.1 = q.name := by simpa using List.find?_some found
      simp [input, found, named]
    · have ne : first.name ≠ q.name := fun eq => unique.1 (eq ▸ List.mem_map_of_mem hq)
      cases hf : (if first.dir == .input then args.find? (fun arg => arg.1 == first.name)
          else none) with
      | none =>
        rw [List.filterMap_cons, hf]
        exact ih unique.2 hq
      | some b =>
        have named : b.1 = first.name := by
          split at hf
          · simpa using List.find?_some hf
          · cases hf
        rw [List.filterMap_cons, hf, List.find?_cons, named,
          show (first.name == q.name) = false from beq_eq_false_iff_ne.mpr ne]
        exact ih unique.2 hq

theorem filter_index {α β γ : Type} (l : List α) (P : α → Bool) (f : α → β) (g : α → γ) (x : α)
    (hx : x ∈ l) (px : P x = true) :
    ∃ i, ∃ hi : i < ((l.filter P).map f).length, ((l.filter P).map f)[i] = f x ∧
      ((l.filter P).map g)[i]? = some (g x) := by
  obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp (List.mem_filter.mpr ⟨hx, px⟩)
  refine ⟨i, by simpa using hi, ?_, ?_⟩
  · simp [same]
  · simp [List.getElem?_eq_getElem hi, same]

theorem outputs_filter (m : Typed.Module) :
    (Lower.module m).1.outputs = (m.ports.filter (·.dir == .output)).map (rename m ·.name) := by
  rw [module_outputs]
  induction m.ports with
  | nil => rfl
  | cons p ps ih =>
    rw [List.filterMap_cons, List.filter_cons]
    split <;> simp_all

theorem instResults_filter (ports : String → List Port) (child : String) :
    instResults ports child = ((ports child).filter (·.dir == .output)).map
      (fun p => (p.name, Lower.type p.ty)) := by
  unfold instResults
  induction ports child with
  | nil => rfl
  | cons p ps ih =>
    rw [List.filterMap_cons, List.filter_cons]
    split <;> simp_all

/-- Typed values have the lowered type. -/
theorem coreValue_ty (ty : Ty) (x : TyValue ty) : (coreValue ty x).ty = Lower.type ty := by
  cases ty <;> rfl

theorem typed_coreValue (env : Mlir.Env) (name : String) (ty : Ty) (x : TyValue ty)
    (h : env name = some (coreValue ty x)) :
    env.typed name (Lower.type ty) = some (coreValue ty x) := by
  simp [Mlir.Env.typed, h, coreValue_ty]

theorem argsMatch_find (M : Meaning ctx) {ports : String → List Port} {child : String}
    (inputs : List ((p : {p : Port // p ∈ ports child}) × Typed.Expr ctx p.val.ty))
    (args : List (String × String × Mlir.Ty)) (matched : M.ArgsMatch inputs args)
    (name : String) (input : (p : {p : Port // p ∈ ports child}) × Typed.Expr ctx p.val.ty)
    (found : inputs.find? (fun i => i.1.val.name == name) = some input) :
    ∃ v, args.find? (fun x => x.1 == name) = some (name, v, Lower.type input.1.val.ty) ∧
      M.env v = some (coreValue _ (M.core input.2)) := by
  obtain ⟨length, pairs⟩ := matched
  induction inputs generalizing args with
  | nil => cases found
  | cons first rest ih =>
    cases args with
    | nil => cases length
    | cons a as =>
      have head := pairs (first, a) (by rw [List.zip_cons_cons]; exact List.mem_cons_self ..)
      obtain ⟨hn, ht, hv⟩ := head
      obtain ⟨a1, a2, a3⟩ := a
      simp only at hn ht hv
      subst hn
      subst ht
      by_cases same : first.1.val.name = name
      · have : first = input := by simpa [List.find?_cons, same] using found
        subst this
        exact ⟨a2, by simp [same], hv⟩
      · have rest' : rest.find? (fun i => i.1.val.name == name) = some input := by
          simpa [List.find?_cons, same] using found
        obtain ⟨v, hf, hv'⟩ := ih as rest' (by simpa using length)
          (fun pair hp => pairs pair (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp))
        refine ⟨v, ?_, hv'⟩
        rw [List.find?_cons, show (first.1.val.name == name) = false from
          beq_eq_false_iff_ne.mpr same]
        exact hf

end Silicon.Core.LowerProof
