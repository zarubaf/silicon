import Silicon.Core.GraphReach

/-! Inferred dependencies contain exactly the reachable data inputs. -/
namespace Silicon.Core.Deps

open GraphReach

private theorem reaches_empty (g : List (Node × List Node)) (target : Node)
    (fuel : Nat) (seen : List Node) : reachesSpec g target fuel [] seen = false := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [reachesSpec, freshNodes] using ih

private theorem visit_mem (g : List (Node × List Node)) (fuel : Nat)
    (pending seen : List Node) (target : Node) :
    target ∈ visit g fuel pending seen ↔
      target ∈ seen ∨ reachesSpec g target fuel pending seen = true := by
  induction fuel generalizing pending seen with
  | zero => simp [visit, reachesSpec]
  | succ fuel ih =>
    change target ∈ (if (frontier g seen pending).isEmpty then updated seen pending
      else visit g fuel (frontier g seen pending) (updated seen pending)) ↔ _
    rw [reachesSpec]
    change _ ↔ target ∈ seen ∨ (if pending.contains target then true
      else reachesSpec g target fuel (frontier g seen pending) (updated seen pending)) = true
    by_cases he : (frontier g seen pending).isEmpty = true
    · have hn : frontier g seen pending = [] := List.isEmpty_iff.mp he
      rw [ite_eq_left he, mem_updated, hn, reaches_empty]
      simp
    · rw [ite_eq_right he, ih, mem_updated]
      by_cases hp : target ∈ pending <;> simp [hp]

theorem mem_visit_iff_reachable (g : List (Node × List Node))
    (pending : List Node) (target : Node) :
    target ∈ visit g (g.length + 1) pending [] ↔
      ∃ start ∈ pending, Reachable g start target := by
  rw [visit_mem]
  simpa using reaches_graph_iff g target pending

theorem infer_entry_inputs (m : Module) (children : String → Option Deps)
    (output : String) (deps : List String) (entry : List.Mem (output, deps) (infer m children))
    (input : String) :
    input ∈ deps ↔ input ∈ inputs m ∧
      Reachable (graph m children) (.name output) (.name input) := by
  obtain ⟨port, _, hp⟩ := List.mem_filterMap.mp entry
  split at hp
  · have he := Option.some.inj hp
    have hn := congrArg Prod.fst he
    have hd := congrArg Prod.snd he
    simp only at hn hd
    rw [← hd, List.mem_filter, List.contains_iff_mem, mem_visit_iff_reachable]
    simp [hn]
  · contradiction

theorem infer_lookup_inputs (m : Module) (children : String → Option Deps)
    (output : String) (deps : List String) (entry : (infer m children).lookup output = some deps)
    (input : String) :
    input ∈ deps ↔ input ∈ inputs m ∧
      Reachable (graph m children) (.name output) (.name input) := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp entry
  apply infer_entry_inputs m children output deps ?_ input
  rw [he]
  exact List.mem_append_right _ (List.mem_cons_self ..)

end Silicon.Core.Deps
