-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Proof.Lower.ModuleShape

/-!
Checked modules give each source name one declaration. The final aliases rename only
named statement results, and every other name keeps its definition.
-/
namespace Silicon.Core.LowerProof

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (m : Typed.Module) (hm : m ∈ t.bodies)

def defs (m : Typed.Module) : List (String × Mlir.Ty) := (Lower.module m).1.definitions

/-- `Has m x ty`: the renamed `x` has type `ty` in the lowered module. -/
def Has (m : Typed.Module) (x : String) (ty : Mlir.Ty) : Prop :=
  (defs m).lookup (rename m x) = some ty

theorem defs_input (p : Port) (hp : p ∈ m.ports) (input : p.dir = .input) :
    (p.name, Lower.type p.ty) ∈ defs m := by
  unfold defs Mlir.Module.definitions Mlir.Module.inputPorts
  rw [module_ports]
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨Lower.port p, List.mem_filter.mpr ⟨List.mem_map_of_mem hp, by simp [Lower.port, input]⟩,
    by simp [Lower.port]⟩

theorem defs_body (entry : List String × Mlir.Op) (he : entry ∈ rawBody m)
    (pair : String × Mlir.Ty) (hp : pair ∈ entry.1.zip entry.2.resultTypes) :
    pair ∈ defs m := by
  unfold defs Mlir.Module.definitions
  rw [module_body]
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨(entry.1, Lower.substitute (rename m) entry.2), List.mem_map.mpr ⟨entry, he, rfl⟩, ?_⟩
  simpa [substitute_resultTypes] using hp

omit raw t h hm in
theorem rename_none (x : String) (absent : (finalAliases m)[x]? = none) : rename m x = x :=
  resolve_none x absent _

include h hm

theorem defs_nodup : ((defs m).map Prod.fst).Nodup := lower_module_defs_nodup raw t h m hm

theorem has_of_mem (x : String) (ty : Mlir.Ty) (same : rename m x = x)
    (member : (x, ty) ∈ defs m) : Has m x ty := by
  unfold Has
  rw [same]
  exact lookup_of_mem (defs_nodup raw t h m hm) member

theorem rename_invalid (x : String) (reserved : Rules.invalidName x = true) :
    rename m x = x := by
  apply rename_none m
  cases found : (finalAliases m)[x]? with
  | none => rfl
  | some v =>
    have key := alias_key_legal raw t h m hm x
      (Std.HashMap.isSome_getElem?_iff_mem.mp (by rw [found]; rfl))
    rw [reserved] at key
    cases key

theorem rename_alias (k v : String) (found : (finalAliases m)[k]? = some v) :
    rename m k = rename m v :=
  resolve_alias (rank := fun x => Typed.rank m.ranks (.name x))
    (fun a b hab hb => alias_decreasing raw t h m hm a b hab hb) k v found

theorem rename_other (x : String) (other : x ∉ (Lower.statements m).filterMap LetName) :
    rename m x = x :=
  rename_none m x ((final_aliases raw t h m hm).1 x other)

theorem has_alias (k v : String) (found : (finalAliases m)[k]? = some v) (ty : Mlir.Ty) :
    Has m k ty ↔ Has m v ty := by
  unfold Has
  rw [rename_alias raw t h m hm k v found]

end

theorem module_wf (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t) :
    WellFormed raw := (check_sound raw t h).1

theorem module_item (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) : Core.Item.module m.erase ∈ raw.items := by
  have erase := check_sound_erase raw t h
  exact erase ▸ (t.environments m hm).2.2

theorem scope_nodup (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) :
    (m.ports.map Port.name ++ m.erase.body.filterMap Rules.definition).Nodup :=
  ((module_wf raw t h).1.2 (.module m.erase) (module_item raw t h m hm)).1

theorem typed_of_raw (m : Typed.Module) (stmt : Core.Stmt) (hs : stmt ∈ m.erase.body) :
    ∃ typed ∈ Lower.statements m, typed.erase = stmt := by
  rw [← statements_erase m] at hs
  exact List.mem_map.mp hs

theorem input_not_letName (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (p : Port) (hp : p ∈ m.ports)
    (input : p.dir = .input) : p.name ∉ (Lower.statements m).filterMap LetName := by
  intro member
  obtain ⟨stmt, hs, named⟩ := List.mem_filterMap.mp member
  apply Check.input_not_driver raw (module_wf raw t h) m.erase
    (checked_erase_member raw t h m hm) p hp input stmt.erase (stmt_erase_member m stmt hs)
  cases stmt <;> simp_all [LetName, Typed.Stmt.erase, Stmt.driverName]

end Silicon.Core.LowerProof
