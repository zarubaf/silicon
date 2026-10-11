-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Interp.Ordered
import Silicon.Core.Semantics.Local

/-! The typed context supplies all nodes to the ordered evaluator. -/
namespace Silicon.Core.Interp

open Semantics

deriving instance DecidableEq for ValueRef

instance : BEq (ValueRef ctx) := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq (ValueRef ctx) where
  eq_of_beq := by simp
  rfl := by simp
instance : Hashable (ValueRef ctx) := ⟨fun ref => hash ref.node⟩

def valueRefs (ctx : Typed.Ctx) : List (ValueRef ctx) :=
  (ctx.map Prod.fst).filterMap fun node =>
    match found : ctx.lookup node with
    | some (.value (.bits width)) => some ⟨node, width, found⟩
    | _ => none

theorem valueRefs_complete (ref : ValueRef ctx) : ref ∈ valueRefs ctx := by
  obtain ⟨node, width, found⟩ := ref
  have member : node ∈ ctx.map Prod.fst := by
    obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp found
    rw [eq]
    simp
  unfold valueRefs
  apply List.mem_filterMap.mpr
  exact ⟨node, member, by
    split
    next w hw =>
      have eq : w = width := by simpa [found] using hw.symm
      subst w
      rfl
    next h => exact False.elim (h width found)⟩

/-! A node index avoids a context scan for each reached cone node. -/
def valueRef? (ctx : Typed.Ctx) (node : Deps.Node) : Option (ValueRef ctx) :=
  match found : ctx.lookup node with
  | some (.value (.bits width)) => some ⟨node, width, found⟩
  | _ => none

theorem valueRef?_self (ref : ValueRef ctx) : valueRef? ctx ref.node = some ref := by
  cases ref with
  | mk node width found =>
    unfold valueRef?
    split
    next w hw =>
      have eq : w = width := by simpa [found] using hw.symm
      subst w
      rfl
    next h => exact False.elim (h width found)

def valueRefIndex (ctx : Typed.Ctx) :=
  tabulate (valueRef? ctx) ((valueRefs ctx).map (·.node))

theorem valueRefIndex_get (ref : ValueRef ctx) :
    ((valueRefIndex ctx).get? ref.node).getD none = some ref := by
  rw [valueRefIndex, tabulate_get _ _ _
    (List.mem_map.mpr ⟨ref, valueRefs_complete ref, rfl⟩), Option.getD_some, valueRef?_self]

abbrev DriverKey := Deps.Node × Nat
abbrev DriverTable (m : Typed.Module) :=
  Std.DHashMap DriverKey (fun key => ValueDriver m key.1 key.2)

def driverTable (m : Typed.Module) (entries : List (PackedDriver m)) : DriverTable m :=
  entries.foldr (fun entry table => table.insert (entry.1, entry.2.1) entry.2.2) ∅

theorem driverTable_total (m : Typed.Module) (entries : List (PackedDriver m))
    (driver : ValueDriver m node width) (member : ⟨node, width, driver⟩ ∈ entries) :
    ((driverTable m entries).get? (node, width)).isSome := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    simp only [driverTable, List.foldr_cons, Std.DHashMap.get?_insert]
    split
    · rfl
    next ne =>
      apply ih
      rcases List.mem_cons.mp member with same | member
      · subst entry
        exact False.elim (ne (by simp))
      · exact member

def indexedDriver (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (table : DriverTable m) (complete : ∀ node width (_v : ValueDriver m node width),
      (table.get? (node, width)).isSome) (ref : ValueRef m.ctx) :
    ValueDriver m ref.node ref.width :=
  (table.get? (ref.node, ref.width)).get (by
    obtain ⟨v⟩ := valueDriver_exists d.design d.wellFormed m hm ref.node ref.width ref.found
    exact complete _ _ v)

end Silicon.Core.Interp
