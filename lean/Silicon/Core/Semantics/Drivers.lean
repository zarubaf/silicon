import Silicon.Core.Semantics.Interface

/-! Name and output checks give each value equation one source. -/
namespace Silicon.Core.Semantics

theorem module_mem (d : Typed.Design) (m : Typed.Module) (hm : m ∈ d.bodies) :
    m.erase ∈ Typed.modules d.erase := by
  exact List.mem_filterMap.mpr ⟨.module m.erase, (d.environments m hm).2.2, rfl⟩

theorem port_found (d : Typed.Design) (wf : WellFormed d.erase) (m : Typed.Module)
    (hm : m ∈ d.bodies) (port : Port) (hp : port ∈ m.ports) (ht : port.ty = .bits width) :
    m.ctx.lookup (.name port.name) = some (.value (.bits width)) := by
  rw [m.context_eq]
  exact Check.module_port_lookup d.erase m.erase wf (module_mem d m hm) port hp ht m.interfaces

private theorem filterMap_unique {α β : Type} (xs : List α) (f : α → Option β)
    (unique : (xs.filterMap f).Nodup) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (name : β) (hna : f a = some name) (hnb : f b = some name) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    have tail : (xs.filterMap f).Nodup := by
      cases hx : f x with
      | none => simpa [List.filterMap_cons, hx] using unique
      | some y =>
        exact (List.nodup_cons.mp (by simpa [List.filterMap_cons, hx] using unique)).2
    have exclude (hx : f x = some name) : name ∉ xs.filterMap f := by
      exact (List.nodup_cons.mp (by simpa [List.filterMap_cons, hx] using unique)).1
    rcases List.mem_cons.mp ha with rfl | haTail
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · rfl
      · exact False.elim (exclude hna (List.mem_filterMap.mpr ⟨b, hbTail, hnb⟩))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact False.elim (exclude hnb (List.mem_filterMap.mpr ⟨a, haTail, hna⟩))
      · exact ih tail haTail hbTail

theorem driver_unique (d : Core.Design) (wf : WellFormed d) (m : Core.Module)
    (hm : m ∈ Typed.modules d) (a b : Core.Stmt) (ha : a ∈ m.body) (hb : b ∈ m.body)
    (name : String) (hna : Core.Stmt.driverName a = some name)
    (hnb : Core.Stmt.driverName b = some name) :
    a = b := by
  exact filterMap_unique m.body Core.Stmt.driverName
    (Check.module_driver_names_nodup d m wf hm) a b ha hb name hna hnb

/-! Grouping retains one name per equation and keeps all names distinct. -/
def equationName : Typed.Equation ctx ports → String
  | .let_ _ _ name _ _ | .reg _ _ name .. | .mem _ _ name ..
  | .inst _ _ name .. | .assign _ _ name .. => name

private theorem equation_labels (eq : Typed.Equation ctx ports) :
    (eq.parts.map (fun part => part.2.erase)).filterMap Core.Stmt.driverName =
      [equationName eq] := by
  cases eq <;> simp [Typed.Equation.parts, Typed.Stmt.erase, Core.Stmt.driverName,
    equationName, List.filterMap_map, List.map_map, Function.comp_def]

theorem equation_names_nodup (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) : (m.body.map equationName).Nodup := by
  have raw := Check.module_driver_names_nodup d.erase m.erase wf
    (module_mem d m hm)
  have perm := ((List.mergeSort_perm (m.body.flatMap Typed.Equation.parts)
    (fun a b => decide (a.1 ≤ b.1))).map (fun part => part.2.erase)).filterMap Core.Stmt.driverName
  have unsorted := perm.nodup_iff.mp raw
  have flat : m.body.flatMap (fun eq => [equationName eq]) = m.body.map equationName := by
    induction m.body with
    | nil => rfl
    | cons eq rest ih => simp [ih]
  simpa only [List.map_flatMap, List.filterMap_flatMap, equation_labels, flat] using unsorted

theorem equation_unique (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (a b : Typed.Equation m.ctx m.interfaces)
    (ha : a ∈ m.body) (hb : b ∈ m.body) (he : equationName a = equationName b) : a = b := by
  apply filterMap_unique m.body (fun eq => some (equationName eq))
    (by simpa using equation_names_nodup d wf m hm) a b ha hb (equationName a) rfl
  simp only [he]

/-! Every declared output has one assignment, including an output read by another equation. -/
theorem output_assignment (d : Core.Design) (wf : WellFormed d) (m : Core.Module)
    (hm : m ∈ Typed.modules d) (port : Port) (hp : port ∈ m.ports)
    (ho : port.dir = .output) :
    ∃ pos expr, Core.Stmt.assign pos port.name expr ∈ m.body ∧
      ∀ otherPos otherExpr, Core.Stmt.assign otherPos port.name otherExpr ∈ m.body →
        otherPos = pos ∧ otherExpr = expr := by
  have count := wf.2.2.2.2.2.1 m hm port hp ho
  have nonempty : Rules.assignments m port.name ≠ [] := by
    intro he
    simp [he] at count
  obtain ⟨pos, hpos⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨stmt, hs, he⟩ := List.mem_filterMap.mp hpos
  cases stmt <;> simp only at he
  all_goals try contradiction
  rename_i p name expr
  split at he <;> try contradiction
  rename_i hn
  have hn : name = port.name := by simpa using hn
  subst name
  cases he
  refine ⟨pos, expr, hs, ?_⟩
  intro p' expr' hs'
  have eq := driver_unique d wf m hm _ _ hs' hs port.name rfl rfl
  cases eq
  exact ⟨rfl, rfl⟩

end Silicon.Core.Semantics
