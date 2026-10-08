import Silicon.Core.Semantics.Interface

/-! Name and output checks give each value equation one source. -/
namespace Silicon.Core.Semantics

theorem module_mem (d : Typed.Design) (m : Typed.Module) (hm : m ∈ d.bodies) :
    m.erase ∈ Typed.modules d.erase := by
  exact List.mem_filterMap.mpr ⟨.module m.erase, (d.environments m hm).2.2, rfl⟩

theorem port_found (d : Typed.Design) (wf : WellFormed d.erase) (m : Typed.Module)
    (hm : m ∈ d.bodies) (port : Port) (hp : port ∈ m.ports) (ht : port.ty = .bits width) :
    m.ctx.lookup (.name port.name) = some (.value (.bits width)) := by
  have ports := (List.nodup_append.mp
    (Check.module_scope_nodup d.erase m.erase wf.1 (module_mem d m hm))).1
  have found := Check.find_port_of_mem m.ports port ports hp
  rw [m.context_eq]
  unfold Typed.contextFromPorts
  rw [Check.port_lookup m.ports _ port.name port found]
  simp [ht]

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
    (name : String) (hna : Check.label a = some name) (hnb : Check.label b = some name) :
    a = b := by
  exact filterMap_unique m.body Check.label
    (Check.labels_nodup d m wf.1 wf.2.1 wf.2.2.2.2.2.1 hm) a b ha hb name hna hnb

/-! Grouping retains one name per equation and keeps all names distinct. -/
def equationName : Typed.Equation ctx ports → String
  | .let_ _ _ name _ _ | .reg _ _ name .. | .mem _ _ name ..
  | .inst _ _ name .. | .assign _ _ name .. => name

private theorem equation_labels (eq : Typed.Equation ctx ports) :
    (eq.parts.map (fun part => part.2.erase)).filterMap Check.label = [equationName eq] := by
  cases eq <;> simp [Typed.Equation.parts, Typed.Stmt.erase, Check.label, Rules.definition,
    equationName, List.filterMap_map, List.map_map, Function.comp_def]

theorem equation_names_nodup (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) : (m.body.map equationName).Nodup := by
  have raw := Check.labels_nodup d.erase m.erase wf.1 wf.2.1 wf.2.2.2.2.2.1
    (module_mem d m hm)
  have perm := ((List.mergeSort_perm (m.body.flatMap Typed.Equation.parts)
    (fun a b => decide (a.1 ≤ b.1))).map (fun part => part.2.erase)).filterMap Check.label
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

/-! Input ports supply values directly; they cannot also name an equation. -/
theorem input_not_driver (d : Core.Design) (wf : WellFormed d) (m : Core.Module)
    (hm : m ∈ Typed.modules d) (port : Port) (hp : port ∈ m.ports)
    (hi : port.dir = .input) (stmt : Core.Stmt) (hs : stmt ∈ m.body) :
    Check.label stmt ≠ some port.name := by
  have scope := List.nodup_append.mp (Check.module_scope_nodup d m wf.1 hm)
  have noDefinition : Rules.definition stmt ≠ some port.name := by
    intro hd
    exact scope.2.2 port.name (List.mem_map.mpr ⟨port, hp, rfl⟩) port.name
      (List.mem_filterMap.mpr ⟨stmt, hs, hd⟩) rfl
  cases stmt with
  | assign pos name expr =>
    intro he
    have he : name = port.name := Option.some.inj he
    subst name
    have resolved := (wf.2.1.2 m hm _ hs).1
    change ((Rules.findPort m port.name).any fun p => p.dir == .output) = true at resolved
    have found := Check.find_port_of_mem m.ports port scope.1 hp
    change Rules.findPort m port.name = some port at found
    rw [found] at resolved
    simp [hi] at resolved
  | _ => exact noDefinition

end Silicon.Core.Semantics
