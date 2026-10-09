import Silicon.Core.Proof.Lower.MemoryPorts

/-!
A source instance connects each child input once, in child port order, with the port type.
-/
namespace Silicon.Core.LowerProof

theorem results_sig (ports : List Port) :
    ports.filterMap (fun p => if p.dir == .output then some (p.name, Lower.type p.ty) else none) =
      ((ports.map Lower.port).filter (·.dir == .output)).map fun p => (p.name, p.ty) := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    cases dir : p.dir <;> simp [Lower.port, dir] <;> simpa using ih

theorem inputs_sig (ports : List Port) :
    ports.filterMap (fun p => if p.dir == .input then some (p.name, Lower.type p.ty) else none) =
      ((ports.map Lower.port).filter (·.dir == .input)).map fun p => (p.name, p.ty) := by
  induction ports with
  | nil => rfl
  | cons p ports ih =>
    cases dir : p.dir <;> simp [Lower.port, dir] <;> simpa using ih

theorem filterMap_pointwise {f g : α → Option β} {l : List α} (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem instance_sig (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (p : Pos) (i child : String)
    (inputs : List ((port : {p : Port // p ∈ m.interfaces child}) × Typed.Expr m.ctx port.val.ty))
    (hs : Typed.Stmt.inst p i child inputs ∈ Lower.statements m)
    (args : List (String × String × Mlir.Ty))
    (pins : args.map (fun arg => (arg.1, arg.2.2)) =
      inputs.map (fun input => (input.1.val.name, Lower.type input.1.val.ty))) :
    SigOk ((m.interfaces child).map Lower.port) (instArgs m.interfaces child args)
      (instResults m.interfaces child) := by
  refine ⟨?_, results_sig _⟩
  rw [← inputs_sig]
  have member := stmt_erase_member m _ hs
  have wf := module_wf raw t h
  have resolved := ((module_wf raw t h).2.1.2 m.erase (checked_erase_member raw t h m hm)
    _ member).1
  obtain ⟨item, found, _⟩ := resolved
  have interfaces : m.interfaces child = item.ports := by
    rw [(t.environments m hm).1]
    have erase := check_sound_erase raw t h
    change Typed.portsOf t.erase child = _
    rw [erase]
    unfold Typed.portsOf
    unfold Rules.findItem at found
    rw [found]
    rfl
  have unique : (item.ports.map Port.name).Nodup :=
    Check.ports_nodup raw item wf.1 (List.mem_of_find?_eq_some found)
  have connected := (wf.2.2.2.2.2.2.2.2.2.1 m.erase (checked_erase_member raw t h m hm) _ member)
  have connections := connected item found
  unfold instArgs
  rw [List.map_filterMap]
  apply filterMap_pointwise
  intro port hp
  by_cases input : port.dir = .input
  · simp only [input, beq_self_eq_true, ↓reduceIte]
    rw [interfaces] at hp
    have once := (connections port hp input).1
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (by omega : 0 < (List.filter
      (fun x => x.1 == port.name) (inputs.map fun input => (input.1.val.name,
        input.2.erase))).length)
    obtain ⟨hx, named⟩ := List.mem_filter.mp hx
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hx
    have find := List.find?_map (f := fun arg : String × String × Mlir.Ty => (arg.1, arg.2.2))
      (p := fun pair => pair.1 == port.name) (l := args)
    simp only [Function.comp_def] at find
    rw [← find, pins, List.find?_map]
    obtain ⟨selected, hselected⟩ : ∃ selected,
        inputs.find? (fun input => input.1.val.name == port.name) = some selected := by
      apply Option.isSome_iff_exists.mp
      apply List.find?_isSome.mpr
      exact ⟨source, hsource, named⟩
    rw [Function.comp_def]
    simp only [hselected, Option.map_some]
    have selectedName : selected.1.val.name = port.name := by
      simpa using List.find?_some hselected
    have same : selected.1.val = port := by
      have hsel : selected.1.val ∈ item.ports := by
        rw [← interfaces]
        exact selected.1.property
      exact Check.named_port_eq _ _ _ unique hsel hp selectedName
    rw [same]
  · simp [input]

end Silicon.Core.LowerProof
