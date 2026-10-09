import Silicon.Core.Proof.Lower.Models

/-!
The reference lowering of a checked design without externs, with each memory extern
replaced by its model, is a well-formed MLIR design.
-/
namespace Silicon.Core.LowerProof

section
variable (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
  (noExterns : t.externs = [])
include h noExterns

theorem design_names :
    ((lower t).withModels.items.map Mlir.Item.name).Nodup := by
  rw [withModels_items, List.map_map]
  have same : Mlir.Item.name ∘ modelImage = Mlir.Item.name := funext image_name
  rw [same]
  apply ((lower_items t noExterns).map _).nodup_iff.mpr
  rw [List.map_append, List.map_map, List.map_map]
  apply List.nodup_append.mpr
  refine ⟨body_names_nodup raw t h, ?_, ?_⟩
  · exact List.Pairwise.map _ (fun _ _ ne eq => ne (moduleName_injective eq))
      (memoryConfigs_nodup t)
  · intro a ha b hb same
    subst same
    obtain ⟨body, hbody, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, _, eq⟩ := List.mem_map.mp hb
    have legal := body_name_legal raw t h body hbody
    have reserved := moduleName_reserved c
    simp only [Function.comp_def, Mlir.Item.name] at eq
    rw [eq] at reserved
    exact Bool.noConfusion (legal.symm.trans reserved)

omit noExterns in
theorem interfaces_item (b : Typed.Module) (hb : b ∈ t.bodies) (child : String) (item : Item)
    (found : Rules.findItem raw child = some item) : b.interfaces child = item.ports := by
  rw [(t.environments b hb).1]
  have erase := check_sound_erase raw t h
  change Typed.portsOf t.erase child = _
  rw [erase]
  unfold Typed.portsOf
  unfold Rules.findItem at found
  rw [found]
  rfl

omit h in
theorem body_in_design (b : Typed.Module) (hb : b ∈ t.bodies) :
    Mlir.Item.module (Lower.module b).1 ∈ (lower t).withModels.items := by
  rw [withModels_items]
  apply List.mem_map.mpr
  refine ⟨_, (lower_items t noExterns).mem_iff.mpr
    (List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩)), rfl⟩

omit h in
theorem config_in_design (c : MemConfig) (hc : c ∈ memoryConfigs t) :
    modelImage (.extern c.moduleName c.ports) ∈ (lower t).withModels.items := by
  rw [withModels_items]
  apply List.mem_map.mpr
  exact ⟨_, (lower_items t noExterns).mem_iff.mpr
    (List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)), rfl⟩

theorem body_signature (b : Typed.Module) (hb : b ∈ t.bodies) :
    (lower t).withModels.signature b.name = some (b.ports.map Lower.port) :=
  signature_of_mem _ (design_names raw t h noExterns) _ (body_in_design t noExterns b hb)

theorem config_signature (c : MemConfig) (hc : c ∈ memoryConfigs t) :
    (lower t).withModels.signature c.moduleName = some c.ports := by
  have sig := signature_of_mem _ (design_names raw t h noExterns) _
    (config_in_design t noExterns c hc)
  rw [image_name, image_ports] at sig
  exact sig

theorem body_wellFormed (b : Typed.Module) (hb : b ∈ t.bodies) :
    (Lower.module b).1.WellFormed (lower t).withModels := by
  apply lower_module_wellFormed raw t h b hb
  · intro p i child inputs hs
    have member := stmt_erase_member b _ hs
    obtain ⟨item, found, _⟩ := ((module_wf raw t h).2.1.2 b.erase
      (checked_erase_member raw t h b hb) _ member).1
    obtain ⟨c, hc, rfl⟩ := raw_item_module raw t h noExterns item
      (List.mem_of_find?_eq_some found)
    have named : c.erase.name = child := by
      simpa [Item.name] using List.find?_some found
    rw [interfaces_item raw t h b hb child _ found, ← named]
    exact body_signature raw t h noExterns c hc
  · intro i p memory w depth clk target ws he
    apply config_signature raw t h noExterns
    apply (memoryConfigs_mem t _).mpr
    refine ⟨b, hb, ?_⟩
    change _ ∈ ((Lower.memoryEntries b (Lower.statementState b)).map Prod.snd).reverse
    rw [List.mem_reverse]
    exact List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨_, he, rfl⟩, rfl⟩

omit h noExterns in
theorem instance_callee (b : Typed.Module) (names : List String)
    (inst callee : String) (args : List (String × String × Mlir.Ty))
    (results : List (String × Mlir.Ty))
    (he : (names, .instance inst callee args results) ∈ (Lower.module b).1.body) :
    (∃ p i inputs, Typed.Stmt.inst p i callee inputs ∈ Lower.statements b) ∨
      ∃ c : MemConfig, callee = c.moduleName := by
  rw [module_body] at he
  obtain ⟨⟨names', op⟩, hraw, same⟩ := List.mem_map.mp he
  have op_shape : ∃ args', op = .instance inst callee args' results := by
    cases op <;> simp only [Lower.substitute, Prod.mk.injEq, reduceCtorEq, and_false] at same
    case «instance» inst' callee' args' results' =>
      obtain ⟨_, rfl, rfl, _, rfl⟩ := same
      exact ⟨args', rfl⟩
  obtain ⟨args', rfl⟩ := op_shape
  unfold rawBody at hraw
  rcases List.mem_append.mp hraw with hraw | hraw
  · rcases List.mem_append.mp hraw with hraw | hraw
    · obtain ⟨⟨tail, body, _, shapes⟩, _⟩ :=
        statements_step (Lower.registers b) (Lower.statements b) {}
      rw [← run_state] at body
      have tailEq : tail = (Lower.statementState b).body.toList := by simpa using body.symm
      rw [← tailEq] at hraw
      obtain ⟨stmt, hs, shape⟩ := shapes _ hraw rfl
      cases stmt <;> simp only [InstShape] at shape
      case inst p i child inputs =>
        obtain ⟨_, _, same⟩ := shape
        simp only [Prod.mk.injEq, Mlir.Op.instance.injEq] at same
        obtain ⟨_, _, rfl, _⟩ := same
        exact Or.inl ⟨p, i, inputs, hs⟩
    · obtain ⟨x, hx, same⟩ := List.mem_map.mp hraw
      obtain ⟨_, _, memory, w, depth, clk, _, _, _, rfl⟩ := memoryEntries_mem b _ x hx
      simp only [memEntry, Prod.mk.injEq, Mlir.Op.instance.injEq] at same
      exact Or.inr ⟨_, same.2.2.1.symm⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := registerEntries_mem b _ _ hraw
    simp only [Prod.mk.injEq, reduceCtorEq, and_false] at same

def bodyRank (t : Typed.Design) (name : String) : Nat :=
  if name ∈ t.bodies.map (·.name) then (t.bodies.map (·.name)).idxOf name + 1 else 0

theorem rank_decreases (b : Typed.Module) (hb : b ∈ t.bodies) (names : List String)
    (inst callee : String) (args : List (String × String × Mlir.Ty))
    (results : List (String × Mlir.Ty))
    (he : (names, .instance inst callee args results) ∈ (Lower.module b).1.body) :
    bodyRank t callee < bodyRank t (Lower.module b).1.name := by
  have unique := body_names_nodup raw t h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  have own : bodyRank t (t.bodies[j]).name = j + 1 := by
    have member : (t.bodies[j]).name ∈ t.bodies.map (·.name) := List.mem_map_of_mem hb
    simp only [bodyRank, member, ↓reduceIte]
    have := unique.idxOf_getElem j (by simpa using hj)
    simp only [List.getElem_map] at this
    rw [this]
  change bodyRank t callee < bodyRank t (t.bodies[j]).name
  rw [own]
  rcases instance_callee _ names inst callee args results he with
    ⟨p, i, inputs, hs⟩ | ⟨c, rfl⟩
  · have member := stmt_erase_member _ _ hs
    have hj' : j < (t.bodies.map Typed.Module.erase).length := by simpa using hj
    have child : callee ∈ Typed.childNames ((t.bodies.map Typed.Module.erase)[j]'hj') := by
      rw [List.getElem_map]
      exact List.mem_filterMap.mpr ⟨_, member, rfl⟩
    have ordered := t.hierarchy
    rw [noExterns] at ordered
    rcases ordered_children [] _ ordered j (by simpa) callee child with absent | ⟨k, hk, named⟩
    · cases absent
    · rw [List.getElem_map] at named
      have member : callee ∈ t.bodies.map (·.name) := by
        rw [← named]
        exact List.mem_map_of_mem (List.getElem_mem _)
      simp only [bodyRank, member, ↓reduceIte]
      have := unique.idxOf_getElem k (by simp; omega)
      simp only [List.getElem_map] at this
      rw [← named]
      show List.idxOf (t.bodies[k]).name (t.bodies.map Typed.Module.name) + 1 < j + 1
      rw [this]
      omega
  · have absent : c.moduleName ∉ t.bodies.map (·.name) := by
      intro member
      obtain ⟨body, hbody, eq⟩ := List.mem_map.mp member
      have legal := body_name_legal raw t h body hbody
      rw [eq, moduleName_reserved] at legal
      cases legal
    simp only [bodyRank, absent, ↓reduceIte]
    omega

end

/-- The reference lowering of a checked design without externs is well formed when it uses
the model of each memory extern. -/
theorem lower_wellFormed (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (noExterns : t.externs = []) : Mlir.WellFormed (lower t).withModels := by
  have source (item : Mlir.Item) (hi : item ∈ (lower t).withModels.items) :
      ∃ item₀, ((∃ b ∈ t.bodies, item₀ = .module (Lower.module b).1) ∨
        ∃ c ∈ memoryConfigs t, item₀ = .extern c.moduleName c.ports) ∧
        item = modelImage item₀ := by
    rw [withModels_items] at hi
    obtain ⟨item₀, h₀, rfl⟩ := List.mem_map.mp hi
    refine ⟨item₀, ?_, rfl⟩
    rcases List.mem_append.mp ((lower_items t noExterns).mem_iff.mp h₀) with h₀ | h₀
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h₀
      exact Or.inl ⟨b, hb, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h₀
      exact Or.inr ⟨c, hc, rfl⟩
  have modules (m : Mlir.Module) (hm : .module m ∈ (lower t).withModels.items) :
      (∃ b ∈ t.bodies, m = (Lower.module b).1) ∨ ∃ c, m = memModel c := by
    obtain ⟨item₀, origin, image⟩ := source _ hm
    rcases image_module item₀ m image.symm with same | model
    · rcases origin with ⟨b, hb, rfl⟩ | ⟨c, _, rfl⟩
      · cases same
        exact Or.inl ⟨b, hb, rfl⟩
      · cases same
    · exact Or.inr model
  refine ⟨design_names raw t h noExterns, ?_, ?_, bodyRank t, ?_⟩
  · intro item hi
    obtain ⟨item₀, origin, rfl⟩ := source item hi
    rw [image_ports]
    rcases origin with ⟨b, hb, rfl⟩ | ⟨c, _, rfl⟩
    · change ((b.ports.map Lower.port).map Mlir.Port.name).Nodup
      rw [List.map_map]
      exact Check.module_ports_nodup raw b.erase (module_wf raw t h)
        (checked_erase_member raw t h b hb)
    · exact memModel_ports c
  · intro m hm
    rcases modules m hm with ⟨b, hb, rfl⟩ | ⟨c, rfl⟩
    · exact body_wellFormed raw t h noExterns b hb
    · exact memModel_wf _ c
  · intro m hm names inst callee args results he
    rcases modules m hm with ⟨b, hb, rfl⟩ | ⟨c, rfl⟩
    · exact rank_decreases raw t h noExterns b hb names inst callee args results he
    · have := memModel_plain c _ he
      cases this

end Silicon.Core.LowerProof
