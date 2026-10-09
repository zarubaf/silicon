import Silicon.Core.Proof.Lower.ModuleFacts

/-!
Each context entry comes from a port or one declaration. Unique scope names give each
source name one context entry.
-/
namespace Silicon.Core.LowerProof

def DeclEntry (interfaces : String → List Port) (node : Deps.Node) (kind : Typed.Kind) :
    Core.Stmt → Prop
  | .let_ _ n w _ | .reg _ n w _ _ => node = .name n ∧ kind = .value (.bits w)
  | .mem _ n w depth _ => node = .name n ∧ kind = .memory w depth
  | .inst _ n child _ => ∃ p ∈ interfaces child, p.dir = .output ∧ node = .port n p.name ∧
      kind = .value p.ty
  | _ => False

def portKind (p : Port) : Typed.Kind :=
  if p.ty == .clock && p.dir == .input then .clock else .value p.ty

theorem context_member (interfaces : String → List Port) (mod : Core.Module) (node : Deps.Node)
    (kind : Typed.Kind) (h : (node, kind) ∈ Typed.contextFromPorts interfaces mod) :
    (∃ p ∈ mod.ports, node = .name p.name ∧ kind = portKind p) ∨
      ∃ s ∈ mod.body, DeclEntry interfaces node kind s := by
  unfold Typed.contextFromPorts at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨p, hp, eq⟩ := List.mem_map.mp h
    cases eq
    exact Or.inl ⟨p, hp, rfl, rfl⟩
  · obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp h
    refine Or.inr ⟨s, hs, ?_⟩
    cases s <;> simp only [List.mem_singleton, List.not_mem_nil] at he
    case let_ => cases he; exact ⟨rfl, rfl⟩
    case reg => cases he; exact ⟨rfl, rfl⟩
    case mem => cases he; exact ⟨rfl, rfl⟩
    case inst p n child xs =>
      obtain ⟨port, hp, he⟩ := List.mem_filterMap.mp he
      split at he
      next hd =>
        cases he
        exact ⟨port, hp, by simpa using hd, rfl, rfl⟩
      next => cases he

def nameKey (entry : Deps.Node × Typed.Kind) : Option String :=
  match entry.1 with
  | .name x => some x
  | .port .. => none

private def declName : Core.Stmt → List String
  | .let_ _ n .. | .reg _ n .. | .mem _ n .. => [n]
  | _ => []

private theorem context_names (interfaces : String → List Port) (mod : Core.Module) :
    (Typed.contextFromPorts interfaces mod).filterMap nameKey =
      mod.ports.map Port.name ++ mod.body.flatMap declName := by
  unfold Typed.contextFromPorts
  rw [List.filterMap_append, List.filterMap_map]
  congr 1
  · simp [Function.comp_def, nameKey]
  · rw [List.filterMap_flatMap]
    congr 1
    funext s
    cases s <;> simp [nameKey, declName]
    case inst p n child xs =>
      intro a b port _ _
      rintro rfl rfl
      rfl

private theorem declName_sublist (body : List Core.Stmt) :
    (body.flatMap declName).Sublist (body.filterMap Rules.definition) := by
  induction body with
  | nil => exact List.Sublist.refl _
  | cons s body ih =>
    cases s <;> simp only [declName, List.flatMap_cons, List.filterMap_cons, Rules.definition,
      List.nil_append, List.singleton_append]
    all_goals first | exact ih.cons_cons _ | exact ih.cons _ | exact ih

theorem filterMap_unique {f : α → Option β} {l : List α} (unique : (l.filterMap f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (x : β) (ka : f a = some x) (kb : f b = some x) :
    a = b := by
  induction l with
  | nil => cases ha
  | cons c l ih =>
    rw [List.filterMap_cons] at unique
    have head (d : α) (hd : d ∈ l) (kd : f d = some x) (kc : f c = some x) : False := by
      rw [kc] at unique
      exact (List.nodup_cons.mp unique).1 (List.mem_filterMap.mpr ⟨d, hd, kd⟩)
    have tail : (l.filterMap f).Nodup := by
      cases hc : f c with
      | none => rw [hc] at unique; exact unique
      | some y => rw [hc] at unique; exact (List.nodup_cons.mp unique).2
    rcases List.mem_cons.mp ha with ea | ha'
    · rcases List.mem_cons.mp hb with eb | hb'
      · rw [ea, eb]
      · exact (head b hb' kb (ea ▸ ka)).elim
    · rcases List.mem_cons.mp hb with eb | hb'
      · exact (head a ha' ka (eb ▸ kb)).elim
      · exact ih tail ha' hb'

theorem context_name_unique (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (x : String) (k₁ k₂ : Typed.Kind)
    (h₁ : (.name x, k₁) ∈ m.ctx) (h₂ : (.name x, k₂) ∈ m.ctx) : k₁ = k₂ := by
  rw [m.context_eq] at h₁ h₂
  have unique : ((Typed.contextFromPorts m.interfaces m.erase).filterMap nameKey).Nodup := by
    rw [context_names]
    have scope := scope_nodup raw t h m hm
    exact scope.sublist ((List.Sublist.refl _).append (declName_sublist _))
  have same := filterMap_unique unique h₁ h₂ x rfl rfl
  cases same
  rfl

theorem lookup_member (ctx : Typed.Ctx) (node : Deps.Node) (kind : Typed.Kind)
    (found : ctx.lookup node = some kind) : (node, kind) ∈ ctx := by
  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp found
  rw [eq]
  simp

theorem lookup_name (raw : Core.Design) (t : Typed.Design) (h : check raw = .ok t)
    (m : Typed.Module) (hm : m ∈ t.bodies) (x : String) (kind : Typed.Kind)
    (member : (.name x, kind) ∈ m.ctx) : m.ctx.lookup (.name x) = some kind := by
  cases found : m.ctx.lookup (.name x) with
  | none =>
    have := List.lookup_eq_none_iff.mp found _ member
    simp at this
  | some other =>
    rw [context_name_unique raw t h m hm x other kind (lookup_member _ _ _ found) member]

end Silicon.Core.LowerProof
