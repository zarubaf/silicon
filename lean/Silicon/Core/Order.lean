import Silicon.Core.Typed

/-! A finite ranked hierarchy always has a child whose prerequisites are available. -/
namespace Silicon.Core

deriving instance ReflBEq, LawfulBEq for Pos, Ty, UnOp, BinOp, Pred, Expr, ResetKind, Reset
deriving instance ReflBEq, LawfulBEq for Stmt, PortDir, Port, Module

end Silicon.Core

namespace Silicon.Core.Typed

private theorem minimum_member (xs : List α) (q : α → Nat) (h : xs ≠ []) :
    ∃ x ∈ xs, ∀ y ∈ xs, q x ≤ q y := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    by_cases ht : xs = []
    · subst xs
      exact ⟨a, by simp, by simp⟩
    · obtain ⟨b, hb, hm⟩ := ih ht
      by_cases hab : q a ≤ q b
      · refine ⟨a, by simp, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans hab (hm y hy)
      · refine ⟨b, by simp [hb], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact hm y hy

private theorem ready_member (pending : List Core.Module) (seen : List String)
    (q : String → Nat) (nonempty : pending ≠ [])
    (closed : ∀ m ∈ pending, ∀ c ∈ childNames m,
      c ∈ seen ∨ ∃ child ∈ pending, child.name = c ∧ q c < q m.name) :
    ∃ m ∈ pending, (childNames m).all seen.contains = true := by
  obtain ⟨m, hm, least⟩ := minimum_member pending (fun m => q m.name) nonempty
  refine ⟨m, hm, List.all_eq_true.mpr ?_⟩
  intro c hc
  rcases closed m hm c hc with hs | ⟨child, hchild, he, hl⟩
  · simpa using hs
  · have := least child hchild
    rw [he] at this
    omega

theorem orderModules_complete (fuel : Nat) (seen : List String)
    (pending : List Core.Module) (q : String → Nat) (bound : pending.length ≤ fuel)
    (closed : ∀ m ∈ pending, ∀ c ∈ childNames m,
      c ∈ seen ∨ ∃ child ∈ pending, child.name = c ∧ q c < q m.name) :
    ∃ sorted, orderModules fuel seen pending = some sorted ∧
      sorted.Perm pending ∧ ordered seen sorted = true := by
  induction fuel generalizing seen pending with
  | zero =>
    have hp : pending = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst pending
    exact ⟨[], rfl, .refl _, rfl⟩
  | succ fuel ih =>
    by_cases hp : pending = []
    · subst pending
      exact ⟨[], rfl, .refl _, rfl⟩
    · obtain ⟨m, hm, ready⟩ := ready_member pending seen q hp closed
      have exists_find : (pending.find? fun m => (childNames m).all seen.contains).isSome := by
        rw [List.isSome_find?]
        exact List.any_eq_true.mpr ⟨m, hm, ready⟩
      obtain ⟨chosen, hc⟩ := Option.isSome_iff_exists.mp exists_find
      have chosen_mem := List.mem_of_find?_eq_some hc
      have chosen_ready := List.find?_some hc
      have smaller : (pending.erase chosen).length ≤ fuel := by
        have := List.length_erase_of_mem chosen_mem
        omega
      have closed' : ∀ m ∈ pending.erase chosen, ∀ c ∈ childNames m,
          c ∈ chosen.name :: seen ∨
            ∃ child ∈ pending.erase chosen, child.name = c ∧ q c < q m.name := by
        intro m hm c hc
        rcases closed m (List.mem_of_mem_erase hm) c hc with hs | ⟨child, hch, he, hl⟩
        · exact Or.inl (List.mem_cons_of_mem _ hs)
        · by_cases hsame : child = chosen
          · subst child
            exact Or.inl (by simp [he])
          · exact Or.inr ⟨child, List.mem_erase_of_ne hsame |>.mpr hch, he, hl⟩
      obtain ⟨rest, hr, perm, ho⟩ := ih (chosen.name :: seen) (pending.erase chosen)
        smaller closed'
      refine ⟨chosen :: rest, ?_, ?_, ?_⟩
      · simp [orderModules, hp, hc, hr]
      · exact (List.Perm.cons chosen perm).trans (List.perm_cons_erase chosen_mem).symm
      · simp [ordered, chosen_ready, ho]


/-! Unique item names make the source layout recoverable after module sorting. -/
private theorem find_named (xs : List α) (name : α → String) (x : α)
    (mem : x ∈ xs) (unique : ∀ y ∈ xs, name y = name x → y = x) :
    xs.find? (fun y => name y == name x) = some x := by
  induction xs with
  | nil => simp at mem
  | cons a xs ih =>
    by_cases he : name a = name x
    · have ha := unique a (by simp) he
      subst a
      simp
    · have ht : x ∈ xs := by
        rcases List.mem_cons.mp mem with h | h
        · subst a
          contradiction
        · exact h
      simp [he, ih ht (fun y hy => unique y (by simp [hy]))]

private theorem unique_item (d : Core.Design) (hn : (d.items.map itemName).Nodup)
    (a b : Core.Item) (ha : a ∈ d.items) (hb : b ∈ d.items)
    (he : itemName a = itemName b) : a = b := by
  have general : ∀ (xs : List Core.Item), (xs.map itemName).Nodup →
      ∀ a ∈ xs, ∀ b ∈ xs, itemName a = itemName b → a = b := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hn a ha b hb he
      obtain ⟨notmem, nodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ha with rfl | hat
      · rcases List.mem_cons.mp hb with rfl | hb
        · rfl
        · exact False.elim (notmem (List.mem_map.mpr ⟨b, hb, he.symm⟩))
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact False.elim (notmem (List.mem_map.mpr ⟨a, hat, he⟩))
        · exact ih nodup a hat b hb he
  exact general d.items hn a ha b hb he

theorem assembleDesign_erase_of_modules (d : Core.Design) (topName : String)
    (itemNames : List String) (externs : List Extern) (typedBodies : List Module) (topPos : Pos)
    (hn : (d.items.map itemName).Nodup)
    (top : topName = d.top) (pos : topPos = d.topPos)
    (names : itemNames = d.items.map itemName)
    (exts : externs = d.items.filterMap fun i => match i with
      | .extern e => some e | _ => none)
    (bodies : (typedBodies.map Module.erase).Perm (modules d)) : assembleDesign topName itemNames externs typedBodies topPos = d := by
  have member : ∀ m, m ∈ typedBodies → Core.Item.module m.erase ∈ d.items := by
    intro m hm
    have hh := bodies.mem_iff.mp (List.mem_map.mpr ⟨m, hm, rfl⟩)
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hh
    cases i <;> cases he
    exact hi
  have ext_member : ∀ e, e ∈ externs → Core.Item.extern e ∈ d.items := by
    intro e he
    rw [exts] at he
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp he
    cases i <;> cases he
    exact hi
  have select : ∀ i ∈ d.items,
      (match typedBodies.find? (fun m => m.name == itemName i) with
       | some m => some (.module m.erase)
       | none => (externs.find? fun e => e.name == itemName i).map Core.Item.extern) =
        some i := by
    intro i hi
    cases i with
    | module m =>
      have hm : m ∈ modules d := List.mem_filterMap.mpr ⟨.module m, hi, rfl⟩
      obtain ⟨tm, htm, erase⟩ := List.mem_map.mp (bodies.mem_iff.mpr hm)
      have name : tm.name = m.name := congrArg Core.Module.name erase
      have exists_find : (typedBodies.find? fun x => x.name == m.name).isSome := by
        rw [List.isSome_find?]
        exact List.any_eq_true.mpr ⟨tm, htm, by simpa using name⟩
      obtain ⟨chosen, found⟩ := Option.isSome_iff_exists.mp exists_find
      have hc := member chosen (List.mem_of_find?_eq_some found)
      have hname : chosen.name = m.name := by simpa using List.find?_some found
      have eq := unique_item d hn _ _ hc hi hname
      simpa only [itemName, found, Option.some.injEq] using eq
    | extern e =>
      have absent : typedBodies.find? (fun m => m.name == e.name) = none := by
        apply List.find?_eq_none.mpr
        intro m hm he
        have hname : m.name = e.name := by simpa using he
        have eq := unique_item d hn _ _ (member m hm) hi hname
        cases eq
      have mem : e ∈ externs := by
        rw [exts]
        exact List.mem_filterMap.mpr ⟨.extern e, hi, rfl⟩
      have found := find_named externs (·.name) e mem (by
        intro other ho he
        have eq := unique_item d hn _ _ (ext_member other ho) hi he
        cases eq
        rfl)
      simp [itemName, absent, found]
  have items : (d.items.map itemName).filterMap (fun n =>
      match typedBodies.find? (·.name == n) with
      | some m => some (.module m.erase)
      | none => (externs.find? (·.name == n)).map Core.Item.extern) = d.items := by
    rw [List.filterMap_map]
    have aux : ∀ (xs : List Core.Item) (f : Core.Item → Option Core.Item),
        (∀ i ∈ xs, f i = some i) → xs.filterMap f = xs := by
      intro xs f h
      induction xs with
      | nil => rfl
      | cons a xs ih =>
        simp only [List.filterMap_cons, h a (by simp)]
        exact congrArg (a :: ·) (ih (fun i hi => h i (by simp [hi])))
    exact aux _ _ select
  dsimp only [assembleDesign]
  rw [top, pos, names]
  congr 1


/-! Source indices recover statement order after state updates are grouped. -/
theorem sortIndexed_of_perm (parts : List (Nat × α)) (body : List α)
    (perm : parts.Perm (body.zipIdx.map fun (s, i) => (i, s))) :
    parts.mergeSort (fun a b => decide (a.1 ≤ b.1)) =
      body.zipIdx.map (fun (s, i) => (i, s)) := by
  let indexed := body.zipIdx.map fun (s, i) => (i, s)
  have sorted : ∀ (xs : List α) start,
      (xs.zipIdx start).Pairwise (fun a b => a.2 ≤ b.2) := by
    intro xs start
    induction xs generalizing start with
    | nil => simp
    | cons s ss ih =>
      simp only [List.zipIdx_cons, List.pairwise_cons]
      refine ⟨?_, ih _⟩
      intro x hx
      have := List.le_snd_of_mem_zipIdx hx
      omega
  have ordered : indexed.Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa [indexed, List.pairwise_map] using sorted body 0
  have merged := List.pairwise_mergeSort
    (le := fun a b : Nat × α => decide (a.1 ≤ b.1))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    parts
  have totalperm := (List.mergeSort_perm parts
    (fun a b => decide (a.1 ≤ b.1))).trans perm
  have exact_order := List.Perm.eq_of_pairwise (le := fun a b => a.1 ≤ b.1)
    (l₁ := parts.mergeSort (fun a b => decide (a.1 ≤ b.1)))
    (l₂ := indexed) (by
      intro a b ha hb hab hba
      have ha := totalperm.mem_iff.mp ha
      obtain ⟨⟨sa, ia⟩, hsa, ea⟩ := List.mem_map.mp ha
      obtain ⟨⟨sb, ib⟩, hsb, eb⟩ := List.mem_map.mp hb
      cases ea
      cases eb
      have idx : ia = ib := by simpa using Nat.le_antisymm hab hba
      subst ib
      have hsa := List.mk_mem_zipIdx_iff_getElem?.mp hsa
      have hsb := List.mk_mem_zipIdx_iff_getElem?.mp hsb
      rw [hsa] at hsb
      cases hsb
      rfl)
    (by simpa using merged) ordered totalperm
  exact exact_order

theorem equationsErase_of_raw_perm (groups : List (Equation ctx ports))
    (body : List Core.Stmt)
    (perm : ((groups.flatMap Equation.parts).map indexedErase).Perm
      (body.zipIdx.map fun (s, i) => (i, s))) : equationsErase groups = body := by
  have sorted := sortIndexed_of_perm _ body perm
  have commute := List.map_mergeSort
    (r := fun a b : Nat × Stmt ctx ports => decide (a.1 ≤ b.1))
    (s := fun a b : Nat × Core.Stmt => decide (a.1 ≤ b.1))
    (f := indexedErase) (l := groups.flatMap Equation.parts) (by intros; rfl)
  rw [← commute] at sorted
  have result := congrArg (List.map Prod.snd) sorted
  simp only [List.map_map, Function.comp_def, indexedErase] at result
  change equationsErase groups = body.zipIdx.map Prod.fst at result
  simpa only [List.zipIdx_map_fst] using result

/-! The final checks follow from the ordering and exact module erasures. -/
theorem elaborateDesign_of_modules (d : Core.Design) (sorted : List Core.Module)
    (bodies : List Module) (names : (d.items.map itemName).Nodup)
    (order : orderModules (modules d).length (externNames d) (modules d) = some sorted)
    (permutation : sorted.Perm (modules d)) (hierarchy : ordered (externNames d) sorted = true)
    (elaborated : elaborateModules d sorted = some bodies)
    (erased : bodies.map Module.erase = sorted) :
    ∃ t, elaborateDesign d = some t := by
  have extnames : (d.items.filterMap (fun i => match i with
      | .extern e => some e | _ => none)).map (·.name) = externNames d := by
    simp only [List.map_filterMap, externNames]
    congr 1
    funext i
    cases i <;> rfl
  unfold elaborateDesign
  simp only [order, bind, Option.bind_some, dite_eq_left permutation]
  have orderedBodies : ordered ((d.items.filterMap (fun i => match i with
      | .extern e => some e | _ => none)).map (·.name)) (bodies.map Module.erase) = true := by
    rw [extnames, erased]
    exact hierarchy
  split
  · rename_i impossible
    rw [elaborated] at impossible
    contradiction
  · rename_i bs found
    rw [elaborated] at found
    cases found
    split
    · split
      · exact ⟨_, rfl⟩
      · rename_i failure
        exfalso
        apply failure
        apply assembleDesign_erase_of_modules d _ _ _ _ _ names rfl rfl rfl rfl
        rw [erased]
        exact permutation
    · rename_i failure
      exact False.elim (failure orderedBodies)

/-! Each module succeeds once grouping preserves its statements and its graph has ranks. -/
theorem elaborateModules_of_groups (d : Core.Design) (ms : List Core.Module)
    (ready : ∀ m ∈ ms, ∃ body groups,
      m.body.mapM (statement d (context d m)) = some body ∧
      groupStatements (context d m) (portsOf d) body = some groups ∧
      equationsErase groups = m.body ∧
      ∃ ranks, FastRanks.certificate (Deps.graph m (designDeps d (d.items.length + 1))) =
        some ranks) :
    ∃ bodies, elaborateModules d ms = some bodies ∧ bodies.map Module.erase = ms := by
  induction ms with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons m ms ih =>
    obtain ⟨body, groups, hb, hg, he, ranks, hr⟩ := ready m (by simp)
    obtain ⟨rest, hrest, erased⟩ := ih (fun m hm => ready m (by simp [hm]))
    unfold elaborateModules
    simp only [statements, hb, bind, Option.bind_some]
    split
    · rename_i failure
      rw [hr] at failure
      contradiction
    · simp only [hg, Option.bind_some]
      split
      · simp only [hrest, Option.bind_some, pure]
        refine ⟨_, rfl, ?_⟩
        simp only [List.map_cons, Module.erase, he, erased]
      · contradiction

end Silicon.Core.Typed
