import Silicon.Core.Typed

/-! Unique item names make the source layout recoverable after module sorting. -/
namespace Silicon.Core.Typed

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
    (bodies : (typedBodies.map Module.erase).Perm (modules d)) :
    assembleDesign topName itemNames externs typedBodies topPos = d := by
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

end Silicon.Core.Typed
