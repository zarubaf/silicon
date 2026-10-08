import Silicon.Core.Semantics.Driver

/-! Finite driver lists permit execution without a choice of witnesses. -/
namespace Silicon.Core.Semantics

abbrev PackedDriver (m : Typed.Module) :=
  (node : Deps.Node) × (width : Nat) × ValueDriver m node width

private def inputDrivers (m : Typed.Module) (p : {p // p ∈ m.ports}) :
    List (PackedDriver m) :=
  match ht : p.val.ty with
  | .clock => []
  | .bits w => if hd : p.val.dir = .input then
      [⟨.name p.val.name, w, .input p.val p.property hd ht⟩] else []

private def equationDrivers (m : Typed.Module) (e : EquationRef m) :
    List (PackedDriver m) :=
  match e with
  | ⟨.let_ i p n w x, h⟩ => [⟨.name n, w, .let_ i p n w x h⟩]
  | ⟨.assign i p n w t x, h⟩ => [⟨.name n, w, .assign i p n w t x h⟩]
  | ⟨.reg i p n w c t r ni np x, h⟩ => [⟨.name n, w, .reg i p n w c t r ni np x h⟩]
  | ⟨.mem .., _⟩ => []
  | ⟨.inst i p n c xs, h⟩ => (m.interfaces c).attach.flatMap fun port =>
    match ht : port.val.ty with
    | .clock => []
    | .bits w => if hd : port.val.dir = .output then
        [⟨.port n port.val.name, w, .inst i p n c xs h port.val port.property hd ht⟩]
      else []

def drivers (m : Typed.Module) : List (PackedDriver m) :=
  m.ports.attach.flatMap (inputDrivers m) ++ m.body.attach.flatMap (equationDrivers m)

theorem driver_mem (m : Typed.Module) (v : ValueDriver m node width) :
    (⟨node, width, v⟩ : PackedDriver m) ∈ drivers m := by
  cases v with
  | input p hp hd ht =>
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨⟨p, hp⟩, by simp, ?_⟩
    cases p
    cases ht
    dsimp at hd
    simp_all [inputDrivers]
  | let_ i p n w x h | assign i p n w t x h | reg i p n w c t r ni np x h =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨⟨_, h⟩, by simp, List.mem_cons_self ..⟩
  | inst i p n c xs h port hp hd ht =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨⟨_, h⟩, by simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨⟨port, hp⟩, by simp, ?_⟩
    cases port
    cases ht
    dsimp at hd
    simp_all

def findValueDriver (m : Typed.Module) (node : Deps.Node) (width : Nat)
    (existsDriver : Nonempty (ValueDriver m node width)) : ValueDriver m node width :=
  let result := (drivers m).find? (fun v => v.1 == node && v.2.1 == width)
  have total : result.isSome := by
    obtain ⟨v⟩ := existsDriver
    exact List.find?_isSome.mpr ⟨⟨node, width, v⟩, driver_mem m v, by simp⟩
  let v := result.get total
  have found : result = some v := (Option.some_get total).symm
  have same : v.1 = node ∧ v.2.1 = width := by
    simpa using List.find?_some found
  same.1 ▸ same.2 ▸ v.2.2

private abbrev PackedMemory (m : Typed.Module) :=
  (name : String) × (width : Nat) × (depth : Nat) × MemoryDriver m name width depth

private def memoryDrivers (m : Typed.Module) : List (PackedMemory m) :=
  m.body.attach.flatMap fun e => match e with
  | ⟨.mem i p n w d c t xs, h⟩ => [⟨n, w, d, .mem i p n w d c t xs h⟩]
  | _ => []

def findMemoryDriver (m : Typed.Module) (name : String) (width depth : Nat)
    (existsDriver : Nonempty (MemoryDriver m name width depth)) :
    MemoryDriver m name width depth :=
  let result := (memoryDrivers m).find?
    (fun v => v.1 == name && v.2.1 == width && v.2.2.1 == depth)
  have total : result.isSome := by
    obtain ⟨v⟩ := existsDriver
    apply List.find?_isSome.mpr
    refine ⟨⟨name, width, depth, v⟩, ?_, by simp⟩
    cases v with
    | mem i p n w d c t xs h =>
      exact List.mem_flatMap.mpr ⟨⟨_, h⟩, by simp, List.mem_cons_self ..⟩
  let v := result.get total
  have found : result = some v := (Option.some_get total).symm
  have same : (v.1 = name ∧ v.2.1 = width) ∧ v.2.2.1 = depth := by
    simpa using List.find?_some found
  same.1.1 ▸ same.1.2 ▸ same.2 ▸ v.2.2.2

end Silicon.Core.Semantics
