import Silicon.Core.Canonical.Reorder

namespace Silicon.Core

namespace Reorder

theorem names {d d' : Design} (h : Reorder d d') (hn : Rules.Names d) : Rules.Names d' := by
  have unique {xs ys : List String} (hp : xs.Perm ys) (hx : Rules.Unique xs) :
      Rules.Unique ys := ⟨hp.nodup_iff.mp hx.1, fun n hm => hx.2 n (hp.mem_iff.mpr hm)⟩
  refine ⟨unique (h.items.map _ _ (fun _ _ hi => hi.name)) hn.1, ?_⟩
  intro i' hi'
  obtain ⟨i, hi, related⟩ := h.items.right hi'
  exact unique related.scope (hn.2 i hi)

theorem numbers {d d' : Design} (h : Reorder d d')
    (hn : Rules.Numbers d) : Rules.Numbers d' := by
  intro i' hi'
  obtain ⟨i, hi, related⟩ := h.items.right hi'
  have old := hn i hi
  refine ⟨?_, ?_⟩
  · rw [← related.ports]
    exact old.1
  · cases related with
    | extern => trivial
    | module m m' _ _ _ body =>
      intro s' hs'
      obtain ⟨s, hs, related⟩ := body.right hs'
      have rule := old.2 s hs
      refine ⟨?_, fun e he node hnode => rule.2 e (related.exprs.mem_iff.mpr he) node hnode⟩
      cases related with
      | same => exact rule.1
      | inst => trivial

theorem dependencies {d d' : Design} (h : Reorder d d')
    (hn : Rules.Dependencies d) : Rules.Dependencies d' := by
  intro i' hi'
  obtain ⟨i, hi, related⟩ := h.items.right hi'
  have old := hn i hi
  cases related with
  | module => trivial
  | extern e e' _ _ ports deps =>
    refine ⟨?_, ?_⟩
    · intro p hp dir
      rw [← (deps.filter _).length_eq]
      exact old.1 p (ports ▸ hp) dir
    · intro dep hd
      have rule := old.2 dep (deps.mem_iff.mpr hd)
      simpa only [ports] using rule

theorem module_right {d d' : Design} (h : Reorder d d') {m' : Module}
    (hm' : m' ∈ Typed.modules d') : ∃ m ∈ Typed.modules d,
      m'.pos = m.pos ∧ m'.name = m.name ∧ m'.ports = m.ports ∧
        Permuted StmtReorder m.body m'.body := by
  obtain ⟨i', hi', ei'⟩ := List.mem_filterMap.mp hm'
  cases i' with
  | extern => cases ei'
  | module m' =>
    cases ei'
    obtain ⟨i, hi, related⟩ := h.items.right hi'
    cases related with
    | module m _ pos name ports body =>
      exact ⟨m, List.mem_filterMap.mpr ⟨_, hi, rfl⟩, pos, name, ports, body⟩

theorem registers {d d' : Design} (h : Reorder d d')
    (hn : Rules.Registers d) : Rules.Registers d' := by
  intro m' hm' s' hs'
  obtain ⟨m, hm, _, _, _, body⟩ := h.module_right hm'
  obtain ⟨s, hs, related⟩ := body.right hs'
  have nexts (n : String) : (Rules.nexts m n).Perm (Rules.nexts m' n) := by
    apply body.filterMap
    intro a b hab
    cases hab <;> rfl
  cases related with
  | inst => trivial
  | same =>
    have rule := hn m hm s' hs
    cases s' <;> try trivial
    rename_i n _ _ _
    dsimp only at rule ⊢
    rw [← (nexts n).length_eq]
    exact rule

theorem outputs {d d' : Design} (h : Reorder d d')
    (hn : Rules.Outputs d) : Rules.Outputs d' := by
  intro m' hm' p hp dir
  obtain ⟨m, hm, _, _, ports, body⟩ := h.module_right hm'
  have perm : (Rules.assignments m p.name).Perm (Rules.assignments m' p.name) := by
    apply body.filterMap
    intro a b hab
    cases hab <;> rfl
  rw [← perm.length_eq]
  exact hn m hm p (ports ▸ hp) dir

theorem writes {d d' : Design} (h : Reorder d d')
    (hn : Rules.Writes d) : Rules.Writes d' := by
  intro m' hm' s' hs'
  obtain ⟨m, hm, _, _, _, body⟩ := h.module_right hm'
  obtain ⟨s, hs, related⟩ := body.right hs'
  have writes (n : String) : (Rules.writes m n).Perm (Rules.writes m' n) := by
    apply body.filterMap
    intro a b hab
    cases hab <;> rfl
  cases related with
  | inst => trivial
  | same =>
    have rule := hn m hm s' hs
    cases s' <;> try trivial
    rename_i n _ _ _
    have perm := writes n
    exact ⟨(perm.map Prod.fst).nodup_iff.mp rule.1, fun i hi =>
      perm.length_eq ▸ rule.2 i ((perm.map Prod.fst).mem_iff.mpr hi)⟩

theorem hierarchy {d d' : Design} (h : Reorder d d')
    (hn : Rules.Hierarchy d) : Rules.Hierarchy d' := by
  obtain ⟨ranks, ranked⟩ := hn
  refine ⟨ranks, ?_⟩
  intro row hrow dep hdep
  obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hrow
  obtain ⟨m, hm, _, name, _, body⟩ := h.module_right hm'
  have children : (Typed.childNames m).Perm (Typed.childNames m') := by
    apply body.filterMap
    intro a b hab
    cases hab <;> rfl
  rw [name]
  exact ranked _ (List.mem_map.mpr ⟨m, hm, rfl⟩) dep
    ((children.map Deps.Node.name).mem_iff.mpr hdep)

end Reorder

private theorem lookup_perm {κ : Type} [BEq κ] [LawfulBEq κ]
    {xs ys : List (κ × α)} (perm : xs.Perm ys)
    (unique : (xs.map Prod.fst).Nodup) (name : κ) :
    xs.lookup name = ys.lookup name := by
  induction perm with
  | nil => rfl
  | cons a perm ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    cases a
    simp only [List.lookup_cons]
    split
    · rfl
    · exact ih unique.2
  | swap a b xs =>
    rcases a with ⟨a, av⟩
    rcases b with ⟨b, bv⟩
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at unique
    simp only [List.lookup_cons]
    cases ha : name == a <;> cases hb : name == b <;> simp_all
  | trans first _ ih₁ ih₂ =>
    exact (ih₁ unique).trans (ih₂ ((first.map Prod.fst).nodup_iff.mp unique))

private theorem find_named {xs : List α} (key : α → String)
    (unique : (xs.map key).Nodup) {x : α} (member : x ∈ xs) :
    xs.find? (fun a => key a == key x) = some x := by
  induction xs with
  | nil => simp at member
  | cons a xs ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have ne : key a ≠ key x := by
        intro eq
        exact unique.1 (eq ▸ List.mem_map.mpr ⟨x, member, rfl⟩)
      simp [ne, ih unique.2 member]

theorem Reorder.findItem {d d' : Design} (h : Reorder d d') (hn : Rules.Names d)
    {name : String} {i' : Item} (found : Rules.findItem d' name = some i') :
    ∃ i, Rules.findItem d name = some i ∧ ItemReorder i i' := by
  obtain ⟨i, hi, related⟩ := h.items.right (List.mem_of_find?_eq_some found)
  have key : Typed.itemName i' = name := by simpa [Rules.findItem] using List.find?_some found
  refine ⟨i, ?_, related⟩
  have eq := find_named Typed.itemName hn.1.1 hi
  simpa only [related.name, key, Rules.findItem] using eq

theorem Reorder.connections {d d' : Design} (h : Reorder d d')
    (hn : Rules.Names d) (hc : Rules.Connections d) : Rules.Connections d' := by
  intro m' hm' s' hs'
  obtain ⟨m, hm, _, _, ports, body⟩ := h.module_right hm'
  obtain ⟨s, hs, related⟩ := body.right hs'
  have rule := hc m hm s hs
  have direct : Rules.directClock m' = Rules.directClock m := by
    funext e
    cases e <;> simp [Rules.directClock, Rules.clockName, Rules.findPort, ports]
  cases related with
  | same =>
    cases s' <;> try trivial
    rename_i child xs
    intro i' found p hp dir
    obtain ⟨i, found, related⟩ := h.findItem hn found
    simpa only [direct] using rule i found p (related.ports ▸ hp) dir
  | inst pos name child xs ys perm =>
    intro i' found p hp dir
    obtain ⟨i, found, related⟩ := h.findItem hn found
    have old := rule i found p (related.ports ▸ hp) dir
    refine ⟨?_, ?_⟩
    · rw [← (perm.filter _).length_eq]
      exact old.1
    · intro clock x hx key
      rw [direct]
      exact old.2 clock x (perm.mem_iff.mpr hx) key

private theorem interfaces_lookup (items : List Item) (name : String) :
    (items.map fun i => (i.name, i.ports)).lookup name =
      ((items.find? fun i => Typed.itemName i == name).map Typed.itemPorts) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    cases item <;>
      simp only [List.map_cons, Item.name, Item.ports, List.lookup_cons,
        List.find?_cons, Typed.itemName]
    all_goals
      rename_i value
      by_cases h : name = value.name
      · simp [h, Typed.itemPorts]
      · simpa only [beq_eq_false_iff_ne.mpr h,
          beq_eq_false_iff_ne.mpr (Ne.symm h), Item.name, Item.ports, Typed.itemName] using ih

theorem Reorder.portsOf {d d' : Design} (h : Reorder d d')
    (hn : Rules.Names d) : Typed.portsOf d = Typed.portsOf d' := by
  have perm : (d.items.map fun i => (i.name, i.ports)).Perm
      (d'.items.map fun i => (i.name, i.ports)) := by
    apply h.items.map
    intro i i' related
    have name := related.name
    have ports := related.ports
    cases i <;> cases i' <;> simp_all [Typed.itemName, Typed.itemPorts, Item.name, Item.ports]
  have unique : (d.items.map fun i => (i.name, i.ports)).map Prod.fst =
      d.items.map Typed.itemName := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    cases i <;> rfl
  funext name
  have eq := lookup_perm perm (unique ▸ hn.1.1) name
  rw [interfaces_lookup, interfaces_lookup] at eq
  exact congrArg (fun p => p.getD []) eq

private def contextEntry (interfaces : String → List Port) : Stmt → Typed.Ctx
  | .let_ _ n w _ | .reg _ n w _ _ => [(.name n, .value (.bits w))]
  | .mem _ n w depth _ => [(.name n, .memory w depth)]
  | .inst _ n child _ => (interfaces child).filterMap fun p =>
    if p.dir == .output then some (.port n p.name, .value p.ty) else none
  | _ => []

private def nodeOwner : Deps.Node → String
  | .name n | .port n _ => n

private theorem contextEntry_owner (interfaces : String → List Port) (s : Stmt)
    (node : Deps.Node) (member : node ∈ (contextEntry interfaces s).map Prod.fst) :
    Rules.definition s = some (nodeOwner node) := by
  cases s <;> simp_all [contextEntry, Rules.definition, nodeOwner]
  obtain ⟨_, p, _, _, eq, _⟩ := member
  subst node
  rfl

private theorem context_keys_nodup (d : Design) (m : Module) (hn : Rules.Names d)
    (hm : m ∈ Typed.modules d) : ((Typed.context d m).map Prod.fst).Nodup := by
  have mi : Item.module m ∈ d.items := by
    obtain ⟨i, hi, eq⟩ := List.mem_filterMap.mp hm
    cases i <;> simp_all
  have unique := (hn.2 (.module m) mi).1
  change ((m.ports.map Port.name) ++ m.body.filterMap Rules.definition).Nodup at unique
  have parts := List.nodup_append.mp unique
  have portUnique (child : String) :
      ((Typed.portsOf d child).map Port.name).Nodup := by
    unfold Typed.portsOf
    cases found : d.items.find? (fun i => Typed.itemName i == child) with
    | none => simp
    | some item =>
      exact Check.ports_nodup d item hn (List.mem_of_find?_eq_some found)
  change (((m.ports.map fun p => (Deps.Node.name p.name,
    if p.ty == .clock && p.dir == .input then Typed.Kind.clock else .value p.ty)) ++
    m.body.flatMap (contextEntry (Typed.portsOf d))).map Prod.fst).Nodup
  simp only [List.map_append, List.map_map, List.map_flatMap]
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def, List.nodup_iff_pairwise_ne] using
      parts.1.map Deps.Node.name (fun _ _ ne eq => ne (Deps.Node.name.inj eq))
  · apply List.flatMap_nodup_owners _ _ Rules.definition nodeOwner parts.2.1
    · intro s _
      cases s with
      | inst p n child xs =>
        simp only [contextEntry, List.map_filterMap]
        apply List.Pairwise.filterMap _ _ (List.pairwise_map.mp (portUnique child))
        intro a b ne x hx y hy eq
        split at hx <;> simp_all
        exact ne (Deps.Node.port.inj (hx.trans hy.2.symm)).2
      | _ => simp [contextEntry]
    · intro s _ n member
      exact contextEntry_owner _ s n member
  · intro a ha b hb eq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    subst b
    obtain ⟨s, hs, member⟩ := List.mem_flatMap.mp hb
    have owner := contextEntry_owner (Typed.portsOf d) s (.name p.name) member
    exact parts.2.2 p.name (List.mem_map.mpr ⟨p, hp, rfl⟩) p.name
      (List.mem_filterMap.mpr ⟨s, hs, owner⟩) rfl

namespace Reorder

theorem context_lookup {d d' : Design} (h : Reorder d d') (hn : Rules.Names d)
    {m m' : Module} (hm : m ∈ Typed.modules d) (ports : m'.ports = m.ports)
    (body : Permuted StmtReorder m.body m'.body) (node : Deps.Node) :
    (Typed.context d m).lookup node = (Typed.context d' m').lookup node := by
  have entries : (m.body.flatMap (contextEntry (Typed.portsOf d))).Perm
      (m'.body.flatMap (contextEntry (Typed.portsOf d'))) := by
    apply body.flatMap
    intro a b hab
    rw [h.portsOf hn]
    cases hab <;> exact .refl _
  have perm : (Typed.context d m).Perm (Typed.context d' m') := by
    change (_ ++ m.body.flatMap (contextEntry (Typed.portsOf d))).Perm
      (_ ++ m'.body.flatMap (contextEntry (Typed.portsOf d')))
    rw [ports]
    exact entries.append_left _
  exact lookup_perm perm (context_keys_nodup d m hn hm) node

theorem findStmt {d : Design} (hn : Rules.Names d) {m m' : Module}
    (hm : m ∈ Typed.modules d) (body : Permuted StmtReorder m.body m'.body)
    {n : String} {s' : Stmt} (found : Rules.findStmt m' n = some s') :
    ∃ s, Rules.findStmt m n = some s ∧ StmtReorder s s' := by
  obtain ⟨s, member, related⟩ := body.right (List.mem_of_find?_eq_some found)
  have mi : Item.module m ∈ d.items := by
    obtain ⟨i, hi, eq⟩ := List.mem_filterMap.mp hm
    cases i <;> simp_all
  have unique := (hn.2 (.module m) mi).1
  change (m.ports.map Port.name ++ m.body.filterMap Rules.definition).Nodup at unique
  have definition : Rules.definition s = some n := by
    rw [related.definition]
    simpa [Rules.findStmt] using List.find?_some found
  exact ⟨s, Check.find_definition _ s n (List.nodup_append.mp unique).2.1 member definition,
    related⟩

end Reorder

theorem Permuted.symm {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Permuted r xs ys) : Permuted (fun b a => r a b) ys xs := by
  obtain ⟨pairs, hp, hq, hr⟩ := h
  refine ⟨pairs.map Prod.swap, ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using hq
  · simpa [List.map_map, Function.comp_def] using hp
  · intro pair member
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
    exact hr p hp

theorem Permuted.imp {r s : α → β → Prop} {xs : List α} {ys : List β}
    (h : Permuted r xs ys) (f : ∀ a b, r a b → s a b) : Permuted s xs ys := by
  obtain ⟨pairs, hp, hq, hr⟩ := h
  exact ⟨pairs, hp, hq, fun p member => f _ _ (hr p member)⟩

theorem StmtReorder.symm {s s' : Stmt} (h : StmtReorder s s') : StmtReorder s' s := by
  cases h with
  | same => exact .same _
  | inst _ _ _ _ _ perm => exact .inst _ _ _ _ _ perm.symm

theorem ItemReorder.symm {i i' : Item} (h : ItemReorder i i') : ItemReorder i' i := by
  cases h with
  | module m m' pos name ports body =>
    exact .module _ _ pos.symm name.symm ports.symm
      (body.symm.imp (fun _ _ h => h.symm))
  | extern e e' pos name ports deps =>
    exact .extern _ _ pos.symm name.symm ports.symm deps.symm

theorem Reorder.symm {d d' : Design} (h : Reorder d d') : Reorder d' d := by
  have names := h.items.map Item.name Item.name (fun _ _ related => related.name)
  have frozen (i : Item) : frozenConnections d.items i = frozenConnections d'.items i := by
    have any (child : String) : d.items.any (·.name == child) =
        d'.items.any (·.name == child) := by
      simpa only [List.any_map, Function.comp_def] using
        names.any_eq (f := fun name => name == child)
    cases i with
    | extern => rfl
    | module m =>
      unfold frozenConnections
      dsimp only
      congr 1
      funext stmt
      cases stmt <;> simp only [unresolvedStmt, any]
  refine ⟨h.1.symm, h.2.1.symm, ?_⟩
  apply h.2.2.symm.imp
  intro a b related
  exact ⟨related.1.symm, by simpa only [← frozen] using related.2.symm⟩

namespace Reorder

theorem instancePort {d d' : Design} (h : Reorder d d') (hn : Rules.Names d)
    {m m' : Module} (hm : m ∈ Typed.modules d) (hm' : m' ∈ Typed.modules d')
    (body : Permuted StmtReorder m.body m'.body) (inst port : String) :
    Rules.instancePort d m inst port = Rules.instancePort d' m' inst port := by
  have items (child : String) :
      (Rules.findItem d child).bind (fun i => (Typed.itemPorts i).find? (·.name == port)) =
      (Rules.findItem d' child).bind (fun i => (Typed.itemPorts i).find? (·.name == port)) := by
    cases found : Rules.findItem d' child with
    | none =>
      cases old : Rules.findItem d child with
      | none => rfl
      | some i =>
        obtain ⟨i', hi', _⟩ := h.symm.findItem (h.names hn) old
        rw [found] at hi'
        contradiction
    | some i' =>
      obtain ⟨i, hi, related⟩ := h.findItem hn found
      simp [hi, related.ports]
  cases found : Rules.findStmt m' inst with
  | none =>
    have absent : Rules.findStmt m inst = none := by
      cases old : Rules.findStmt m inst with
      | none => rfl
      | some s =>
        obtain ⟨s', hs', _⟩ := findStmt (h.names hn) hm'
          (body.symm.imp (fun _ _ h => h.symm)) old
        rw [found] at hs'
        contradiction
    simp [Rules.instancePort, found, absent]
  | some s' =>
    obtain ⟨s, hs, related⟩ := findStmt hn hm body found
    cases related with
    | same => cases s' <;> simp [Rules.instancePort, found, hs, items]
    | inst p n child xs ys perm => simp [Rules.instancePort, found, hs, items]

theorem resolved {d d' : Design} (h : Reorder d d') (hn : Rules.Names d)
    (hr : Rules.Resolved d) : Rules.Resolved d' := by
  refine ⟨?_, ?_⟩
  · cases found : Rules.findItem d d.top with
    | none =>
      have top := hr.1
      simp [found] at top
    | some i =>
      obtain ⟨i', hi', related⟩ := h.symm.findItem (h.names hn) found
      rw [h.1, hi']
      have top := hr.1
      cases related <;> simp_all
  · intro m' hm' s' hs'
    obtain ⟨m, hm, _, _, ports, body⟩ := h.module_right hm'
    obtain ⟨s, hs, related⟩ := body.right hs'
    have old := hr.2 m hm s hs
    have context := h.context_lookup hn hm ports body
    have instanceEq := h.instancePort hn hm hm' body
    have clock (n : String) : Rules.clockName m n = Rules.clockName m' n := by
      simp [Rules.clockName, Rules.findPort, ports]
    have memory (n : String) : Rules.memory d m n = Rules.memory d' m' n := by
      simp only [Rules.memory, context]
    refine ⟨?_, ?_⟩
    · cases related with
      | inst p n child xs ys perm =>
        obtain ⟨i, hi, rule⟩ := old.1
        obtain ⟨i', hi', related⟩ := h.symm.findItem (h.names hn) hi
        exact ⟨i', hi', fun x hx => related.ports ▸ rule x (perm.mem_iff.mpr hx)⟩
      | same =>
        cases s' with
        | let_ => trivial
        | reg | mem => simpa only [Rules.ResolvedTarget, clock] using old.1
        | write => simpa only [Rules.ResolvedTarget, memory] using old.1
        | assign => simpa only [Rules.ResolvedTarget, Rules.findPort, ports] using old.1
        | inst p n child xs =>
          obtain ⟨i, hi, rule⟩ := old.1
          obtain ⟨i', hi', related⟩ := h.symm.findItem (h.names hn) hi
          exact ⟨i', hi', fun x hx => related.ports ▸ rule x hx⟩
        | next p n e =>
          cases found : Rules.findStmt m' n with
          | none =>
            cases foundOld : Rules.findStmt m n with
            | none => simp [Rules.ResolvedTarget, foundOld] at old
            | some s =>
              obtain ⟨s', hs', _⟩ := findStmt (h.names hn) hm'
                (body.symm.imp (fun _ _ h => h.symm)) foundOld
              rw [found] at hs'
              contradiction
          | some s' =>
            obtain ⟨s, foundOld, related⟩ := findStmt hn hm body found
            cases related with
            | same s => simpa [Rules.ResolvedTarget, foundOld, found] using old.1
            | inst => simp [Rules.ResolvedTarget, foundOld] at old
    · intro e he node hnode
      have rule := old.2 e (related.exprs.mem_iff.mpr he) node hnode
      cases node <;> try trivial
      all_goals simpa only [Rules.ResolvedNode, Typed.valueTy, context,
        instanceEq, memory] using rule

end Reorder

namespace Reorder

private theorem valueExprs {d d' : Design} (h : Reorder d d') (hn : Rules.Names d)
    {m m' : Module} (ports : m'.ports = m.ports) {s s' : Stmt}
    (related : StmtReorder s s') :
    (Rules.valueExprs d m s).Perm (Rules.valueExprs d' m' s') := by
  have direct : Rules.directClock m = Rules.directClock m' := by
    funext e
    cases e <;> simp [Rules.directClock, Rules.clockName, Rules.findPort, ports]
  have anyPorts (design : Design) (child : String) (f : Port → Bool) :
      (Rules.findItem design child).any (fun i => (Typed.itemPorts i).any f) =
        (Typed.portsOf design child).any f := by
    cases found : Rules.findItem design child <;>
      unfold Rules.findItem at found <;> simp [Typed.portsOf, found]
  cases related with
  | same s =>
    cases s <;> simp only [Rules.valueExprs, anyPorts, h.portsOf hn, direct] <;> exact .refl _
  | inst p n child xs ys perm =>
    simp only [Rules.valueExprs, anyPorts, h.portsOf hn, direct]
    exact perm.filterMap _

theorem clocks {d d' : Design} (h : Reorder d d') (hn : Rules.Names d)
    (hc : Rules.Clocks d) : Rules.Clocks d' := by
  intro i' hi'
  obtain ⟨i, hi, related⟩ := h.items.right hi'
  have old := hc i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [← related.ports]
    exact old.1
  · rw [← related.ports]
    exact old.2.1
  · cases related with
    | extern => trivial
    | module m m' _ _ ports body =>
      have hm : m ∈ Typed.modules d := List.mem_filterMap.mpr ⟨_, hi, rfl⟩
      have hm' : m' ∈ Typed.modules d' := List.mem_filterMap.mpr ⟨_, hi', rfl⟩
      intro s' hs' e he node hnode
      obtain ⟨s, hs, related⟩ := body.right hs'
      have rule := old.2.2 s hs e ((h.valueExprs hn ports related).mem_iff.mpr he) node hnode
      have context := h.context_lookup hn hm ports body
      have instances := h.instancePort hn hm hm' body
      cases node <;> try trivial
      all_goals simpa only [Rules.ClockNode, Typed.valueTy, context, instances] using rule

end Reorder

private theorem list_map_preimage (f : α → β) (ys : List β)
    (existsPreimage : ∀ y ∈ ys, ∃ x, f x = y) : ∃ xs : List α, xs.map f = ys := by
  induction ys with
  | nil => exact ⟨[], rfl⟩
  | cons y ys ih =>
    obtain ⟨x, rfl⟩ := existsPreimage y (by simp)
    obtain ⟨xs, rfl⟩ := ih (fun y hy => existsPreimage y (by simp [hy]))
    exact ⟨x :: xs, rfl⟩

theorem StmtReorder.typed {s s' : Stmt} (related : StmtReorder s s')
    (t : Typed.Stmt ctx ports) (erase : t.erase = s) :
    ∃ t' : Typed.Stmt ctx ports, t'.erase = s' := by
  cases related with
  | same => exact ⟨t, erase⟩
  | inst p n child xs ys perm =>
    cases t <;> simp only [Typed.Stmt.erase] at erase <;> try contradiction
    rename_i inputs
    cases erase
    obtain ⟨inputs', he⟩ := list_map_preimage
      (fun x : (port : {p : Port // p ∈ ports child}) × Typed.Expr ctx port.val.ty =>
        (x.1.val.name, x.2.erase)) ys (fun y hy => by
          obtain ⟨x, _, hx⟩ := List.mem_map.mp (perm.mem_iff.mpr hy)
          exact ⟨x, hx⟩)
    exact ⟨.inst p n child inputs', congrArg (Stmt.inst p n child) he⟩

theorem Reorder.widths {d d' : Design} (h : Reorder d d') (hn : Rules.Names d)
    (hw : Rules.Widths d) : Rules.Widths d' := by
  intro m' hm' s' hs'
  obtain ⟨m, hm, _, _, ports, body⟩ := h.module_right hm'
  obtain ⟨s, hs, related⟩ := body.right hs'
  obtain ⟨t, erase⟩ := hw m hm s hs
  let transported := t.recontext (h.context_lookup hn hm ports body)
  have erased : transported.erase = s :=
    (t.recontext_erase (h.context_lookup hn hm ports body)).trans erase
  have result := related.typed transported erased
  rw [h.portsOf hn] at result
  exact result

private theorem connection_keys_nodup (d : Design) (m : Module)
    (hm : m ∈ Typed.modules d) (hr : Rules.Resolved d) (hc : Rules.Connections d)
    (p : Pos) (n child : String) (xs : List (String × Expr))
    (hs : Stmt.inst p n child xs ∈ m.body) : (xs.map Prod.fst).Nodup := by
  obtain ⟨item, hi, resolved⟩ := (hr.2 m hm _ hs).1
  apply List.nodup_iff_count_of_mem.mpr
  intro key member
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp member
  obtain ⟨port, hp, matchPort⟩ := List.any_eq_true.mp (resolved x hx)
  simp only [Bool.and_eq_true, beq_iff_eq] at matchPort
  have count := (hc m hm _ hs item hi port hp matchPort.2).1
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  simpa only [Function.comp_def, matchPort.1] using count

private theorem module_graph_perm (d : Design) (m m' : Module)
    (hm : m ∈ Typed.modules d) (hr : Rules.Resolved d) (hc : Rules.Connections d)
    (ports : m'.ports = m.ports) (body : Permuted StmtReorder m.body m'.body)
    (children : String → Option Deps) : (Deps.graph m children).Perm (Deps.graph m' children) := by
  apply Deps.graph_perm _ _ _ _ ports.symm
  obtain ⟨pairs, hp, hq, related⟩ := body
  apply (hp.flatMap_right (Deps.equations children)).symm.trans
  apply List.Perm.trans _ (hq.flatMap_right (Deps.equations children))
  simp only [List.flatMap_map]
  have same (pair : Stmt × Stmt) (member : pair ∈ pairs) :
      Deps.equations children pair.1 = Deps.equations children pair.2 := by
    rcases pair with ⟨a, b⟩
    have rel := related (a, b) member
    have hs : a ∈ m.body := hp.mem_iff.mp (List.mem_map.mpr ⟨(a, b), member, rfl⟩)
    cases rel with
    | same => rfl
    | inst p n child xs ys perm =>
      have lookup := lookup_perm perm (connection_keys_nodup d m hm hr hc p n child xs hs)
      simp only [Deps.equations, lookup]
  apply List.Perm.of_eq
  change (pairs.map _).flatten = (pairs.map _).flatten
  congr 1
  exact List.map_congr_left same

private theorem find_perm (key : α → String) {xs ys : List α} (perm : xs.Perm ys)
    (unique : (xs.map key).Nodup) (name : String) :
    xs.find? (fun x => key x == name) = ys.find? (fun x => key x == name) := by
  cases found : ys.find? (fun x => key x == name) with
  | none =>
    apply List.find?_eq_none.mpr
    intro x hx
    exact List.find?_eq_none.mp found x (perm.mem_iff.mp hx)
  | some y =>
    have member := perm.mem_iff.mpr (List.mem_of_find?_eq_some found)
    have named : key y = name := by simpa using List.find?_some found
    simpa only [named] using find_named key unique member

private theorem extern_deps_reorder (e e' : Extern) (ports : e'.ports = e.ports)
    (deps : e.deps.Perm e'.deps)
    (valid : (∀ p ∈ e.ports, p.dir = .output →
      (e.deps.filter (·.output == p.name)).length = 1) ∧
      ∀ dep ∈ e.deps,
        (e.ports.any fun p => p.dir == .output && p.name == dep.output) = true ∧
        dep.inputs.Nodup ∧ ∀ n ∈ dep.inputs,
          (e.ports.any fun p => p.name == n && p.dir == .input && p.ty != .clock) = true) :
    Typed.externDeps e = Typed.externDeps e' := by
  have unique : (e.deps.map Dep.output).Nodup := by
    apply List.nodup_iff_count_of_mem.mpr
    intro name member
    obtain ⟨dep, hd, rfl⟩ := List.mem_map.mp member
    obtain ⟨port, hp, matchPort⟩ := List.any_eq_true.mp (valid.2 dep hd).1
    simp only [Bool.and_eq_true, beq_iff_eq] at matchPort
    have count := valid.1 port hp matchPort.1
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    simpa only [Function.comp_def, matchPort.2] using count
  simp only [Typed.externDeps, ports, find_perm Dep.output deps unique]
  rfl

theorem Reorder.designDeps {d d' : Design} (h : Reorder d d')
    (hn : Rules.Names d) (hr : Rules.Resolved d) (ho : Rules.Outputs d)
    (hc : Rules.Connections d) (hd : Rules.Dependencies d) (fuel : Nat) :
    Typed.designDeps d fuel = Typed.designDeps d' fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have tables : (Typed.dependencyTable d (fuel + 1)).Perm
        (Typed.dependencyTable d' (fuel + 1)) := by
      unfold Typed.dependencyTable
      obtain ⟨pairs, hp, hq, related⟩ := h.items
      apply (hp.map _).symm.trans
      apply List.Perm.trans _ (hq.map _)
      simp only [List.map_map]
      apply List.Perm.of_eq
      apply List.map_congr_left
      intro pair member
      rcases pair with ⟨a, b⟩
      have rel := related (a, b) member
      have hi : a ∈ d.items := hp.mem_iff.mp (List.mem_map.mpr ⟨(a, b), member, rfl⟩)
      cases rel with
      | module m m' _ name ports body =>
        simp only [Function.comp_apply, Typed.itemName, name]
        congr 1
        change Deps.infer m (Typed.designDeps d fuel) =
          Deps.infer m' (Typed.designDeps d' fuel)
        rw [← ih]
        have hm : m ∈ Typed.modules d := List.mem_filterMap.mpr ⟨_, hi, rfl⟩
        have perm := module_graph_perm d m m' hm hr hc ports body (Typed.designDeps d fuel)
        exact Deps.infer_graph_congr m m' _ _ ports.symm perm.length_eq
          (lookup_perm perm (Check.combinational_graph_keys_nodup d m hn hr ho hm fuel))
      | extern e e' _ name ports deps =>
        simp only [Function.comp_apply, Typed.itemName, name]
        congr 1
        exact extern_deps_reorder e e' ports deps (hd _ hi)
    funext name
    apply lookup_perm tables _ name
    simpa only [Typed.dependencyTable, List.map_map, Function.comp_def] using hn.1.1

theorem Reorder.combinational {d d' : Design} (h : Reorder d d')
    (hn : Rules.Names d) (hr : Rules.Resolved d) (ho : Rules.Outputs d)
    (hc : Rules.Connections d) (hd : Rules.Dependencies d)
    (hg : Rules.Combinational d) : Rules.Combinational d' := by
  intro m' hm'
  obtain ⟨m, hm, _, _, ports, body⟩ := h.module_right hm'
  obtain ⟨ranks, ranked⟩ := hg m hm
  have size : d.items.length = d'.items.length := by
    have p := h.items.map (fun _ => ()) (fun _ => ()) (fun _ _ _ => rfl)
    simpa using p.length_eq
  have children := h.designDeps hn hr ho hc hd (d.items.length + 1)
  rw [size] at children
  have graph := module_graph_perm d m m' hm hr hc ports body
    (Typed.designDeps d (d'.items.length + 1))
  refine ⟨ranks, ?_⟩
  intro row member dep read
  rw [← children] at member
  have old := graph.mem_iff.mpr member
  rw [← size] at old
  exact ranked row old dep read

theorem wellFormed_reorder {d d' : Design} (h : Reorder d d')
    (wf : WellFormed d) : WellFormed d' := by
  obtain ⟨hn, hr, hw, hnum, hreg, hout, hcomb, hclock, hh, hc, hwrite, hd⟩ := wf
  exact ⟨h.names hn, h.resolved hn hr, h.widths hn hw, h.numbers hnum,
    h.registers hreg, h.outputs hout, h.combinational hn hr hout hc hd hcomb,
    h.clocks hn hclock, h.hierarchy hh, h.connections hn hc, h.writes hwrite,
    h.dependencies hd⟩

theorem canonicalize_check (d : Design) (t : Typed.Design) (h : check d = .ok t) :
    ∃ t', check (canonicalize d) = .ok t' :=
  check_complete _ (wellFormed_reorder (canonicalize_reorder d) (check_sound d t h).1)

end Silicon.Core
