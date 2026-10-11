-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Interp
import Silicon.Core.Canonical.View

/-! Unique write ports fix the update order after any source permutation. -/
namespace Silicon.Core.Semantics

private theorem same_key_eq (key : α → Nat) (xs : List α)
    (unique : (xs.map key).Nodup) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (same : key a = key b) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp ha with rfl | haTail
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · rfl
      · exact False.elim (unique.1 (same ▸ List.mem_map.mpr ⟨b, hbTail, rfl⟩))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact False.elim (unique.1 (same ▸ List.mem_map.mpr ⟨a, haTail, rfl⟩))
      · exact ih unique.2 haTail hbTail

private theorem sort_key_perm (key : α → Nat) (xs ys : List α) (perm : xs.Perm ys)
    (unique : (xs.map key).Nodup) :
    xs.mergeSort (fun a b => decide (key a ≤ key b)) =
      ys.mergeSort (fun a b => decide (key a ≤ key b)) := by
  have sorted (zs : List α) := List.pairwise_mergeSort
    (le := fun a b : α => decide (key a ≤ key b))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) zs
  have left := List.mergeSort_perm xs (fun a b => decide (key a ≤ key b))
  have right := List.mergeSort_perm ys (fun a b => decide (key a ≤ key b))
  apply List.Perm.eq_of_pairwise (le := fun a b => key a ≤ key b)
    (fun a b ha hb ab ba => same_key_eq key xs unique a b
      (left.mem_iff.mp ha) (perm.mem_iff.mpr (right.mem_iff.mp hb)) (Nat.le_antisymm ab ba))
    (by simpa using sorted xs) (by simpa using sorted ys)
  exact left.trans (perm.trans right.symm)

abbrev WriteValues (width : Nat) := Nat × Nat × Value width × Value 1

def evalWrite (values : Valuation ctx) (memories : Memories ctx)
    (write : Typed.Write ctx width depth) : WriteValues width :=
  (write.port, (evalExpr values memories write.addr).toNat,
    evalExpr values memories write.data, evalExpr values memories write.enable)

private theorem nextMemory_evaluated (values : Valuation ctx) (memories : Memories ctx)
    (memory : Fin depth → Value width) (writes : List (Typed.Write ctx width depth)) :
    nextMemory values memories memory writes =
      ((writes.map (evalWrite values memories)).mergeSort (fun a b => a.1 ≤ b.1)).foldl
        (fun current write => memoryWrite current write.2.1 write.2.2.1 write.2.2.2) memory := by
  have commute := List.map_mergeSort
    (r := fun a b : Typed.Write ctx width depth => decide (a.port ≤ b.port))
    (s := fun a b : WriteValues width => decide (a.1 ≤ b.1))
    (f := evalWrite values memories) (l := writes) (by intros; rfl)
  rw [← commute, List.foldl_map]
  rfl

theorem nextMemory_eq_of_evaluated {ctx ctx' : Typed.Ctx}
    (values : Valuation ctx) (values' : Valuation ctx')
    (memories : Memories ctx) (memories' : Memories ctx')
    (memory : Fin depth → Value width) (writes : List (Typed.Write ctx width depth))
    (writes' : List (Typed.Write ctx' width depth))
    (unique : (writes.map Typed.Write.port).Nodup)
    (same : (writes.map (evalWrite values memories)).Perm
      (writes'.map (evalWrite values' memories'))) :
    nextMemory values memories memory writes = nextMemory values' memories' memory writes' := by
  rw [nextMemory_evaluated, nextMemory_evaluated]
  rw [sort_key_perm Prod.fst _ _ same]
  simpa only [List.map_map, Function.comp_def, evalWrite] using unique

theorem typed_write_ports_nodup (d : CertifiedDesign) (m : Typed.Module)
    (hm : m ∈ d.design.bodies) (i : Nat) (p : Pos) (name : String) (width depth : Nat)
    (clock : String) (target : m.ctx.lookup (.name name) = some (.memory width depth))
    (writes : List (Typed.Write m.ctx width depth))
    (member : .mem i p name width depth clock target writes ∈ m.body) :
    (writes.map Typed.Write.port).Nodup := by
  let select (part : Nat × Typed.Stmt m.ctx m.interfaces) : Option Nat :=
    match part.2.erase with
    | .write _ n port _ _ _ => if n == name then some port else none
    | _ => none
  have rawMember : Core.Stmt.mem p name width depth clock ∈ m.erase.body := by
    apply (Ownership.mem_equationsErase m.body _).mpr
    exact ⟨.mem i p name width depth clock target writes, member, i,
      .mem p name width depth clock, by simp [Typed.Equation.parts], rfl⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rule, _⟩ := d.wellFormed
  have unique := (rule m.erase (module_mem d.design m hm) _ rawMember).1
  have sorted : (((m.body.flatMap Typed.Equation.parts).mergeSort
      (fun a b => decide (a.1 ≤ b.1))).filterMap select).Nodup := by
    simp only [Rules.writes, Typed.Module.erase, Typed.equationsErase,
      List.map_filterMap, List.filterMap_map, Function.comp_def] at unique
    suffices eq : (fun part : Nat × Typed.Stmt m.ctx m.interfaces =>
        (match part.2.erase with
        | .write p n port _ _ _ => if n == name then some (port, p) else none
        | _ => none).map Prod.fst) = select by
      exact (congrArg (fun f =>
        (((m.body.flatMap Typed.Equation.parts).mergeSort
          (fun a b => decide (a.1 ≤ b.1))).filterMap f).Nodup) eq).mp unique
    funext part
    rcases part with ⟨index, stmt⟩
    cases stmt <;> simp [select, Typed.Stmt.erase]
  have flat := ((List.mergeSort_perm (m.body.flatMap Typed.Equation.parts)
    (fun a b => decide (a.1 ≤ b.1))).filterMap select).nodup_iff.mp sorted
  have sub : (Typed.Equation.mem i p name width depth clock target writes).parts.Sublist
      (m.body.flatMap Typed.Equation.parts) :=
    List.sublist_flatten_of_mem (List.mem_map.mpr
      ⟨.mem i p name width depth clock target writes, member, rfl⟩)
  have own := flat.sublist (sub.filterMap select)
  simpa [Typed.Equation.parts, select, Typed.Stmt.erase, List.filterMap_map,
    Function.comp_def] using own

end Silicon.Core.Semantics

/-! Register updates use the same erased reset and next equations at each name. -/
namespace Silicon.Core.Semantics

theorem nextRegister_erase_eq {ctx ctx' : Typed.Ctx}
    (lookup : ∀ n, ctx.lookup n = ctx'.lookup n) (values : NamedValues)
    (memories : NamedMemories) (reset : Option (Typed.Reset ctx width))
    (reset' : Option (Typed.Reset ctx' width)) (next : Typed.Expr ctx (.bits width))
    (next' : Typed.Expr ctx' (.bits width))
    (resetEq : reset.map Typed.Reset.erase = reset'.map Typed.Reset.erase)
    (nextEq : next.erase = next'.erase) :
    nextRegister (values.valuation ctx) (memories.typed ctx) reset next =
      nextRegister (values.valuation ctx') (memories.typed ctx') reset' next' := by
  have nextValue := evalExpr_erase_eq lookup values memories next next' nextEq
  cases reset with
  | none =>
    cases reset' with
    | none => exact nextValue
    | some => cases resetEq
  | some reset =>
    cases reset' with
    | none => cases resetEq
    | some reset' =>
      have same := Option.some.inj resetEq
      have signal := congrArg Core.Reset.signal same
      have value := congrArg Core.Reset.value same
      have signalEq := evalExpr_erase_eq lookup values memories reset.signal reset'.signal signal
      have valueEq := evalExpr_erase_eq lookup values memories reset.value reset'.value value
      simp only [nextRegister, signalEq, valueEq, nextValue]

/-! A write ignores source indices and retains its explicit priority port. -/
def writeSyntax (name : String) (write : Typed.Write ctx width depth) : Core.Stmt :=
  .write write.pos name write.port write.addr.erase write.data.erase write.enable.erase

theorem evalWrite_erase_eq {ctx ctx' : Typed.Ctx}
    (lookup : ∀ n, ctx.lookup n = ctx'.lookup n) (values : NamedValues)
    (memories : NamedMemories) (name : String) (a : Typed.Write ctx width depth)
    (b : Typed.Write ctx' width depth) (same : writeSyntax name a = writeSyntax name b) :
    evalWrite (values.valuation ctx) (memories.typed ctx) a =
      evalWrite (values.valuation ctx') (memories.typed ctx') b := by
  have fields := Core.Stmt.write.inj same
  have addr := evalExpr_erase_eq lookup values memories a.addr b.addr fields.2.2.2.1
  have data := evalExpr_erase_eq lookup values memories a.data b.data fields.2.2.2.2.1
  have enable := evalExpr_erase_eq lookup values memories a.enable b.enable fields.2.2.2.2.2
  simp only [evalWrite, fields.2.2.1, addr, data, enable]

end Silicon.Core.Semantics

/-! Local named solutions share inputs, state cells, and child outputs. -/
namespace Silicon.Core.Semantics

theorem stateMemories_named_eq (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (state : State d env m hm) (state' : State d' env' m' hm')
    (lookup : ∀ node, m.ctx.lookup node = m'.ctx.lookup node)
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state') :
    (stateMemories m (designChildren d env m hm) state).named =
      (stateMemories m' (designChildren d' env' m' hm') state').named := by
  funext name address
  cases found : m.ctx.lookup (.name name) with
  | none => simp [Memories.named, found, ← lookup]
  | some kind =>
    cases kind with
    | value | clock => simp [Memories.named, found, ← lookup]
    | memory width depth =>
      have found' := (lookup (.name name)).symm.trans found
      have equal := stateMemories_eq_of_named d d' env env' noExterns noExterns' m m' hm hm'
        state state' (fun path => congrFun same path) name width depth found found'
      by_cases bound : address < depth
      · rw [Memories.named_at _ name width depth found ⟨address, bound⟩,
          Memories.named_at _ name width depth found' ⟨address, bound⟩]
        exact congrArg (fun memory => (memory ⟨address, bound⟩).toNat) equal
      · have absent (ctx : Typed.Ctx) (mem : Memories ctx)
            (hf : ctx.lookup (.name name) = some (.memory width depth)) :
            mem.named name address = 0 := by
          unfold Memories.named
          split
          · rename_i w size hs
            have eq : width = w ∧ depth = size := by simpa [hf] using hs
            rcases eq with ⟨rfl, rfl⟩
            simp [bound]
          · rfl
        rw [absent _ _ found, absent _ _ found']

/-! Compare child outputs at the same port with the parent's candidate values. -/
def InstanceOutputsAgree (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (m m' : Typed.Module) (hm : m ∈ d.design.bodies)
    (hm' : m' ∈ d'.design.bodies) (state : State d env m hm) (state' : State d' env' m' hm')
    (values : NamedValues) : Prop :=
  ∀ i p name child (inputs : List (Connection m.ctx (m.interfaces child)))
    (member : .inst i p name child inputs ∈ m.body)
    i' (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (member' : .inst i' p name child inputs' ∈ m'.body),
    (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)) →
    ∀ port (hp : port ∈ m.interfaces child) (hp' : port ∈ m'.interfaces child)
      (dir : port.dir = .output),
    let e : EquationRef m := ⟨.inst i p name child inputs, member⟩
    let e' : EquationRef m' := ⟨.inst i' p name child inputs', member'⟩
    (designChildren d env m hm e).out (state e)
      (connectionValues d m hm (values.valuation m.ctx)
        (stateMemories m (designChildren d env m hm) state) e) ⟨port, hp, dir⟩ =
    (designChildren d' env' m' hm' e').out (state' e')
      (connectionValues d' m' hm' (values.valuation m'.ctx)
        (stateMemories m' (designChildren d' env' m' hm') state') e') ⟨port, hp', dir⟩

theorem named_solution_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (input : Input m) (input' : Input m')
    (inputEq : ∀ port hp hp' dir, input ⟨port, hp, dir⟩ = input' ⟨port, hp', dir⟩)
    (values : NamedValues) (solved : IsNamedSolution d env m hm state input values)
    (children : InstanceOutputsAgree d d' env env' m m' hm hm' state state' values) :
    IsNamedSolution d' env' m' hm' state' input' values := by
  have lookup := order.typed_context m m' hm hm' related
  have interfaces := order.typed_interfaces m m' hm hm'
  have memories := stateMemories_named_eq d d' env env' noExterns noExterns' m m' hm hm'
    state state' lookup same
  cases related with
  | module _ _ _ _ ports body =>
    have portEq : m'.ports = m.ports := ports
    refine ⟨?_, ?_⟩
    · intro node
      rw [← lookup]
      exact solved.1 node
    · intro node width found driver
      cases driver with
      | input port hp dir bits =>
        have hpLeft : port ∈ m.ports := portEq ▸ hp
        have eq := named_solution_input d env m hm state input values solved port hpLeft dir bits
        change BitVec.ofNat width (values (.name port.name)) = _
        rw [eq, inputEq port hpLeft hp dir]
        simp [ValueDriver.eval]
      | let_ i p name width expr member =>
        have raw : Core.Stmt.let_ p name width expr.erase ∈ m'.erase.body :=
          (Ownership.mem_equationsErase m'.body _).mpr
            ⟨_, member, i, .let_ p name width expr, by simp [Typed.Equation.parts], rfl⟩
        obtain ⟨s, hs, rel⟩ := body.right raw
        cases rel
        have eq := named_solution_let d env m hm state input values solved p name width
          expr.erase hs ((lookup (.name name)).trans found)
        rw [evalNamedExpr_lookup_congr lookup, memories, evalNamedExpr_typed,
          Memories.named_typed] at eq
        have eq := congrArg (BitVec.ofNat width) (Option.some.inj eq)
        simpa [ValueDriver.eval, NamedValues.valuation] using eq.symm
      | assign i p name width target expr member =>
        have raw : Core.Stmt.assign p name expr.erase ∈ m'.erase.body :=
          (Ownership.mem_equationsErase m'.body _).mpr
            ⟨_, member, i, .assign p name width target expr,
              by simp [Typed.Equation.parts], rfl⟩
        obtain ⟨s, hs, rel⟩ := body.right raw
        cases rel
        have eq := named_solution_assign d env m hm state input values solved p name width
          expr.erase hs ((lookup (.name name)).trans found)
        rw [evalNamedExpr_lookup_congr lookup, memories, evalNamedExpr_typed,
          Memories.named_typed] at eq
        have eq := congrArg (BitVec.ofNat width) (Option.some.inj eq)
        simpa [ValueDriver.eval, NamedValues.valuation] using eq.symm
      | reg i p name width clock target reset ni np next member =>
        have raw : Core.Stmt.reg p name width clock (reset.map Typed.Reset.erase) ∈
            m'.erase.body := (Ownership.mem_equationsErase m'.body _).mpr
          ⟨_, member, i, .reg p name width clock reset, by simp [Typed.Equation.parts], rfl⟩
        obtain ⟨s, hs, rel⟩ := body.right raw
        cases rel
        have eq := named_solution_register d env noExterns m hm state input values solved
          p name width clock _ hs ((lookup (.name name)).trans found)
        rw [same, namedState_register d' env' noExterns' m' hm' state' i p name width clock
          target reset ni np next member] at eq
        exact (eq_of_heq (NamedCell.register.inj (Option.some.inj eq)).2).symm
      | inst i p name child inputs member port hp dir bits =>
        have raw := instance_member m' i p name child inputs member
        obtain ⟨s, hs, rel⟩ := body.right raw
        have matching : ∃ rawInputs, Core.Stmt.inst p name child rawInputs ∈ m.erase.body ∧
            rawInputs.Perm (inputs.map fun x => (x.1.val.name, x.2.erase)) := by
          cases rel with
          | same => exact ⟨_, hs, .refl _⟩
          | inst => exact ⟨_, hs, by assumption⟩
        obtain ⟨rawInputs, hs, perm⟩ := matching
        obtain ⟨j, ins, memberLeft, erased⟩ := Ownership.inst_equation m.body _ _ _ _ hs
        have hpLeft : port ∈ m.interfaces child := interfaces ▸ hp
        have eq := solved.2 (.port name port.name) width ((lookup _).trans found)
          (.inst j p name child ins memberLeft port hpLeft dir bits)
        have childEq := children j p name child ins memberLeft i inputs member
          (erased ▸ perm) port hpLeft hp dir
        exact eq.trans (congrArg (cast (congrArg TyValue bits)) childEq)

end Silicon.Core.Semantics

/-! A checked register has one next equation, independent of statement order. -/
namespace Silicon.Core.Semantics

private theorem unique_filterMap (f : α → Option β) (xs : List α)
    (one : (xs.filterMap f).length = 1) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (va vb : β) (fa : f a = some va) (fb : f b = some vb) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    cases fx : f x with
    | none =>
      have neA : a ≠ x := by intro eq; subst a; rw [fx] at fa; contradiction
      have neB : b ≠ x := by intro eq; subst b; rw [fx] at fb; contradiction
      exact ih (by simpa [fx] using one) (List.mem_of_ne_of_mem neA ha)
        (List.mem_of_ne_of_mem neB hb)
    | some value =>
      have empty : xs.filterMap f = [] := by simpa [fx] using one
      have absent (v : α) (result : β) (hv : f v = some result) : v ∉ xs := by
        intro member
        have hm : result ∈ xs.filterMap f := List.mem_filterMap.mpr ⟨v, member, hv⟩
        simp [empty] at hm
      have ea : a = x := (List.mem_cons.mp ha).resolve_right (absent a va fa)
      have eb : b = x := (List.mem_cons.mp hb).resolve_right (absent b vb fb)
      exact ea.trans eb.symm

theorem next_erase_reorder (d : CertifiedDesign)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies)
    (body : Permuted (StmtReorder d.design.erase.items) m.erase.body m'.erase.body)
    (i i' : Nat) (p p' : Pos) (name : String) (width : Nat) (clock clock' : String)
    (target : Typed.valueTy m.ctx name = some (.bits width))
    (target' : Typed.valueTy m'.ctx name = some (.bits width))
    (reset : Option (Typed.Reset m.ctx width)) (reset' : Option (Typed.Reset m'.ctx width))
    (ni ni' : Nat) (np np' : Pos) (next : Typed.Expr m.ctx (.bits width))
    (next' : Typed.Expr m'.ctx (.bits width))
    (member : .reg i p name width clock target reset ni np next ∈ m.body)
    (member' : .reg i' p' name width clock' target' reset' ni' np' next' ∈ m'.body) :
    next.erase = next'.erase := by
  have reg : Core.Stmt.reg p name width clock (reset.map Typed.Reset.erase) ∈ m.erase.body :=
    (Ownership.mem_equationsErase m.body _).mpr
      ⟨_, member, i, .reg p name width clock reset, by simp [Typed.Equation.parts], rfl⟩
  have hn : Core.Stmt.next np name next.erase ∈ m.erase.body :=
    (Ownership.mem_equationsErase m.body _).mpr
      ⟨_, member, ni, .next np name width target next, by simp [Typed.Equation.parts], rfl⟩
  have hn' : Core.Stmt.next np' name next'.erase ∈ m'.erase.body :=
    (Ownership.mem_equationsErase m'.body _).mpr
      ⟨_, member', ni', .next np' name width target' next', by simp [Typed.Equation.parts], rfl⟩
  obtain ⟨s, hs, rel⟩ := body.right hn'
  cases rel
  obtain ⟨_, _, _, _, registers, _⟩ := d.wellFormed
  have one := registers m.erase (module_mem d.design m hm) _ reg
  have eq := unique_filterMap
    (fun s : Core.Stmt => match s with
      | Core.Stmt.next p n _ => if n == name then some p else none
      | _ => none) m.erase.body one _ _ hn hs np np' (by simp) (by simp)
  exact (Core.Stmt.next.inj eq).2.2

end Silicon.Core.Semantics

/-! Memory write syntax follows its owner and its explicit priority port. -/
namespace Silicon.Core.Semantics

theorem write_member_iff (d : CertifiedDesign) (m : Typed.Module) (hm : m ∈ d.design.bodies)
    (i : Nat) (p : Pos) (name : String) (width depth : Nat) (clock : String)
    (target : m.ctx.lookup (.name name) = some (.memory width depth))
    (writes : List (Typed.Write m.ctx width depth))
    (member : .mem i p name width depth clock target writes ∈ m.body)
    (pos : Pos) (port : Nat) (addr data enable : Core.Expr) :
    Core.Stmt.write pos name port addr data enable ∈ m.erase.body ↔
      ∃ write ∈ writes, writeSyntax name write = .write pos name port addr data enable := by
  constructor
  · intro raw
    obtain ⟨equation, he, index, stmt, part, erased⟩ :=
      (Ownership.mem_equationsErase m.body _).mp raw
    cases equation <;> simp only [Typed.Equation.parts, List.mem_cons, List.not_mem_nil,
      or_false] at part
    case reg i p n w clock target reset ni np next =>
      rcases part with part | part <;> cases part <;> cases erased
    case mem j q n w size clock' target' writes' =>
      rcases part with part | part
      · cases part; cases erased
      · obtain ⟨write, hw, part⟩ := List.mem_map.mp part
        cases part
        have fields := Core.Stmt.write.inj erased
        have names : n = name := fields.2.1
        subst n
        have eq := equation_unique d.design d.wellFormed m hm _ _ he member rfl
        cases eq
        exact ⟨write, hw, erased⟩
    all_goals cases part; cases erased
  · rintro ⟨write, hw, erased⟩
    exact (Ownership.mem_equationsErase m.body _).mpr
      ⟨_, member, write.index,
        .write write.pos name write.port width depth target write.addr write.data write.enable,
        by exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨write, hw, rfl⟩), erased⟩

private theorem syntax_nodup (name : String) (writes : List (Typed.Write ctx width depth))
    (unique : (writes.map Typed.Write.port).Nodup) :
    (writes.map (writeSyntax name)).Nodup := by
  simp only [List.Nodup, List.pairwise_map] at unique ⊢
  apply unique.imp
  intro a b ne eq
  exact ne (Core.Stmt.write.inj eq).2.2.1

theorem writeSyntax_perm (d d' : CertifiedDesign) (m m' : Typed.Module)
    (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (body : Permuted (StmtReorder d.design.erase.items) m.erase.body m'.erase.body)
    (i i' : Nat) (p p' : Pos) (name : String) (width depth : Nat) (clock clock' : String)
    (target : m.ctx.lookup (.name name) = some (.memory width depth))
    (target' : m'.ctx.lookup (.name name) = some (.memory width depth))
    (writes : List (Typed.Write m.ctx width depth))
    (writes' : List (Typed.Write m'.ctx width depth))
    (member : .mem i p name width depth clock target writes ∈ m.body)
    (member' : .mem i' p' name width depth clock' target' writes' ∈ m'.body) :
    (writes.map (writeSyntax name)).Perm (writes'.map (writeSyntax name)) := by
  apply (List.perm_ext_iff_of_nodup
    (syntax_nodup name writes (typed_write_ports_nodup d m hm i p name width depth clock
      target writes member))
    (syntax_nodup name writes' (typed_write_ports_nodup d' m' hm' i' p' name width depth clock'
      target' writes' member'))).mpr
  intro stmt
  constructor
  · intro hs
    obtain ⟨write, hw, rfl⟩ := List.mem_map.mp hs
    have raw := (write_member_iff d m hm i p name width depth clock target writes member
      write.pos write.port write.addr.erase write.data.erase write.enable.erase).mpr
        ⟨write, hw, rfl⟩
    obtain ⟨s, hs, rel⟩ := body.left raw
    cases rel
    obtain ⟨write', hw', eq⟩ := (write_member_iff d' m' hm' i' p' name width depth clock'
      target' writes' member' _ _ _ _ _).mp hs
    exact List.mem_map.mpr ⟨write', hw', eq⟩
  · intro hs
    obtain ⟨write, hw, rfl⟩ := List.mem_map.mp hs
    have raw := (write_member_iff d' m' hm' i' p' name width depth clock' target' writes' member'
      write.pos write.port write.addr.erase write.data.erase write.enable.erase).mpr
        ⟨write, hw, rfl⟩
    obtain ⟨s, hs, rel⟩ := body.right raw
    cases rel
    obtain ⟨write', hw', eq⟩ := (write_member_iff d m hm i p name width depth clock
      target writes member _ _ _ _ _).mp hs
    exact List.mem_map.mpr ⟨write', hw', eq⟩

private def evalWriteSyntax (ctx : Typed.Ctx) (values : NamedValues) (memories : NamedMemories)
    (width depth : Nat) : Core.Stmt → WriteValues width
  | .write _ _ port addr data enable =>
    (port, (evalNamedExpr ctx values memories addr (Typed.addressWidth depth)).getD 0,
      BitVec.ofNat width ((evalNamedExpr ctx values memories data width).getD 0),
      BitVec.ofNat 1 ((evalNamedExpr ctx values memories enable 1).getD 0))
  | _ => (0, 0, 0, 0)

private theorem evalWriteSyntax_typed (values : NamedValues) (memories : NamedMemories)
    (name : String) (write : Typed.Write ctx width depth) :
    evalWriteSyntax ctx values memories width depth (writeSyntax name write) =
      evalWrite (values.valuation ctx) (memories.typed ctx) write := by
  simp [evalWriteSyntax, writeSyntax, evalNamedExpr_typed, evalWrite]

theorem evalWrites_perm {ctx ctx' : Typed.Ctx}
    (lookup : ∀ node, ctx.lookup node = ctx'.lookup node)
    (values : NamedValues) (memories : NamedMemories) (name : String)
    (writes : List (Typed.Write ctx width depth)) (writes' : List (Typed.Write ctx' width depth))
    (perm : (writes.map (writeSyntax name)).Perm (writes'.map (writeSyntax name))) :
    (writes.map (evalWrite (values.valuation ctx) (memories.typed ctx))).Perm
      (writes'.map (evalWrite (values.valuation ctx') (memories.typed ctx'))) := by
  have mapped := perm.map (evalWriteSyntax ctx values memories width depth)
  have congr : evalWriteSyntax ctx values memories width depth =
      evalWriteSyntax ctx' values memories width depth := by
    funext stmt
    cases stmt <;> simp only [evalWriteSyntax]
    simp only [evalNamedExpr_lookup_congr lookup]
  simp only [List.map_map, Function.comp_def] at mapped
  have left : (writes.map fun write =>
      evalWriteSyntax ctx values memories width depth (writeSyntax name write)) =
      writes.map (evalWrite (values.valuation ctx) (memories.typed ctx)) :=
    List.map_congr_left fun write _ => evalWriteSyntax_typed values memories name write
  have right : (writes'.map fun write =>
      evalWriteSyntax ctx values memories width depth (writeSyntax name write)) =
      writes'.map (evalWrite (values.valuation ctx') (memories.typed ctx')) := by
    apply List.map_congr_left
    intro write _
    rw [congr, evalWriteSyntax_typed]
  rw [left, right] at mapped
  exact mapped

end Silicon.Core.Semantics

/-! Named candidate values update each state cell through its erased equations. -/
namespace Silicon.Core.Semantics

def nextFromValues (d : CertifiedDesign) (env : Env d.design)
    (m : Typed.Module) (hm : m ∈ d.design.bodies) (state : State d env m hm)
    (values : NamedValues) : State d env m hm :=
  let memories := stateMemories m (designChildren d env m hm) state
  nextLocalState m (designChildren d env m hm) state (values.valuation m.ctx) memories
    (connectionValues d m hm (values.valuation m.ctx) memories)

def InstanceNextAgree (d d' : CertifiedDesign) (env : Env d.design) (env' : Env d'.design)
    (noExterns : d.design.externs = []) (noExterns' : d'.design.externs = [])
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (state : State d env m hm) (state' : State d' env' m' hm') (values : NamedValues) : Prop :=
  ∀ i p name child (inputs : List (Connection m.ctx (m.interfaces child)))
    (_member : .inst i p name child inputs ∈ m.body)
    i' (inputs' : List (Connection m'.ctx (m'.interfaces child)))
    (_member' : .inst i' p name child inputs' ∈ m'.body),
    (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm
      (inputs'.map fun x => (x.1.val.name, x.2.erase)) →
    ∀ path, namedState d env noExterns m hm (nextFromValues d env m hm state values)
      (name :: path) = namedState d' env' noExterns' m' hm'
        (nextFromValues d' env' m' hm' state' values) (name :: path)

private theorem next_some_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (values : NamedValues)
    (children : InstanceNextAgree d d' env env' noExterns noExterns' m m' hm hm'
      state state' values)
    (path : List String) (cell : NamedCell)
    (value : namedState d env noExterns m hm (nextFromValues d env m hm state values) path =
      some cell) :
    namedState d' env' noExterns' m' hm' (nextFromValues d' env' m' hm' state' values) path =
      some cell := by
  have lookup := order.typed_context m m' hm hm' related
  have memories := stateMemories_named_eq d d' env env' noExterns noExterns' m m' hm hm'
    state state' lookup same
  cases related with
  | module _ _ _ _ _ body =>
    cases path with
    | nil => simp [namedState] at value
    | cons name path =>
      have original := value
      rw [namedState] at value
      split at value
      · contradiction
      · rename_i equation found
        have member := List.mem_of_find?_eq_some found
        have named : equationName equation = name := by simpa using List.find?_some found
        cases equation with
        | let_ | assign => contradiction
        | reg i p n width clock target reset ni np next =>
          change n = name at named
          subst n
          dsimp only at value
          split at value
          · rename_i empty
            have hp : path = [] := by simpa using empty
            subst path
            have raw : Core.Stmt.reg p name width clock (reset.map Typed.Reset.erase) ∈
                m.erase.body := (Ownership.mem_equationsErase m.body _).mpr
              ⟨_, member, i, .reg p name width clock reset,
                by simp [Typed.Equation.parts], rfl⟩
            obtain ⟨s, hs, rel⟩ := body.left raw
            cases rel
            obtain ⟨j, target', reset', nj, nq, next', member', resetEq⟩ :=
              Ownership.reg_equation m'.body _ _ _ _ _ hs
            have nextEq := next_erase_reorder d m m' hm body i j p p name width clock clock
              target target' reset reset' ni nj np nq next next' member member'
            have eq := nextRegister_erase_eq lookup values
              (stateMemories m (designChildren d env m hm) state).named
              reset reset' next next' resetEq.symm nextEq
            rw [Memories.named_typed, memories, Memories.named_typed] at eq
            rw [namedState_register d' env' noExterns' m' hm' _ j p name width clock target'
              reset' nj nq next' member']
            change some (.register width (nextRegister (values.valuation m'.ctx)
              (stateMemories m' (designChildren d' env' m' hm') state') reset' next')) = some cell
            rw [← eq]
            exact value
          · contradiction
        | mem i p n width depth clock target writes =>
          change n = name at named
          subst n
          dsimp only at value
          split at value
          · rename_i empty
            have hp : path = [] := by simpa using empty
            subst path
            have raw : Core.Stmt.mem p name width depth clock ∈ m.erase.body :=
              (Ownership.mem_equationsErase m.body _).mpr
                ⟨_, member, i, .mem p name width depth clock,
                  by simp [Typed.Equation.parts], rfl⟩
            obtain ⟨s, hs, rel⟩ := body.left raw
            cases rel
            obtain ⟨j, target', writes', member'⟩ := Ownership.mem_equation m'.body _ _ _ _ _ hs
            have writesPerm := writeSyntax_perm d d' m m' hm hm' body i j p p name width depth
              clock clock target target' writes writes' member member'
            have evaluated := evalWrites_perm lookup values
              (stateMemories m (designChildren d env m hm) state).named name
              writes writes' writesPerm
            rw [Memories.named_typed, memories, Memories.named_typed] at evaluated
            have cells := congrFun same [name]
            rw [namedState_memory d env noExterns m hm state i p name width depth clock
              target writes member, namedState_memory d' env' noExterns' m' hm' state' j p
              name width depth clock target' writes' member'] at cells
            have cellsEq := eq_of_heq (NamedCell.memory.inj (Option.some.inj cells)).2.2
            have eq := nextMemory_eq_of_evaluated (values.valuation m.ctx)
              (values.valuation m'.ctx) (stateMemories m (designChildren d env m hm) state)
              (stateMemories m' (designChildren d' env' m' hm') state')
              (state ⟨.mem i p name width depth clock target writes, member⟩) writes writes'
              (typed_write_ports_nodup d m hm i p name width depth clock target writes member)
              evaluated
            rw [cellsEq] at eq
            rw [namedState_memory d' env' noExterns' m' hm' _ j p name width depth clock
              target' writes' member']
            change some (.memory width depth (nextMemory (values.valuation m'.ctx)
              (stateMemories m' (designChildren d' env' m' hm') state')
              (state' ⟨.mem j p name width depth clock target' writes', member'⟩) writes')) =
                some cell
            rw [← eq, ← cellsEq]
            exact value
          · contradiction
        | inst i p n child inputs =>
          change n = name at named
          subst n
          have raw := instance_member m i p name child inputs member
          obtain ⟨s, hs, rel⟩ := body.left raw
          have matching : ∃ rawInputs, Core.Stmt.inst p name child rawInputs ∈ m'.erase.body ∧
              (inputs.map fun x => (x.1.val.name, x.2.erase)).Perm rawInputs := by
            cases rel with
            | same => exact ⟨_, hs, .refl _⟩
            | inst => exact ⟨_, hs, by assumption⟩
          obtain ⟨rawInputs, hs, perm⟩ := matching
          obtain ⟨j, ins, member', erased⟩ := Ownership.inst_equation m'.body _ _ _ _ hs
          exact (children i p name child inputs member j ins member' (erased ▸ perm)
            path).symm.trans original

theorem namedNextState_reorder (d d' : CertifiedDesign) (env : Env d.design)
    (env' : Env d'.design) (noExterns : d.design.externs = [])
    (noExterns' : d'.design.externs = []) (order : Reorder d.design.erase d'.design.erase)
    (m m' : Typed.Module) (hm : m ∈ d.design.bodies) (hm' : m' ∈ d'.design.bodies)
    (related : ItemReorder d.design.erase.items (.module m.erase) (.module m'.erase))
    (state : State d env m hm) (state' : State d' env' m' hm')
    (same : namedState d env noExterns m hm state = namedState d' env' noExterns' m' hm' state')
    (values : NamedValues)
    (children : InstanceNextAgree d d' env env' noExterns noExterns' m m' hm hm'
      state state' values) :
    namedState d env noExterns m hm (nextFromValues d env m hm state values) =
      namedState d' env' noExterns' m' hm' (nextFromValues d' env' m' hm' state' values) := by
  funext path
  apply Option.ext
  intro cell
  constructor
  · exact next_some_reorder d d' env env' noExterns noExterns' order m m' hm hm' related
      state state' same values children path cell
  · apply next_some_reorder d' d env' env noExterns' noExterns order.symm m' m hm' hm
      (related.symm.changeItems order.resolves)
      state' state same.symm values
    intro i p name child inputs member i' inputs' member' perm path
    exact (children i' p name child inputs' member' i inputs member perm.symm path).symm

end Silicon.Core.Semantics
