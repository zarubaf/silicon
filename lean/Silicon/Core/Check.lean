import Silicon.Core.List
import Silicon.Core.Complete
import Silicon.Core.GraphReach
import Silicon.Core.GraphCycleIndex
import Std.Data.HashSet.Lemmas

/-! Check design rules and report errors at source positions. -/

namespace Silicon.Core.Rules

open Typed (modules valueTy)

def findItem (d : Design) (n : String) : Option Item :=
  d.items.find? fun i => Item.name i == n

def definition : Stmt → Option String
  | .let_ _ n _ _ | .reg _ n _ _ _ | .mem _ n _ _ _ | .inst _ n _ _ => some n
  | _ => none

def findStmt (m : Module) (n : String) : Option Stmt :=
  m.body.find? fun s => definition s == some n

def findPort (m : Module) (n : String) : Option Port := m.ports.find? (·.name == n)

def instancePort (d : Design) (m : Module) (i n : String) : Option Port := do
  let .inst _ _ child _ ← findStmt m i | none
  let item ← findItem d child
  (Item.ports item).find? (·.name == n)

def memory (d : Design) (m : Module) (n : String) : Option (Nat × Nat) :=
  match (Typed.context d m).lookup (.name n) with
  | some (.memory w depth) => some (w, depth) | _ => none

def clockName (m : Module) (n : String) : Bool :=
  (findPort m n).any fun p => p.dir == .input && p.ty == .clock

def children : Expr → List Expr
  | .un _ _ a | .extract _ a _ _ | .replicate _ a _ | .read _ _ a => [a]
  | .bin _ _ a b | .icmp _ _ a b => [a, b]
  | .mux _ a b c => [a, b, c]
  | _ => []

def exprNodes : Expr → List Expr
  | e@(.un _ _ a) | e@(.extract _ a _ _) | e@(.replicate _ a _)
  | e@(.read _ _ a) => e :: exprNodes a
  | e@(.bin _ _ a b) | e@(.icmp _ _ a b) => e :: (exprNodes a ++ exprNodes b)
  | e@(.mux _ a b c) => e :: (exprNodes a ++ exprNodes b ++ exprNodes c)
  | e => [e]

def stmtExprs : Stmt → List Expr
  | .let_ _ _ _ e | .next _ _ e | .assign _ _ e => [e]
  | .reg _ _ _ _ r => r.toList.flatMap fun r => [r.signal, r.value]
  | .write _ _ _ a v e => [a, v, e]
  | .inst _ _ _ xs => xs.map Prod.snd
  | _ => []

def directClock (m : Module) : Expr → Bool
  | .ref _ n => clockName m n
  | _ => false

def valueExprs (d : Design) (m : Module) : Stmt → List Expr
  | .inst _ _ child xs => xs.filterMap fun (n, e) =>
    let clock := (findItem d child).any fun i =>
      (Item.ports i).any fun p => p.name == n && p.ty == .clock
    if clock && directClock m e then none else some e
  | s => stmtExprs s

/-! These predicates state the semantic rules without diagnostic code. -/
def scopeNames (i : Item) : List String :=
  (Item.ports i).map Port.name ++ match i with
    | .module m => m.body.filterMap definition
    | .extern _ => []

/-! Lowering reserves a prefix for internal names and a dot for instance results. -/
def reservedName (n : String) : Bool := n.startsWith "silicon_" || n.contains '.'

def Unique (names : List String) : Prop :=
  names.Nodup ∧ ∀ n ∈ names, Rules.reservedName n = false

def Names (d : Design) : Prop :=
  Unique (d.items.map Item.name) ∧ ∀ i ∈ d.items, Unique (scopeNames i)

def ResolvedNode (d : Design) (m : Module) : Expr → Prop
  | .ref _ n => (valueTy (Typed.context d m) n).isSome = true
  | .port _ i n => (instancePort d m i n).any (·.dir == .output) = true
  | .read _ n _ => (memory d m n).isSome = true
  | _ => True

def ResolvedTarget (d : Design) (m : Module) : Stmt → Prop
  | .reg _ _ _ c _ | .mem _ _ _ _ c => clockName m c = true
  | .next _ n _ => (match findStmt m n with
      | some (.reg ..) => true | _ => false) = true
  | .write _ n _ _ _ _ => (memory d m n).isSome = true
  | .assign _ n _ => (findPort m n).any (·.dir == .output) = true
  | .inst _ _ child xs => ∃ i, findItem d child = some i ∧
      ∀ x ∈ xs, (Item.ports i).any (fun p => p.name == x.1 && p.dir == .input) = true
  | _ => True

def Resolved (d : Design) : Prop :=
  ((findItem d d.top).any fun i => match i with | .module _ => true | _ => false) = true ∧
  ∀ m ∈ modules d, ∀ s ∈ m.body, ResolvedTarget d m s ∧
    ∀ e ∈ stmtExprs s, ∀ node ∈ exprNodes e, ResolvedNode d m node

def Width (w : Nat) : Prop := 0 < w ∧ w ≤ 65536

def DeclaredNode : Expr → Prop
  | .const _ w v => Width w ∧ v < 2 ^ w
  | .extract _ _ _ w | .replicate _ _ w => 0 < w
  | _ => True

def DeclaredStmt : Stmt → Prop
  | .let_ _ _ w _ | .reg _ _ w _ _ => Width w
  | .mem _ _ w depth _ => Width w ∧ 0 < depth ∧ depth ≤ 16777216
  | _ => True

def Numbers (d : Design) : Prop :=
  ∀ i ∈ d.items,
    (∀ p ∈ Item.ports i, match p.ty with | .bits w => Width w | .clock => True) ∧
    match i with
    | .extern _ => True
    | .module m => ∀ s ∈ m.body, DeclaredStmt s ∧
        ∀ e ∈ stmtExprs s, ∀ node ∈ exprNodes e, DeclaredNode node

def ClockNode (d : Design) (m : Module) : Expr → Prop
  | .ref _ n => valueTy (Typed.context d m) n ≠ some .clock
  | .port _ i n => (instancePort d m i n).any (·.ty == .clock) = false
  | _ => True

def Clocks (d : Design) : Prop :=
  ∀ i ∈ d.items,
    ((Item.ports i).filter fun p => p.dir == .input && p.ty == .clock).length ≤ 1 ∧
    (∀ p ∈ Item.ports i, p.dir = .output → p.ty ≠ .clock) ∧
    match i with
    | .extern _ => True
    | .module m => ∀ s ∈ m.body, ∀ e ∈ valueExprs d m s,
        ∀ node ∈ exprNodes e, ClockNode d m node

def Connections (d : Design) : Prop :=
  ∀ m ∈ modules d, ∀ s ∈ m.body, match s with
    | .inst _ _ child xs => ∀ i, findItem d child = some i →
        ∀ p ∈ Item.ports i, p.dir = .input →
          (xs.filter (·.1 == p.name)).length = 1 ∧
          (p.ty = .clock → ∀ x ∈ xs, x.1 = p.name → directClock m x.2 = true)
    | _ => True

def Dependencies (d : Design) : Prop :=
  ∀ i ∈ d.items, match i with
    | .module _ => True
    | .extern x =>
      (∀ p ∈ x.ports, p.dir = .output → (x.deps.filter (·.output == p.name)).length = 1) ∧
      ∀ dep ∈ x.deps,
        (x.ports.any fun p => p.dir == .output && p.name == dep.output) = true ∧
        dep.inputs.Nodup ∧ ∀ n ∈ dep.inputs,
          (x.ports.any fun p => p.name == n && p.dir == .input && p.ty != .clock) = true

def nexts (m : Module) (name : String) : List Pos :=
  m.body.filterMap fun s => match s with
    | .next p n _ => if n == name then some p else none | _ => none

def assignments (m : Module) (name : String) : List Pos :=
  m.body.filterMap fun s => match s with
    | .assign p n _ => if n == name then some p else none | _ => none

def writes (m : Module) (name : String) : List (Nat × Pos) :=
  m.body.filterMap fun s => match s with
    | .write p n index _ _ _ => if n == name then some (index, p) else none | _ => none

def Registers (d : Design) : Prop :=
  ∀ m ∈ modules d, ∀ s ∈ m.body, match s with
    | .reg _ n _ _ _ => (nexts m n).length = 1 | _ => True

def Outputs (d : Design) : Prop :=
  ∀ m ∈ modules d, ∀ p ∈ m.ports, p.dir = .output → (assignments m p.name).length = 1

def Writes (d : Design) : Prop :=
  ∀ m ∈ modules d, ∀ s ∈ m.body, match s with
    | .mem _ n _ _ _ => ((writes m n).map Prod.fst).Nodup ∧
        ∀ index ∈ (writes m n).map Prod.fst, index < (writes m n).length
    | _ => True

def Widths (d : Design) : Prop :=
  ∀ m ∈ modules d, ∀ s ∈ m.body,
    ∃ t : Typed.Stmt (Typed.context d m) (Typed.portsOf d), t.erase = s

def Combinational (d : Design) : Prop :=
  ∀ m ∈ modules d,
    ∃ ranks, Typed.Ranked (Deps.graph m (Typed.designDeps d d.depsFuel)) ranks

def Hierarchy (d : Design) : Prop := ∃ ranks, Typed.Ranked (Typed.hierarchyGraph d) ranks

end Silicon.Core.Rules

namespace Silicon.Core.Check

open Rules GraphReach

/-!
Parsed source supplies atom positions for paths with at most two entries.
Callers must keep paths within that depth to obtain a field position.
A deeper path or a constructed AST can lack this source entry.
In that case, diagnostics use the position that the enclosing form declares.
-/
def atomPos (form : Pos) (path : List Nat) : Pos :=
  match form.locate path with
  | some atom => atom
  | none => form

def exprPos : Expr → Pos
  | .ref p _ | .port p _ _ | .const p _ _ | .un p _ _ | .bin p _ _ _
  | .icmp p _ _ _ | .mux p _ _ _ | .extract p _ _ _ | .replicate p _ _
  | .read p _ _ => p

def stmtPos : Stmt → Pos
  | .let_ p _ _ _ | .reg p _ _ _ _ | .next p _ _ | .mem p _ _ _ _
  | .write p _ _ _ _ _ | .inst p _ _ _ | .assign p _ _ => p

open Typed (modules valueTy)

def itemPos : Item → Pos
  | .module m => m.pos
  | .extern e => e.pos

private def err (code : ErrorCode) (pos : Pos) (msg : String) : List Error :=
  [⟨code, pos, msg⟩]

private def require (ok : Bool) (code : ErrorCode) (p : Pos) (msg : String) : List Error :=
  if ok then [] else err code p msg

private def duplicateNames : List String → List (String × Pos) → List Error
  | _, [] => []
  | seen, (n, p) :: rest =>
    require (!(seen.contains n) && !(Rules.reservedName n)) .E002 p "name is not unique" ++
      duplicateNames (n :: seen) rest

private def indexedDuplicateNames (seen : Std.HashSet String) :
    List (String × Pos) → List Error
  | [] => []
  | (n, p) :: rest =>
    require (!(seen.contains n) && !(Rules.reservedName n)) .E002 p "name is not unique" ++
      indexedDuplicateNames (seen.insert n) rest

private theorem indexedDuplicateNames_eq (seen : List String)
    (index : Std.HashSet String) (xs : List (String × Pos))
    (hi : ∀ n, index.contains n = seen.contains n) :
    indexedDuplicateNames index xs = duplicateNames seen xs := by
  induction xs generalizing seen index with
  | nil => rfl
  | cons entry xs ih =>
    obtain ⟨n, p⟩ := entry
    simp only [indexedDuplicateNames, duplicateNames, hi]
    congr 1
    apply ih
    intro k
    simp only [Std.HashSet.contains_insert, List.contains_cons, hi]
    by_cases h : n = k
    · subst k; simp
    · simp [h, show (k == n) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]

private def duplicateNamesIndexed (seen : List String) (xs : List (String × Pos)) :
    List Error := indexedDuplicateNames (Std.HashSet.ofList seen) xs

@[csimp] private theorem duplicateNames_indexed : duplicateNames = duplicateNamesIndexed := by
  funext seen xs
  symm
  exact indexedDuplicateNames_eq seen _ xs (fun _ => Std.HashSet.contains_ofList)

theorem duplicateNames_spec (seen : List String) (xs : List (String × Pos)) :
    duplicateNames seen xs = [] ↔
      (xs.map Prod.fst).Nodup ∧
      ∀ n ∈ xs.map Prod.fst, n ∉ seen ∧ Rules.reservedName n = false := by
  induction xs generalizing seen with
  | nil => simp [duplicateNames]
  | cons x xs ih =>
    rcases x with ⟨n, p⟩
    simp only [duplicateNames, List.append_eq_nil_iff, ih, List.map_cons,
      List.nodup_cons, List.mem_cons, forall_eq_or_imp]
    have req (ok : Bool) : require ok .E002 p "name is not unique" = [] ↔ ok = true := by
      cases ok <;> simp [require, err]
    have cond : (!seen.contains n && !Rules.reservedName n) = true ↔
        n ∉ seen ∧ Rules.reservedName n = false := by simp
    simp only [req, cond, not_or]
    constructor
    · rintro ⟨⟨hn, hp⟩, hd, hr⟩
      refine ⟨⟨?_, hd⟩, ⟨hn, hp⟩, ?_⟩
      · intro hmem
        exact (hr n hmem).1.1 rfl
      · intro a ha
        exact ⟨(hr a ha).1.2, (hr a ha).2⟩
    · rintro ⟨⟨hn, hd⟩, ⟨hs, hp⟩, hr⟩
      refine ⟨⟨hs, hp⟩, hd, ?_⟩
      intro a ha
      refine ⟨⟨?_, (hr a ha).1⟩, (hr a ha).2⟩
      intro he
      exact hn (he ▸ ha)

def e002 (d : Design) : List Error :=
  duplicateNames [] (d.items.map fun i => (Item.name i, atomPos (itemPos i) [1])) ++
  d.items.flatMap fun i =>
    let ports := (Item.ports i).map fun p => (p.name, atomPos p.pos [1])
    let names := match i with
      | .module m => m.body.filterMap fun s => (definition s).map (·, atomPos (stmtPos s) [1])
      | _ => []
    duplicateNames [] (ports ++ names)

private def foldExpr (f : Expr → List Error) (e : Expr) : List Error :=
  (exprNodes e).flatMap f

private def resolvedExprUsing (typeOf : String → Option Ty)
    (d : Design) (m : Module) : Expr → List Error
  | .ref p n => require (typeOf n).isSome .E003 p "expected a value"
  | .port p i n => require ((instancePort d m i n).any (·.dir == .output))
      .E003 p "expected an instance output"
  | .read p n _ => require (memory d m n).isSome .E003 (atomPos p [1]) "expected a memory"
  | _ => []

private def resolvedExpr (d : Design) (m : Module) : Expr → List Error :=
  resolvedExprUsing (valueTy (Typed.context d m)) d m

private def resolvedStmtUsing (resolve : Expr → List Error)
    (d : Design) (m : Module) (s : Stmt) : List Error :=
  let target := match s with
    | .reg p _ _ c _ =>
      require (clockName m c) .E003 (atomPos p [3]) "expected a clock input"
    | .mem p _ _ _ c =>
      require (clockName m c) .E003 (atomPos p [4]) "expected a clock input"
    | .next p n _ => require (match findStmt m n with
        | some (.reg ..) => true | _ => false) .E003 (atomPos p [1]) "expected a register"
    | .write p n _ _ _ _ =>
      require (memory d m n).isSome .E003 (atomPos p [1]) "expected a memory"
    | .assign p n _ => require ((findPort m n).any (·.dir == .output))
        .E003 (atomPos p [1]) "expected an output"
    | .inst p _ child xs => match findItem d child with
      | none => err .E003 (atomPos p [2]) "expected a module or extern"
      | some i => xs.zipIdx.flatMap fun ((n, _), index) =>
        require ((Item.ports i).any fun q => q.name == n && q.dir == .input)
          .E003 (atomPos p [3 + index, 0]) "expected a child input"
    | _ => []
  target ++ (stmtExprs s).flatMap (foldExpr resolve)

private def resolvedStmt (d : Design) (m : Module) : Stmt → List Error :=
  resolvedStmtUsing (resolvedExpr d m) d m

private def resolvedModule (d : Design) (m : Module) : List Error :=
  m.body.flatMap (resolvedStmt d m)

private def indexedValueTy (index : Std.HashMap Deps.Node Typed.Kind) (n : String) :
    Option Ty :=
  match index[Deps.Node.name n]? with
  | some (.value ty) => some ty
  | some .clock => some .clock
  | _ => none

private theorem indexedValueTy_eq (ctx : Typed.Ctx) (n : String) :
    indexedValueTy (firstIndex ctx) n = valueTy ctx n := by
  simp only [indexedValueTy, firstIndex_lookup, valueTy]
  rfl

private def indexedResolvedModule (d : Design) (m : Module) : List Error :=
  let index := firstIndex (Typed.context d m)
  let typeOf := fun n => indexedValueTy index n
  m.body.flatMap (resolvedStmtUsing (resolvedExprUsing typeOf d m) d m)

@[csimp] private theorem resolvedModule_indexed : resolvedModule = indexedResolvedModule := by
  funext d m
  simp only [resolvedModule, indexedResolvedModule, resolvedStmt, resolvedExpr, indexedValueTy_eq]

def e003 (d : Design) : List Error :=
  require ((findItem d d.top).any fun i => match i with
    | .module _ => true | _ => false) .E003 d.topPos "expected a top module" ++
  (modules d).flatMap (resolvedModule d)

private def widthNumber (p : Pos) (w : Nat) : List Error :=
  require (0 < w && w ≤ 65536) .E005 p "width is outside the allowed range"

private def declaredExpr : Expr → List Error
  | .const p w v => widthNumber (atomPos p [1]) w ++
      require (v == 0 || Nat.log2 v < w) .E005 (atomPos p [2]) "constant does not fit its width"
  | .extract p _ _ w => require (0 < w) .E005 (atomPos p [3]) "extract width is zero"
  | .replicate p _ k => require (0 < k) .E005 (atomPos p [2]) "replication count is zero"
  | _ => []

def e005 (d : Design) : List Error :=
  d.items.flatMap fun i =>
    (Item.ports i).flatMap (fun p => match p.ty with
      | .bits w => widthNumber (atomPos p.pos [2, 1]) w | _ => []) ++
    match i with
    | .extern _ => []
    | .module m => m.body.flatMap fun s =>
      (match s with
        | .let_ p _ w _ | .reg p _ w _ _ => widthNumber (atomPos p [2, 1]) w
        | .mem p _ w depth _ => widthNumber (atomPos p [2, 1]) w ++
          require (0 < depth && depth ≤ 16777216) .E005 (atomPos p [3]) "invalid memory depth"
        | _ => []) ++ (stmtExprs s).flatMap (foldExpr (declaredExpr))

private def clocksExprUsing (typeOf : String → Option Ty)
    (d : Design) (m : Module) : Expr → List Error
  | .ref p n => require (typeOf n != some .clock)
      .E009 p "clock used as a value"
  | .port p i n => require (!((instancePort d m i n).any (·.ty == .clock)))
      .E009 p "clock used as a value"
  | _ => []

private def clocksExpr (d : Design) (m : Module) : Expr → List Error :=
  clocksExprUsing (valueTy (Typed.context d m)) d m

private def clockBody (d : Design) (m : Module) : List Error :=
  m.body.flatMap fun s => (valueExprs d m s).flatMap (foldExpr (clocksExpr d m))

private def indexedClockBody (d : Design) (m : Module) : List Error :=
  let index := firstIndex (Typed.context d m)
  let typeOf := fun n => indexedValueTy index n
  m.body.flatMap fun s =>
    (valueExprs d m s).flatMap (foldExpr (clocksExprUsing typeOf d m))

@[csimp] private theorem clockBody_indexed : clockBody = indexedClockBody := by
  funext d m
  simp only [clockBody, indexedClockBody, clocksExpr, indexedValueTy_eq]

def e009 (d : Design) : List Error :=
  d.items.flatMap fun i =>
    let cs := (Item.ports i).filter fun p => p.dir == .input && p.ty == .clock
    (cs.drop 1).flatMap (fun p => err .E009 p.pos "second clock input") ++
    ((Item.ports i).filter fun p => p.dir == .output && p.ty == .clock).flatMap
      (fun p => err .E009 p.pos "clock output") ++
    match i with
    | .extern _ => []
    | .module m => clockBody d m

def e011 (d : Design) : List Error :=
  (modules d).flatMap fun m => m.body.flatMap fun s => match s with
    | .inst pos _ child xs => match findItem d child with
      | none => []
      | some i => (Item.ports i).flatMap fun p =>
        if p.dir != .input then [] else
        let connections := xs.filter (·.1 == p.name)
        let duplicate := ((xs.zipIdx.filter (fun x => x.1.1 == p.name))[1]?).map
          fun x => atomPos pos [3 + x.2, 0]
        require (connections.length == 1) .E011 (duplicate.getD pos)
          "input must connect exactly once" ++
        if p.ty == .clock then connections.flatMap fun (_, e) =>
          require (directClock m e) .E011 (exprPos e) "expected a parent clock input"
        else []
    | _ => []

private def dependencyInputs (x : Extern) (dep : Dep) : List Error :=
  let entries := dep.inputs.zipIdx
  entries.flatMap fun (n, index) =>
    require (!(dep.inputs.take index).contains n)
      .E013 (atomPos dep.pos [2, index]) "duplicate dependency input" ++
    require (x.ports.any fun p => p.name == n && p.dir == .input && p.ty != .clock)
      .E013 (atomPos dep.pos [2, index]) "dependency must be a bits input"

def e013 (d : Design) : List Error :=
  d.items.flatMap fun i => match i with
    | .module _ => []
    | .extern x =>
      x.ports.flatMap (fun p => if p.dir == .output then
        let entries := x.deps.filter (·.output == p.name)
        match entries with
        | [] => err .E013 (atomPos p.pos [1]) "missing dependency entry"
        | _ :: second :: _ => err .E013 (atomPos second.pos [1]) "duplicate dependency entry"
        | [_] => []
        else []) ++
      x.deps.flatMap fun dep =>
        require (x.ports.any fun p => p.dir == .output && p.name == dep.output)
          .E013 (atomPos dep.pos [1]) "dependency target must be an output" ++
        dependencyInputs x dep

/-! Diagnostics use the same typed inference as statement construction. -/
def expressionTy (d : Design) (m : Module) (e : Expr) : Option Ty :=
  (Typed.infer (Typed.context d m) e).map Sigma.fst

private def operandErrorsWith (typeOf : Expr → Option Ty) (e : Expr) : List Error :=
  if (children e).all (fun a => (typeOf a).isSome) &&
      (typeOf e).isNone then err .E004 (exprPos e) "operand width mismatch" else []

private def targetWidthWith (typeOf : Expr → Option Ty) (p : Pos) (w : Nat)
    (e : Expr) : List Error :=
  match typeOf e with
  | some actual => require (actual == .bits w) .E004 p "target width mismatch"
  | none => []

private def stmtErrorsWith (d : Design) (m : Module)
    (typeOf : Expr → Option Ty) (s : Stmt) : List Error :=
    (valueExprs d m s).flatMap (foldExpr (operandErrorsWith typeOf)) ++
    match s with
    | .let_ p _ w e => targetWidthWith typeOf p w e
    | .next p n e | .assign p n e => match valueTy (Typed.context d m) n with
      | some (.bits w) => targetWidthWith typeOf p w e | _ => []
    | .reg p _ w _ reset => reset.toList.flatMap fun r =>
      if [r.signal, r.value].all (fun e => (typeOf e).isSome) then
        let pos := atomPos p [4]
        targetWidthWith typeOf pos 1 r.signal ++ targetWidthWith typeOf pos w r.value
      else []
    | .write p n _ a v en => match memory d m n with
      | some (w, depth) =>
        if [a, v, en].all (fun e => (typeOf e).isSome) then
          targetWidthWith typeOf p (Typed.addressWidth depth) a ++
            targetWidthWith typeOf p w v ++ targetWidthWith typeOf p 1 en
        else []
      | none => []
    | .inst p _ child xs => match findItem d child with
      | none => []
      | some i => xs.zipIdx.flatMap fun ((n, e), index) =>
        match (Item.ports i).find? (·.name == n) with
        | some port => match port.ty with
          | .bits w => targetWidthWith typeOf (atomPos p [3 + index]) w e | _ => []
        | none => []
    | _ => []

private abbrev operandErrors (d : Design) (m : Module) :=
  operandErrorsWith (expressionTy d m)

private abbrev targetWidth (d : Design) (m : Module) :=
  targetWidthWith (expressionTy d m)

def stmtErrors (d : Design) (m : Module) : Stmt → List Error :=
  stmtErrorsWith d m (expressionTy d m)

def e004 (d : Design) : List Error :=
  (modules d).flatMap fun m => m.body.flatMap (stmtErrors d m)

/-! The type pass shares one indexed context across all expressions of a module. -/
private def indexedE004 (d : Design) : List Error :=
  (modules d).flatMap fun m =>
    let ctx := Typed.context d m
    let index := firstIndex ctx
    let infer := Typed.inferWith ctx (fun n => index[n]?)
      (fun n => firstIndex_lookup ctx n)
    let typeOf := fun e => (infer e).map Sigma.fst
    m.body.flatMap (stmtErrorsWith d m typeOf)

@[csimp] private theorem e004_eq_indexed : e004 = indexedE004 := by
  funext d
  simp only [e004, indexedE004, Typed.inferWith_eq]
  rfl

private def exactlyOne (code : ErrorCode) (p : Pos) (ps : List Pos) : List Error :=
  match ps with
  | [] => err code p "missing driver"
  | _ :: second :: _ => err code second "duplicate driver"
  | [_] => []

def e006 (d : Design) : List Error :=
  (modules d).flatMap fun m => m.body.flatMap fun s => match s with
    | .reg p n _ _ _ => exactlyOne .E006 p (m.body.filterMap fun s => match s with
      | .next q k _ => if k == n then some q else none | _ => none)
    | _ => []

def e007 (d : Design) : List Error :=
  (modules d).flatMap fun m => m.ports.flatMap fun p =>
    if p.dir != .output then [] else
    exactlyOne .E007 p.pos (m.body.filterMap fun s => match s with
      | .assign q n _ => if n == p.name then some q else none | _ => none)

private def duplicateWrites : List Nat → List (Nat × Pos) → List Error
  | _, [] => []
  | seen, (n, p) :: rest =>
    (if seen.contains n then err .E012 p "duplicate write index" else []) ++
      duplicateWrites (n :: seen) rest

def e012 (d : Design) : List Error :=
  (modules d).flatMap fun m => m.body.flatMap fun s => match s with
    | .mem p n _ _ _ =>
      let writes := m.body.filterMap fun s => match s with
        | .write q k index _ _ _ => if k == n then some (index, q) else none | _ => none
      let duplicates := duplicateWrites [] writes
      if !duplicates.isEmpty then duplicates else
        require (writes.all fun (index, _) => index < writes.length)
          .E012 p "write indices must be contiguous from zero"
    | _ => []

private def reaches (g : Typed.Graph) (target : Deps.Node) := reachesSpec g target

private def indexedReachesAux (g : Std.HashMap Deps.Node (List Deps.Node))
    (target : Deps.Node) : Nat → List Deps.Node → Std.HashSet Deps.Node → Bool
  | 0, _, _ => false
  | fuel + 1, pending, seen =>
    if pending.contains target then true else
    let fresh := pending.foldl (fun acc n =>
      if seen.contains n || acc.contains n then acc else n :: acc) []
    let seen := seen.insertMany fresh
    let next := fresh.flatMap fun n => (g[n]?).getD []
    indexedReachesAux g target fuel (next.filter fun n => !seen.contains n) seen

private theorem indexedReachesAux_eq (g : Typed.Graph) (target : Deps.Node)
    (fuel : Nat) (pending seen : List Deps.Node) (index : Std.HashSet Deps.Node)
    (hindex : ∀ n, index.contains n = seen.contains n) :
    indexedReachesAux (firstIndex g) target fuel pending index =
      reachesSpec g target fuel pending seen := by
  induction fuel generalizing pending seen index with
  | zero => rfl
  | succ fuel ih =>
    simp only [indexedReachesAux, reachesSpec]
    split
    · rfl
    · simp only [hindex, firstIndex_lookup]
      have hi (n : Deps.Node) :
          (index.insertMany (freshNodes seen pending [])).contains n =
            (freshNodes seen pending [] ++ seen).contains n := by
        simp only [Std.HashSet.contains_insertMany_list, List.contains_append, hindex, Bool.or_comm]
      simp only [freshNodes] at hi ⊢
      simp only [hi]
      apply ih
      exact hi

private def indexedReaches (g : Typed.Graph) (target : Deps.Node)
    (fuel : Nat) (pending seen : List Deps.Node) : Bool :=
  indexedReachesAux (firstIndex g) target fuel pending (Std.HashSet.ofList seen)

@[csimp] private theorem reaches_indexed : reaches = indexedReaches := by
  funext g target fuel pending seen
  symm
  exact indexedReachesAux_eq g target fuel pending seen _ (fun _ => Std.HashSet.contains_ofList)

section BoundedCycles

variable {α : Type} [BEq α]

theorem walk_trail (g : List (α × List α)) {k : Nat} {x y : α} (h : Walk g k x y) :
    ∃ xs, xs.length = k ∧ Trail g xs x y := by
  induction h with
  | refl x => exact ⟨[], rfl, .refl x⟩
  | @step x y z k he hw ih =>
    obtain ⟨xs, hl, ht⟩ := ih
    exact ⟨x :: xs, by simp [hl], .step he ht⟩

theorem trail_mem_walk (g : List (α × List α)) {xs : List α} {x y n : α}
    (h : Trail g xs x y) (hm : n ∈ xs) :
    ∃ k, k < xs.length ∧ Walk g k x n := by
  induction h with
  | refl x => simp at hm
  | @step x y z xs he ht ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨0, by simp, .refl _⟩
    · obtain ⟨k, hk, hw⟩ := ih hm
      exact ⟨k+1, by simp; omega, .step he hw⟩

variable [LawfulBEq α]

theorem trail_repeat_cycle (g : List (α × List α)) {xs : List α} {x y : α}
    (h : Trail g xs x y) (hn : ¬xs.Nodup) :
    ∃ k n, 0 < k ∧ k < xs.length ∧ Walk g k n n := by
  induction h with
  | refl x => simp at hn
  | @step x y z xs he ht ih =>
    by_cases hmem : x ∈ xs
    · obtain ⟨k, hk, hw⟩ := trail_mem_walk g ht hmem
      exact ⟨k+1, x, by omega, by simp; omega, .step he hw⟩
    · have hnd : ¬xs.Nodup := by simpa [List.nodup_cons, hmem] using hn
      obtain ⟨k, n, hk, hl, hw⟩ := ih hnd
      exact ⟨k, n, hk, by simp; omega, hw⟩

theorem bounded_cycle (g : List (α × List α)) (k : Nat) (n : α)
    (hk : 0 < k) (hw : Walk g k n n) :
    ∃ length node, 0 < length ∧ length ≤ g.length ∧ Walk g length node node := by
  induction k using Nat.strongRecOn generalizing n with
  | ind k ih =>
    obtain ⟨xs, hl, ht⟩ := walk_trail g hw
    by_cases hn : xs.Nodup
    · refine ⟨k, n, hk, ?_, hw⟩
      have hb := hn.length_le_of_subset (trail_subset g ht)
      simpa [hl] using hb
    · obtain ⟨short, node, hp, hs, hc⟩ := trail_repeat_cycle g ht hn
      exact ih short (by omega) node hp hc
theorem bounded_cycle_row (g : List (α × List α)) (k : Nat) (n : α)
    (hk : 0 < k) (hw : Walk g k n n) :
    ∃ node edges child length, (node, edges) ∈ g ∧ child ∈ edges ∧
      length < g.length + 1 ∧ Walk g length child node := by
  obtain ⟨length, node, hp, hb, hc⟩ := bounded_cycle g k n hk hw
  cases hc with
  | refl => omega
  | @step x y z len hedge htail =>
    cases he : g.lookup node with
    | none => simp [he] at hedge
    | some edges =>
      obtain ⟨before, after, hg, _⟩ := List.lookup_eq_some_iff.mp he
      refine ⟨node, edges, y, len, ?_, ?_, by omega, htail⟩
      · simp [hg]
      · simpa [he] using hedge

end BoundedCycles

def e010 (d : Design) : List Error :=
  let g := Typed.hierarchyGraph d
  if (Typed.FastRanks.certificate g).isSome then [] else
  (modules d).flatMap fun m => m.body.flatMap fun s => match s with
    | .inst p _ child _ =>
      if reaches g (.name m.name) (g.length + 1) [.name child] [] then
        err .E010 p "instance cycle" else []
    | _ => []

private def nodePos (m : Module) (n : Deps.Node) : Pos :=
  ((m.body.find? fun s => match n, s with
    | .name n, .let_ _ k _ _ | .name n, .assign _ k _ => n == k
    | .port n _, .inst _ k _ _ => n == k
    | _, _ => false).map stmtPos).getD m.pos

private def e008All (d : Design) : List Error :=
  (modules d).flatMap fun m =>
    let g := Deps.graph m (Typed.designDeps d d.depsFuel)
    if (Typed.FastRanks.certificate g).isSome then [] else
    g.flatMap fun (n, edges) =>
      if reaches g n (g.length + 1) edges [] then
        err .E008 (nodePos m n) "combinational cycle" else []

/-! Stable position order lets cycle search stop at the first diagnostic. -/
private def cycleCandidates (m : Module) (g : Typed.Graph) :
    List (Pos × Deps.Node × List Deps.Node) :=
  (g.map fun row => (nodePos m row.1, row)).mergeSort fun a b =>
    a.1.line < b.1.line || (a.1.line == b.1.line && a.1.col ≤ b.1.col)

private def positionEntries : List Stmt → List (Deps.Node × Pos)
  | [] => []
  | .let_ p n _ _ :: rest | .assign p n _ :: rest =>
    (.name n, p) :: positionEntries rest
  | .inst p n _ _ :: rest => (.port n "", p) :: positionEntries rest
  | _ :: rest => positionEntries rest

private def positionKey : Deps.Node → Deps.Node
  | .name n => .name n
  | .port n _ => .port n ""

private theorem positionEntries_lookup (body : List Stmt) (n : Deps.Node) :
    (positionEntries body).lookup (positionKey n) =
      (body.find? fun s => match n, s with
        | .name n, .let_ _ k _ _ | .name n, .assign _ k _ => n == k
        | .port n _, .inst _ k _ _ => n == k
        | _, _ => false).map stmtPos := by
  have names (a b : String) : (Deps.Node.name a == .name b) = (a == b) := rfl
  have ports (a b : String) : (Deps.Node.port a "" == .port b "") = (a == b) := by
    change ((a == b) && ("" == "")) = (a == b)
    simp
  have mixed₁ (a b c : String) : (Deps.Node.name a == .port b c) = false := rfl
  have mixed₂ (a b c : String) : (Deps.Node.port a b == .name c) = false := rfl
  induction body with
  | nil => rfl
  | cons s body ih =>
    cases s <;> cases n <;>
      simp_all only [positionEntries, positionKey, List.lookup_cons, List.find?_cons]
    all_goals split <;> simp_all [stmtPos]

private def indexedCycleCandidates (m : Module) (g : Typed.Graph) :
    List (Pos × Deps.Node × List Deps.Node) :=
  let index := firstIndex (positionEntries m.body)
  (g.map fun row => ((index[positionKey row.1]?).getD m.pos, row)).mergeSort fun a b =>
    a.1.line < b.1.line || (a.1.line == b.1.line && a.1.col ≤ b.1.col)

@[csimp] private theorem cycleCandidates_indexed : cycleCandidates = indexedCycleCandidates := by
  funext m g
  simp only [cycleCandidates, indexedCycleCandidates, firstIndex_lookup,
    positionEntries_lookup, nodePos]

private def cycleDiagnostic (m : Module) (g : Typed.Graph) : List Error :=
  match (cycleCandidates m g).find? fun x => reaches g x.2.1 (g.length + 1) x.2.2 [] with
  | some (pos, _) => err .E008 pos "combinational cycle"
  | none => []

def e008 (d : Design) : List Error :=
  (modules d).flatMap fun m =>
    let g := Deps.graph m (Typed.designDeps d d.depsFuel)
    if (Typed.FastRanks.certificate g).isSome then [] else cycleDiagnostic m g

private theorem cycleDiagnostic_nil (m : Module) (g : Typed.Graph) :
    cycleDiagnostic m g = [] ↔
      (g.flatMap fun (n, edges) => if reaches g n (g.length + 1) edges [] then
        err .E008 (nodePos m n) "combinational cycle" else []) = [] := by
  unfold cycleDiagnostic
  have hp : (cycleCandidates m g).Perm (g.map fun row => (nodePos m row.1, row)) :=
    List.mergeSort_perm _ _
  cases hf : (cycleCandidates m g).find?
      (fun x => reaches g x.2.1 (g.length + 1) x.2.2 []) with
  | none =>
    simp only [List.flatMap_eq_nil_iff, true_iff]
    intro row hr
    have hm := hp.mem_iff.mpr (List.mem_map.mpr ⟨row,hr,rfl⟩)
    have hn := List.find?_eq_none.mp hf _ hm
    simp only at hn
    simp [hn]
  | some row =>
    simp only [err, List.cons_ne_self, false_iff]
    intro hnil
    have hr := hp.mem_iff.mp (List.mem_of_find?_eq_some hf)
    obtain ⟨original,hm,he⟩ := List.mem_map.mp hr
    subst row
    have hh := List.find?_some hf
    have hn := List.flatMap_eq_nil_iff.mp hnil original hm
    simp [hh] at hn

private theorem e008_nil (d : Design) : e008 d = [] ↔ e008All d = [] := by
  simp only [e008,e008All,List.flatMap_eq_nil_iff]
  apply forall_congr'
  intro m
  apply forall_congr'
  intro hm
  split
  · rfl
  · exact cycleDiagnostic_nil _ _

@[simp] theorem require_nil (ok : Bool) (code : ErrorCode) (p : Pos) (msg : String) :
    require ok code p msg = [] ↔ ok = true := by
  cases ok <;> simp [require, err]

@[simp] theorem foldExpr_nil (f : Expr → List Error) (e : Expr) :
    foldExpr f e = [] ↔ ∀ node ∈ exprNodes e, f node = [] := by
  simp [foldExpr, List.flatMap_eq_nil_iff]

private theorem constant_bound (v w : Nat) :
    (v = 0 ∨ Nat.log2 v < w) ↔ v < 2 ^ w := by
  by_cases h : v = 0
  · simp [h, Nat.two_pow_pos]
  · simp [h, Nat.log2_lt h]

@[simp] theorem declaredExpr_nil (e : Expr) :
    declaredExpr e = [] ↔ Rules.DeclaredNode e := by
  cases e <;> simp [declaredExpr, Rules.DeclaredNode, widthNumber, Rules.Width,
    constant_bound]

theorem e005_spec (d : Design) : e005 d = [] ↔ Rules.Numbers d := by
  simp only [e005, Rules.Numbers, List.flatMap_eq_nil_iff, List.append_eq_nil_iff]
  apply forall_congr'; intro i
  apply forall_congr'; intro _
  apply and_congr
  · apply forall_congr'; intro p
    apply forall_congr'; intro _
    cases p.ty <;> simp [widthNumber, Rules.Width]
  · cases i with
    | extern e => simp
    | module m =>
      simp only [List.flatMap_eq_nil_iff, List.append_eq_nil_iff, foldExpr_nil,
        declaredExpr_nil]
      apply forall_congr'; intro s
      apply forall_congr'; intro _
      apply and_congr_left; intro _
      cases s <;> simp [Rules.DeclaredStmt, widthNumber, Rules.Width, and_assoc]

@[simp] theorem resolvedExpr_nil (d : Design) (m : Module) (e : Expr) :
    resolvedExpr d m e = [] ↔ Rules.ResolvedNode d m e := by
  cases e <;> simp [resolvedExpr, resolvedExprUsing, Rules.ResolvedNode]

@[simp] theorem forall_zipIdx (xs : List α) (P : α → Prop) (offset : Nat) :
    (∀ x ∈ xs.zipIdx offset, P x.1) ↔ ∀ x ∈ xs, P x := by
  induction xs generalizing offset with
  | nil => simp
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.mem_cons, forall_eq_or_imp, ih]

theorem resolvedStmt_nil (d : Design) (m : Module) (s : Stmt) :
    resolvedStmt d m s = [] ↔ Rules.ResolvedTarget d m s ∧
      ∀ e ∈ stmtExprs s, ∀ node ∈ exprNodes e, Rules.ResolvedNode d m node := by
  simp only [resolvedStmt, resolvedStmtUsing, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    foldExpr_nil, resolvedExpr_nil]
  apply and_congr_left; intro _
  cases s <;> simp only [Rules.ResolvedTarget, require_nil]
  case inst pos name child xs _ =>
    cases h : findItem d child with
    | none => simp [err]
    | some i =>
      simp only [List.flatMap_eq_nil_iff, require_nil, Option.some.injEq,
        exists_eq_left']
      exact forall_zipIdx xs
        (fun x => ((Item.ports i).any fun p => p.name == x.1 && p.dir == .input) = true) 0

theorem e003_spec (d : Design) : e003 d = [] ↔ Rules.Resolved d := by
  simp [e003, resolvedModule, Rules.Resolved, List.flatMap_eq_nil_iff, resolvedStmt_nil]

@[simp] theorem clocksExpr_nil (d : Design) (m : Module) (e : Expr) :
    clocksExpr d m e = [] ↔ Rules.ClockNode d m e := by
  cases e <;> simp [clocksExpr, clocksExprUsing, Rules.ClockNode]

theorem e009_spec (d : Design) : e009 d = [] ↔ Rules.Clocks d := by
  simp only [e009, clockBody, Rules.Clocks, List.flatMap_eq_nil_iff, List.append_eq_nil_iff]
  apply forall_congr'; intro i
  apply forall_congr'; intro _
  rw [and_assoc]
  apply and_congr
  · simp only [err, reduceCtorEq, imp_false]
    rw [← List.eq_nil_iff_forall_not_mem, List.drop_eq_nil_iff]
  · apply and_congr
    · simp [err, List.mem_filter]
    · cases i <;> simp [List.flatMap_eq_nil_iff]

theorem e011_spec (d : Design) : e011 d = [] ↔ Rules.Connections d := by
  simp only [e011, Rules.Connections, List.flatMap_eq_nil_iff]
  apply forall_congr'; intro m
  apply forall_congr'; intro _
  apply forall_congr'; intro s
  apply forall_congr'; intro _
  cases s <;> try simp
  case inst p n child xs _ =>
    cases h : findItem d child with
    | none => simp
    | some i =>
      simp only [Option.some.injEq, forall_eq', List.flatMap_eq_nil_iff]
      apply forall_congr'; intro port
      apply forall_congr'; intro _
      cases port.dir <;> simp [List.flatMap_eq_nil_iff, List.mem_filter,
        and_imp, beq_iff_eq]

private theorem exactlyOne_spec (code : ErrorCode) (p : Pos) (ps : List Pos) :
    exactlyOne code p ps = [] ↔ ps.length = 1 := by
  cases ps with
  | nil => simp [exactlyOne, err]
  | cons q qs => cases qs <;> simp [exactlyOne, err]

theorem e006_spec (d : Design) : e006 d = [] ↔ Rules.Registers d := by
  simp only [e006, List.flatMap_eq_nil_iff, Rules.Registers]
  apply forall_congr'
  intro m
  apply forall_congr'
  intro hm
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  cases s <;> simp [exactlyOne_spec, Rules.nexts]

theorem e007_spec (d : Design) : e007 d = [] ↔ Rules.Outputs d := by
  simp only [e007, List.flatMap_eq_nil_iff, Rules.Outputs]
  apply forall_congr'
  intro m
  apply forall_congr'
  intro hm
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  have hi : (PortDir.input != PortDir.output) = true := by decide
  have ho : (PortDir.output != PortDir.output) = false := by decide
  cases p.dir
  · simp [hi]
  · simp [exactlyOne_spec, Rules.assignments]

theorem e002_spec (d : Design) : e002 d = [] ↔ Rules.Names d := by
  simp only [e002, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    duplicateNames_spec, List.map_map]
  simp only [List.not_mem_nil, not_false_eq_true, true_and, Function.comp_def,
    Rules.Names, Rules.Unique]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  cases i <;> simp [Rules.scopeNames, List.map_append, List.map_map,
    List.map_filterMap, Function.comp_def, Option.map_map]

private theorem duplicateWrites_spec (seen : List Nat) (xs : List (Nat × Pos)) :
    duplicateWrites seen xs = [] ↔
      (xs.map Prod.fst).Nodup ∧ ∀ n ∈ xs.map Prod.fst, n ∉ seen := by
  induction xs generalizing seen with
  | nil => simp [duplicateWrites]
  | cons x xs ih =>
    rcases x with ⟨n, p⟩
    simp only [duplicateWrites, List.append_eq_nil_iff, ih, List.map_cons,
      List.nodup_cons, List.mem_cons, forall_eq_or_imp]
    have cond : (if seen.contains n then err .E012 p "duplicate write index" else []) = [] ↔
        n ∉ seen := by simp [err]
    simp only [cond, not_or]
    constructor
    · rintro ⟨hn, hd, hr⟩
      refine ⟨⟨?_, hd⟩, hn, ?_⟩
      · intro hmem
        exact (hr n hmem).1 rfl
      · intro a ha
        exact (hr a ha).2
    · rintro ⟨⟨hn, hd⟩, hs, hr⟩
      refine ⟨hs, hd, ?_⟩
      intro a ha
      refine ⟨?_, hr a ha⟩
      intro he
      exact hn (he ▸ ha)

private theorem writeErrors_spec (xs : List (Nat × Pos)) (p : Pos) :
    (if !(duplicateWrites [] xs).isEmpty then duplicateWrites [] xs else
      require (xs.all fun (index, _) => index < xs.length)
        .E012 p "write indices must be contiguous from zero") = [] ↔
      (xs.map Prod.fst).Nodup ∧ ∀ index ∈ xs.map Prod.fst, index < xs.length := by
  have dup : duplicateWrites [] xs = [] ↔ (xs.map Prod.fst).Nodup := by
    simp [duplicateWrites_spec]
  by_cases h : duplicateWrites [] xs = []
  · simp [h, dup.mp h, require, err]
  · have hn : ¬(xs.map Prod.fst).Nodup := fun hn => h (dup.mpr hn)
    have he : (duplicateWrites [] xs).isEmpty = false := by
      cases hd : duplicateWrites [] xs with
      | nil => exact False.elim (h hd)
      | cons _ _ => rfl
    simp [he, h, hn]

theorem e012_spec (d : Design) : e012 d = [] ↔ Rules.Writes d := by
  simp only [e012, List.flatMap_eq_nil_iff, Rules.Writes]
  apply forall_congr'
  intro m
  apply forall_congr'
  intro hm
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  cases s <;> try exact iff_of_true rfl trivial
  exact writeErrors_spec _ _

theorem zipIdx_fresh_iff (xs : List α) :
    (∀ entry ∈ xs.zipIdx, entry.1 ∉ xs.take entry.2) ↔ xs.Nodup := by
  constructor
  · intro h
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij he
    have hm : (xs[j], j) ∈ xs.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      exact List.getElem?_eq_getElem hj
    apply h _ hm
    exact List.mem_take_iff_getElem.mpr ⟨i, by omega, he⟩
  · intro h entry hm ht
    rcases entry with ⟨a, i⟩
    obtain ⟨hi, ha⟩ := List.mem_zipIdx' hm
    obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp ht
    have heq := h.eq_of_getElem_eq (by omega : j < xs.length) hi (he.trans ha)
    omega

theorem dependencyInputs_spec (x : Extern) (dep : Dep) :
    dependencyInputs x dep = [] ↔ dep.inputs.Nodup ∧ ∀ n ∈ dep.inputs,
      (x.ports.any fun p => p.name == n && p.dir == .input && p.ty != .clock) = true := by
  simp only [dependencyInputs, List.flatMap_eq_nil_iff, List.append_eq_nil_iff, require_nil]
  have fresh (seen : List String) (n : String) : (!seen.contains n) = true ↔ n ∉ seen := by
    simp
  simp only [fresh, forall_and, zipIdx_fresh_iff]
  exact and_congr Iff.rfl (forall_zipIdx dep.inputs (fun n =>
    (x.ports.any fun p => p.name == n && p.dir == .input && p.ty != .clock) = true) 0)

theorem depsCount_spec (p : Port) (entries : List Dep) :
    (match entries with
      | [] => err .E013 (atomPos p.pos [1]) "missing dependency entry"
      | _ :: second :: _ => err .E013 (atomPos second.pos [1]) "duplicate dependency entry"
      | [_] => []) = [] ↔ entries.length = 1 := by
  cases entries with
  | nil => simp [err]
  | cons a rest => cases rest <;> simp [err]

theorem e013_spec (d : Design) : e013 d = [] ↔ Rules.Dependencies d := by
  simp only [e013, List.flatMap_eq_nil_iff, Rules.Dependencies]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  cases i with
  | module m => simp
  | extern x =>
    simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
    apply and_congr
    · apply forall_congr'
      intro p
      apply forall_congr'
      intro hp
      by_cases h : p.dir = .output
      · simp [h, depsCount_spec]
      · simp [h]
    · apply forall_congr'
      intro dep
      apply forall_congr'
      intro hd
      simp only [require_nil, dependencyInputs_spec]

theorem infer_children (t : Typed.Expr ctx ty) :
    ∀ child ∈ Rules.children t.erase, (Typed.infer ctx child).isSome = true := by
  cases t with
  | ref p node h => cases node <;> simp [Typed.Expr.erase, Rules.children]
  | clock p n h => simp [Typed.Expr.erase, Rules.children]
  | const p w v => simp [Typed.Expr.erase, Rules.children]
  | un p op a => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]
  | bin p op ho a b => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]
  | concat p a b hb => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]
  | icmp p op a b => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]
  | mux p c a b => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]
  | extract p a lo count hb => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]
  | replicate p a count hb => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]
  | read p n found a => simp [Typed.Expr.erase, Rules.children, Typed.infer_complete]

theorem expressionTy_children (d : Design) (m : Module) (e : Expr)
    (h : (expressionTy d m e).isSome = true) :
    (children e).all (fun a => (expressionTy d m a).isSome) = true := by
  cases hi : Typed.infer (Typed.context d m) e with
  | none => simp [expressionTy, hi] at h
  | some t =>
    have he := Typed.infer_erase (Typed.context d m) e t hi
    rw [← he]
    simpa only [List.all_eq_true, expressionTy, Option.isSome_map] using infer_children t.2

private theorem operandErrors_spec (d : Design) (m : Module) (e : Expr) :
    operandErrors d m e = [] ↔
      ((children e).all (fun a => (expressionTy d m a).isSome) = true →
        (expressionTy d m e).isSome = true) := by
  unfold operandErrors operandErrorsWith
  cases hc : (children e).all (fun a => (expressionTy d m a).isSome) <;>
    cases he : expressionTy d m e <;> simp [err]

theorem operands_spec (d : Design) (m : Module) (e : Expr) :
    foldExpr (operandErrors d m) e = [] ↔ (expressionTy d m e).isSome = true := by
  have step (e : Expr) (childrenTyped : Prop)
      (hc : (children e).all (fun a => (expressionTy d m a).isSome) = true ↔ childrenTyped) :
      (operandErrors d m e = [] ∧ childrenTyped) ↔ (expressionTy d m e).isSome = true := by
    rw [operandErrors_spec, hc]
    constructor
    · exact fun h => h.1 h.2
    · intro h
      exact ⟨fun _ => h, hc.mp (expressionTy_children d m e h)⟩
  induction e with
  | ref p n => simp [foldExpr, exprNodes, operandErrors_spec, children]
  | port p i n => simp [foldExpr, exprNodes, operandErrors_spec, children]
  | const p w v => simp [foldExpr, exprNodes, operandErrors_spec, children]
  | un p o a ih | extract p a lo count ih | replicate p a count ih | read p n a ih =>
    simp only [foldExpr, exprNodes, List.flatMap_cons, List.append_eq_nil_iff] at ih ⊢
    simp only [ih]
    exact step _ _ (by simp [children])
  | bin p o a b ia ib | icmp p o a b ia ib =>
    simp only [foldExpr] at ia ib
    simp only [foldExpr, exprNodes, List.flatMap_cons, List.flatMap_append,
      List.append_eq_nil_iff, ia, ib]
    exact step _ _ (by simp [children])
  | mux p c a b ic ia ib =>
    simp only [foldExpr] at ic ia ib
    simp only [foldExpr, exprNodes, List.flatMap_cons, List.flatMap_append,
      List.append_eq_nil_iff, ic, ia, ib]
    exact step _ _ (by simp [children, and_assoc])
theorem expressionTy_spec (d : Design) (m : Module) (e : Expr) (ty : Ty) :
    expressionTy d m e = some ty ↔
      ∃ t : Typed.Expr (Typed.context d m) ty, t.erase = e := by
  constructor
  · intro h
    obtain ⟨⟨actual, t⟩, ht, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨t, Typed.infer_erase _ _ _ ht⟩
  · rintro ⟨t, rfl⟩
    simp [expressionTy, Typed.infer_complete]

theorem targetWidth_spec (d : Design) (m : Module) (p : Pos) (w : Nat) (e : Expr)
    (h : (expressionTy d m e).isSome = true) :
    targetWidth d m p w e = [] ↔
      ∃ t : Typed.Expr (Typed.context d m) (.bits w), t.erase = e := by
  rw [← expressionTy_spec]
  cases he : expressionTy d m e with
  | none => simp [he] at h
  | some ty => simp [targetWidth, targetWidthWith, he]




private theorem port_clock_lookup (ps : List Port) (tail : Typed.Ctx) (n : String)
    (h : (ps.find? (·.name == n)).any (fun p => p.dir == .input && p.ty == .clock) = true) :
    ((ps.map fun p => (Deps.Node.name p.name,
      if p.ty == .clock && p.dir == .input then Typed.Kind.clock else .value p.ty)) ++
      tail).lookup (.name n) = some .clock := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    by_cases hn : p.name = n
    · simp [hn] at h
      obtain ⟨hd, ht⟩ := h
      simp [hn, ht, hd]
    · simp [hn] at h
      have hb : (Deps.Node.name n == Deps.Node.name p.name) = false := by
        simp [Ne.symm hn]
      simpa [List.lookup, hb] using ih h

theorem directClock_typed (d : Design) (m : Module) (e : Expr)
    (h : Rules.directClock m e = true) :
    ∃ t : Typed.Expr (Typed.context d m) .clock, t.erase = e := by
  cases e <;> simp only [Rules.directClock, Bool.false_eq_true] at h
  rename_i p n
  exact ⟨.clock p n (port_clock_lookup m.ports _ n h), rfl⟩



open Rules
open Typed (modules valueTy)
theorem operands_targetWidth (d : Design) (m : Module) (p : Pos) (w : Nat) (e : Expr) :
    (foldExpr (operandErrors d m) e = [] ∧ targetWidth d m p w e = []) ↔
      Typed.HasExpr (Typed.context d m) (.bits w) e := by
  rw [operands_spec]
  constructor
  · rintro ⟨h, ht⟩
    exact (targetWidth_spec d m p w e h).mp ht
  · intro h
    have he := (expressionTy_spec d m e (.bits w)).mpr h
    exact ⟨by simp [he], (targetWidth_spec d m p w e (by simp [he])).mpr h⟩

theorem stmtErrors_let (d : Design) (m : Module) (p : Pos) (n : String)
    (w : Nat) (e : Expr) :
    stmtErrors d m (.let_ p n w e) = [] ↔
      Typed.HasStmt (Typed.context d m) (Typed.portsOf d) (.let_ p n w e) := by
  rw [Typed.hasStmt_let]
  simpa [stmtErrors, stmtErrorsWith, valueExprs, stmtExprs] using operands_targetWidth d m p w e

theorem stmtErrors_next (d : Design) (m : Module) (p : Pos) (n : String)
    (e : Expr) (h : ∃ w, Typed.valueTy (Typed.context d m) n = some (.bits w)) :
    stmtErrors d m (.next p n e) = [] ↔
      Typed.HasStmt (Typed.context d m) (Typed.portsOf d) (.next p n e) := by
  obtain ⟨w, hw⟩ := h
  rw [Typed.hasStmt_next]
  simp only [hw, Option.some.injEq, Ty.bits.injEq, exists_eq_left']
  simpa [stmtErrors, stmtErrorsWith, valueExprs, stmtExprs, hw] using operands_targetWidth d m p w e

theorem stmtErrors_assign (d : Design) (m : Module) (p : Pos) (n : String)
    (e : Expr) (h : ∃ w, Typed.valueTy (Typed.context d m) n = some (.bits w)) :
    stmtErrors d m (.assign p n e) = [] ↔
      Typed.HasStmt (Typed.context d m) (Typed.portsOf d) (.assign p n e) := by
  obtain ⟨w, hw⟩ := h
  rw [Typed.hasStmt_assign]
  simp only [hw, Option.some.injEq, Ty.bits.injEq, exists_eq_left']
  simpa [stmtErrors, stmtErrorsWith, valueExprs, stmtExprs, hw] using operands_targetWidth d m p w e
theorem stmtErrors_reg (d : Design) (m : Module) (p : Pos) (n : String)
    (w : Nat) (c : String) (r : Option Reset) :
    stmtErrors d m (.reg p n w c r) = [] ↔
      Typed.HasStmt (Typed.context d m) (Typed.portsOf d) (.reg p n w c r) := by
  rw [Typed.hasStmt_reg]
  cases r with
  | none => simp [stmtErrors, stmtErrorsWith, valueExprs, stmtExprs]
  | some r =>
    simp only [stmtErrors, stmtErrorsWith, valueExprs, stmtExprs, Option.toList_some,
      List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_eq_nil_iff, operands_spec,
      List.all_cons, List.all_nil, Bool.and_true, Option.mem_some_iff]
    constructor
    · rintro ⟨⟨hs, hv⟩, ht⟩ _ rfl
      simp only [hs, hv, Bool.true_and, ↓reduceIte, List.append_eq_nil_iff] at ht
      exact ⟨(targetWidth_spec d m _ 1 r.signal hs).mp ht.1,
        (targetWidth_spec d m _ w r.value hv).mp ht.2⟩
    · intro h
      obtain ⟨hs, hv⟩ := h r rfl
      have es := (expressionTy_spec d m r.signal (.bits 1)).mpr hs
      have ev := (expressionTy_spec d m r.value (.bits w)).mpr hv
      simp only [es, ev, Option.isSome_some, Bool.true_and, ↓reduceIte,
        List.append_eq_nil_iff, true_and]
      exact ⟨(targetWidth_spec d m _ 1 r.signal (by simp [es])).mpr hs,
        (targetWidth_spec d m _ w r.value (by simp [ev])).mpr hv⟩

theorem stmtErrors_mem (d : Design) (m : Module) (p : Pos) (n : String)
    (w depth : Nat) (c : String) :
    stmtErrors d m (.mem p n w depth c) = [] ↔
      Typed.HasStmt (Typed.context d m) (Typed.portsOf d) (.mem p n w depth c) := by
  simp only [stmtErrors, stmtErrorsWith, valueExprs, stmtExprs, List.flatMap_nil,
    List.append_nil]
  exact iff_of_true trivial (Typed.hasStmt_mem _ _ _ _ _ _ _)

theorem stmtErrors_write (d : Design) (m : Module) (p : Pos) (n : String)
    (i : Nat) (a v en : Expr)
    (h : ∃ w depth, (Typed.context d m).lookup (.name n) = some (.memory w depth)) :
    stmtErrors d m (.write p n i a v en) = [] ↔
      Typed.HasStmt (Typed.context d m) (Typed.portsOf d) (.write p n i a v en) := by
  obtain ⟨w, depth, hm⟩ := h
  rw [Typed.hasStmt_write]
  simp only [hm, Option.some.injEq, Typed.Kind.memory.injEq]
  have rhs : (∃ w' depth', (w = w' ∧ depth = depth') ∧
      Typed.HasExpr (Typed.context d m) (.bits (Typed.addressWidth depth')) a ∧
      Typed.HasExpr (Typed.context d m) (.bits w') v ∧
      Typed.HasExpr (Typed.context d m) (.bits 1) en) ↔
      Typed.HasExpr (Typed.context d m) (.bits (Typed.addressWidth depth)) a ∧
      Typed.HasExpr (Typed.context d m) (.bits w) v ∧
      Typed.HasExpr (Typed.context d m) (.bits 1) en := by
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩; exact h
    · intro h; exact ⟨w, depth, ⟨rfl, rfl⟩, h⟩
  rw [rhs]
  simp only [stmtErrors, stmtErrorsWith, valueExprs, stmtExprs, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_eq_nil_iff, operands_spec, memory, hm,
    List.all_cons, List.all_nil, Bool.and_true]
  constructor
  · rintro ⟨⟨ha, hv, he⟩, ht⟩
    simp only [ha, hv, he, Bool.true_and, ↓reduceIte, List.append_eq_nil_iff] at ht
    exact ⟨(targetWidth_spec d m _ _ a ha).mp ht.1.1,
      (targetWidth_spec d m _ _ v hv).mp ht.1.2,
      (targetWidth_spec d m _ _ en he).mp ht.2⟩
  · rintro ⟨ha, hv, he⟩
    have ea := (expressionTy_spec d m a (.bits (Typed.addressWidth depth))).mpr ha
    have ev := (expressionTy_spec d m v (.bits w)).mpr hv
    have ee := (expressionTy_spec d m en (.bits 1)).mpr he
    simp only [ea, ev, ee, Option.isSome_some, Bool.true_and, ↓reduceIte,
      List.append_eq_nil_iff, true_and]
    exact ⟨⟨(targetWidth_spec d m _ _ a (by simp [ea])).mpr ha,
      (targetWidth_spec d m _ _ v (by simp [ev])).mpr hv⟩,
      (targetWidth_spec d m _ _ en (by simp [ee])).mpr he⟩
theorem find_port_of_mem (ps : List Port) (p : Port)
    (hn : (ps.map Port.name).Nodup) (hp : p ∈ ps) :
    ps.find? (·.name == p.name) = some p := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hne : q.name ≠ p.name := by
        intro he
        exact hn.1 (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      simpa [hne] using ih hn.2 hp

theorem named_port_eq (ps : List Port) (p q : Port)
    (hn : (ps.map Port.name).Nodup) (hp : p ∈ ps) (hq : q ∈ ps)
    (he : p.name = q.name) : p = q := by
  have h1 := find_port_of_mem ps p hn hp
  have h2 := find_port_of_mem ps q hn hq
  rw [he, h2] at h1
  exact (Option.some.inj h1).symm

theorem any_clock_port (ps : List Port) (p : Port) (n : String)
    (hn : (ps.map Port.name).Nodup) (hp : p ∈ ps) (he : p.name = n) :
    ps.any (fun q => q.name == n && q.ty == .clock) = (p.ty == .clock) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨q, hq, hqn, hqt⟩
    have eq := named_port_eq ps p q hn hp hq (he.trans hqn.symm)
    simpa [eq] using hqt
  · intro ht
    exact ⟨p, hp, he, ht⟩

theorem targetWidth_nil (d : Design) (m : Module) (p : Pos) (w : Nat) (e : Expr) :
    targetWidth d m p w e = [] ↔ (expressionTy d m e).all (· == .bits w) = true := by
  cases he : expressionTy d m e <;> simp [targetWidth, targetWidthWith, he]

def connectionOK (d : Design) (m : Module) (ps : List Port) (x : String × Expr) : Prop :=
  ((ps.any (fun q => q.name == x.1 && q.ty == .clock) && directClock m x.2) = true ∨
    (expressionTy d m x.2).isSome = true) ∧
  match ps.find? (·.name == x.1) with
  | some p => match p.ty with
    | .bits w => (expressionTy d m x.2).all (· == .bits w) = true
    | .clock => True
  | none => True

theorem connectionOK_spec (d : Design) (m : Module) (ps : List Port) (x : String × Expr)
    (hn : (ps.map Port.name).Nodup)
    (hr : ∃ p ∈ ps, p.name = x.1 ∧ (p.ty = .clock → directClock m x.2 = true)) :
    connectionOK d m ps x ↔
      ∃ p ∈ ps, p.name = x.1 ∧ Typed.HasExpr (Typed.context d m) p.ty x.2 := by
  obtain ⟨p, hp, he, hc⟩ := hr
  have hf : ps.find? (·.name == x.1) = some p := by
    rw [← he]; exact find_port_of_mem ps p hn hp
  have rhs : (∃ q ∈ ps, q.name = x.1 ∧ Typed.HasExpr (Typed.context d m) q.ty x.2) ↔
      Typed.HasExpr (Typed.context d m) p.ty x.2 := by
    constructor
    · rintro ⟨q, hq, hqn, ht⟩
      have eq := named_port_eq ps p q hn hp hq (he.trans hqn.symm)
      simpa [eq] using ht
    · exact fun ht => ⟨p, hp, he, ht⟩
  rw [rhs]
  unfold connectionOK
  rw [hf, any_clock_port ps p x.1 hn hp he]
  cases ht : p.ty with
  | clock =>
    have hd := hc ht
    simp only [ht, hd, beq_self_eq_true, Bool.and_self, true_or, and_true]
    exact iff_of_true trivial (by exact directClock_typed d m x.2 hd)
  | bits w =>
    have hb : (Ty.bits w == Ty.clock) = false := by simp
    simp only [ht, hb, Bool.false_and, Bool.false_eq_true, false_or]
    rw [← operands_spec, ← targetWidth_nil d m (exprPos x.2)]
    exact operands_targetWidth d m (exprPos x.2) w x.2
theorem filtered_operands (d : Design) (m : Module) (xs : List (String × Expr))
    (skip : String × Expr → Bool) :
    ((xs.filterMap fun x => if skip x then none else some x.2).flatMap
      (foldExpr (operandErrors d m)) = []) ↔
      ∀ x ∈ xs, skip x = true ∨ (expressionTy d m x.2).isSome = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : skip x <;> simp only [List.filterMap_cons, h, Bool.false_eq_true,
      ↓reduceIte, List.flatMap_cons, List.append_eq_nil_iff, operands_spec, ih,
      List.mem_cons, forall_eq_or_imp, false_or, true_or, true_and]

def connectionTarget (d : Design) (m : Module) (pos : Pos) (ps : List Port)
    (x : String × Expr) : List Error :=
  match ps.find? (·.name == x.1) with
  | some port => match port.ty with
    | .bits w => targetWidth d m pos w x.2
    | _ => []
  | none => []

def connectionTargetOK (d : Design) (m : Module) (ps : List Port)
    (x : String × Expr) : Prop :=
  match ps.find? (·.name == x.1) with
  | some port => match port.ty with
    | .bits w => (expressionTy d m x.2).all (· == .bits w) = true
    | .clock => True
  | none => True

theorem connectionTarget_nil (d : Design) (m : Module) (pos : Pos) (ps : List Port)
    (x : String × Expr) : connectionTarget d m pos ps x = [] ↔
      connectionTargetOK d m ps x := by
  unfold connectionTarget connectionTargetOK
  cases hf : ps.find? (·.name == x.1) with
  | none => simp
  | some p => cases ht : p.ty <;> simp [ht, targetWidth_nil]

theorem stmtErrors_inst_normalize (d : Design) (m : Module) (p : Pos) (n child : String)
    (xs : List (String × Expr)) (item : Item) (hi : findItem d child = some item) :
    stmtErrors d m (.inst p n child xs) = [] ↔
      ∀ x ∈ xs, connectionOK d m (Item.ports item) x := by
  simp only [stmtErrors, stmtErrorsWith]
  rw [hi]
  change ((valueExprs d m (.inst p n child xs)).flatMap
    (foldExpr (operandErrors d m)) ++ xs.zipIdx.flatMap (fun x =>
      connectionTarget d m (atomPos p [3 + x.2]) (Item.ports item) x.1)) = [] ↔ _
  rw [List.append_eq_nil_iff]
  rw [show valueExprs d m (.inst p n child xs) =
      xs.filterMap (fun x => if (Item.ports item).any
        (fun q => q.name == x.1 && q.ty == .clock) && directClock m x.2
        then none else some x.2) by simp [valueExprs, hi]]
  rw [filtered_operands]
  simp only [List.flatMap_eq_nil_iff, connectionTarget_nil]
  rw [forall_zipIdx xs (connectionTargetOK d m (Item.ports item)) 0]
  simp only [connectionOK, connectionTargetOK, forall_and]

theorem stmtErrors_inst (d : Design) (m : Module) (p : Pos) (n child : String)
    (xs : List (String × Expr)) (item : Item) (hi : findItem d child = some item)
    (hn : ((Item.ports item).map Port.name).Nodup)
    (hr : ∀ x ∈ xs, ∃ port ∈ Item.ports item, port.name = x.1 ∧
      (port.ty = .clock → directClock m x.2 = true)) :
    stmtErrors d m (.inst p n child xs) = [] ↔
      Typed.HasStmt (Typed.context d m) (Typed.portsOf d) (.inst p n child xs) := by
  rw [stmtErrors_inst_normalize d m p n child xs item hi, Typed.hasStmt_inst]
  have ports : Typed.portsOf d child = Item.ports item := by
    change ((findItem d child).map Item.ports).getD [] = _
    simp [hi]
  rw [ports]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  exact connectionOK_spec d m (Item.ports item) x hn (hr x hx)
theorem ports_nodup (d : Design) (item : Item) (hn : Names d) (hi : item ∈ d.items) :
    ((Item.ports item).map Port.name).Nodup := by
  have h := (hn.2 item hi).1
  cases item with
  | extern x => simpa [scopeNames, Item.ports] using h
  | module m =>
    simp only [scopeNames, Item.ports, List.nodup_append] at h
    exact h.1

theorem instance_requirements (d : Design) (m : Module) (p : Pos) (n child : String)
    (xs : List (String × Expr)) (hm : m ∈ modules d)
    (hs : Stmt.inst p n child xs ∈ m.body)
    (hn : Names d) (hr : Resolved d) (hc : Connections d) :
    ∃ item, findItem d child = some item ∧ ((Item.ports item).map Port.name).Nodup ∧
      ∀ x ∈ xs, ∃ port ∈ Item.ports item, port.name = x.1 ∧
        (port.ty = .clock → directClock m x.2 = true) := by
  obtain ⟨item, hi, hx⟩ := (hr.2 m hm (.inst p n child xs) hs).1
  refine ⟨item, hi, ports_nodup d item hn (List.mem_of_find?_eq_some hi), ?_⟩
  intro x hmem
  obtain ⟨port, hp, hport⟩ := List.any_eq_true.mp (hx x hmem)
  simp only [Bool.and_eq_true, beq_iff_eq] at hport
  obtain ⟨hn, hd⟩ := hport
  refine ⟨port, hp, hn, ?_⟩
  intro ht
  exact (hc m hm (.inst p n child xs) hs item hi port hp hd).2 ht x hmem hn.symm

theorem e004_from_targets (d : Design) (hn : Names d) (hr : Resolved d)
    (hc : Connections d)
    (targets : ∀ m ∈ modules d, ∀ s ∈ m.body,
      match s with
      | .next _ n _ | .assign _ n _ => ∃ w, valueTy (Typed.context d m) n = some (.bits w)
      | _ => True) :
    e004 d = [] ↔ Widths d := by
  change (modules d).flatMap (fun m => m.body.flatMap (stmtErrors d m)) = [] ↔ _
  simp only [List.flatMap_eq_nil_iff, Widths]
  apply forall_congr'
  intro m
  apply forall_congr'
  intro hm
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  change stmtErrors d m s = [] ↔ Typed.HasStmt _ _ s
  cases s with
  | let_ p n w e => exact stmtErrors_let d m p n w e
  | reg p n w c r => exact stmtErrors_reg d m p n w c r
  | mem p n w depth c => exact stmtErrors_mem d m p n w depth c
  | next p n e => exact stmtErrors_next d m p n e (targets m hm _ hs)
  | assign p n e => exact stmtErrors_assign d m p n e (targets m hm _ hs)
  | write p n i a v en =>
    apply stmtErrors_write
    have h := (hr.2 m hm (.write p n i a v en) hs).1
    change (memory d m n).isSome = true at h
    unfold memory at h
    cases he : (Typed.context d m).lookup (.name n) with
    | none => simp [he] at h
    | some kind =>
      cases kind with
      | clock => simp [he] at h
      | value ty => simp [he] at h
      | memory w depth => exact ⟨w, depth, rfl⟩
  | inst p n child xs =>
    obtain ⟨item, hi, hp, hx⟩ := instance_requirements d m p n child xs hm hs hn hr hc
    exact stmtErrors_inst d m p n child xs item hi hp hx


open Typed

private def bodyContext (d : Design) (ss : List Stmt) : Ctx :=
  context d ⟨⟨0, 0, []⟩, "", [], ss⟩

private theorem bodyContext_cons (d : Design) (s : Stmt) (ss : List Stmt) :
    bodyContext d (s :: ss) = bodyContext d [s] ++ bodyContext d ss := by
  simp [bodyContext, context, contextFromPorts]

private theorem entry_no_name (d : Design) (s : Stmt) (n : String)
    (h : definition s ≠ some n) : (bodyContext d [s]).lookup (.name n) = none := by
  cases s with
  | let_ p k w e | reg p k w c r | mem p k w depth c =>
    have hn : k ≠ n := by simpa [definition] using h
    have hb : (Deps.Node.name n == Deps.Node.name k) = false := by simp [Ne.symm hn]
    simp [bodyContext, context, contextFromPorts, List.lookup, hb]
  | next p k e | write p k i a v en | assign p k e => simp [bodyContext, context, contextFromPorts]
  | inst p name child xs =>
    simp only [bodyContext, context, contextFromPorts, List.map_nil, List.nil_append,
      List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    change ((portsOf d child).filterMap fun p =>
      if p.dir == .output then some (Deps.Node.port name p.name, Kind.value p.ty) else none).lookup
      (.name n) = none
    rw [List.lookup_eq_none_iff]
    intro entry he
    obtain ⟨port, _, hp⟩ := List.mem_filterMap.mp he
    split at hp <;> try contradiction
    cases hp
    simp

private theorem body_reg (d : Design) (ss : List Stmt) (n : String)
    (p : Pos) (w : Nat) (clock : String) (reset : Option Reset)
    (h : ss.find? (fun s => definition s == some n) = some (.reg p n w clock reset)) :
    (bodyContext d ss).lookup (.name n) = some (.value (.bits w)) := by
  induction ss with
  | nil => simp at h
  | cons s ss ih =>
    by_cases hd : definition s = some n
    · simp [hd] at h
      subst s
      simp [bodyContext, context, contextFromPorts]
    · simp [hd] at h
      rw [bodyContext_cons, List.lookup_append, entry_no_name d s n hd]
      simpa using ih h

private theorem port_lookup (ps : List Port) (tail : Ctx) (n : String) (p : Port)
    (h : ps.find? (·.name == n) = some p) :
    ((ps.map fun p => (Deps.Node.name p.name,
      if p.ty == .clock && p.dir == .input then Kind.clock else .value p.ty)) ++
      tail).lookup (.name n) =
      some (if p.ty == .clock && p.dir == .input then .clock else .value p.ty) := by
  induction ps with
  | nil => simp at h
  | cons q ps ih =>
    by_cases hn : q.name = n
    · simp [hn] at h
      subst q
      simp [hn]
    · simp [hn] at h
      have hb : (Deps.Node.name n == Deps.Node.name q.name) = false := by
        simp [Ne.symm hn]
      simpa [List.lookup, hb] using ih h

private theorem no_port_lookup (ps : List Port) (n : String)
    (h : ps.find? (·.name == n) = none) :
    (ps.map fun p => (Deps.Node.name p.name,
      if p.ty == .clock && p.dir == .input then Kind.clock else .value p.ty)).lookup
      (.name n) = none := by
  rw [List.lookup_eq_none_iff]
  intro entry he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  have hn := List.find?_eq_none.mp h p hp
  simp at hn
  simp [Ne.symm hn]

private theorem module_mem (d : Design) (m : Module) (hm : m ∈ modules d) :
    Item.module m ∈ d.items := by
  obtain ⟨i, hi, h⟩ := List.mem_filterMap.mp hm
  cases i with
  | module m' => cases h; exact hi
  | extern e => contradiction

private theorem register_no_port (d : Design) (m : Module) (n : String)
    (p : Pos) (w : Nat) (c : String) (r : Option Reset)
    (hn : Names d) (hm : m ∈ modules d)
    (hs : findStmt m n = some (.reg p n w c r)) : findPort m n = none := by
  have unique := (hn.2 (.module m) (module_mem d m hm)).1
  change ((m.ports.map Port.name) ++ m.body.filterMap definition).Nodup at unique
  have disjoint := (List.nodup_append.mp unique).2.2
  have mem : .reg p n w c r ∈ m.body := List.mem_of_find?_eq_some hs
  have defmem : n ∈ m.body.filterMap definition :=
    List.mem_filterMap.mpr ⟨_, mem, rfl⟩
  apply List.find?_eq_none.mpr
  intro port hp he
  have name : port.name = n := by simpa using he
  exact disjoint port.name (List.mem_map.mpr ⟨port, hp, rfl⟩) n defmem name

theorem target_next (d : Design) (m : Module) (p : Pos) (n : String) (e : Expr)
    (hn : Names d) (hm : m ∈ modules d) (_hs : .next p n e ∈ m.body)
    (hr : ResolvedTarget d m (.next p n e)) :
    ∃ w, valueTy (context d m) n = some (.bits w) := by
  cases hf : findStmt m n with
  | none => simp [ResolvedTarget, hf] at hr
  | some s =>
    cases s <;> simp only [ResolvedTarget, hf, Bool.false_eq_true] at hr
    rename_i pos name width clock reset
    have he := List.find?_some hf
    simp only [definition, beq_iff_eq, Option.some.injEq] at he
    subst name
    have hp := register_no_port d m n pos width clock reset hn hm hf
    refine ⟨width, ?_⟩
    unfold valueTy
    have hc : (context d m).lookup (.name n) = some (.value (.bits width)) := by
      rw [context, contextFromPorts, List.lookup_append, no_port_lookup m.ports n hp]
      exact body_reg d m.body n pos width clock reset hf
    rw [hc]

theorem target_assign (d : Design) (m : Module) (p : Pos) (n : String) (e : Expr)
    (_hn : Names d) (hm : m ∈ modules d) (_hs : .assign p n e ∈ m.body)
    (hr : ResolvedTarget d m (.assign p n e)) (hc : Clocks d) :
    ∃ w, valueTy (context d m) n = some (.bits w) := by
  simp only [ResolvedTarget, Option.any_eq_true] at hr
  obtain ⟨port, hp, hd⟩ := hr
  have dir : port.dir = .output := by simpa using hd
  have notClock := ((hc (.module m) (module_mem d m hm)).2.1 port
    (List.mem_of_find?_eq_some hp)) dir
  cases ht : port.ty with
  | clock => exact False.elim (notClock ht)
  | bits width =>
    refine ⟨width, ?_⟩
    have lookup := port_lookup m.ports (bodyContext d m.body) n port hp
    simp [ht] at lookup
    unfold valueTy
    change (match (context d m).lookup (.name n) with
      | some (.value ty) => some ty | some .clock => some .clock | _ => none) = _
    rw [show (context d m).lookup (.name n) = some (.value (.bits width)) from
      by simpa [context, contextFromPorts, bodyContext] using lookup]


theorem e004_spec (d : Design) (hn : Names d) (hr : Resolved d)
    (hcl : Clocks d) (hc : Connections d) : e004 d = [] ↔ Widths d := by
  apply e004_from_targets d hn hr hc
  intro m hm s hs
  cases s with
  | next p n e => exact target_next d m p n e hn hm hs (hr.2 m hm _ hs).1
  | assign p n e => exact target_assign d m p n e hn hm hs (hr.2 m hm _ hs).1 hcl
  | _ => trivial

/-! Syntax errors precede these nine semantic passes. -/
/-! Unique equation keys make the bounded rank construction complete. -/

private theorem hierarchy_keys_nodup (d : Design) (h : Rules.Names d) :
    ((Typed.hierarchyGraph d).map Prod.fst).Nodup := by
  have hn := h.1.1
  unfold Typed.hierarchyGraph Typed.modules
  simp only [List.map_map]
  have sub : ∀ (xs : List Item),
      (xs.filterMap (fun i => match i with | .module m => some m | _ => none) |>.map
        (fun m => Deps.Node.name m.name)).Sublist
        (xs.map fun i => Deps.Node.name (Item.name i)) := by
    intro xs
    induction xs with
    | nil => exact .slnil
    | cons i xs ih =>
      cases i with
      | module m => simpa only [List.filterMap_cons, List.map_cons, Item.name] using
          List.Sublist.cons_cons (Deps.Node.name m.name) ih
      | extern e => simpa using List.Sublist.cons _ ih
  apply (sub d.items).nodup
  have inj : ∀ (xs : List String), xs.Nodup → (xs.map Deps.Node.name).Nodup := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.nodup_cons, List.map_cons]
      intro h
      exact ⟨by simpa using h.1, ih h.2⟩
  simpa only [List.map_map, Function.comp_def] using inj (d.items.map Item.name) hn

private theorem filterMap_keys_sublist {α β κ : Type} (xs : List α) (f : α → Option β)
    (keyA : α → κ) (keyB : β → κ)
    (h : ∀ a b, f a = some b → keyB b = keyA a) :
    ((xs.filterMap f).map keyB).Sublist (xs.map keyA) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hf : f a with
    | none => simpa [List.filterMap_cons, hf] using List.Sublist.cons (keyA a) ih
    | some b =>
      simpa only [List.filterMap_cons, hf, List.map_cons, h a b hf] using
        List.Sublist.cons_cons (keyA a) ih

private theorem inferred_keys_nodup (m : Module) (children : String → Option Deps)
    (h : (m.ports.map Port.name).Nodup) : ((Deps.infer m children).map Prod.fst).Nodup := by
  apply List.Nodup.sublist (l₂ := m.ports.map Port.name) _ h
  unfold Deps.infer
  apply filterMap_keys_sublist
  intro p b hb
  split at hb
  · cases hb
    rfl
  · cases hb

private theorem extern_keys_nodup (e : Extern) (h : (e.ports.map Port.name).Nodup) :
    ((Typed.externDeps e).map Prod.fst).Nodup := by
  apply List.Nodup.sublist (l₂ := e.ports.map Port.name) _ h
  unfold Typed.externDeps
  apply filterMap_keys_sublist
  intro p b hb
  split at hb
  · cases hb
    rfl
  · cases hb


private theorem design_deps_keys_nodup (d : Design) (h : Rules.Names d) (fuel : Nat)
    (name : String) (deps : Deps) (hd : Typed.designDeps d fuel name = some deps) :
    (deps.map Prod.fst).Nodup := by
  unfold Typed.designDeps at hd
  have hm : (name, deps) ∈ Typed.dependencyTable d fuel := by
    obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hd
    rw [he]
    simp
  cases fuel with
  | zero => simp [Typed.dependencyTable] at hm
  | succ fuel =>
    simp only [Typed.dependencyTable, List.mem_map] at hm
    obtain ⟨item, hi, he⟩ := hm
    have hp : ((Item.ports item).map Port.name).Nodup := by
      have hs := (h.2 item hi).1
      unfold Rules.scopeNames at hs
      exact (List.nodup_append.mp hs).1
    cases item with
    | extern e =>
      cases he
      exact extern_keys_nodup e hp
    | module m =>
      cases he
      exact inferred_keys_nodup m _ hp


private def label := Stmt.driverName

private def owner : Deps.Node → String
  | .name n | .port n _ => n

private theorem nodup_of_countP_le_one {α : Type} [DecidableEq α] (xs : List α)
    (h : ∀ a, xs.countP (fun x => decide (x = a)) ≤ 1) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.nodup_cons]
    have ha := h a
    simp only [List.countP_cons, decide_true, ite_true] at ha
    constructor
    · intro hm
      have hp : 0 < xs.countP (fun x => decide (x = a)) :=
        List.countP_pos_iff.mpr ⟨a, hm, by simp⟩
      omega
    · apply ih
      intro b
      have hb := h b
      simp only [List.countP_cons] at hb
      omega

private theorem filterMap_nodup_counts {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → Option β)
    (h : ∀ b, xs.countP (fun a => decide (f a = some b)) ≤ 1) :
    (xs.filterMap f).Nodup := by
  apply nodup_of_countP_le_one
  intro b
  rw [List.countP_filterMap]
  have he : (fun a => (Option.map (fun x => decide (x = b)) (f a)).getD false) =
      (fun a => decide (f a = some b)) := by
    funext a
    cases hf : f a <;> simp
  rw [he]
  exact h b

private theorem countP_le_one_of_nodup {α : Type} [DecidableEq α] (xs : List α)
    (h : xs.Nodup) (a : α) : xs.countP (fun x => decide (x = a)) ≤ 1 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.nodup_cons] at h
    have hi := ih h.2
    by_cases he : b = a
    · subst b
      have hz : xs.countP (fun x => decide (x = a)) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx
        intro he
        have he : x = a := of_decide_eq_true he
        subst x
        exact h.1 hx
      simp [hz]
    · simp [he]
      exact hi

private theorem countP_some_le_one {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → Option β) (h : (xs.filterMap f).Nodup) (b : β) :
    xs.countP (fun a => decide (f a = some b)) ≤ 1 := by
  have hb := countP_le_one_of_nodup (xs.filterMap f) h b
  rw [List.countP_filterMap] at hb
  have he : (fun a => (Option.map (fun x => decide (x = b)) (f a)).getD false) =
      (fun a => decide (f a = some b)) := by
    funext a
    cases hf : f a <;> simp
  rwa [he] at hb

private theorem module_scope_nodup (d : Design) (m : Module)
    (names : Rules.Names d) (hm : m ∈ Typed.modules d) :
    (m.ports.map Port.name ++ m.body.filterMap Rules.definition).Nodup := by
  have hi : Item.module m ∈ d.items := by
    obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hm
    cases i <;> simp_all [Typed.modules]
  exact (names.2 (.module m) hi).1

private theorem labels_nodup (d : Design) (m : Module)
    (names : Rules.Names d) (resolved : Rules.Resolved d) (outputs : Rules.Outputs d)
    (hm : m ∈ Typed.modules d) : (m.body.filterMap label).Nodup := by
  have hscope := List.nodup_append.mp (module_scope_nodup d m names hm)
  apply filterMap_nodup_counts
  intro n
  by_cases hasAssign : ∃ p e, Stmt.assign p n e ∈ m.body
  · obtain ⟨pos, expr, hs⟩ := hasAssign
    have ht := (resolved.2 m hm (.assign pos n expr) hs).1
    change ((Rules.findPort m n).any fun p => p.dir == .output) = true at ht
    obtain ⟨port, hp, ho⟩ := (Option.any_eq_true _ _).mp ht
    have hpn : port.name = n := by
      have := List.find?_some hp
      simpa [Rules.findPort] using this
    have hpm : port ∈ m.ports := List.mem_of_find?_eq_some hp
    have hout := outputs m hm port hpm (by simpa using ho)
    rw [hpn] at hout
    have absent : n ∉ m.body.filterMap Rules.definition := by
      intro hd
      exact hscope.2.2 n (List.mem_map.mpr ⟨port, hpm, hpn⟩) n hd rfl
    have per : ∀ s ∈ m.body, (decide (label s = some n)) =
        ((match s with
          | .assign p k _ => if k == n then some p else none
          | _ => none) : Option Pos).isSome := by
      intro s hs
      have hd : Rules.definition s ≠ some n := by
        intro he
        exact absent (List.mem_filterMap.mpr ⟨s, hs, he⟩)
      cases s <;> simp_all [label, Stmt.driverName, Rules.definition] <;> split <;> simp_all
    rw [Rules.assignments, List.length_filterMap_eq_countP] at hout
    apply Nat.le_of_eq
    calc
      _ = _ := List.countP_congr (fun s hs => by rw [per s hs])
      _ = 1 := hout
  · apply Nat.le_trans (m := m.body.countP (fun s => decide (Rules.definition s = some n)))
    · apply List.countP_mono_left
      intro s hs hl
      simp only [decide_eq_true_eq] at hl ⊢
      cases s <;> simp_all [label, Stmt.driverName, Rules.definition]
    · exact countP_some_le_one m.body Rules.definition hscope.2.1 n


private theorem graph_keys (m : Module) (children : String → Option Deps) :
    (Deps.graph m children).map Prod.fst =
      m.body.flatMap (fun s => (Deps.equations children s).map Prod.fst) := by
  unfold Deps.graph
  simp only [List.map_map, List.map_flatMap]
  rfl

private theorem map_nodup_injective {α β : Type} (xs : List α) (f : α → β)
    (hi : ∀ a b, f a = f b → a = b) (hn : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.nodup_cons] at hn
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hn.2⟩
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact hn.1 (hi b a he ▸ hb)

private theorem equations_keys_inst (children : String → Option Deps) (pos : Pos)
    (name child : String) (inputs : List (String × Expr)) :
    (Deps.equations children (.inst pos name child inputs)).map Prod.fst =
      ((children child).getD []).map (fun p => Deps.Node.port name p.1) := List.map_map

private theorem graph_keys_nodup (d : Design) (m : Module) (children : String → Option Deps)
    (names : Rules.Names d) (resolved : Rules.Resolved d) (outputs : Rules.Outputs d)
    (hm : m ∈ Typed.modules d)
    (hc : ∀ name deps, children name = some deps → (deps.map Prod.fst).Nodup) :
    ((Deps.graph m children).map Prod.fst).Nodup := by
  rw [graph_keys]
  apply List.flatMap_nodup_owners m.body
    (fun s => (Deps.equations children s).map Prod.fst) label owner
    (labels_nodup d m names resolved outputs hm)
  · intro s _
    cases s with
    | inst pos n child inputs =>
      rw [equations_keys_inst]
      cases hd : children child with
      | none =>
        exact List.nodup_nil
      | some deps =>
        have hn := hc child deps hd
        have hi : ∀ a b, Deps.Node.port n a = Deps.Node.port n b → a = b := by
          intro a b h
          cases h
          rfl
        change (deps.map fun p => Deps.Node.port n p.1).Nodup
        have hh := map_nodup_injective (deps.map Prod.fst) (Deps.Node.port n) hi hn
        change ((deps : List (String × List String)).map Prod.fst |>.map
          (Deps.Node.port n)).Nodup at hh
        have he : (deps.map Prod.fst).map (Deps.Node.port n) =
            deps.map (fun p => Deps.Node.port n p.1) := List.map_map
        rwa [he] at hh
    | _ => simp [Deps.equations]
  · intro s _ node hn
    cases s with
    | inst pos name child inputs =>
      rw [equations_keys_inst] at hn
      obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hn
      rfl
    | _ => simp_all [Deps.equations, label, Stmt.driverName, owner]


theorem combinational_graph_keys_nodup (d : Design) (m : Module)
    (names : Rules.Names d) (resolved : Rules.Resolved d) (outputs : Rules.Outputs d)
    (hm : m ∈ Typed.modules d) (fuel : Nat) :
    ((Deps.graph m (Typed.designDeps d fuel)).map Prod.fst).Nodup :=
  graph_keys_nodup d m _ names resolved outputs hm
    (design_deps_keys_nodup d names fuel)

theorem combinational_rank_iff (d : Design) (m : Module)
    (names : Rules.Names d) (resolved : Rules.Resolved d) (outputs : Rules.Outputs d)
    (hm : m ∈ Typed.modules d) (fuel : Nat) :
    let g := Deps.graph m (Typed.designDeps d fuel)
    Typed.Ranked g (Typed.graphRanks g g.length) ↔ ∃ r, Typed.Ranked g r :=
  Typed.graphRanks_iff _ (combinational_graph_keys_nodup d m names resolved outputs hm fuel)

theorem hierarchy_rank_iff (d : Design) (names : Rules.Names d) :
    let g := Typed.hierarchyGraph d
    Typed.Ranked g (Typed.graphRanks g g.length) ↔ Rules.Hierarchy d :=
  Typed.graphRanks_iff _ (hierarchy_keys_nodup d names)

/-! Without a cycle, reachable-key counts provide a decreasing rank witness. -/

private def Reach (g : Typed.Graph) (x y : Deps.Node) : Prop := ∃ k, Walk g k x y

private noncomputable def countReach (g : Typed.Graph) (n : Deps.Node) : Nat := by
  classical
  exact g.countP fun row => decide (Reach g n row.1)

private theorem counts_edge (g : Typed.Graph) (n dep : Deps.Node)
    (hn : n ∈ g.map Prod.fst) (hedge : dep ∈ (g.lookup n).getD [])
    (noCycle : ∀ k x, 0 < k → ¬ Walk g k x x) : countReach g dep < countReach g n := by
  classical
  unfold countReach
  apply Typed.countP_strict
  · intro row _ hd
    simp only [decide_eq_true_eq] at hd ⊢
    obtain ⟨k, hw⟩ := hd
    exact ⟨k+1, Walk.step hedge hw⟩
  · obtain ⟨row, hr, he⟩ := List.mem_map.mp hn
    refine ⟨row, hr, ?_, ?_⟩
    · simp only [decide_eq_false_iff_not]
      rintro ⟨k, hw⟩
      rw [he] at hw
      exact noCycle (k+1) n (by omega) (Walk.step hedge hw)
    · simp only [decide_eq_true_eq]
      exact ⟨0, he ▸ Walk.refl row.1⟩

private theorem rank_map_keys (keys : List Deps.Node) (q : Deps.Node → Nat) (n : Deps.Node)
    (h : n ∈ keys) : Typed.rank (keys.map (fun x => (x, q x))) n = q n := by
  induction keys with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : n = x
    · subst n; simp [Typed.rank]
    · have ht : n ∈ xs := (List.mem_cons.mp h).resolve_left hx
      have hb : (n == x) = false := by simp [hx]
      simpa [Typed.rank, List.lookup, hb] using ih ht

private theorem rank_map_absent (keys : List Deps.Node) (q : Deps.Node → Nat) (n : Deps.Node)
    (h : n ∉ keys) : Typed.rank (keys.map (fun x => (x, q x))) n = 0 := by
  have hn : (keys.map (fun x => (x, q x))).lookup n = none := by
    simp [List.lookup_eq_none_iff]
    intro a ha he
    subst a
    exact h ha
  simp [Typed.rank, hn]

private theorem ranked_of_no_cycle (g : Typed.Graph) (hn : (g.map Prod.fst).Nodup)
    (noCycle : ∀ k x, 0 < k → ¬ Walk g k x x) : ∃ r, Typed.Ranked g r := by
  let keys := g.map Prod.fst
  let ranks := keys.map fun n => (n, countReach g n)
  refine ⟨ranks, ?_⟩
  intro row hr dep hd
  have hm : row.1 ∈ keys := List.mem_map.mpr ⟨row, hr, rfl⟩
  have hl := GraphReach.lookup_row_nodup g row.1 row.2 hn hr
  have hedge : dep ∈ (g.lookup row.1).getD [] := by simpa [hl] using hd
  have hc := counts_edge g row.1 dep hm hedge noCycle
  change Typed.rank (keys.map fun n => (n, countReach g n)) dep <
    Typed.rank (keys.map fun n => (n, countReach g n)) row.1
  rw [rank_map_keys keys (countReach g) row.1 hm]
  by_cases hdep : dep ∈ keys
  · rw [rank_map_keys keys (countReach g) dep hdep]
    exact hc
  · rw [rank_map_absent keys (countReach g) dep hdep]
    omega

theorem graph_cycle_of_not_ranked (g : Typed.Graph) (hn : (g.map Prod.fst).Nodup)
    (h : ¬ Typed.Ranked g (Typed.graphRanks g g.length)) :
    ∃ length node, 0 < length ∧ Walk g length node node := by
  classical
  apply Classical.byContradiction
  intro hc
  apply h
  apply (Typed.graphRanks_iff g hn).mpr
  apply ranked_of_no_cycle g hn
  intro k x hk hw
  exact hc ⟨k, x, hk, hw⟩


/-! The cycle passes reject every graph without a decreasing rank. -/
theorem e008_spec (d : Design) (hn : Rules.Names d) (hr : Rules.Resolved d)
    (ho : Rules.Outputs d) : e008 d = [] ↔ Rules.Combinational d := by
  rw [e008_nil]
  simp only [e008All, List.flatMap_eq_nil_iff, Rules.Combinational]
  apply forall_congr'
  intro m
  apply forall_congr'
  intro hm
  let g := Deps.graph m (Typed.designDeps d d.depsFuel)
  have hkeys := combinational_graph_keys_nodup d m hn hr ho hm d.depsFuel
  have hc : (Typed.FastRanks.certificate g).isSome = true ↔
      Typed.Ranked g (Typed.graphRanks g g.length) :=
    (Option.isSome_iff_exists.trans (Typed.FastRanks.certificate_iff g hkeys)).trans
      (Typed.graphRanks_iff g hkeys).symm
  dsimp only [g] at hc
  simp only [hc]
  by_cases hg : Typed.Ranked g (Typed.graphRanks g g.length)
  all_goals dsimp only [g] at hg
  · simp only [hg, ite_true]
    exact iff_of_true trivial ⟨_, hg⟩
  · have hno : ¬∃ r, Typed.Ranked g r := fun h =>
      hg ((combinational_rank_iff d m hn hr ho hm _).mpr h)
    obtain ⟨k, n, hk, hw⟩ := graph_cycle_of_not_ranked g
      (combinational_graph_keys_nodup d m hn hr ho hm _) hg
    obtain ⟨node, edges, child, length, hrow, hchild, hb, hp⟩ := bounded_cycle_row g k n hk hw
    have hreach := reaches_initial g node child (g.length + 1) length edges hp hb hchild
    simp only [hg, ite_false]
    constructor
    · intro hnil
      have hrowNil := (List.flatMap_eq_nil_iff.mp hnil) (node, edges) hrow
      dsimp only [g] at hreach
      simp [reaches, hreach, err] at hrowNil
    · intro h
      exact False.elim (hno h)

theorem e010_spec (d : Design) (hn : Rules.Names d) :
    e010 d = [] ↔ Rules.Hierarchy d := by
  unfold e010 reaches
  let g := Typed.hierarchyGraph d
  have equivalent := Typed.FastRanks.certificate_iff g (hierarchy_keys_nodup d hn)
  by_cases hc : (Typed.FastRanks.certificate g).isSome = true
  · dsimp only [g] at hc
    simp only [hc, ite_true]
    exact iff_of_true trivial (equivalent.mp (Option.isSome_iff_exists.mp hc))
  · have hno : ¬Rules.Hierarchy d := fun h =>
      hc (Option.isSome_iff_exists.mpr (equivalent.mpr h))
    have hg : ¬Typed.Ranked g (Typed.graphRanks g g.length) := fun h => hno ⟨_, h⟩
    obtain ⟨k, n, hk, hw⟩ := graph_cycle_of_not_ranked g (hierarchy_keys_nodup d hn) hg
    obtain ⟨node, edges, child, length, hrow, hchild, hb, hp⟩ := bounded_cycle_row g k n hk hw
    obtain ⟨m, hm, he⟩ := List.mem_map.mp hrow
    cases he
    obtain ⟨childName, hchildMem, he⟩ := List.mem_map.mp hchild
    subst child
    obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hchildMem
    cases s <;> simp only [Option.some.injEq, reduceCtorEq] at he
    rename_i p name module inputs
    subst childName
    have hreach := reaches_initial g (.name m.name) (.name module)
      (g.length + 1) length [.name module] hp hb (by simp)
    dsimp only [g] at hc
    simp only [hc]
    constructor
    · intro hnil
      have hmNil := (List.flatMap_eq_nil_iff.mp hnil) m hm
      have hsNil := (List.flatMap_eq_nil_iff.mp hmNil) (.inst p name module inputs) hs
      dsimp only [g] at hreach
      simp [hreach, err] at hsNil
    · intro h
      exact False.elim (hno h)

/-! A component label answers all cycle queries for the same graph. -/
private def cycleDiagnosticWith (m : Module) (g : Typed.Graph)
    (label : Deps.Node → Nat) : List Error :=
  match (cycleCandidates m g).find? fun x => GraphSCC.cyclic label x.2.1 x.2.2 with
  | some (pos, _) => err .E008 pos "combinational cycle"
  | none => []

private theorem find_congr (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?_cons, h x (by simp)]
    split
    · rfl
    · exact ih (fun x hx => h x (by simp [hx]))

private theorem cycleDiagnosticWith_eq (m : Module) (g : Typed.Graph)
    (unique : (g.map Prod.fst).Nodup) (c : GraphSCC.Certificate g) :
    cycleDiagnosticWith m g c.label = cycleDiagnostic m g := by
  unfold cycleDiagnosticWith cycleDiagnostic
  have eq := find_congr (cycleCandidates m g)
    (fun x => GraphSCC.cyclic c.label x.2.1 x.2.2)
    (fun x => reaches g x.2.1 (g.length + 1) x.2.2 []) (by
      intro row hr
      have hp : (cycleCandidates m g).Perm (g.map fun row => (nodePos m row.1, row)) :=
        List.mergeSort_perm _ _
      obtain ⟨⟨n, edges⟩, hn, he⟩ := List.mem_map.mp (hp.mem_iff.mp hr)
      subst row
      have lookup := GraphReach.lookup_row_nodup g n edges unique hn
      have eq := c.cyclic_eq_reaches n
      simpa [lookup, reaches] using eq)
  rw [eq]

private def hierarchyDiagnosticWith (d : Design) (label : Deps.Node → Nat) : List Error :=
  (modules d).flatMap fun m => m.body.flatMap fun s => match s with
    | .inst p _ child _ =>
      if label (.name child) == label (.name m.name) then err .E010 p "instance cycle" else []
    | _ => []

private theorem component_edge_query (g : Typed.Graph) (c : GraphSCC.Certificate g)
    (x y : Deps.Node) (he : y ∈ (g.lookup x).getD []) :
    (c.label y == c.label x) = reaches g x (g.length + 1) [y] [] := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, reaches, reaches_graph_iff, List.mem_singleton, exists_eq_left]
  constructor
  · intro h
    have hs := c.edge_nodes x y he
    exact c.connected y hs.2 x hs.1 h
  · intro h
    exact Nat.le_antisymm (c.edge_order x y he) (c.reachable_order h)

private theorem flatMap_congr (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem hierarchyDiagnosticWith_eq (d : Design) (hn : Rules.Names d)
    (c : GraphSCC.Certificate (Typed.hierarchyGraph d)) :
    hierarchyDiagnosticWith d c.label =
      ((modules d).flatMap fun m => m.body.flatMap fun s => match s with
        | .inst p _ child _ =>
          if reaches (Typed.hierarchyGraph d) (.name m.name) ((Typed.hierarchyGraph d).length + 1)
              [.name child] [] then err .E010 p "instance cycle" else []
        | _ => []) := by
  apply flatMap_congr
  intro m hm
  apply flatMap_congr
  intro s hs
  cases s <;> try rfl
  rename_i p name child inputs
  have hrow : (.name m.name, (Typed.childNames m).map Deps.Node.name) ∈
      Typed.hierarchyGraph d := List.mem_map.mpr ⟨m, hm, rfl⟩
  have lookup := GraphReach.lookup_row_nodup (Typed.hierarchyGraph d) (.name m.name)
    ((Typed.childNames m).map Deps.Node.name) (hierarchy_keys_nodup d hn) hrow
  have edge : Deps.Node.name child ∈ ((Typed.hierarchyGraph d).lookup (.name m.name)).getD [] := by
    rw [lookup]
    exact List.mem_map.mpr ⟨child, List.mem_filterMap.mpr ⟨.inst p name child inputs,
      hs, rfl⟩, rfl⟩
  dsimp only
  rw [component_edge_query _ c _ _ edge]

private theorem ranked_walk_le (g : Typed.Graph) (r : Typed.Ranks)
    (ranked : Typed.Ranked g r) {length : Nat} {x y : Deps.Node} (walk : Walk g length x y) :
    Typed.rank r y ≤ Typed.rank r x := by
  induction walk with
  | refl => exact Nat.le_refl _
  | @step x y z length edge _ ih =>
    cases hl : g.lookup x with
    | none => simp [hl] at edge
    | some children =>
      have row := GraphIndex.lookup_mem hl
      have step := ranked (x, children) row y (by simpa [hl] using edge)
      dsimp only at step
      omega

private theorem ranked_reaches_false (g : Typed.Graph) (r : Typed.Ranks)
    (ranked : Typed.Ranked g r) (source : Deps.Node) (children : List Deps.Node)
    (lower : ∀ child ∈ children, Typed.rank r child < Typed.rank r source) :
    reaches g source (g.length + 1) children [] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨child, hc, length, walk⟩ := (reaches_graph_iff g source children).mp h
  have := ranked_walk_le g r ranked walk
  have := lower child hc
  omega

private theorem cycleDiagnostic_ranked (m : Module) (g : Typed.Graph) (r : Typed.Ranks)
    (ranked : Typed.Ranked g r) : cycleDiagnostic m g = [] := by
  unfold cycleDiagnostic
  have none : (cycleCandidates m g).find?
      (fun x => reaches g x.2.1 (g.length + 1) x.2.2 []) = none := by
    apply List.find?_eq_none.mpr
    intro row hr
    have hp : (cycleCandidates m g).Perm (g.map fun row => (nodePos m row.1, row)) :=
      List.mergeSort_perm _ _
    obtain ⟨⟨n, edges⟩, hn, he⟩ := List.mem_map.mp (hp.mem_iff.mp hr)
    subst row
    simp only [ranked_reaches_false g r ranked n edges (ranked (n, edges) hn),
      Bool.false_eq_true, not_false_eq_true]
  rw [none]

private theorem hierarchyDiagnosticWith_ranked (d : Design) (hn : Rules.Names d)
    (c : GraphSCC.Certificate (Typed.hierarchyGraph d)) (r : Typed.Ranks)
    (ranked : Typed.Ranked (Typed.hierarchyGraph d) r) :
    hierarchyDiagnosticWith d c.label = [] := by
  rw [hierarchyDiagnosticWith_eq d hn c]
  apply List.flatMap_eq_nil_iff.mpr
  intro m hm
  apply List.flatMap_eq_nil_iff.mpr
  intro s hs
  cases s <;> try rfl
  rename_i p name child inputs
  have row : (.name m.name, (Typed.childNames m).map Deps.Node.name) ∈
      Typed.hierarchyGraph d := List.mem_map.mpr ⟨m, hm, rfl⟩
  have edge : Deps.Node.name child ∈ (Typed.childNames m).map Deps.Node.name :=
    List.mem_map.mpr ⟨child, List.mem_filterMap.mpr ⟨.inst p name child inputs, hs, rfl⟩, rfl⟩
  have no := ranked_reaches_false (Typed.hierarchyGraph d) r ranked (.name m.name)
    [.name child] (by
      intro n hn
      have he : n = .name child := by simpa using hn
      subst n
      exact ranked _ row _ edge)
  simp only [no, Bool.false_eq_true, ite_false]

private def e008With (d : Design)
    (certify : (g : Typed.Graph) → GraphSCC.Certificate g) : List Error :=
  (modules d).flatMap fun m =>
    let g := Deps.graph m (Typed.designDeps d d.depsFuel)
    cycleDiagnosticWith m g (certify g).label

private theorem e008With_eq (d : Design) (hn : Rules.Names d) (hr : Rules.Resolved d)
    (ho : Rules.Outputs d) (certify : (g : Typed.Graph) → GraphSCC.Certificate g) :
    e008With d certify = e008 d := by
  apply flatMap_congr
  intro m hm
  dsimp only
  rw [cycleDiagnosticWith_eq m _ (combinational_graph_keys_nodup d m hn hr ho hm _) (certify _)]
  split
  · rename_i accepted
    obtain ⟨r, found⟩ := Option.isSome_iff_exists.mp accepted
    exact cycleDiagnostic_ranked m _ r (Typed.FastRanks.certificate_sound _ r found)
  · rfl

private def e010With (d : Design)
    (certify : (g : Typed.Graph) → GraphSCC.Certificate g) : List Error :=
  hierarchyDiagnosticWith d (certify (Typed.hierarchyGraph d)).label

private theorem e010With_eq (d : Design) (hn : Rules.Names d)
    (certify : (g : Typed.Graph) → GraphSCC.Certificate g) : e010With d certify = e010 d := by
  unfold e010With e010
  dsimp only
  split
  · rename_i accepted
    obtain ⟨r, found⟩ := Option.isSome_iff_exists.mp accepted
    exact hierarchyDiagnosticWith_ranked d hn (certify _) r
      (Typed.FastRanks.certificate_sound _ r found)
  · exact hierarchyDiagnosticWith_eq d hn (certify _)

def localErrors (d : Design) : List (List Error) :=
  [e002 d, e003 d, e005 d, e009 d, e011 d ++ e013 d, e004 d,
    e006 d ++ e007 d ++ e012 d]

def errors (d : Design) : List (List Error) :=
  localErrors d ++ [e010 d, e008 d]

end Silicon.Core.Check

namespace Silicon.Core

/-! Each conjunct states one semantic rule from the core IR specification. -/
def WellFormed (d : Design) : Prop :=
  Rules.Names d ∧ Rules.Resolved d ∧ Rules.Widths d ∧ Rules.Numbers d ∧
  Rules.Registers d ∧ Rules.Outputs d ∧ Rules.Combinational d ∧ Rules.Clocks d ∧
  Rules.Hierarchy d ∧ Rules.Connections d ∧ Rules.Writes d ∧ Rules.Dependencies d

namespace Check

def earlier (a b : Error) : Bool :=
  a.pos.line < b.pos.line || (a.pos.line == b.pos.line && a.pos.col < b.pos.col)

def lowest : List Error → Option Error
  | [] => none
  | e :: es => some (es.foldl (fun a b => if earlier b a then b else a) e)

def firstError : List (List Error) → Option Error
  | [] => none
  | es :: rest => (lowest es).or (firstError rest)

/-! This boundary permits compiled diagnostics to share graph results. -/
def diagnostic (d : Design) : Option Error := firstError (errors d)

theorem firstError_none (passes : List (List Error)) :
    firstError passes = none ↔ ∀ es ∈ passes, es = [] := by
  induction passes with
  | nil => simp [firstError]
  | cons es rest ih =>
    cases es <;> simp [firstError, lowest, Option.or, ih]

private theorem firstError_append (xs ys : List (List Error)) :
    firstError (xs ++ ys) = (firstError xs).or (firstError ys) := by
  induction xs with
  | nil => rfl
  | cons xs rest ih =>
    simp only [List.cons_append, firstError, ih]
    cases lowest xs <;> rfl

private theorem local_requirements (d : Design) (h : firstError (localErrors d) = none) :
    Rules.Names d ∧ Rules.Resolved d ∧ Rules.Outputs d := by
  have all := (firstError_none _).mp h
  refine ⟨(e002_spec d).mp (all _ (by simp [localErrors])),
    (e003_spec d).mp (all _ (by simp [localErrors])), ?_⟩
  have outputs := all (e006 d ++ e007 d ++ e012 d) (by simp [localErrors])
  have hnil := List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp outputs).1
  exact (e007_spec d).mp hnil.2

/-! Earlier diagnostics finish before either cycle pass constructs a graph index. -/
private def diagnosticWith (certify : (g : Typed.Graph) → GraphSCC.Certificate g)
    (d : Design) : Option Error :=
  match firstError (localErrors d) with
  | some e => some e
  | none => match lowest (e010With d certify) with
    | some e => some e
    | none => lowest (e008With d certify)

private theorem diagnosticWith_eq (certify : (g : Typed.Graph) → GraphSCC.Certificate g) :
    diagnosticWith certify = diagnostic := by
  funext d
  unfold diagnostic errors
  rw [firstError_append]
  cases he : firstError (localErrors d) with
  | some e => simp [diagnosticWith, he, Option.or]
  | none =>
    obtain ⟨hn, hr, ho⟩ := local_requirements d he
    simp only [diagnosticWith, he, e010With_eq d hn, e008With_eq d hn hr ho,
      firstError, Option.or_none]
    cases lowest (e010 d) <;> rfl

private def indexedDiagnostic : Design → Option Error :=
  diagnosticWith (fun g => GraphCycleIndex.certificate g (firstIndex g)
    (firstIndex_lookup g))

@[csimp] private theorem diagnostic_components : diagnostic = indexedDiagnostic := by
  exact (diagnosticWith_eq _).symm

private theorem pass_results (d : Design) : firstError (errors d) = none ↔
    Rules.Names d ∧ Rules.Resolved d ∧ e004 d = [] ∧ Rules.Numbers d ∧
    Rules.Registers d ∧ Rules.Outputs d ∧ e008 d = [] ∧ Rules.Clocks d ∧
    e010 d = [] ∧ Rules.Connections d ∧ Rules.Writes d ∧ Rules.Dependencies d := by
  rw [firstError_none]
  simp only [errors, localErrors, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc,
    forall_eq_or_imp, List.append_eq_nil_iff, e002_spec, e003_spec, e005_spec,
    e006_spec, e007_spec, e009_spec, e011_spec, e012_spec, e013_spec]
  simp [and_assoc, and_left_comm, and_comm]

theorem no_errors (d : Design) : firstError (errors d) = none ↔ WellFormed d := by
  rw [pass_results]
  constructor
  · rintro ⟨hn, hr, hw, hnum, hreg, hout, hcomb, hclock, hhier, hconn, hwrite, hdeps⟩
    exact ⟨hn, hr, (e004_spec d hn hr hclock hconn).mp hw, hnum, hreg, hout,
      (e008_spec d hn hr hout).mp hcomb, hclock, (e010_spec d hn).mp hhier,
      hconn, hwrite, hdeps⟩
  · rintro ⟨hn, hr, hw, hnum, hreg, hout, hcomb, hclock, hhier, hconn, hwrite, hdeps⟩
    exact ⟨hn, hr, (e004_spec d hn hr hclock hconn).mpr hw, hnum, hreg, hout,
      (e008_spec d hn hr hout).mpr hcomb, hclock, (e010_spec d hn).mpr hhier,
      hconn, hwrite, hdeps⟩

/-! Declarative typed witnesses suffice to construct every statement in a body. -/
theorem interface_unique (d : Design) (hn : Rules.Names d) :
    ∀ n, ∀ a ∈ Typed.portsOf d n, ∀ b ∈ Typed.portsOf d n,
      a.name = b.name → a = b := by
  intro n a ha b hb he
  cases hf : Rules.findItem d n with
  | none =>
    unfold Rules.findItem at hf
    simp [Typed.portsOf, hf] at ha
  | some item =>
    have ps : Typed.portsOf d n = Item.ports item := by
      unfold Rules.findItem at hf
      simp [Typed.portsOf, hf]
    rw [ps] at ha hb
    exact named_port_eq _ a b (ports_nodup d item hn (List.mem_of_find?_eq_some hf)) ha hb he

theorem body_complete (d : Design) (m : Module) (hm : m ∈ Typed.modules d)
    (hn : Rules.Names d) (hw : Rules.Widths d) :
    ∃ body, m.body.mapM (Typed.statement d (Typed.context d m)) = some body ∧
      body.map Typed.Stmt.erase = m.body := by
  have aux : ∀ ss : List Core.Stmt,
      (∀ s ∈ ss, Typed.HasStmt (Typed.context d m) (Typed.portsOf d) s) →
      ∃ body, ss.mapM (Typed.statement d (Typed.context d m)) = some body ∧
        body.map Typed.Stmt.erase = ss := by
    intro ss witnesses
    induction ss with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons s ss ih =>
      obtain ⟨t, ht⟩ := witnesses s (by simp)
      obtain ⟨ts, hts, erase⟩ := ih (fun s hs => witnesses s (by simp [hs]))
      refine ⟨t :: ts, ?_, ?_⟩
      · simp only [List.mapM_cons, ← ht,
          Typed.statement_complete d _ (interface_unique d hn), hts]
        rfl
      · simp [ht, erase]
  exact aux m.body (hw m hm)

/-! A unique declaration fixes the context entry of each state equation. -/
theorem find_definition (ss : List Stmt) (s : Stmt) (n : String)
    (unique : (ss.filterMap Rules.definition).Nodup) (mem : s ∈ ss)
    (decl : Rules.definition s = some n) :
    ss.find? (fun x => Rules.definition x == some n) = some s := by
  induction ss with
  | nil => simp at mem
  | cons a ss ih =>
    rcases List.mem_cons.mp mem with rfl | hs
    · simp [decl]
    · have tail : (ss.filterMap Rules.definition).Nodup := by
        cases ha : Rules.definition a with
        | none => simpa [List.filterMap_cons, ha] using unique
        | some k =>
          exact (List.nodup_cons.mp (by simpa only [List.filterMap_cons, ha] using unique)).2
      have ne : Rules.definition a ≠ some n := by
        intro he
        have notmem : n ∉ ss.filterMap Rules.definition := by
          exact (List.nodup_cons.mp (by simpa only [List.filterMap_cons, he] using unique)).1
        exact notmem (List.mem_filterMap.mpr ⟨s, hs, decl⟩)
      simp [ne, ih tail hs]

private theorem declaration_no_port (d : Design) (m : Module) (s : Stmt) (n : String)
    (hn : Rules.Names d) (hm : m ∈ Typed.modules d) (hs : s ∈ m.body)
    (hd : Rules.definition s = some n) : Rules.findPort m n = none := by
  have unique := (hn.2 (.module m) (module_mem d m hm)).1
  change ((m.ports.map Port.name) ++ m.body.filterMap Rules.definition).Nodup at unique
  have disjoint := (List.nodup_append.mp unique).2.2
  apply List.find?_eq_none.mpr
  intro p hp he
  have name : p.name = n := by simpa using he
  exact disjoint p.name (List.mem_map.mpr ⟨p, hp, rfl⟩) n
    (List.mem_filterMap.mpr ⟨s, hs, hd⟩) name

private theorem body_mem (d : Design) (ss : List Stmt) (n : String)
    (p : Pos) (w depth : Nat) (clock : String)
    (h : ss.find? (fun s => Rules.definition s == some n) = some (.mem p n w depth clock)) :
    (bodyContext d ss).lookup (.name n) = some (.memory w depth) := by
  induction ss with
  | nil => simp at h
  | cons s ss ih =>
    by_cases hd : Rules.definition s = some n
    · simp [hd] at h
      subst s
      simp [bodyContext, Typed.context, Typed.contextFromPorts]
    · simp [hd] at h
      rw [bodyContext_cons, List.lookup_append, entry_no_name d s n hd]
      simpa using ih h

theorem state_ready (d : Design) (m : Module) (hm : m ∈ Typed.modules d)
    (hn : Rules.Names d) (regs : Rules.Registers d)
    (body : List (Typed.Stmt (Typed.context d m) (Typed.portsOf d)))
    (erase : body.map Typed.Stmt.erase = m.body) : Typed.StateReady body := by
  have unique : (m.body.filterMap Rules.definition).Nodup := by
    have h := (hn.2 (.module m) (module_mem d m hm)).1
    exact (List.nodup_append.mp h).2.1
  intro s hs
  have raw : s.erase ∈ m.body := erase ▸ List.mem_map.mpr ⟨s, hs, rfl⟩
  cases s
  all_goals try trivial
  case reg p n w c reset =>
    have hp := declaration_no_port d m _ n hn hm raw rfl
    have hf := find_definition m.body _ n unique raw (by rfl)
    constructor
    · unfold Typed.valueTy
      have hc : (Typed.context d m).lookup (.name n) = some (.value (.bits w)) := by
        rw [Typed.context, Typed.contextFromPorts, List.lookup_append,
          no_port_lookup m.ports n hp]
        exact body_reg d m.body n p w c (reset.map Typed.Reset.erase) hf
      rw [hc]
    · have count := regs m hm _ raw
      change (Rules.nexts m n).length = 1 at count
      unfold Rules.nexts at count
      rw [← erase, List.filterMap_map] at count
      have equal : (fun s : Typed.Stmt (Typed.context d m) (Typed.portsOf d) =>
          match s.erase with
          | .next p name _ => if name == n then some p else none
          | _ => none) = (fun s => match s with
          | .next p name _ _ _ => if name == n then some p else none
          | _ => none) := by
        funext s
        cases s <;> rfl
      simp only [Function.comp_def] at count
      rw [equal] at count
      apply Eq.trans ?_ count
      congr 2
      funext x
      cases x <;> rfl
  case mem p n w depth c =>
    change (Typed.context d m).lookup (.name n) = some (.memory w depth)
    have hp := declaration_no_port d m _ n hn hm raw rfl
    have hf := find_definition m.body _ n unique raw (by rfl)
    rw [Typed.context, Typed.contextFromPorts, List.lookup_append,
      no_port_lookup m.ports n hp]
    exact body_mem d m.body n p w depth c hf

/-! Every state update has one declaration in the same body. -/
private theorem declaration_count (ss : List Stmt) (n : String) (p : Stmt → Bool)
    (unique : (ss.filterMap Rules.definition).Nodup)
    (defines : ∀ s ∈ ss, p s = true → Rules.definition s = some n)
    (witness : ∃ s ∈ ss, p s = true) : ss.countP p = 1 := by
  have bound := countP_some_le_one ss Rules.definition unique n
  have mono : ss.countP p ≤ ss.countP (fun s => decide (Rules.definition s = some n)) := by
    apply List.countP_mono_left
    intro s hs hp
    exact decide_eq_true (defines s hs hp)
  have positive := List.countP_pos_iff.mpr witness
  omega

private theorem memory_declaration (d : Design) (m : Module) (n : String) (w depth : Nat)
    (lookup : (Typed.context d m).lookup (.name n) = some (.memory w depth)) :
    ∃ p c, Stmt.mem p n w depth c ∈ m.body := by
  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp lookup
  have mem : (Deps.Node.name n, Typed.Kind.memory w depth) ∈ Typed.context d m := by
    rw [eq]
    simp
  unfold Typed.context Typed.contextFromPorts at mem
  rcases List.mem_append.mp mem with hp | hs
  · obtain ⟨p, _, he⟩ := List.mem_map.mp hp
    split at he <;> cases he
  · obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp hs
    cases s <;> simp only [List.mem_singleton] at he
    all_goals try contradiction
    case let_ => cases he
    case reg => cases he
    case mem p name width size clock =>
      cases he
      exact ⟨p, clock, hs⟩
    case inst p name child xs =>
      obtain ⟨port, _, he⟩ := List.mem_filterMap.mp he
      split at he <;> cases he

private def registerName (n : String) : Stmt → Bool
  | .reg _ name .. => name == n | _ => false

private def memoryName (n : String) : Stmt → Bool
  | .mem _ name .. => name == n | _ => false

theorem update_owners (d : Design) (m : Module) (hm : m ∈ Typed.modules d)
    (hn : Rules.Names d) (resolved : Rules.Resolved d)
    (body : List (Typed.Stmt (Typed.context d m) (Typed.portsOf d)))
    (erase : body.map Typed.Stmt.erase = m.body) : Typed.UpdateOwners body := by
  have unique : (m.body.filterMap Rules.definition).Nodup := by
    exact (List.nodup_append.mp (module_scope_nodup d m hn hm)).2.1
  intro s hs
  have raw : s.erase ∈ m.body := erase ▸ List.mem_map.mpr ⟨s, hs, rfl⟩
  have target := (resolved.2 m hm _ raw).1
  cases s
  all_goals try trivial
  case next p n w ht value =>
    simp only [Typed.Stmt.erase, Rules.ResolvedTarget] at target
    have witness : ∃ s ∈ m.body, registerName n s = true := by
      cases hf : Rules.findStmt m n with
      | none => simp [hf] at target
      | some s =>
        have mem := List.mem_of_find?_eq_some hf
        have name := List.find?_some hf
        cases s <;> simp only [hf, Bool.false_eq_true] at target
        rename_i p name width clock reset
        simp only [Rules.definition, beq_iff_eq, Option.some.injEq] at name
        exact ⟨_, mem, by simp [registerName, name]⟩
    have count := declaration_count m.body n (registerName n) unique (by
      intro s _ hp
      cases s <;> simp_all [registerName, Rules.definition]) witness
    rw [← erase, List.countP_map] at count
    dsimp only
    rw [← List.countP_eq_length_filter]
    apply Eq.trans ?_ count
    congr 1
    funext s
    cases s <;> rfl
  case write p n index w depth ht addr data enable =>
    obtain ⟨mp, clock, mem⟩ := memory_declaration d m n w depth ht
    have count := declaration_count m.body n (memoryName n) unique (by
      intro s _ hp
      cases s <;> simp_all [memoryName, Rules.definition])
      ⟨.mem mp n w depth clock, mem, by simp [memoryName]⟩
    rw [← erase, List.countP_map] at count
    dsimp only
    rw [← List.countP_eq_length_filter]
    apply Eq.trans ?_ count
    congr 1
    funext s
    cases s <;> rfl

/-! Resolution supplies each child, and hierarchy ranks select a ready module. -/
theorem hierarchy_order (d : Design) (resolved : Rules.Resolved d)
    (hierarchy : Rules.Hierarchy d) :
    ∃ sorted, Typed.orderModules (Typed.modules d).length (Typed.externNames d)
      (Typed.modules d) = some sorted ∧ sorted.Perm (Typed.modules d) ∧
      Typed.ordered (Typed.externNames d) sorted = true := by
  obtain ⟨ranks, ranked⟩ := hierarchy
  apply Typed.orderModules_complete _ _ _ (fun n => Typed.rank ranks (.name n))
    (Nat.le_refl _)
  intro m hm child hc
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hc
  cases s <;> simp only at he
  all_goals try contradiction
  rename_i pos name target inputs
  cases he
  obtain ⟨item, found, _⟩ := (resolved.2 m hm _ hs).1
  have item_mem := List.mem_of_find?_eq_some found
  have item_name : Item.name item = child := by
    simpa [Rules.findItem] using List.find?_some found
  cases item with
  | extern e =>
    left
    exact List.mem_filterMap.mpr ⟨.extern e, item_mem, by simpa [Item.name] using item_name⟩
  | module childModule =>
    right
    refine ⟨childModule, List.mem_filterMap.mpr ⟨.module childModule, item_mem, rfl⟩,
      item_name, ?_⟩
    apply ranked (.name m.name, (Typed.childNames m).map Deps.Node.name)
      (List.mem_map.mpr ⟨m, hm, rfl⟩)
    exact List.mem_map.mpr ⟨child, List.mem_filterMap.mpr ⟨_, hs, rfl⟩, rfl⟩

/-! Semantic rules suffice for typed construction, grouping, and exact source erasure. -/
theorem elaborate_complete (d : Design) (wf : WellFormed d) :
    ∃ t, Typed.elaborateDesign d = some t := by
  obtain ⟨hn, hr, hw, _, hreg, hout, hcomb, _, hhier, _, _, _⟩ := wf
  obtain ⟨sorted, order, perm, hierarchy⟩ := hierarchy_order d hr hhier
  have ready : ∀ m ∈ sorted, ∃ body groups,
      m.body.mapM (Typed.statement d (Typed.context d m)) = some body ∧
      Typed.groupStatements (Typed.context d m) (Typed.portsOf d) body = some groups ∧
      Typed.equationsErase groups = m.body ∧
      ∃ ranks, Typed.FastRanks.certificate
        (Deps.graph m (Typed.designDeps d d.depsFuel)) = some ranks := by
    intro m hm
    have mem := perm.mem_iff.mp hm
    obtain ⟨body, hb, erased⟩ := body_complete d m mem hn hw
    obtain ⟨groups, hg⟩ := Typed.groupStatements_total body
      (state_ready d m mem hn hreg body erased)
    refine ⟨body, groups, hb, hg, ?_, ?_⟩
    · rw [← erased]
      exact Typed.equationsErase_of_raw_perm groups _
        (Typed.groupStatements_coverage body (update_owners d m mem hn hr body erased) groups hg)
    · exact Typed.FastRanks.certificate_complete _
        (combinational_graph_keys_nodup d m hn hr hout mem _) (hcomb m mem)
  obtain ⟨bodies, hb, erased⟩ := Typed.elaborateModules_of_groups d sorted ready
  exact Typed.elaborateDesign_of_modules d sorted bodies hn.1.1 order perm hierarchy hb erased

/-! Semantic clients use checked port and driver facts without checker scope details. -/
theorem module_ports_nodup (d : Design) (m : Module) (wf : WellFormed d)
    (hm : m ∈ Typed.modules d) : (m.ports.map Port.name).Nodup :=
  (List.nodup_append.mp (module_scope_nodup d m wf.1 hm)).1

theorem module_port_lookup (d : Design) (m : Module) (wf : WellFormed d)
    (hm : m ∈ Typed.modules d) (port : Port) (hp : port ∈ m.ports)
    (ht : port.ty = .bits width) (interfaces : String → List Port) :
    (Typed.contextFromPorts interfaces m).lookup (.name port.name) =
      some (.value (.bits width)) := by
  have found := find_port_of_mem m.ports port (module_ports_nodup d m wf hm) hp
  unfold Typed.contextFromPorts
  rw [port_lookup m.ports _ port.name port found]
  simp [ht]

theorem module_driver_names_nodup (d : Design) (m : Module) (wf : WellFormed d)
    (hm : m ∈ Typed.modules d) : (m.body.filterMap Stmt.driverName).Nodup := by
  have same : Stmt.driverName = label := by
    funext stmt
    cases stmt <;> rfl
  rw [same]
  exact labels_nodup d m wf.1 wf.2.1 wf.2.2.2.2.2.1 hm

theorem input_not_driver (d : Design) (wf : WellFormed d) (m : Module)
    (hm : m ∈ Typed.modules d) (port : Port) (hp : port ∈ m.ports)
    (hi : port.dir = .input) (stmt : Stmt) (hs : stmt ∈ m.body) :
    stmt.driverName ≠ some port.name := by
  have scope := List.nodup_append.mp (module_scope_nodup d m wf.1 hm)
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
    have found := find_port_of_mem m.ports port scope.1 hp
    change Rules.findPort m port.name = some port at found
    rw [found] at resolved
    simp [hi] at resolved
  | _ => exact noDefinition

end Check

/-! Diagnostics finish before elaboration constructs the typed design. -/
def check (d : Design) : Except Error Typed.Design :=
  match he : Check.diagnostic d with
  | some e => .error e
  | none => match ht : Typed.elaborateDesign d with
    | some t => .ok t
    | none => False.elim (by
        obtain ⟨t, accepted⟩ := Check.elaborate_complete d ((Check.no_errors d).mp he)
        rw [ht] at accepted
        contradiction)

theorem check_sound_erase (d : Design) (t : Typed.Design) (h : check d = .ok t) :
    t.erase = d := by
  unfold check at h
  split at h
  · contradiction
  · rename_i he
    split at h
    · rename_i typed accepted
      cases h
      exact Typed.elaborateDesign_erase d t accepted
    · rename_i failure
      obtain ⟨typed, accepted⟩ := Check.elaborate_complete d ((Check.no_errors d).mp he)
      rw [failure] at accepted
      contradiction

theorem check_sound (d : Design) (t : Typed.Design) (h : check d = .ok t) :
    WellFormed d ∧ t.erase.erasePos = d.erasePos := by
  unfold check at h
  split at h
  next => contradiction
  next he =>
    split at h
    next t' ht =>
      cases h
      exact ⟨(Check.no_errors d).mp he,
        congrArg Design.erasePos (Typed.elaborateDesign_erase d t ht)⟩
    next failure =>
      obtain ⟨typed, accepted⟩ := Check.elaborate_complete d ((Check.no_errors d).mp he)
      rw [failure] at accepted
      contradiction

/-! Every declaratively well-formed design has a typed checker result. -/
theorem check_complete (d : Design) (wf : WellFormed d) : ∃ t, check d = .ok t := by
  obtain ⟨t, ht⟩ := Check.elaborate_complete d wf
  refine ⟨t, ?_⟩
  unfold check
  split
  · rename_i failure
    change Check.firstError (Check.errors d) = some _ at failure
    rw [(Check.no_errors d).mpr wf] at failure
    contradiction
  · split
    · rename_i accepted
      rw [ht] at accepted
      cases accepted
      rfl
    · rename_i failure
      rw [ht] at failure
      contradiction

end Silicon.Core
