import Silicon.Core.Typed

namespace Silicon.Core.Check

def exprPos : Expr → Pos
  | .ref p _ | .port p _ _ | .const p _ _ | .un p _ _ | .bin p _ _ _
  | .icmp p _ _ _ | .mux p _ _ _ | .extract p _ _ _ | .replicate p _ _
  | .read p _ _ => p

def stmtPos : Stmt → Pos
  | .let_ p _ _ _ | .reg p _ _ _ _ | .next p _ _ | .mem p _ _ _ _
  | .write p _ _ _ _ _ | .inst p _ _ _ | .assign p _ _ => p

def itemName : Item → String
  | .module m => m.name
  | .extern e => e.name

def itemPos : Item → Pos
  | .module m => m.pos
  | .extern e => e.pos

def itemPorts : Item → List Port
  | .module m => m.ports
  | .extern e => e.ports

def modules (d : Design) : List Module :=
  d.items.filterMap fun i => match i with | .module m => some m | _ => none

def findItem (d : Design) (n : String) : Option Item :=
  d.items.find? fun i => itemName i == n

def definition : Stmt → Option String
  | .let_ _ n _ _ | .reg _ n _ _ _ | .mem _ n _ _ _ | .inst _ n _ _ => some n
  | _ => none

def findStmt (m : Module) (n : String) : Option Stmt :=
  m.body.find? fun s => definition s == some n

def findPort (m : Module) (n : String) : Option Port := m.ports.find? (·.name == n)

def valueTy (m : Module) (n : String) : Option Ty :=
  match findPort m n with
  | some p => some p.ty
  | none => match findStmt m n with
    | some (.let_ _ _ w _) | some (.reg _ _ w _ _) => some (.bits w)
    | _ => none

def instancePort (d : Design) (m : Module) (i n : String) : Option Port := do
  let .inst _ _ child _ ← findStmt m i | none
  let item ← findItem d child
  (itemPorts item).find? (·.name == n)

def memory (m : Module) (n : String) : Option (Nat × Nat) :=
  match findStmt m n with | some (.mem _ _ w depth _) => some (w, depth) | _ => none

def clockName (m : Module) (n : String) : Bool :=
  (findPort m n).any fun p => p.dir == .input && p.ty == .clock

abbrev addressWidth := Typed.addressWidth

private def err (code : ErrorCode) (pos : Pos) (msg : String) : List Error :=
  [⟨code, pos, msg⟩]

private def require (ok : Bool) (code : ErrorCode) (p : Pos) (msg : String) : List Error :=
  if ok then [] else err code p msg

private def duplicateNames : List String → List (String × Pos) → List Error
  | _, [] => []
  | seen, (n, p) :: rest =>
    require (!(seen.contains n) && !(n.startsWith "silicon_")) .E002 p "name is not unique" ++
      duplicateNames (n :: seen) rest

def e002 (d : Design) : List Error :=
  duplicateNames [] (d.items.map fun i => (itemName i, d.locate (itemPos i) [1])) ++
  d.items.flatMap fun i =>
    let ports := (itemPorts i).map fun p => (p.name, d.locate p.pos [1])
    let names := match i with
      | .module m => m.body.filterMap fun s => (definition s).map (·, d.locate (stmtPos s) [1])
      | _ => []
    duplicateNames [] (ports ++ names)

private def children : Expr → List Expr
  | .un _ _ a | .extract _ a _ _ | .replicate _ a _ | .read _ _ a => [a]
  | .bin _ _ a b | .icmp _ _ a b => [a, b]
  | .mux _ a b c => [a, b, c]
  | _ => []

private def foldExpr (f : Expr → List Error) : Expr → List Error
  | e@(.un _ _ a) | e@(.extract _ a _ _) | e@(.replicate _ a _)
  | e@(.read _ _ a) => f e ++ foldExpr f a
  | e@(.bin _ _ a b) | e@(.icmp _ _ a b) => f e ++ foldExpr f a ++ foldExpr f b
  | e@(.mux _ a b c) => f e ++ foldExpr f a ++ foldExpr f b ++ foldExpr f c
  | e => f e

private def stmtExprs : Stmt → List Expr
  | .let_ _ _ _ e | .next _ _ e | .assign _ _ e => [e]
  | .reg _ _ _ _ r => r.toList.flatMap fun r => [r.signal, r.value]
  | .write _ _ _ a v e => [a, v, e]
  | .inst _ _ _ xs => xs.map Prod.snd
  | _ => []

private def resolvedExpr (d : Design) (m : Module) : Expr → List Error
  | .ref p n => require (valueTy m n).isSome .E003 p "expected a value"
  | .port p i n => require ((instancePort d m i n).any (·.dir == .output))
      .E003 p "expected an instance output"
  | .read p n _ => require (memory m n).isSome .E003 (d.locate p [1]) "expected a memory"
  | _ => []

private def resolvedStmt (d : Design) (m : Module) (s : Stmt) : List Error :=
  let target := match s with
    | .reg p _ _ c _ =>
      require (clockName m c) .E003 (d.locate p [3]) "expected a clock input"
    | .mem p _ _ _ c =>
      require (clockName m c) .E003 (d.locate p [4]) "expected a clock input"
    | .next p n _ => require (match findStmt m n with
        | some (.reg ..) => true | _ => false) .E003 (d.locate p [1]) "expected a register"
    | .write p n _ _ _ _ => require (memory m n).isSome .E003 (d.locate p [1]) "expected a memory"
    | .assign p n _ => require ((findPort m n).any (·.dir == .output))
        .E003 (d.locate p [1]) "expected an output"
    | .inst p _ child xs => match findItem d child with
      | none => err .E003 (d.locate p [2]) "expected a module or extern"
      | some i => xs.zipIdx.flatMap fun ((n, _), index) =>
        require ((itemPorts i).any fun q => q.name == n && q.dir == .input)
          .E003 (d.locate p [3 + index, 0]) "expected a child input"
    | _ => []
  target ++ (stmtExprs s).flatMap (foldExpr (resolvedExpr d m))

def e003 (d : Design) : List Error :=
  require ((findItem d d.top).any fun i => match i with
    | .module _ => true | _ => false) .E003 d.topPos "expected a top module" ++
  (modules d).flatMap fun m => m.body.flatMap (resolvedStmt d m)

private def widthNumber (p : Pos) (w : Nat) : List Error :=
  require (0 < w && w ≤ 65536) .E005 p "width is outside the allowed range"

private def declaredExpr (d : Design) : Expr → List Error
  | .const p w v => widthNumber (d.locate p [1]) w ++
      require (v == 0 || Nat.log2 v < w) .E005 (d.locate p [2]) "constant does not fit its width"
  | .extract p _ _ w => require (0 < w) .E005 (d.locate p [3]) "extract width is zero"
  | .replicate p _ k => require (0 < k) .E005 (d.locate p [2]) "replication count is zero"
  | _ => []

def e005 (d : Design) : List Error :=
  d.items.flatMap fun i =>
    (itemPorts i).flatMap (fun p => match p.ty with
      | .bits w => widthNumber (d.locate p.pos [2, 1]) w | _ => []) ++
    match i with
    | .extern _ => []
    | .module m => m.body.flatMap fun s =>
      (match s with
        | .let_ p _ w _ | .reg p _ w _ _ => widthNumber (d.locate p [2, 1]) w
        | .mem p _ w depth _ => widthNumber (d.locate p [2, 1]) w ++
          require (0 < depth && depth ≤ 16777216) .E005 (d.locate p [3]) "invalid memory depth"
        | _ => []) ++ (stmtExprs s).flatMap (foldExpr (declaredExpr d))

private def clocksExpr (d : Design) (m : Module) : Expr → List Error
  | .ref p n => require (valueTy m n != some .clock) .E009 p "clock used as a value"
  | .port p i n => require (!((instancePort d m i n).any (·.ty == .clock)))
      .E009 p "clock used as a value"
  | _ => []

private def directClock (m : Module) : Expr → Bool
  | .ref _ n => clockName m n
  | _ => false

private def valueExprs (d : Design) (m : Module) : Stmt → List Expr
  | .inst _ _ child xs => xs.filterMap fun (n, e) =>
    let clock := (findItem d child).any fun i =>
      (itemPorts i).any fun p => p.name == n && p.ty == .clock
    if clock && directClock m e then none else some e
  | s => stmtExprs s

def e009 (d : Design) : List Error :=
  d.items.flatMap fun i =>
    let cs := (itemPorts i).filter fun p => p.dir == .input && p.ty == .clock
    (cs.drop 1).flatMap (fun p => err .E009 p.pos "second clock input") ++
    ((itemPorts i).filter fun p => p.dir == .output && p.ty == .clock).flatMap
      (fun p => err .E009 p.pos "clock output") ++
    match i with
    | .extern _ => []
    | .module m => m.body.flatMap fun s =>
      (valueExprs d m s).flatMap (foldExpr (clocksExpr d m))

def e011 (d : Design) : List Error :=
  (modules d).flatMap fun m => m.body.flatMap fun s => match s with
    | .inst pos _ child xs => match findItem d child with
      | none => []
      | some i => (itemPorts i).flatMap fun p =>
        if p.dir != .input then [] else
        let connections := xs.filter (·.1 == p.name)
        require (connections.length == 1) .E011 pos "input must connect exactly once" ++
        if p.ty == .clock then connections.flatMap fun (_, e) =>
          require (directClock m e) .E011 (exprPos e) "expected a parent clock input"
        else []
    | _ => []

private def dependencyInputs (d : Design) (x : Extern) (dep : Dep) : List Error :=
  let entries := dep.inputs.zipIdx
  entries.flatMap fun (n, index) =>
    require (!(dep.inputs.take index).contains n)
      .E013 (d.locate dep.pos [2, index]) "duplicate dependency input" ++
    require (x.ports.any fun p => p.name == n && p.dir == .input && p.ty != .clock)
      .E013 (d.locate dep.pos [2, index]) "dependency must be a bits input"

def e013 (d : Design) : List Error :=
  d.items.flatMap fun i => match i with
    | .module _ => []
    | .extern x =>
      x.ports.flatMap (fun p => if p.dir == .output then
        let entries := x.deps.filter (·.output == p.name)
        match entries with
        | [] => err .E013 p.pos "missing dependency entry"
        | _ :: second :: _ => err .E013 second.pos "duplicate dependency entry"
        | [_] => []
        else []) ++
      x.deps.flatMap fun dep =>
        require (x.ports.any fun p => p.dir == .output && p.name == dep.output)
          .E013 (d.locate dep.pos [1]) "dependency target must be an output" ++
        dependencyInputs d x dep

/-! Width inference fails at a bad operand rule and thus suppresses outer errors. -/
def inferWidth (d : Design) (m : Module) : Expr → Option Nat
  | .ref _ n => do
    let .bits w ← valueTy m n | none
    pure w
  | .port _ i n => do
    let p ← instancePort d m i n
    let .bits w := p.ty | none
    pure w
  | .const _ w _ => some w
  | .un _ _ a => inferWidth d m a
  | .bin _ op a b => do
    let wa ← inferWidth d m a
    let wb ← inferWidth d m b
    if op == .concat then if wa + wb ≤ 65536 then some (wa + wb) else none
    else if wa == wb then some wa else none
  | .icmp _ _ a b => do
    let wa ← inferWidth d m a
    let wb ← inferWidth d m b
    if wa == wb then some 1 else none
  | .mux _ c a b => do
    let wc ← inferWidth d m c
    let wa ← inferWidth d m a
    let wb ← inferWidth d m b
    if wc == 1 && wa == wb then some wa else none
  | .extract _ a lo w => do
    let wa ← inferWidth d m a
    if lo + w ≤ wa then some w else none
  | .replicate _ a k => do
    let wa ← inferWidth d m a
    if wa * k ≤ 65536 then some (wa * k) else none
  | .read _ n a => do
    let (w, depth) ← memory m n
    let wa ← inferWidth d m a
    if wa == addressWidth depth then some w else none

private def operandErrors (d : Design) (m : Module) (e : Expr) : List Error :=
  if (children e).all (fun a => (inferWidth d m a).isSome) &&
      (inferWidth d m e).isNone then err .E004 (exprPos e) "operand width mismatch" else []

private def targetWidth (d : Design) (m : Module) (p : Pos) (w : Nat)
    (e : Expr) : List Error :=
  match inferWidth d m e with
  | some actual => require (actual == w) .E004 p "target width mismatch"
  | none => []

def e004 (d : Design) : List Error :=
  (modules d).flatMap fun m => m.body.flatMap fun s =>
    (valueExprs d m s).flatMap (foldExpr (operandErrors d m)) ++
    match s with
    | .let_ p _ w e => targetWidth d m p w e
    | .next p n e | .assign p n e => match valueTy m n with
      | some (.bits w) => targetWidth d m p w e | _ => []
    | .reg p _ w _ reset => reset.toList.flatMap fun r =>
      if [r.signal, r.value].all (fun e => (inferWidth d m e).isSome) then
        let pos := d.locate p [4]
        targetWidth d m pos 1 r.signal ++ targetWidth d m pos w r.value
      else []
    | .write p n _ a v en => match memory m n with
      | some (w, depth) =>
        if [a, v, en].all (fun e => (inferWidth d m e).isSome) then
          targetWidth d m p (addressWidth depth) a ++
            targetWidth d m p w v ++ targetWidth d m p 1 en
        else []
      | none => []
    | .inst p _ child xs => match findItem d child with
      | none => []
      | some i => xs.zipIdx.flatMap fun ((n, e), index) =>
        match (itemPorts i).find? (·.name == n) with
        | some port => match port.ty with
          | .bits w => targetWidth d m (d.locate p [3 + index]) w e | _ => []
        | none => []
    | _ => []

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

private def reachable [BEq α] (g : List (α × List α)) : Nat → List α → α → Bool
  | 0, _, _ => false
  | fuel + 1, ns, target => ns.contains target ||
      reachable g fuel (ns.flatMap fun n => (g.lookup n).getD []) target

def e010 (d : Design) : List Error :=
  let g := (modules d).map fun m => (m.name, m.body.filterMap fun s => match s with
    | .inst _ _ child _ => some child | _ => none)
  (modules d).flatMap fun m => m.body.flatMap fun s => match s with
    | .inst p _ child _ => if reachable g (g.length + 1) [child] m.name then
        err .E010 p "instance cycle" else []
    | _ => []

abbrev inferDeps := Typed.designDeps

private def nodePos (m : Module) (n : Deps.Node) : Pos :=
  ((m.body.find? fun s => match n, s with
    | .name n, .let_ _ k _ _ | .name n, .assign _ k _ => n == k
    | .port n _, .inst _ k _ _ => n == k
    | _, _ => false).map stmtPos).getD m.pos

def e008 (d : Design) : List Error :=
  (modules d).flatMap fun m =>
    let g := Deps.graph m (inferDeps d (d.items.length + 1))
    g.flatMap fun (n, edges) =>
      if reachable g (g.length + 1) edges n then
        err .E008 (nodePos m n) "combinational cycle" else []

/-! Syntax errors precede these nine semantic passes. -/
def errors (d : Design) : List (List Error) :=
  [e002 d, e003 d, e005 d, e009 d, e011 d ++ e013 d, e004 d,
    e006 d ++ e007 d ++ e012 d, e010 d, e008 d]

end Silicon.Core.Check

namespace Silicon.Core

/-! Each conjunct states one semantic rule from the core IR specification. -/
def WellFormed (d : Design) : Prop :=
  Check.e002 d = [] ∧ Check.e003 d = [] ∧ Check.e004 d = [] ∧ Check.e005 d = [] ∧
  Check.e006 d = [] ∧ Check.e007 d = [] ∧ Check.e008 d = [] ∧ Check.e009 d = [] ∧
  Check.e010 d = [] ∧ Check.e011 d = [] ∧ Check.e012 d = [] ∧ Check.e013 d = []

instance (d : Design) : Decidable (WellFormed d) :=
  inferInstanceAs (Decidable
    (Check.e002 d = [] ∧ Check.e003 d = [] ∧ Check.e004 d = [] ∧ Check.e005 d = [] ∧
    Check.e006 d = [] ∧ Check.e007 d = [] ∧ Check.e008 d = [] ∧ Check.e009 d = [] ∧
    Check.e010 d = [] ∧ Check.e011 d = [] ∧ Check.e012 d = [] ∧ Check.e013 d = []))

namespace Check

def earlier (a b : Error) : Bool :=
  a.pos.line < b.pos.line || (a.pos.line == b.pos.line && a.pos.col < b.pos.col)

def lowest : List Error → Option Error
  | [] => none
  | e :: es => some (es.foldl (fun a b => if earlier b a then b else a) e)

def firstError : List (List Error) → Option Error
  | [] => none
  | es :: rest => (lowest es).or (firstError rest)

theorem firstError_none (passes : List (List Error)) :
    firstError passes = none ↔ ∀ es ∈ passes, es = [] := by
  induction passes with
  | nil => simp [firstError]
  | cons es rest ih =>
    cases es <;> simp [firstError, lowest, Option.or, ih]

theorem no_errors (d : Design) : firstError (errors d) = none ↔ WellFormed d := by
  rw [firstError_none]
  simp only [errors, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, List.append_eq_nil_iff, WellFormed]
  simp [and_assoc, and_left_comm, and_comm]

end Check

/-! Diagnostics finish before elaboration constructs the typed design. -/
def check (d : Design) : Except Error Typed.Design :=
  match Check.firstError (Check.errors d) with
  | some e => .error e
  | none => match Typed.elaborateDesign d with
    | some t => .ok t
    | none => .error ⟨.E004, d.topPos, "typed elaboration failed"⟩

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
    next => contradiction

end Silicon.Core
