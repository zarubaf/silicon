import Silicon.Core.Deps

/-!
Typed expressions separate clocks from data. Each reference carries its lookup proof.
The context contains the values, clock inputs, and memories of one module.
-/
namespace Silicon.Core.Typed

inductive Kind where
  | value (ty : Ty)
  | clock
  | memory (width depth : Nat)
  deriving DecidableEq, BEq, Repr

abbrev Ctx := List (Deps.Node × Kind)

def addressWidth (depth : Nat) : Nat := max 1 (Nat.log2 (depth - 1) + 1)

/-! Only a clock input can construct an expression of clock type. -/
inductive Expr (ctx : Ctx) : Ty → Type where
  | ref (pos : Pos) (node : Deps.Node)
      (found : ctx.lookup node = some (.value (.bits width))) : Expr ctx (.bits width)
  | clock (pos : Pos) (name : String)
      (found : ctx.lookup (.name name) = some .clock) : Expr ctx .clock
  | const (pos : Pos) (width value : Nat) : Expr ctx (.bits width)
  | un (pos : Pos) (op : UnOp) (arg : Expr ctx (.bits width)) : Expr ctx (.bits width)
  | bin (pos : Pos) (op : BinOp) (ordinary : op ≠ .concat)
      (lhs rhs : Expr ctx (.bits width)) : Expr ctx (.bits width)
  | concat (pos : Pos) (lhs : Expr ctx (.bits a)) (rhs : Expr ctx (.bits b))
      (bound : a + b ≤ 65536) : Expr ctx (.bits (a + b))
  | icmp (pos : Pos) (pred : Pred) (lhs rhs : Expr ctx (.bits width)) : Expr ctx (.bits 1)
  | mux (pos : Pos) (cond : Expr ctx (.bits 1))
      (yes no : Expr ctx (.bits width)) : Expr ctx (.bits width)
  | extract (pos : Pos) (arg : Expr ctx (.bits width)) (lo count : Nat)
      (bound : lo + count ≤ width) : Expr ctx (.bits count)
  | replicate (pos : Pos) (arg : Expr ctx (.bits width)) (count : Nat)
      (bound : width * count ≤ 65536) : Expr ctx (.bits (width * count))
  | read (pos : Pos) (name : String)
      (found : ctx.lookup (.name name) = some (.memory width depth))
      (addr : Expr ctx (.bits (addressWidth depth))) : Expr ctx (.bits width)

/-! Erasure keeps all source positions for diagnostics and round trips. -/
def Expr.erase : Expr ctx ty → Core.Expr
  | .ref p (.name n) _ => .ref p n
  | .ref p (.port i n) _ => .port p i n
  | .clock p n _ => .ref p n
  | .const p w v => .const p w v
  | .un p o a => .un p o a.erase
  | .bin p o _ a b => .bin p o a.erase b.erase
  | .concat p a b _ => .bin p .concat a.erase b.erase
  | .icmp p o a b => .icmp p o a.erase b.erase
  | .mux p c a b => .mux p c.erase a.erase b.erase
  | .extract p a l n _ => .extract p a.erase l n
  | .replicate p a n _ => .replicate p a.erase n
  | .read p n _ a => .read p n a.erase

abbrev Term (ctx : Ctx) := (ty : Ty) × Expr ctx ty

def castTerm (t : Term ctx) (ty : Ty) : Option (Expr ctx ty) :=
  if h : t.1 = ty then some (h ▸ t.2) else none

def infer (ctx : Ctx) : Core.Expr → Option (Term ctx)
  | .ref p n => match h : ctx.lookup (.name n) with
    | some (.value (.bits w)) => some ⟨.bits w, .ref p (.name n) h⟩
    | some .clock => some ⟨.clock, .clock p n h⟩
    | _ => none
  | .port p i n => match h : ctx.lookup (.port i n) with
    | some (.value (.bits w)) => some ⟨.bits w, .ref p (.port i n) h⟩
    | _ => none
  | .const p w v => some ⟨.bits w, .const p w v⟩
  | .un p o a => do
    let ⟨.bits w, a⟩ ← infer ctx a | none
    return ⟨.bits w, .un p o a⟩
  | .bin p o a b => do
    let ⟨.bits wa, a⟩ ← infer ctx a | none
    let ⟨.bits wb, b⟩ ← infer ctx b | none
    if ho : o = .concat then
      if hb : wa + wb ≤ 65536 then return ⟨.bits (wa + wb), .concat p a b hb⟩
      else none
    else if hw : wb = wa then return ⟨.bits wa, .bin p o ho a (hw ▸ b)⟩
    else none
  | .icmp p o a b => do
    let ⟨.bits wa, a⟩ ← infer ctx a | none
    let ⟨.bits wb, b⟩ ← infer ctx b | none
    if hw : wb = wa then return ⟨.bits 1, .icmp p o a (hw ▸ b)⟩ else none
  | .mux p c a b => do
    let c ← infer ctx c >>= (castTerm · (.bits 1))
    let ⟨.bits wa, a⟩ ← infer ctx a | none
    let b ← infer ctx b >>= (castTerm · (.bits wa))
    return ⟨.bits wa, .mux p c a b⟩
  | .extract p a lo count => do
    let ⟨.bits w, a⟩ ← infer ctx a | none
    if h : lo + count ≤ w then return ⟨.bits count, .extract p a lo count h⟩ else none
  | .replicate p a count => do
    let ⟨.bits w, a⟩ ← infer ctx a | none
    if hb : w * count ≤ 65536 then return ⟨.bits (w * count), .replicate p a count hb⟩
    else none
  | .read p n a => do
    match h : ctx.lookup (.name n) with
    | some (.memory w depth) =>
      let a ← infer ctx a >>= (castTerm · (.bits (addressWidth depth)))
      return ⟨.bits w, .read p n h a⟩
    | _ => none

/-! Type casts preserve syntax because they change only the type index. -/
theorem castTerm_erase (t : Term ctx) (ty : Ty) (e : Expr ctx ty)
    (h : castTerm t ty = some e) : e.erase = t.2.erase := by
  unfold castTerm at h
  split at h
  next ht => cases ht; cases h; rfl
  next => contradiction

/-! Context construction exposes only data outputs of child instances. -/
def itemName : Item → String
  | .module m => m.name
  | .extern e => e.name

def itemPorts : Item → List Port
  | .module m => m.ports
  | .extern e => e.ports

def portsOf (d : Core.Design) (name : String) : List Port :=
  ((d.items.find? fun i => itemName i == name).map itemPorts).getD []

def context (d : Core.Design) (m : Core.Module) : Ctx :=
  (m.ports.map fun p => (.name p.name,
    if p.ty == .clock && p.dir == .input then .clock else .value p.ty)) ++
  m.body.flatMap fun s => match s with
    | .let_ _ n w _ | .reg _ n w _ _ => [(.name n, .value (.bits w))]
    | .mem _ n w depth _ => [(.name n, .memory w depth)]
    | .inst _ n child _ => (portsOf d child).filterMap fun p =>
      if p.dir == .output then some (.port n p.name, .value p.ty) else none
    | _ => []

def valueTy (ctx : Ctx) (n : String) : Ty :=
  match ctx.lookup (.name n) with
  | some (.value ty) => ty
  | some .clock => .clock
  | _ => .bits 0

/-! Each request gives the type required by its statement or child port. -/
def requests (d : Core.Design) (m : Core.Module) : List (Core.Expr × Ty) :=
  let ctx := context d m
  m.body.flatMap fun s => match s with
    | .let_ _ _ w e => [(e, .bits w)]
    | .next _ n e | .assign _ n e => [(e, valueTy ctx n)]
    | .reg _ _ w _ reset => reset.toList.flatMap fun r =>
      [(r.signal, .bits 1), (r.value, .bits w)]
    | .write _ n _ a v en => match ctx.lookup (.name n) with
      | some (.memory w depth) =>
        [(a, .bits (addressWidth depth)), (v, .bits w), (en, .bits 1)]
      | _ => []
    | .inst _ _ child inputs => inputs.map fun (n, e) =>
      (e, (((portsOf d child).find? fun p => p.name == n).map Port.ty).getD (.bits 0))
    | _ => []

/-! The list index fixes both the syntax and the type of every expression. -/
inductive Expressions (ctx : Ctx) : List (Core.Expr × Ty) → Type where
  | nil : Expressions ctx []
  | cons (expr : Expr ctx ty) (erases : expr.erase = raw)
      (rest : Expressions ctx tail) : Expressions ctx ((raw, ty) :: tail)

def expressions (ctx : Ctx) : (rs : List (Core.Expr × Ty)) → Option (Expressions ctx rs)
  | [] => some .nil
  | (raw, ty) :: tail => do
    let t ← infer ctx raw
    let e ← castTerm t ty
    if h : e.erase = raw then
      let rest ← expressions ctx tail
      return .cons e h rest
    else none

abbrev Graph := List (Deps.Node × List Deps.Node)
abbrev Ranks := List (Deps.Node × Nat)

def rank (r : Ranks) (n : Deps.Node) : Nat := (r.lookup n).getD 0

def graphRanks (g : Graph) : Nat → Ranks
  | 0 => []
  | fuel + 1 =>
    let previous := graphRanks g fuel
    g.map fun (n, deps) => (n, 1 + (deps.map (rank previous)).foldl max 0)

/-! A decreasing rank on every read edge rules out a combinational cycle. -/
def Ranked (g : Graph) (r : Ranks) : Prop :=
  ∀ row ∈ g, ∀ dep ∈ row.2, rank r dep < rank r row.1

instance (g : Graph) (r : Ranks) : Decidable (Ranked g r) :=
  inferInstanceAs (Decidable (∀ row ∈ g, ∀ dep ∈ row.2, rank r dep < rank r row.1))

/-! Extern contracts keep output and input port order. -/
def externDeps (e : Extern) : Deps :=
  e.ports.filterMap fun p =>
    if p.dir == .output then
      let names := ((e.deps.find? fun dep => dep.output == p.name).map Dep.inputs).getD []
      some (p.name, e.ports.filterMap fun q =>
        if q.dir == .input && names.contains q.name then some q.name else none)
    else none

def designDeps (d : Core.Design) : Nat → String → Option Deps
  | 0, _ => none
  | fuel + 1, name => do
    let i ← d.items.find? fun i => itemName i == name
    match i with
    | .extern e => pure (externDeps e)
    | .module m => pure (Deps.infer m (designDeps d fuel))

structure Module (design : Core.Design) where
  source : Core.Module
  terms : Expressions (context design source) (requests design source)
  ranks : Ranks
  acyclic : Ranked (Deps.graph source (designDeps design (design.items.length + 1))) ranks

def childNames (m : Core.Module) : List String :=
  m.body.filterMap fun s => match s with
    | .inst _ _ child _ => some child
    | _ => none

def externNames (d : Core.Design) : List String :=
  d.items.filterMap fun i => match i with | .extern e => some e.name | _ => none

def modules (d : Core.Design) : List Core.Module :=
  d.items.filterMap fun i => match i with | .module m => some m | _ => none

def ordered (seen : List String) : List Core.Module → Bool
  | [] => true
  | m :: rest => (childNames m).all seen.contains && ordered (m.name :: seen) rest

/-! A design keeps a complete module list with each child before its parent. -/
structure Design where
  source : Core.Design
  bodies : List (Module source)
  coverage : (bodies.map (·.source)).Perm (modules source)
  hierarchy : ordered (externNames source) (bodies.map (·.source)) = true

def Design.erase (d : Design) : Core.Design := d.source

def orderModules : Nat → List String → List Core.Module → Option (List Core.Module)
  | 0, _, pending => if pending.isEmpty then some [] else none
  | fuel + 1, seen, pending =>
    if pending.isEmpty then some [] else do
      let m ← pending.find? fun m => (childNames m).all seen.contains
      let rest ← orderModules fuel (m.name :: seen) (pending.erase m)
      return m :: rest

/-! Each module carries its typed expressions and a rank proof for its graph. -/
def elaborateModules (d : Core.Design) : List Core.Module → Option (List (Module d))
  | [] => some []
  | m :: rest => do
    let terms ← expressions (context d m) (requests d m)
    let graph := Deps.graph m (designDeps d (d.items.length + 1))
    let ranks := graphRanks graph graph.length
    if h : Ranked graph ranks then
      let body : Module d := ⟨m, terms, ranks, h⟩
      let rest ← elaborateModules d rest
      return body :: rest
    else none

def elaborateDesign (d : Core.Design) : Option Design := do
  let sorted ← orderModules (modules d).length (externNames d) (modules d)
  let bodies ← elaborateModules d sorted
  if hc : (bodies.map (·.source)).Perm (modules d) then
    if hh : ordered (externNames d) (bodies.map (·.source)) = true then
      some ⟨d, bodies, hc, hh⟩
    else none
  else none

theorem elaborateDesign_erase (d : Core.Design) (t : Design)
    (h : elaborateDesign d = some t) : t.erase = d := by
  simp only [elaborateDesign, bind, Option.bind_eq_some_iff] at h
  obtain ⟨sorted, _, bodies, _, h⟩ := h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rfl

end Silicon.Core.Typed
