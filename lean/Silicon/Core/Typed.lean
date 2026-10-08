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

theorem infer_erase (ctx : Ctx) (raw : Core.Expr) (t : Term ctx)
    (h : infer ctx raw = some t) : t.2.erase = raw := by
  induction raw generalizing t with
  | ref p n =>
    simp only [infer] at h
    split at h <;> try contradiction
    all_goals cases h; rfl
  | port p i n =>
    simp only [infer] at h
    split at h <;> try contradiction
    cases h
    rfl
  | const p w v => cases h; rfl
  | un p o a ih =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    cases h
    simp only [Expr.erase, ih _ hx]
  | bin p o a b ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    split at h <;> try contradiction
    split at h
    next ho =>
      split at h <;> try contradiction
      cases h
      simp only [Expr.erase, ia _ hx, ib _ hy, ho]
    next ho =>
      split at h <;> try contradiction
      next hw =>
        cases hw
        cases h
        simp only [Expr.erase, ia _ hx, ib _ hy]
  | icmp p o a b ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    split at h <;> try contradiction
    split at h <;> try contradiction
    next hw =>
      cases hw
      cases h
      simp only [Expr.erase, ia _ hx, ib _ hy]
  | mux p c a b ic ia ib =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, ⟨tc, hc, hx⟩, y, hy, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨z, ⟨tb, hb, hz⟩, h⟩ := h
    cases h
    simp only [Expr.erase, castTerm_erase _ _ _ hx, castTerm_erase _ _ _ hz,
      ic _ hc, ia _ hy, ib _ hb]
  | extract p a lo count ih =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    simp only [Expr.erase, ih _ hx]
  | replicate p a count ih =>
    simp only [infer, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    simp only [Expr.erase, ih _ hx]
  | read p n a ih =>
    simp only [infer] at h
    split at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, ⟨ta, ha, hx⟩, h⟩ := h
    cases h
    simp only [Expr.erase, castTerm_erase _ _ _ hx, ih _ ha]

theorem infer_complete (e : Expr ctx ty) : infer ctx e.erase = some ⟨ty, e⟩ := by
  induction e with
  | ref p node found =>
    cases node <;> simp only [Expr.erase, infer] <;> split
    all_goals first
      | (rename_i h; rw [found] at h; cases h <;> rfl)
      | (simp_all)
  | clock p n found =>
    simp only [Expr.erase, infer]
    split
    all_goals first
      | (rename_i h; rw [found] at h; cases h <;> rfl)
      | (simp_all)
  | const p w v => rfl
  | un p o a ih => simp [Expr.erase, infer, ih]
  | bin p o ho a b ia ib => simp [Expr.erase, infer, ia, ib, ho]
  | concat p a b hb ia ib => simp [Expr.erase, infer, ia, ib, hb]
  | icmp p o a b ia ib => simp [Expr.erase, infer, ia, ib]
  | mux p c a b ic ia ib => simp [Expr.erase, infer, ic, ia, ib, castTerm]
  | extract p a lo count hb ih => simp [Expr.erase, infer, ih, hb]
  | replicate p a count hb ih => simp [Expr.erase, infer, ih, hb]
  | read p n found a ih =>
    simp only [Expr.erase, infer]
    split
    · rename_i w depth h
      rw [found] at h
      cases h
      simp [ih, castTerm]
    · simp_all

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

def valueTy (ctx : Ctx) (n : String) : Option Ty :=
  match ctx.lookup (.name n) with
  | some (.value ty) => some ty
  | some .clock => some .clock
  | _ => none

/-! A statement stores typed operands. Erasure rebuilds each source form. -/
structure Reset (ctx : Ctx) (width : Nat) where
  kind : ResetKind
  signal : Expr ctx (.bits 1)
  value : Expr ctx (.bits width)

def Reset.erase (r : Reset ctx width) : Core.Reset :=
  ⟨r.kind, r.signal.erase, r.value.erase⟩

inductive Stmt (ctx : Ctx) (ports : String → List Port) where
  | let_ (pos : Pos) (name : String) (width : Nat) (value : Expr ctx (.bits width))
  | reg (pos : Pos) (name : String) (width : Nat) (clock : String)
      (reset : Option (Reset ctx width))
  | next (pos : Pos) (name : String) (width : Nat)
      (target : valueTy ctx name = some (.bits width)) (value : Expr ctx (.bits width))
  | mem (pos : Pos) (name : String) (width depth : Nat) (clock : String)
  | write (pos : Pos) (name : String) (port width depth : Nat)
      (target : ctx.lookup (.name name) = some (.memory width depth))
      (addr : Expr ctx (.bits (addressWidth depth))) (data : Expr ctx (.bits width))
      (enable : Expr ctx (.bits 1))
  | inst (pos : Pos) (name module : String)
      (inputs : List ((p : {p : Port // p ∈ ports module}) × Expr ctx p.val.ty))
  | assign (pos : Pos) (name : String) (width : Nat)
      (target : valueTy ctx name = some (.bits width)) (value : Expr ctx (.bits width))

def Stmt.erase : Stmt ctx ports → Core.Stmt
  | .let_ p n w e => .let_ p n w e.erase
  | .reg p n w c r => .reg p n w c (r.map Reset.erase)
  | .next p n _ _ e => .next p n e.erase
  | .mem p n w depth c => .mem p n w depth c
  | .write p n index _ _ _ a v en => .write p n index a.erase v.erase en.erase
  | .inst p n child xs => .inst p n child (xs.map fun input => (input.1.val.name, input.2.erase))
  | .assign p n _ _ e => .assign p n e.erase

def expression (ctx : Ctx) (raw : Core.Expr) (ty : Ty) : Option (Expr ctx ty) :=
  infer ctx raw >>= (castTerm · ty)

def statement (d : Core.Design) (ctx : Ctx) : Core.Stmt → Option (Stmt ctx (portsOf d))
  | .let_ p n w e => return .let_ p n w (← expression ctx e (.bits w))
  | .reg p n w c r => do
    let reset ← r.mapM fun r => do
      let signal ← expression ctx r.signal (.bits 1)
      let value ← expression ctx r.value (.bits w)
      return (⟨r.kind, signal, value⟩ : Reset ctx w)
    return .reg p n w c reset
  | .next p n e => do
    match h : valueTy ctx n with
    | some (.bits w) => return .next p n w h (← expression ctx e (.bits w))
    | _ => none
  | .mem p n w depth c => some (.mem p n w depth c)
  | .write p n index a v en => do
    match h : ctx.lookup (.name n) with
    | some (.memory w depth) =>
      let addr ← expression ctx a (.bits (addressWidth depth))
      let data ← expression ctx v (.bits w)
      let enable ← expression ctx en (.bits 1)
      return .write p n index w depth h addr data enable
    | _ => none
  | .inst p n child xs => do
    let inputs ← xs.mapM fun (k, raw) => do
      let port ← (portsOf d child).attach.find? (·.val.name == k)
      let e ← expression ctx raw port.val.ty
      return (⟨port, e⟩ : (p : {p : Port // p ∈ portsOf d child}) × Expr ctx p.val.ty)
    return .inst p n child inputs
  | .assign p n e => do
    match h : valueTy ctx n with
    | some (.bits w) => return .assign p n w h (← expression ctx e (.bits w))
    | _ => none



def HasExpr (ctx : Ctx) (ty : Ty) (e : Core.Expr) : Prop :=
  ∃ t : Expr ctx ty, t.erase = e

def HasStmt (ctx : Ctx) (ports : String → List Port) (s : Core.Stmt) : Prop :=
  ∃ t : Stmt ctx ports, t.erase = s

theorem hasStmt_let (ctx : Ctx) (ports : String → List Port)
    (p : Pos) (n : String) (w : Nat) (e : Core.Expr) :
    HasStmt ctx ports (.let_ p n w e) ↔ HasExpr ctx (.bits w) e := by
  constructor
  · rintro ⟨t, h⟩
    cases t <;> cases h
    rename_i value
    exact ⟨value, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨.let_ p n w t, rfl⟩

theorem hasStmt_next (ctx : Ctx) (ports : String → List Port)
    (p : Pos) (n : String) (e : Core.Expr) :
    HasStmt ctx ports (.next p n e) ↔
      ∃ w, valueTy ctx n = some (.bits w) ∧ HasExpr ctx (.bits w) e := by
  constructor
  · rintro ⟨t, h⟩
    cases t <;> cases h
    rename_i w value target
    exact ⟨w, target, value, rfl⟩
  · rintro ⟨w, target, t, rfl⟩
    exact ⟨.next p n w target t, rfl⟩

theorem hasStmt_assign (ctx : Ctx) (ports : String → List Port)
    (p : Pos) (n : String) (e : Core.Expr) :
    HasStmt ctx ports (.assign p n e) ↔
      ∃ w, valueTy ctx n = some (.bits w) ∧ HasExpr ctx (.bits w) e := by
  constructor
  · rintro ⟨t, h⟩
    cases t <;> cases h
    rename_i w value target
    exact ⟨w, target, value, rfl⟩
  · rintro ⟨w, target, t, rfl⟩
    exact ⟨.assign p n w target t, rfl⟩

theorem hasStmt_mem (ctx : Ctx) (ports : String → List Port)
    (p : Pos) (n : String) (w depth : Nat) (clock : String) :
    HasStmt ctx ports (.mem p n w depth clock) := ⟨.mem p n w depth clock, rfl⟩

theorem hasStmt_write (ctx : Ctx) (ports : String → List Port)
    (p : Pos) (n : String) (index : Nat) (a v en : Core.Expr) :
    HasStmt ctx ports (.write p n index a v en) ↔
      ∃ w depth, ctx.lookup (.name n) = some (.memory w depth) ∧
        HasExpr ctx (.bits (addressWidth depth)) a ∧
        HasExpr ctx (.bits w) v ∧ HasExpr ctx (.bits 1) en := by
  constructor
  · rintro ⟨t, h⟩
    cases t <;> cases h
    rename_i w depth addr data enable target
    exact ⟨w, depth, target, ⟨addr, rfl⟩, ⟨data, rfl⟩, ⟨enable, rfl⟩⟩
  · rintro ⟨w, depth, target, ⟨addr, rfl⟩, ⟨data, rfl⟩, ⟨enable, rfl⟩⟩
    exact ⟨.write p n index w depth target addr data enable, rfl⟩
theorem hasReset (ctx : Ctx) (w : Nat) (r : Core.Reset) :
    (∃ t : Reset ctx w, t.erase = r) ↔
      HasExpr ctx (.bits 1) r.signal ∧ HasExpr ctx (.bits w) r.value := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t.signal, rfl⟩, ⟨t.value, rfl⟩⟩
  · rintro ⟨⟨signal, hs⟩, ⟨value, hv⟩⟩
    refine ⟨⟨r.kind, signal, value⟩, ?_⟩
    cases r
    simp_all [Reset.erase]

theorem hasStmt_reg (ctx : Ctx) (ports : String → List Port)
    (p : Pos) (n : String) (w : Nat) (clock : String) (r : Option Core.Reset) :
    HasStmt ctx ports (.reg p n w clock r) ↔
      ∀ reset ∈ r, HasExpr ctx (.bits 1) reset.signal ∧
        HasExpr ctx (.bits w) reset.value := by
  constructor
  · rintro ⟨t, h⟩
    cases t <;> cases h
    rename_i reset
    cases reset with
    | none => simp
    | some reset =>
      simp only [Option.map_some, Option.mem_some_iff]
      rintro _ rfl
      exact ⟨⟨reset.signal, rfl⟩, ⟨reset.value, rfl⟩⟩
  · intro h
    cases r with
    | none => exact ⟨.reg p n w clock none, rfl⟩
    | some r =>
      obtain ⟨t, ht⟩ := (hasReset ctx w r).mpr (h r rfl)
      exact ⟨.reg p n w clock (some t), by simp [Stmt.erase, ht]⟩

theorem hasInputs (ctx : Ctx) (ps : List Port) (xs : List (String × Core.Expr)) :
    (∃ ts : List ((p : {p : Port // p ∈ ps}) × Expr ctx p.val.ty),
      ts.map (fun x => (x.1.val.name, x.2.erase)) = xs) ↔
      ∀ x ∈ xs, ∃ p ∈ ps, p.name = x.1 ∧ HasExpr ctx p.ty x.2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    constructor
    · rintro ⟨ts, h⟩
      cases ts with
      | nil => simp at h
      | cons t ts =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨rfl, ht⟩ := h
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨⟨t.1.val, t.1.property, rfl, t.2, rfl⟩, ih.mp ⟨ts, ht⟩⟩
    · intro h
      obtain ⟨p, hp, hn, e, he⟩ := h x (by simp)
      obtain ⟨ts, hts⟩ := ih.mpr (fun y hy => h y (by simp [hy]))
      refine ⟨⟨⟨p, hp⟩, e⟩ :: ts, ?_⟩
      simp only [List.map_cons, hts, List.cons.injEq]
      exact ⟨Prod.ext hn he, trivial⟩

theorem hasStmt_inst (ctx : Ctx) (ports : String → List Port)
    (p : Pos) (n child : String) (xs : List (String × Core.Expr)) :
    HasStmt ctx ports (.inst p n child xs) ↔
      ∀ x ∈ xs, ∃ port ∈ ports child,
        port.name = x.1 ∧ HasExpr ctx port.ty x.2 := by
  rw [← hasInputs]
  constructor
  · rintro ⟨t, h⟩
    cases t <;> cases h
    exact ⟨_, rfl⟩
  · rintro ⟨ts, rfl⟩
    exact ⟨.inst p n child ts, rfl⟩
theorem hasExpr_clock (ctx : Ctx) (e : Core.Expr) :
    HasExpr ctx .clock e ↔
      ∃ p n, e = .ref p n ∧ ctx.lookup (.name n) = some .clock := by
  constructor
  · rintro ⟨t, rfl⟩
    cases t with
    | clock p n found => exact ⟨p, n, rfl, found⟩
  · rintro ⟨p, n, rfl, found⟩
    exact ⟨.clock p n found, rfl⟩

/-! State definitions own their typed updates. Indices retain the input layout. -/
structure Write (ctx : Ctx) (width depth : Nat) where
  index : Nat
  pos : Pos
  port : Nat
  addr : Expr ctx (.bits (addressWidth depth))
  data : Expr ctx (.bits width)
  enable : Expr ctx (.bits 1)

inductive Equation (ctx : Ctx) (ports : String → List Port) where
  | let_ (index : Nat) (pos : Pos) (name : String) (width : Nat)
      (value : Expr ctx (.bits width))
  | reg (index : Nat) (pos : Pos) (name : String) (width : Nat) (clock : String)
      (target : valueTy ctx name = some (.bits width)) (reset : Option (Reset ctx width))
      (nextIndex : Nat) (nextPos : Pos) (next : Expr ctx (.bits width))
  | mem (index : Nat) (pos : Pos) (name : String) (width depth : Nat) (clock : String)
      (target : ctx.lookup (.name name) = some (.memory width depth))
      (writes : List (Write ctx width depth))
  | inst (index : Nat) (pos : Pos) (name module : String)
      (inputs : List ((p : {p : Port // p ∈ ports module}) × Expr ctx p.val.ty))
  | assign (index : Nat) (pos : Pos) (name : String) (width : Nat)
      (target : valueTy ctx name = some (.bits width)) (value : Expr ctx (.bits width))

def Equation.parts : Equation ctx ports → List (Nat × Stmt ctx ports)
  | .let_ i p n w e => [(i, .let_ p n w e)]
  | .reg i p n w c h r ni np ne => [(i, .reg p n w c r), (ni, .next np n w h ne)]
  | .mem i p n w depth c h ws => (i, .mem p n w depth c) :: ws.map fun wr =>
      (wr.index, .write wr.pos n wr.port w depth h wr.addr wr.data wr.enable)
  | .inst i p n child xs => [(i, .inst p n child xs)]
  | .assign i p n w h e => [(i, .assign p n w h e)]

def equationsErase (body : List (Equation ctx ports)) : List Core.Stmt :=
  ((body.flatMap Equation.parts).mergeSort (fun a b => a.1 ≤ b.1)).map (fun s => s.2.erase)

def groupStatements (ctx : Ctx) (ports : String → List Port)
    (body : List (Stmt ctx ports)) : Option (List (Equation ctx ports)) := do
  let groups ← body.zipIdx.mapM fun (s, index) => match s with
    | .let_ p n w e => pure (some (.let_ index p n w e))
    | .reg p n w c r => do
      if h : valueTy ctx n = some (.bits w) then
        let nexts := body.zipIdx.filterMap fun (s, index) => match s with
          | .next p name width _ e =>
            if name == n then some (index, p, (⟨.bits width, e⟩ : Term ctx)) else none
          | _ => none
        let [(ni, np, ne)] := nexts | none
        let ne ← castTerm ne (.bits w)
        pure (some (.reg index p n w c h r ni np ne))
      else none
    | .mem p n w depth c => do
      if h : ctx.lookup (.name n) = some (.memory w depth) then
        let writes ← body.zipIdx.mapM fun (s, index) => match s with
          | .write p name port width size _ a v en => do
            if name == n then
              let a ← castTerm ⟨.bits (addressWidth size), a⟩ (.bits (addressWidth depth))
              let v ← castTerm ⟨.bits width, v⟩ (.bits w)
              pure (some (⟨index, p, port, a, v, en⟩ : Write ctx w depth))
            else pure none
          | _ => pure none
        pure (some (.mem index p n w depth c h (writes.filterMap id)))
      else none
    | .inst p n child xs => pure (some (.inst index p n child xs))
    | .assign p n w h e => pure (some (.assign index p n w h e))
    | .next .. | .write .. => pure none
  return groups.filterMap id

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

/-! Rank iteration stabilizes within one round per distinct graph key. -/
private theorem lookup_map_row (g : Graph) (hn : (g.map Prod.fst).Nodup)
    (f : Deps.Node × List Deps.Node → Nat) (row : Deps.Node × List Deps.Node)
    (hm : row ∈ g) : (g.map fun x => (x.1, f x)).lookup row.1 = some (f row) := by
  induction g with
  | nil => simp at hm
  | cons a g ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp
    · have ne : row.1 ≠ a.1 := by
        intro h
        apply hn.1
        exact List.mem_map.mpr ⟨row, hm, h⟩
      have hb : (row.1 == a.1) = false := beq_eq_false_iff_ne.mpr ne
      simp [List.lookup_cons, hb, ih hn.2 hm]

private theorem rank_succ_row (g : Graph) (hn : (g.map Prod.fst).Nodup)
    (row : Deps.Node × List Deps.Node) (hm : row ∈ g) (f : Nat) :
    rank (graphRanks g (f+1)) row.1 =
      1 + (row.2.map (rank (graphRanks g f))).foldl max 0 := by
  simp only [rank, graphRanks]
  rw [lookup_map_row g hn _ row hm]
  rfl

private theorem rank_absent (g : Graph) (n : Deps.Node)
    (h : n ∉ g.map Prod.fst) (f : Nat) : rank (graphRanks g f) n = 0 := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [rank, graphRanks]
    have hn : (g.map fun (k, ds) =>
        (k, 1 + (ds.map (rank (graphRanks g f))).foldl max 0)).lookup n = none := by
      rw [List.lookup_eq_none_iff]
      intro k hm
      rcases List.mem_map.mp hm with ⟨⟨k',ds⟩, hmem, he⟩
      cases he
      simp only [bne_iff_ne]
      intro he
      apply h
      exact List.mem_map.mpr ⟨(k',ds), hmem, he.symm⟩
    rw [hn]
    rfl

private theorem max_mem (xs : List Nat) (n : Nat) (h : n ∈ xs) (base : Nat) :
    n ≤ xs.foldl max base := by
  induction xs generalizing base with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldl_cons]
    rcases h with rfl | h
    · have aux : ∀ (ys : List Nat) (b : Nat), b ≤ ys.foldl max b := by
        intro ys
        induction ys with
        | nil => simp
        | cons a ys ih =>
          intro b
          exact Nat.le_trans (Nat.le_max_left _ _) (ih (max b a))
      exact Nat.le_trans (Nat.le_max_right _ _) (aux xs _)
    · exact ih h _

private theorem ranks_stable (g : Graph) (hn : (g.map Prod.fst).Nodup)
    (q : Deps.Node → Nat)
    (pos : ∀ n ∈ g.map Prod.fst, 0 < q n)
    (edges : ∀ row ∈ g, ∀ dep ∈ row.2, q dep < q row.1) :
    ∀ f n, q n ≤ f → rank (graphRanks g (f+1)) n = rank (graphRanks g f) n := by
  intro f
  induction f with
  | zero =>
    intro n h
    have absent : n ∉ g.map Prod.fst := by
      intro hm
      have := pos n hm
      omega
    rw [rank_absent g n absent, rank_absent g n absent]
  | succ f ih =>
    intro n h
    by_cases hm : n ∈ g.map Prod.fst
    · rcases List.mem_map.mp hm with ⟨row, hr, rfl⟩
      rw [rank_succ_row g hn row hr, rank_succ_row g hn row hr]
      congr 2
      apply List.map_congr_left
      intro dep hd
      apply ih
      have := edges row hr dep hd
      omega
    · rw [rank_absent g n hm, rank_absent g n hm]

private theorem ranks_complete_bounded (g : Graph) (hn : (g.map Prod.fst).Nodup)
    (q : Deps.Node → Nat) (bound : Nat)
    (pos : ∀ n ∈ g.map Prod.fst, 0 < q n)
    (bounded : ∀ n ∈ g.map Prod.fst, q n ≤ bound)
    (edges : ∀ row ∈ g, ∀ dep ∈ row.2, q dep < q row.1) :
    Ranked g (graphRanks g bound) := by
  intro row hr dep hd
  have hm : row.1 ∈ g.map Prod.fst := List.mem_map.mpr ⟨row, hr, rfl⟩
  have hp := pos row.1 hm
  have hb := bounded row.1 hm
  have he := edges row hr dep hd
  cases bound with
  | zero => omega
  | succ b =>
    rw [rank_succ_row g hn row hr]
    rw [ranks_stable g hn q pos edges b dep (by omega)]
    have hh := max_mem (row.2.map (rank (graphRanks g b)))
      (rank (graphRanks g b) dep) (List.mem_map.mpr ⟨dep, hd, rfl⟩) 0
    omega

theorem countP_strict {α : Type} (xs : List α) (p q : α → Bool)
    (mono : ∀ x ∈ xs, p x = true → q x = true)
    (extra : ∃ x ∈ xs, p x = false ∧ q x = true) : xs.countP p < xs.countP q := by
  induction xs with
  | nil => simp at extra
  | cons a xs ih =>
    have mt : ∀ x ∈ xs, p x = true → q x = true := by
      intro x hx
      exact mono x (List.mem_cons_of_mem a hx)
    have le := List.countP_mono_left mt
    rcases extra with ⟨x, hx, hp, hq⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [hp, hq]
      omega
    · have lt := ih mt ⟨x, hx, hp, hq⟩
      have ma := mono a (List.mem_cons_self ..)
      cases ha : p a <;> cases hb : q a <;> simp_all <;> omega

private def compressed (g : Graph) (r : Ranks) (n : Deps.Node) : Nat :=
   if n ∈ g.map Prod.fst then
     g.countP fun row => decide (rank r row.1 ≤ rank r n)
   else 0

private theorem compressed_pos (g : Graph) (r : Ranks) (n : Deps.Node)
    (hm : n ∈ g.map Prod.fst) : 0 < compressed g r n := by
  simp only [compressed, ite_eq_left hm]
  rw [List.countP_pos_iff]
  rcases List.mem_map.mp hm with ⟨row, hr, rfl⟩
  exact ⟨row, hr, by simp⟩

private theorem compressed_bound (g : Graph) (r : Ranks) (n : Deps.Node) :
    compressed g r n ≤ g.length := by
  unfold compressed
  split
  · exact List.countP_le_length
  · exact Nat.zero_le _

private theorem compressed_edges (g : Graph) (r : Ranks) (h : Ranked g r)
    (row : Deps.Node × List Deps.Node) (hr : row ∈ g) (dep : Deps.Node)
    (hd : dep ∈ row.2) : compressed g r dep < compressed g r row.1 := by
  have hm : row.1 ∈ g.map Prod.fst := List.mem_map.mpr ⟨row, hr, rfl⟩
  have he := h row hr dep hd
  by_cases hmdep : dep ∈ g.map Prod.fst
  · simp only [compressed, ite_eq_left hm, ite_eq_left hmdep]
    apply countP_strict
    · intro x _ hx
      simp only [decide_eq_true_eq] at hx ⊢
      omega
    · exact ⟨row, hr, by simp; omega, by simp⟩
  · simpa only [compressed, ite_eq_right hmdep] using compressed_pos g r row.1 hm

theorem graphRanks_complete (g : Graph) (hn : (g.map Prod.fst).Nodup)
    (h : ∃ r, Ranked g r) : Ranked g (graphRanks g g.length) := by
  rcases h with ⟨r, hr⟩
  apply ranks_complete_bounded g hn (compressed g r) g.length
  · exact compressed_pos g r
  · intro n _
    exact compressed_bound g r n
  · exact compressed_edges g r hr

theorem graphRanks_iff (g : Graph) (hn : (g.map Prod.fst).Nodup) :
    Ranked g (graphRanks g g.length) ↔ ∃ r, Ranked g r :=
  ⟨fun h => ⟨_, h⟩, graphRanks_complete g hn⟩

/-! Extern contracts keep output and input port order. -/
def externDeps (e : Extern) : Deps :=
  e.ports.filterMap fun p =>
    if p.dir == .output then
      let names := ((e.deps.find? fun dep => dep.output == p.name).map Dep.inputs).getD []
      some (p.name, e.ports.filterMap fun q =>
        if q.dir == .input && names.contains q.name then some q.name else none)
    else none

/-! Each round shares the previous dependency table across all child reads. -/
def dependencyTable (d : Core.Design) : Nat → List (String × Deps)
  | 0 => []
  | fuel + 1 =>
    let previous := dependencyTable d fuel
    d.items.map fun i =>
      let deps := match i with
        | .extern e => externDeps e
        | .module m => Deps.infer m (fun name => previous.lookup name)
      (itemName i, deps)

def designDeps (d : Core.Design) (fuel : Nat) : String → Option Deps :=
  let table := dependencyTable d fuel
  fun name => table.lookup name

structure Module where
  pos : Pos
  name : String
  ports : List Port
  ctx : Ctx
  interfaces : String → List Port
  body : List (Equation ctx interfaces)
  children : String → Option Deps
  ranks : Ranks
  acyclic : Ranked (Deps.graph ⟨pos, name, ports, equationsErase body⟩ children) ranks

def Module.erase (m : Module) : Core.Module :=
  ⟨m.pos, m.name, m.ports, equationsErase m.body⟩

def childNames (m : Core.Module) : List String :=
  m.body.filterMap fun s => match s with
    | .inst _ _ child _ => some child
    | _ => none

def externNames (d : Core.Design) : List String :=
  d.items.filterMap fun i => match i with | .extern e => some e.name | _ => none

def modules (d : Core.Design) : List Core.Module :=
  d.items.filterMap fun i => match i with | .module m => some m | _ => none

def hierarchyGraph (d : Core.Design) : Graph :=
  (modules d).map fun m => (.name m.name, (childNames m).map Deps.Node.name)

def ordered (seen : List String) : List Core.Module → Bool
  | [] => true
  | m :: rest => (childNames m).all seen.contains && ordered (m.name :: seen) rest

/-! Item names retain file order while module bodies keep hierarchy order. -/
structure Design where
  top : String
  itemNames : List String
  externs : List Extern
  bodies : List Module
  topPos : Pos
  hierarchy : ordered (externs.map (·.name)) (bodies.map Module.erase) = true

def Design.erase (d : Design) : Core.Design :=
  let items := d.itemNames.filterMap fun n =>
    match d.bodies.find? (·.name == n) with
    | some m => some (.module m.erase)
    | none => (d.externs.find? (·.name == n)).map Item.extern
  ⟨d.top, items, d.topPos⟩

def orderModules : Nat → List String → List Core.Module → Option (List Core.Module)
  | 0, _, pending => if pending.isEmpty then some [] else none
  | fuel + 1, seen, pending =>
    if pending.isEmpty then some [] else do
      let m ← pending.find? fun m => (childNames m).all seen.contains
      let rest ← orderModules fuel (m.name :: seen) (pending.erase m)
      return m :: rest

/-! Grouped erasure retains the order and syntax of each source form. -/
def elaborateModules (d : Core.Design) : List Core.Module → Option (List Module)
  | [] => some []
  | m :: rest => do
    let body ← m.body.mapM (statement d (context d m))
    let graph := Deps.graph m (designDeps d (d.items.length + 1))
    let ranks := graphRanks graph graph.length
    if h : Ranked graph ranks then
      let groups ← groupStatements (context d m) (portsOf d) body
      if hg : equationsErase groups = m.body then
        let typed : Module := ⟨m.pos, m.name, m.ports, context d m, portsOf d, groups,
          designDeps d (d.items.length + 1), ranks, by simpa [graph, hg] using h⟩
        let rest ← elaborateModules d rest
        return typed :: rest
      else none
    else none

def elaborateDesign (d : Core.Design) : Option Design := do
  let sorted ← orderModules (modules d).length (externNames d) (modules d)
  if _hc : sorted.Perm (modules d) then
    let bodies ← elaborateModules d sorted
    let externs := d.items.filterMap fun i => match i with
      | .extern e => some e | _ => none
    if hh : ordered (externs.map (·.name)) (bodies.map Module.erase) = true then
      let t : Design := ⟨d.top, d.items.map itemName, externs, bodies, d.topPos, hh⟩
      if t.erase = d then some t else none
    else none
  else none

theorem elaborateDesign_erase (d : Core.Design) (t : Design)
    (h : elaborateDesign d = some t) : t.erase = d := by
  simp only [elaborateDesign, bind, Option.bind_eq_some_iff] at h
  obtain ⟨sorted, _, h⟩ := h
  split at h <;> try contradiction
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨bodies, _, h⟩ := h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next he => cases h; exact he

end Silicon.Core.Typed
