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

def inferWith (ctx : Ctx) (lookup : Deps.Node → Option Kind)
    (correct : ∀ n, lookup n = ctx.lookup n) : Core.Expr → Option (Term ctx)
  | .ref p n => match h : lookup (.name n) with
    | some (.value (.bits w)) => some ⟨.bits w, .ref p (.name n) ((correct _).symm.trans h)⟩
    | some .clock => some ⟨.clock, .clock p n ((correct _).symm.trans h)⟩
    | _ => none
  | .port p i n => match h : lookup (.port i n) with
    | some (.value (.bits w)) => some ⟨.bits w, .ref p (.port i n) ((correct _).symm.trans h)⟩
    | _ => none
  | .const p w v => some ⟨.bits w, .const p w v⟩
  | .un p o a => do
    let ⟨.bits w, a⟩ ← inferWith ctx lookup correct a | none
    return ⟨.bits w, .un p o a⟩
  | .bin p o a b => do
    let ⟨.bits wa, a⟩ ← inferWith ctx lookup correct a | none
    let ⟨.bits wb, b⟩ ← inferWith ctx lookup correct b | none
    if ho : o = .concat then
      if hb : wa + wb ≤ 65536 then return ⟨.bits (wa + wb), .concat p a b hb⟩
      else none
    else if hw : wb = wa then return ⟨.bits wa, .bin p o ho a (hw ▸ b)⟩
    else none
  | .icmp p o a b => do
    let ⟨.bits wa, a⟩ ← inferWith ctx lookup correct a | none
    let ⟨.bits wb, b⟩ ← inferWith ctx lookup correct b | none
    if hw : wb = wa then return ⟨.bits 1, .icmp p o a (hw ▸ b)⟩ else none
  | .mux p c a b => do
    let c ← inferWith ctx lookup correct c >>= (castTerm · (.bits 1))
    let ⟨.bits wa, a⟩ ← inferWith ctx lookup correct a | none
    let b ← inferWith ctx lookup correct b >>= (castTerm · (.bits wa))
    return ⟨.bits wa, .mux p c a b⟩
  | .extract p a lo count => do
    let ⟨.bits w, a⟩ ← inferWith ctx lookup correct a | none
    if h : lo + count ≤ w then return ⟨.bits count, .extract p a lo count h⟩ else none
  | .replicate p a count => do
    let ⟨.bits w, a⟩ ← inferWith ctx lookup correct a | none
    if hb : w * count ≤ 65536 then return ⟨.bits (w * count), .replicate p a count hb⟩
    else none
  | .read p n a => do
    match h : lookup (.name n) with
    | some (.memory w depth) =>
      let a ← inferWith ctx lookup correct a >>= (castTerm · (.bits (addressWidth depth)))
      return ⟨.bits w, .read p n ((correct _).symm.trans h) a⟩
    | _ => none

def infer (ctx : Ctx) : Core.Expr → Option (Term ctx) :=
  inferWith ctx (fun n => ctx.lookup n) (fun _ => rfl)

/-! A shared index changes lookup cost but retains each intrinsic lookup proof. -/
theorem inferWith_eq (ctx : Ctx) (lookup : Deps.Node → Option Kind)
    (correct : ∀ n, lookup n = ctx.lookup n) : inferWith ctx lookup correct = infer ctx := by
  have he : lookup = (fun n => ctx.lookup n) := funext correct
  subst lookup
  rfl

/-! Type casts preserve syntax because they change only the type index. -/
theorem castTerm_erase (t : Term ctx) (ty : Ty) (e : Expr ctx ty)
    (h : castTerm t ty = some e) : e.erase = t.2.erase := by
  unfold castTerm at h
  split at h
  next ht => cases ht; cases h; rfl
  next => contradiction

theorem infer_erase (ctx : Ctx) (raw : Core.Expr) (t : Term ctx)
    (h : infer ctx raw = some t) : t.2.erase = raw := by
  unfold infer at h
  induction raw generalizing t with
  | ref p n =>
    simp only [inferWith] at h
    split at h <;> try contradiction
    all_goals cases h; rfl
  | port p i n =>
    simp only [inferWith] at h
    split at h <;> try contradiction
    cases h
    rfl
  | const p w v => cases h; rfl
  | un p o a ih =>
    simp only [inferWith, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    cases h
    simp only [Expr.erase, ih _ hx]
  | bin p o a b ia ib =>
    simp only [inferWith, bind, Option.bind_eq_some_iff] at h
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
    simp only [inferWith, bind, Option.bind_eq_some_iff] at h
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
    simp only [inferWith, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, ⟨tc, hc, hx⟩, y, hy, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨z, ⟨tb, hb, hz⟩, h⟩ := h
    cases h
    simp only [Expr.erase, castTerm_erase _ _ _ hx, castTerm_erase _ _ _ hz,
      ic _ hc, ia _ hy, ib _ hb]
  | extract p a lo count ih =>
    simp only [inferWith, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    simp only [Expr.erase, ih _ hx]
  | replicate p a count ih =>
    simp only [inferWith, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    simp only [Expr.erase, ih _ hx]
  | read p n a ih =>
    simp only [inferWith] at h
    split at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, ⟨ta, ha, hx⟩, h⟩ := h
    cases h
    simp only [Expr.erase, castTerm_erase _ _ _ hx, ih _ ha]

theorem infer_complete (e : Expr ctx ty) : infer ctx e.erase = some ⟨ty, e⟩ := by
  unfold infer
  induction e with
  | ref p node found =>
    cases node <;> simp only [Expr.erase, inferWith] <;> split
    all_goals first
      | (rename_i h; rw [found] at h; cases h <;> rfl)
      | (simp_all)
  | clock p n found =>
    simp only [Expr.erase, inferWith]
    split
    all_goals first
      | (rename_i h; rw [found] at h; cases h <;> rfl)
      | (simp_all)
  | const p w v => rfl
  | un p o a ih => simp [Expr.erase, inferWith, ih]
  | bin p o ho a b ia ib => simp [Expr.erase, inferWith, ia, ib, ho]
  | concat p a b hb ia ib => simp [Expr.erase, inferWith, ia, ib, hb]
  | icmp p o a b ia ib => simp [Expr.erase, inferWith, ia, ib]
  | mux p c a b ic ia ib => simp [Expr.erase, inferWith, ic, ia, ib, castTerm]
  | extract p a lo count hb ih => simp [Expr.erase, inferWith, ih, hb]
  | replicate p a count hb ih => simp [Expr.erase, inferWith, ih, hb]
  | read p n found a ih =>
    simp only [Expr.erase, inferWith]
    split
    · rename_i w depth h
      rw [found] at h
      cases h
      simp [ih, castTerm]
    · simp_all

/-! Context construction exposes only data outputs of child instances. -/
def portsOf (d : Core.Design) (name : String) : List Port :=
  ((d.items.find? fun i => Item.name i == name).map Item.ports).getD []

def contextFromPorts (interfaces : String → List Port) (m : Core.Module) : Ctx :=
  (m.ports.map fun p => (.name p.name,
    if p.ty == .clock && p.dir == .input then .clock else .value p.ty)) ++
  m.body.flatMap fun s => match s with
    | .let_ _ n w _ | .reg _ n w _ _ => [(.name n, .value (.bits w))]
    | .mem _ n w depth _ => [(.name n, .memory w depth)]
    | .inst _ n child _ => (interfaces child).filterMap fun p =>
      if p.dir == .output then some (.port n p.name, .value p.ty) else none
    | _ => []

def context (d : Core.Design) (m : Core.Module) : Ctx :=
  contextFromPorts (portsOf d) m

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

def expressionWith (ctx : Ctx) (inferFn : Core.Expr → Option (Term ctx))
    (raw : Core.Expr) (ty : Ty) : Option (Expr ctx ty) :=
  inferFn raw >>= (castTerm · ty)

def expression (ctx : Ctx) (raw : Core.Expr) (ty : Ty) : Option (Expr ctx ty) :=
  expressionWith ctx (infer ctx) raw ty

def statementWith (d : Core.Design) (ctx : Ctx) (inferFn : Core.Expr → Option (Term ctx)) :
    Core.Stmt → Option (Stmt ctx (portsOf d))
  | .let_ p n w e => return .let_ p n w (← expressionWith ctx inferFn e (.bits w))
  | .reg p n w c r => do
    let reset ← r.mapM fun r => do
      let signal ← expressionWith ctx inferFn r.signal (.bits 1)
      let value ← expressionWith ctx inferFn r.value (.bits w)
      return (⟨r.kind, signal, value⟩ : Reset ctx w)
    return .reg p n w c reset
  | .next p n e => do
    match h : valueTy ctx n with
    | some (.bits w) => return .next p n w h (← expressionWith ctx inferFn e (.bits w))
    | _ => none
  | .mem p n w depth c => some (.mem p n w depth c)
  | .write p n index a v en => do
    match h : ctx.lookup (.name n) with
    | some (.memory w depth) =>
      let addr ← expressionWith ctx inferFn a (.bits (addressWidth depth))
      let data ← expressionWith ctx inferFn v (.bits w)
      let enable ← expressionWith ctx inferFn en (.bits 1)
      return .write p n index w depth h addr data enable
    | _ => none
  | .inst p n child xs => do
    let inputs ← xs.mapM fun (k, raw) => do
      let port ← (portsOf d child).attach.find? (·.val.name == k)
      let e ← expressionWith ctx inferFn raw port.val.ty
      return (⟨port, e⟩ : (p : {p : Port // p ∈ portsOf d child}) × Expr ctx p.val.ty)
    return .inst p n child inputs
  | .assign p n e => do
    match h : valueTy ctx n with
    | some (.bits w) => return .assign p n w h (← expressionWith ctx inferFn e (.bits w))
    | _ => none


def statement (d : Core.Design) (ctx : Ctx) : Core.Stmt → Option (Stmt ctx (portsOf d)) :=
  statementWith d ctx (infer ctx)

def statements (d : Core.Design) (ctx : Ctx) (body : List Core.Stmt) :
    Option (List (Stmt ctx (portsOf d))) :=
  body.mapM (statement d ctx)

private def statementsIndexed (d : Core.Design) (ctx : Ctx) (body : List Core.Stmt) :
    Option (List (Stmt ctx (portsOf d))) :=
  let index := Deps.Node.index ctx
  let inferFn := inferWith ctx (fun n => index[n]?) (fun n => Deps.Node.index_lookup ctx n)
  body.mapM (statementWith d ctx inferFn)

@[csimp] private theorem statements_indexed : statements = statementsIndexed := by
  funext d ctx body
  simp only [statementsIndexed, inferWith_eq]
  rfl


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

private theorem find_unique {α : Type} (xs : List α) (p : α → Bool) (a : α)
    (ha : a ∈ xs) (hp : p a = true) (hu : ∀ b ∈ xs, p b = true → b = a) :
    xs.find? p = some a := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    by_cases hb : p b = true
    · simp [hu b (by simp) hb, hp]
    · simp only [List.find?_cons, hb]
      apply ih
      · simpa [List.mem_cons, show a ≠ b from fun h => hb (h ▸ hp)] using ha
      · intro b hm
        exact hu b (by simp [hm])

private theorem find_port (ps : List Port)
    (unique : ∀ a ∈ ps, ∀ b ∈ ps, a.name = b.name → a = b)
    (p : {p : Port // p ∈ ps}) :
    ps.attach.find? (·.val.name == p.val.name) = some p := by
  apply find_unique
  · simp
  · simp
  · intro q _ h
    apply Subtype.ext
    exact unique q.val q.property p.val p.property (by simpa using h)

theorem statement_complete (d : Core.Design) (ctx : Ctx)
    (unique : ∀ n, ∀ a ∈ portsOf d n, ∀ b ∈ portsOf d n, a.name = b.name → a = b)
    (t : Stmt ctx (portsOf d)) : statement d ctx t.erase = some t := by
  have ex {ty : Ty} (e : Expr ctx ty) : expressionWith ctx (infer ctx) e.erase ty = some e := by
    simp [expressionWith, infer_complete, castTerm]
  cases t with
  | let_ p n w e => simp [Stmt.erase, statement, statementWith, ex]
  | reg p n w c r =>
    cases r <;> simp [Stmt.erase, statement, statementWith, Reset.erase, ex]
  | next p n w h e =>
    simp only [Stmt.erase, statement, statementWith]
    split
    · rename_i w' h'
      rw [h] at h'
      cases h'
      simp [ex]
    · simp_all
  | mem p n w depth c => rfl
  | write p n index w depth h a v en =>
    simp only [Stmt.erase, statement, statementWith]
    split
    · rename_i w' depth' h'
      rw [h] at h'
      cases h'
      simp [ex]
    · simp_all
  | inst p n child xs =>
    simp only [Stmt.erase, statement, statementWith]
    have hm : List.mapM (fun (k, raw) => do
        let port ← (portsOf d child).attach.find? (·.val.name == k)
        let e ← expressionWith ctx (infer ctx) raw port.val.ty
        return (⟨port, e⟩ : (p : {p : Port // p ∈ portsOf d child}) × Expr ctx p.val.ty))
        (xs.map fun input => (input.1.val.name, input.2.erase)) = some xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, List.mapM_cons]
        rw [find_port _ (unique child) x.1]
        simp only [bind, Option.bind_some, ex, pure]
        simp only [bind, pure] at ih
        rw [ih]
        rfl
    rw [hm]
    rfl
  | assign p n w h e =>
    simp only [Stmt.erase, statement, statementWith]
    split
    · rename_i w' h'
      rw [h] at h'
      cases h'
      simp [ex]
    · simp_all

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

def nextTerms (body : List (Stmt ctx ports)) (name : String) (start : Nat := 0) :
    List (Nat × Pos × Term ctx) :=
  (body.zipIdx start).filterMap fun (s, index) => match s with
    | .next p n width _ e =>
      if n == name then some (index, p, (⟨.bits width, e⟩ : Term ctx)) else none
    | _ => none

def groupStatement (ctx : Ctx) (ports : String → List Port)
    (body : List (Stmt ctx ports)) (entry : Stmt ctx ports × Nat) :
    Option (Option (Equation ctx ports)) :=
  match entry with
  | (s, index) => match s with
    | .let_ p n w e => pure (some (.let_ index p n w e))
    | .reg p n w c r => do
      if h : valueTy ctx n = some (.bits w) then
        let nexts := nextTerms body n
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

def groupStatements (ctx : Ctx) (ports : String → List Port)
    (body : List (Stmt ctx ports)) : Option (List (Equation ctx ports)) := do
  let groups ← body.zipIdx.mapM (groupStatement ctx ports body)
  return groups.filterMap id

private theorem mapM_total {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨y :: ys, by simp only [List.mapM_cons, hy, hys, bind, Option.bind_some, pure]⟩

def StateReady (body : List (Stmt ctx ports)) : Prop :=
  ∀ s ∈ body, match s with
  | .reg _ n w _ _ => valueTy ctx n = some (.bits w) ∧
      (body.filterMap fun s => match s with
        | .next p name _ _ _ => if name == n then some p else none
        | _ => none).length = 1
  | .mem _ n w depth _ => ctx.lookup (.name n) = some (.memory w depth)
  | _ => True

private theorem nextTerms_length (body : List (Stmt ctx ports)) (n : String) (start : Nat) :
    (nextTerms body n start).length =
    (body.filterMap fun s => match s with
      | .next p name _ _ _ => if name == n then some p else none
      | _ => none).length := by
  unfold nextTerms
  induction body generalizing start with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.zipIdx_cons, List.filterMap_cons]
    dsimp only at ih
    cases s <;> simp only <;> try exact ih (start + 1)
    rename_i p name width target value
    by_cases hn : name == n <;> simp only [hn, Bool.false_eq_true, ↓reduceIte, List.length_cons, ih]

private theorem nextTerms_type (body : List (Stmt ctx ports)) (n : String) (w : Nat)
    (target : valueTy ctx n = some (.bits w)) (start : Nat) (i : Nat) (p : Pos)
    (t : Term ctx)
    (hm : (i,p,t) ∈ nextTerms body n start) : t.1 = .bits w := by
  obtain ⟨⟨s,index⟩, hmem, h⟩ := List.mem_filterMap.mp hm
  cases s <;> simp only at h <;> try contradiction
  rename_i pos name width found value
  split at h <;> try contradiction
  next hn =>
    simp only [beq_iff_eq] at hn
    subst name
    rw [target] at found
    cases found
    cases h
    rfl

private theorem groupStatement_total (body : List (Stmt ctx ports))
    (ready : StateReady body) (entry : Stmt ctx ports × Nat) (hm : entry.1 ∈ body) :
    ∃ e, groupStatement ctx ports body entry = some e := by
  obtain ⟨s,index⟩ := entry
  have hr := ready s hm
  cases s with
  | reg p n w c r =>
    simp only [StateReady] at ready
    change valueTy ctx n = some (.bits w) ∧ _ at hr
    obtain ⟨target, one⟩ := hr
    simp only [groupStatement, dite_eq_left target]
    have hl := nextTerms_length body n 0
    rw [one] at hl
    obtain ⟨x,hx⟩ := List.length_eq_one_iff.mp hl
    obtain ⟨ni,np,ne⟩ := x
    rw [hx]
    have ht := nextTerms_type body n w target 0 ni np ne (by rw [hx]; simp)
    simp [castTerm, ht]
  | mem p n w depth c =>
    change ctx.lookup (.name n) = some (.memory w depth) at hr
    simp only [groupStatement, dite_eq_left hr, bind, Option.bind_eq_some_iff]
    obtain ⟨ws,hws⟩ := mapM_total body.zipIdx (fun (s,index) => match s with
      | .write p name port width size _ a v en => do
        if name == n then
          let a ← castTerm ⟨.bits (addressWidth size), a⟩ (.bits (addressWidth depth))
          let v ← castTerm ⟨.bits width, v⟩ (.bits w)
          pure (some (⟨index,p,port,a,v,en⟩ : Write ctx w depth))
        else pure none
      | _ => pure none) (by
        intro entry hmem
        obtain ⟨s,index⟩ := entry
        cases s <;> try exact ⟨none,rfl⟩
        rename_i pos name port width size found a v en
        by_cases hn : name = n
        · subst name
          rw [hr] at found
          cases found
          simp [castTerm]
        · simp [hn])
    exact ⟨some (.mem index p n w depth c hr (ws.filterMap id)), ws, hws, rfl⟩
  | _ => simp [groupStatement]

theorem groupStatements_total (body : List (Stmt ctx ports)) (ready : StateReady body) :
    ∃ groups, groupStatements ctx ports body = some groups := by
  obtain ⟨groups,hg⟩ := mapM_total body.zipIdx (groupStatement ctx ports body)
    (fun entry hm => groupStatement_total body ready entry (List.fst_mem_of_mem_zipIdx hm))
  exact ⟨groups.filterMap id, by simp [groupStatements,hg]⟩


def UpdateOwners (body : List (Stmt ctx ports)) : Prop :=
  ∀ s ∈ body, match s with
  | .next _ n .. => (body.filter fun s => match s with
      | .reg _ name .. => name == n | _ => false).length = 1
  | .write _ n .. => (body.filter fun s => match s with
      | .mem _ name .. => name == n | _ => false).length = 1
  | _ => True

def indexedErase (e : Nat × Stmt ctx ports) : Nat × Core.Stmt := (e.1,e.2.erase)

def groupExpansion (body : List (Stmt ctx ports)) (entry : Stmt ctx ports × Nat) :
    List (Nat × Core.Stmt) :=
  match entry with
  | (s@(.reg _ n _ _ _),index) => (index,s.erase) ::
    (nextTerms body n).map fun (i,p,t) => (i,.next p n t.2.erase)
  | (s@(.mem _ n _ _ _),index) => (index,s.erase) ::
    body.zipIdx.filterMap fun (s,i) => match s with
      | .write _ name .. => if name == n then some (i,s.erase) else none
      | _ => none
  | (.next ..,_) | (.write ..,_) => []
  | (s,index) => [(index,s.erase)]

private theorem mapM_map_eq {α β γ : Type} (xs : List α) (f : α → Option β)
    (g : β → γ) (k : α → γ) (ys : List β) (h : xs.mapM f = some ys)
    (step : ∀ x ∈ xs, ∀ y, f x = some y → g y = k x) : ys.map g = xs.map k := by
  induction xs generalizing ys with
  | nil => cases h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨y,hy,zs,hzs,h⟩ := h
    cases h
    simp only [List.map_cons, step x (by simp) y hy,
      ih zs hzs (fun x hx => step x (by simp [hx]))]

private theorem groupStatement_parts (body : List (Stmt ctx ports))
    (entry : Stmt ctx ports × Nat) (out : Option (Equation ctx ports))
    (h : groupStatement ctx ports body entry = some out) :
    (out.toList.flatMap Equation.parts).map indexedErase = groupExpansion body entry := by
  obtain ⟨s,index⟩ := entry
  cases s with
  | reg p n w c r =>
    simp only [groupStatement] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    next ni np ne he =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨next, hn, h⟩ := h
      cases h
      simp only [groupExpansion, he, Option.toList_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Equation.parts, List.map_cons, List.map_nil,
        indexedErase, Stmt.erase, castTerm_erase _ _ _ hn]
  | mem p n w depth c =>
    simp only [groupStatement] at h
    split at h <;> try contradiction
    next target =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨writes, hw, h⟩ := h
      cases h
      simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Equation.parts, List.map_cons, indexedErase, groupExpansion]
      congr 1
      rw [List.map_map]
      -- Each cast changes only a type index, so every selected write keeps its syntax.
      have hm := mapM_map_eq body.zipIdx _
        (fun wr : Option (Write ctx w depth) => wr.map fun wr =>
          (wr.index, Core.Stmt.write wr.pos n wr.port wr.addr.erase wr.data.erase wr.enable.erase))
        (fun (s,i) => match s with
          | .write _ name .. => if name == n then some (i,s.erase) else none
          | _ => none) writes hw (by
          intro entry hmem out ho
          obtain ⟨s,i⟩ := entry
          cases s <;> simp only at ho ⊢ <;> try (cases ho; rfl)
          rename_i p name port width size found a v en
          split at ho
          next hn =>
            simp only [Option.bind_eq_some_iff] at ho
            obtain ⟨addr,ha,data,hv,ho⟩ := ho
            cases ho
            simp only [Option.map_some, Stmt.erase, hn, ↓reduceIte,
              castTerm_erase _ _ _ ha, castTerm_erase _ _ _ hv]
            simp only [beq_iff_eq] at hn
            simp [hn]
          next hn => cases ho; simp [hn])
      have hf := congrArg (List.filterMap id) hm
      simpa only [List.filterMap_map, List.map_filterMap, Function.comp_def,
        indexedErase, Stmt.erase, id_eq] using hf
  | _ => cases h; rfl
theorem groupStatements_parts (body : List (Stmt ctx ports))
    (groups : List (Equation ctx ports)) (h : groupStatements ctx ports body = some groups) :
    (groups.flatMap Equation.parts).map indexedErase =
      body.zipIdx.flatMap (groupExpansion body) := by
  simp only [groupStatements, bind, Option.bind_eq_some_iff] at h
  obtain ⟨outs,ho,h⟩ := h
  cases h
  have hm := mapM_map_eq body.zipIdx (groupStatement ctx ports body)
    (fun out => (out.toList.flatMap Equation.parts).map indexedErase)
    (groupExpansion body) outs ho (fun entry _ out he => groupStatement_parts body entry out he)
  have hf := congrArg List.flatten hm
  have law (os : List (Option (Equation ctx ports))) :
      (os.filterMap id |>.flatMap Equation.parts).map indexedErase =
      (os.map fun out => (out.toList.flatMap Equation.parts).map indexedErase).flatten := by
    induction os with
    | nil => rfl
    | cons out os ih => cases out <;> simp [ih]
  rw [law]
  exact hf


private theorem flatMap_append_perm {α β : Type} (xs : List α) (f g : α → List β) :
    (xs.flatMap fun x => f x ++ g x).Perm (xs.flatMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    have h := ih.append_left (f x ++ g x)
    apply h.trans
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := g x) (l₂ := xs.flatMap f)).append_right
        (xs.flatMap g) |>.append_left (f x)

private theorem matrix_perm {α β γ : Type} (xs : List α) (ys : List β) (f : α → β → List γ) :
    (xs.flatMap fun x => ys.flatMap (f x)).Perm
      (ys.flatMap fun y => xs.flatMap fun x => f x y) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (ih.append_left _).trans (flatMap_append_perm ys (f x) _).symm

private theorem filter_union_perm {α : Type} (xs : List α) (p q : α → Bool)
    (disjoint : ∀ x ∈ xs, p x = true → q x = false) :
    (xs.filter p ++ xs.filter q).Perm (xs.filter fun x => p x || q x) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    have ih := ih (fun y hy => disjoint y (by simp [hy]))
    have hd := disjoint x (by simp)
    cases hp : p x <;> cases hq : q x <;> simp only [hp,hq] at hd
    all_goals simp only [List.filter_cons, hp, hq, Bool.or_false, Bool.or_true,
      List.cons_append, Bool.false_eq_true, ↓reduceIte]
    · exact ih
    · exact List.perm_middle.trans (ih.cons x)
    · exact ih.cons x
    · simp at hd

private theorem filter_single {α : Type} (xs : List α) (p : α → Bool) (a : α)
    (hn : xs.Nodup) (ha : a ∈ xs) (hp : p a = true)
    (unique : ∀ x ∈ xs, p x = true → x = a) : xs.filter p = [a] := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hnx,hns⟩ := List.nodup_cons.mp hn
    by_cases hx : p x = true
    · have eq := unique x (by simp) hx
      subst x
      have empty : xs.filter p = [] := List.filter_eq_nil_iff.mpr (by
        intro y hy hyp
        have := unique y (by simp [hy]) hyp
        subst y
        exact hnx hy)
      simp [hp,empty]
    · rw [List.filter_cons]
      simp only [hx, Bool.false_eq_true, ↓reduceIte]
      apply ih hns
      · rcases List.mem_cons.mp ha with rfl | h
        · exact False.elim (hx hp)
        · exact h
      · intro y hy
        exact unique y (by simp [hy])

private theorem indexed_nodup {α : Type} (xs : List α) : xs.zipIdx.Nodup := by
  apply List.Pairwise.of_map (S := Ne) Prod.snd (fun a b h he => h (congrArg Prod.snd he))
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' _

private theorem indexed_eq {α : Type} (xs : List α) (a b : α × Nat)
    (ha : a ∈ xs.zipIdx) (hb : b ∈ xs.zipIdx) (hi : a.2 = b.2) : a = b := by
  have ea := List.mem_zipIdx_iff_getElem?.mp ha
  have eb := List.mem_zipIdx_iff_getElem?.mp hb
  rw [hi,eb] at ea
  exact Prod.ext (Option.some.inj ea).symm hi

private theorem indexed_filter {α : Type} (xs : List α) (a : α × Nat)
    (ha : a ∈ xs.zipIdx) : xs.zipIdx.filter (fun x => x.2 == a.2) = [a] := by
  apply filter_single _ _ a (indexed_nodup xs) ha (by simp)
  intro b hb h
  exact indexed_eq xs b a hb ha (by simpa using h)

def isUpdate : Stmt ctx ports → Bool
  | .next .. | .write .. => true
  | _ => false

def takesUpdate (owner candidate : Stmt ctx ports) : Bool :=
  match owner,candidate with
  | .reg _ n .., .next _ name .. => n == name
  | .mem _ n .., .write _ name .. => n == name
  | _, _ => false

def ownsEntry (owner candidate : Stmt ctx ports × Nat) : Bool :=
  !isUpdate owner.1 && (owner.2 == candidate.2 || takesUpdate owner.1 candidate.1)

private theorem nextTerms_erased (body : List (Stmt ctx ports))
    (p : Pos) (n : String) (w : Nat) (c : String) (r : Option (Reset ctx w)) (start : Nat) :
    ((nextTerms body n start).map fun (i,p,t) => (i,Core.Stmt.next p n t.2.erase)) =
      ((body.zipIdx start).filter fun x => takesUpdate (.reg p n w c r) x.1).map
        (fun (s,i) => (i,s.erase)) := by
  unfold nextTerms
  induction body generalizing start with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.zipIdx_cons, List.filterMap_cons, List.filter_cons]
    dsimp only at ih
    cases s <;> simp only [takesUpdate] <;> try exact ih (start+1)
    rename_i pos name width target value
    by_cases hn : name = n
    · subst name
      simp only [BEq.rfl, ↓reduceIte, List.map_cons, Stmt.erase]
      simpa only [takesUpdate, Stmt.erase] using
        congrArg (List.cons (start, Core.Stmt.next pos n value.erase)) (ih (start+1))
    · have hn' : n ≠ name := Ne.symm hn
      simp only [beq_iff_eq, hn, hn', ↓reduceIte]
      simpa only [takesUpdate, beq_iff_eq] using ih (start+1)

private theorem no_takes (owner : Stmt ctx ports) (ho : isUpdate owner = true) :
    ∀ candidate, takesUpdate owner candidate = false := by
  intro candidate
  cases owner <;> cases candidate <;> simp_all [isUpdate,takesUpdate]

private theorem groupExpansion_eq (body : List (Stmt ctx ports)) (entry : Stmt ctx ports × Nat) :
    groupExpansion body entry =
      (if isUpdate entry.1 then [] else [(entry.2,entry.1.erase)]) ++
      ((body.zipIdx.filter fun x => takesUpdate entry.1 x.1).map
        fun (s,i) => (i,s.erase)) := by
  obtain ⟨s,index⟩ := entry
  cases s with
  | reg p n w c r =>
    simp only [groupExpansion, isUpdate, Bool.false_eq_true, ↓reduceIte,
      List.singleton_append]
    exact congrArg (List.cons (index, (Stmt.reg p n w c r).erase))
      (nextTerms_erased body p n w c r 0)
  | mem p n w depth c =>
    simp only [groupExpansion, isUpdate, Bool.false_eq_true, ↓reduceIte, List.singleton_append]
    congr 1
    generalize body.zipIdx = xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      obtain ⟨s,i⟩ := x
      simp only [takesUpdate, beq_iff_eq] at ih
      cases s <;> simp only [List.filterMap_cons, List.filter_cons, takesUpdate,
        beq_iff_eq] <;> try exact ih
      rename_i pos name port width size target addr data enable
      by_cases hn : name = n
      · subst name
        simp only [↓reduceIte, List.map_cons, ih]
      · simp only [hn, Ne.symm hn, ↓reduceIte, ih]
  | _ =>
    simp only [groupExpansion, isUpdate, ↓reduceIte, Bool.false_eq_true]
    have empty {α β : Type} (xs : List α) (p : α → Bool) (f : α → β)
        (hp : ∀ x ∈ xs, p x = false) : (xs.filter p).map f = [] := by
      rw [List.filter_eq_nil_iff.mpr (by simpa using hp)]
      rfl
    rw [empty _ _ _ (by intro x _; cases x.1 <;> rfl)]
    rfl
private theorem groupExpansion_perm (body : List (Stmt ctx ports))
    (entry : Stmt ctx ports × Nat) (hm : entry ∈ body.zipIdx) :
    (groupExpansion body entry).Perm
      ((body.zipIdx.filter (ownsEntry entry)).map fun (s,i) => (i,s.erase)) := by
  rw [groupExpansion_eq]
  cases hu : isUpdate entry.1 with
  | true =>
    have empty : (body.zipIdx.filter fun x => takesUpdate entry.1 x.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x _
      simp [no_takes entry.1 hu]
    simp [empty, ownsEntry, hu]
  | false =>
    have disjoint : ∀ x ∈ body.zipIdx, (x.2 == entry.2) = true →
        takesUpdate entry.1 x.1 = false := by
      intro x hx hi
      have eq := indexed_eq body x entry hx hm (by simpa using hi)
      subst x
      cases entry.1 <;> rfl
    have hp := (filter_union_perm body.zipIdx (fun x => x.2 == entry.2)
      (fun x => takesUpdate entry.1 x.1) disjoint).map
      (fun (s,i) => (i,s.erase))
    rw [indexed_filter body entry hm] at hp
    unfold ownsEntry
    simpa only [List.map_append, List.map_cons, List.map_nil, hu, Bool.false_eq_true,
      ↓reduceIte, Bool.not_false, Bool.true_and, BEq.comm] using hp
private theorem filter_zipIdx_length {α : Type} (xs : List α) (p : α → Bool)
    (start : Nat) : ((xs.zipIdx start).filter fun x => p x.1).length =
      (xs.filter p).length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.filter_cons]
    cases hp : p x <;> simp [ih]

private theorem owns_update (body : List (Stmt ctx ports)) (owner candidate : Stmt ctx ports × Nat)
    (ho : owner ∈ body.zipIdx) (hc : candidate ∈ body.zipIdx)
    (hu : isUpdate candidate.1 = true) : ownsEntry owner candidate =
      takesUpdate owner.1 candidate.1 := by
  by_cases hi : owner.2 = candidate.2
  · have he := indexed_eq body owner candidate ho hc hi
    subst owner
    cases he : candidate.1 <;> simp [ownsEntry,isUpdate,takesUpdate,he] at hu ⊢
  · cases he : owner.1 <;> cases hf : candidate.1 <;>
        simp [ownsEntry,isUpdate,takesUpdate,he,hf,hi] at hu ⊢

private theorem owner_count (body : List (Stmt ctx ports)) (owners : UpdateOwners body)
    (candidate : Stmt ctx ports × Nat) (hc : candidate ∈ body.zipIdx) :
    (body.zipIdx.filter fun owner => ownsEntry owner candidate).length = 1 := by
  cases hu : isUpdate candidate.1 with
  | false =>
    have he : (body.zipIdx.filter fun owner => ownsEntry owner candidate) =
        body.zipIdx.filter (fun x => x.2 == candidate.2) := by
      apply List.filter_congr
      intro owner ho
      by_cases hi : owner.2 = candidate.2
      · have he := indexed_eq body owner candidate ho hc hi
        subst owner
        simp [ownsEntry,hu]
      · cases he : owner.1 <;> cases hf : candidate.1 <;>
        simp [ownsEntry,isUpdate,takesUpdate,he,hf,hi] at hu ⊢
    rw [he,indexed_filter body candidate hc]
    rfl
  | true =>
    rw [List.filter_congr (fun owner ho => owns_update body owner candidate ho hc hu)]
    rw [filter_zipIdx_length body (fun s => takesUpdate s candidate.1) 0]
    have hr := owners candidate.1 (List.fst_mem_of_mem_zipIdx hc)
    obtain ⟨s,index⟩ := candidate
    cases s <;> simp only [isUpdate] at hu <;> try contradiction
    all_goals
      change (body.filter _).length = 1 at hr
      apply Eq.trans _ hr
      apply congrArg List.length
      apply List.filter_congr
      intro s _
      cases s <;> rfl
private theorem flatMap_congr_perm {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, (f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    exact (h x (by simp)).append (ih (fun x hx => h x (by simp [hx])))

private theorem filter_map_flatMap {α β : Type} (xs : List α) (p : α → Bool) (f : α → β) :
    (xs.filter p).map f = xs.flatMap (fun x => if p x then [f x] else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp, ih]

theorem groupExpansion_coverage (body : List (Stmt ctx ports)) (owners : UpdateOwners body) :
    (body.zipIdx.flatMap (groupExpansion body)).Perm
      (body.zipIdx.map fun (s,i) => (i,s.erase)) := by
  have he := flatMap_congr_perm body.zipIdx (groupExpansion body)
    (fun owner => (body.zipIdx.filter (ownsEntry owner)).map fun (s,i) => (i,s.erase))
    (fun entry hm => groupExpansion_perm body entry hm)
  simp only [filter_map_flatMap] at he
  have ht := matrix_perm body.zipIdx body.zipIdx
    (fun owner candidate => if ownsEntry owner candidate then
      [(candidate.2,candidate.1.erase)] else [])
  apply (he.trans ht).trans
  apply List.Perm.of_eq
  rw [List.map_eq_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro candidate hc
  rw [← filter_map_flatMap]
  obtain ⟨owner,ho⟩ := List.length_eq_one_iff.mp (owner_count body owners candidate hc)
  rw [ho]
  rfl

theorem groupStatements_coverage (body : List (Stmt ctx ports)) (owners : UpdateOwners body)
    (groups : List (Equation ctx ports)) (hg : groupStatements ctx ports body = some groups) :
    ((groups.flatMap Equation.parts).map indexedErase).Perm
      ((body.map Stmt.erase).zipIdx.map fun (s,i) => (i,s)) := by
  rw [groupStatements_parts body groups hg]
  simpa only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq] using
    groupExpansion_coverage body owners

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

private def ranked (g : Graph) (r : Ranks) : Bool :=
  let index := Deps.Node.index r
  g.all fun row => row.2.all fun dep => (index[dep]?).getD 0 < (index[row.1]?).getD 0

private theorem ranked_iff (g : Graph) (r : Ranks) : ranked g r = true ↔ Ranked g r := by
  simp only [ranked, List.all_eq_true, decide_eq_true_eq, Deps.Node.index_lookup, Ranked]
  rfl

instance (g : Graph) (r : Ranks) : Decidable (Ranked g r) :=
  decidable_of_iff (ranked g r = true) (ranked_iff g r)

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

/-! Finite graphs admit ranks bounded by their number of equations. -/
theorem bounded_ranks (g : Graph) (h : ∃ r, Ranked g r) :
    ∃ q : Deps.Node → Nat, (∀ n, q n ≤ g.length) ∧
      ∀ row ∈ g, ∀ dep ∈ row.2, q dep < q row.1 := by
  obtain ⟨r, hr⟩ := h
  exact ⟨compressed g r, compressed_bound g r, compressed_edges g r hr⟩

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

/-!
Completed nodes share cached heights across dependency paths.
One step per graph node bounds a path; a cycle exhausts that bound.
-/
namespace FastRanks

abbrev Cache := Std.HashMap Deps.Node Nat
abbrev GraphIndex := Std.HashMap Deps.Node (List Deps.Node)
def inputs (visit : Deps.Node → Cache → Option (Nat × Cache)) :
    List Deps.Node → Nat → Cache → Option (Nat × Cache)
  | [], best, cache => some (best, cache)
  | n :: ns, best, cache => do
    let (v, cache) ← visit n cache
    inputs visit ns (max best v) cache

def visit (g : GraphIndex) : Nat → Deps.Node → Cache → Option (Nat × Cache)
  | 0, _, _ => none
  | fuel + 1, n, cache => do
    match cache[n]? with
    | some v => some (v, cache)
    | none =>
      let (best, cache) ← match g[n]? with
        | none => some (0, cache)
        | some edges => inputs (visit g fuel) edges 0 cache
      let v := if (g[n]?).isSome then best + 1 else 0
      some (v, cache.insert n v)

def Sound (q : Deps.Node → Nat) (cache : Cache) : Prop :=
  ∀ n v, cache[n]? = some v → v = q n

theorem inputs_total (q : Deps.Node → Nat) (xs : List Deps.Node)
    (f : Deps.Node → Cache → Option (Nat × Cache))
    (hf : ∀ n ∈ xs, ∀ cache, Sound q cache →
      ∃ out, f n cache = some (q n, out) ∧ Sound q out)
    (best : Nat) (cache : Cache) (hc : Sound q cache) :
    ∃ out, inputs f xs best cache = some ((xs.map q).foldl max best, out) ∧ Sound q out := by
  induction xs generalizing best cache with
  | nil => exact ⟨cache, rfl, hc⟩
  | cons n ns ih =>
    obtain ⟨middle, hm, hs⟩ := hf n (by simp) cache hc
    obtain ⟨out, ho, hs⟩ := ih (fun n hn => hf n (by simp [hn])) (max best (q n)) middle hs
    refine ⟨out, ?_, hs⟩
    simp [inputs, hm, ho]

theorem visit_total (g : GraphIndex) (q : Deps.Node → Nat)
    (height : ∀ n, q n = match g[n]? with
      | none => 0 | some edges => 1 + (edges.map q).foldl max 0)
    (fuel : Nat) (n : Deps.Node) (cache : Cache)
    (bound : q n < fuel) (hc : Sound q cache) :
    ∃ out, visit g fuel n cache = some (q n, out) ∧ Sound q out := by
  induction fuel generalizing n cache with
  | zero => omega
  | succ fuel ih =>
    cases he : cache[n]? with
    | some v =>
      have hv := hc n v he
      subst v
      exact ⟨cache, by simp [visit, he], hc⟩
    | none =>
      have hh := height n
      cases hg : g[n]? with
      | none =>
        simp only [hg] at hh
        refine ⟨cache.insert n 0, ?_, ?_⟩
        · simp [visit, he, hg, hh]
        · intro k v hv
          simp only [Std.HashMap.getElem?_insert] at hv
          split at hv
          · rename_i hk
            simp only [beq_iff_eq] at hk
            subst k
            cases hv
            exact hh.symm
          · exact hc k v hv
      | some edges =>
        simp only [hg] at hh
        change q n = 1 + (edges.map q).foldl max 0 at hh
        obtain ⟨out, ho, hs⟩ := inputs_total q edges (visit g fuel) (by
          intro child hchild cache hc
          apply ih child cache
          · have hm := max_mem (edges.map q) (q child)
              (List.mem_map.mpr ⟨child, hchild, rfl⟩) 0
            omega
          · exact hc) 0 cache hc
        refine ⟨out.insert n (q n), ?_, ?_⟩
        · simp [visit, he, hg, ho, hh, Nat.add_comm]
        · intro k v hv
          simp only [Std.HashMap.getElem?_insert] at hv
          split at hv
          · rename_i hk
            simp only [beq_iff_eq] at hk
            subst k
            cases hv
            rfl
          · exact hs k v hv
def rows (f : Deps.Node → Cache → Option (Nat × Cache)) :
    List Deps.Node → Cache → Option (Ranks × Cache)
  | [], cache => some ([], cache)
  | n :: ns, cache => do
    let (v, cache) ← f n cache
    let (rest, cache) ← rows f ns cache
    some ((n, v) :: rest, cache)

theorem rows_total (q : Deps.Node → Nat) (ns : List Deps.Node)
    (f : Deps.Node → Cache → Option (Nat × Cache))
    (hf : ∀ n ∈ ns, ∀ cache, Sound q cache →
      ∃ out, f n cache = some (q n, out) ∧ Sound q out)
    (cache : Cache) (hc : Sound q cache) :
    ∃ out, rows f ns cache = some (ns.map (fun n => (n, q n)), out) ∧ Sound q out := by
  induction ns generalizing cache with
  | nil => exact ⟨cache, rfl, hc⟩
  | cons n ns ih =>
    obtain ⟨middle, hm, hs⟩ := hf n (by simp) cache hc
    obtain ⟨out, ho, hs⟩ := ih (fun n hn => hf n (by simp [hn])) middle hs
    refine ⟨out, ?_, hs⟩
    simp [rows, hm, ho]

def certificate (g : Graph) : Option Ranks := do
  let (r, _) ← rows (visit (Deps.Node.index g) (g.length + 1)) (g.map Prod.fst) {}
  if Ranked g r then some r else none

theorem certificate_sound (g : Graph) (r : Ranks) (h : certificate g = some r) : Ranked g r := by
  simp only [certificate, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨rs, cache⟩, _, h⟩ := h
  split at h
  · cases h; assumption
  · contradiction

theorem mapped_rank (ns : List Deps.Node) (q : Deps.Node → Nat) (n : Deps.Node) :
    rank (ns.map fun k => (k, q k)) n = if n ∈ ns then q n else 0 := by
  induction ns with
  | nil => rfl
  | cons k ns ih =>
    by_cases h : n = k
    · subst n; simp [rank]
    · simp only [rank, List.map_cons, List.lookup_cons,
        show (n == k) = false from beq_eq_false_iff_ne.mpr h]
      simpa only [Typed.rank, List.mem_cons, h, false_or] using ih

theorem certificate_of_height (g : Graph) (q : Deps.Node → Nat)
    (height : ∀ n, q n = match g.lookup n with
      | none => 0 | some edges => 1 + (edges.map q).foldl max 0)
    (bounded : ∀ n, q n ≤ g.length)
    (decreasing : ∀ row ∈ g, ∀ dep ∈ row.2, q dep < q row.1) :
    ∃ r, certificate g = some r := by
  obtain ⟨cache, hc, _⟩ := rows_total q (g.map Prod.fst)
    (visit (Deps.Node.index g) (g.length + 1)) (by
      intro n _ cache hs
      apply visit_total (Deps.Node.index g) q
      · intro n; simpa only [Deps.Node.index_lookup] using height n
      · have := bounded n; omega
      · exact hs) {} (by intro n v h; simp at h)
  have ranks (n : Deps.Node) : rank ((g.map Prod.fst).map fun k => (k, q k)) n = q n := by
    rw [mapped_rank]
    split
    · rfl
    · rename_i hn
      have ha : g.lookup n = none := by
        rw [List.lookup_eq_none_iff]
        intro k hk
        simp only [bne_iff_ne]
        intro he
        exact hn (List.mem_map.mpr ⟨k, hk, he.symm⟩)
      simpa only [ha] using (height n).symm
  have ranked : Ranked g ((g.map Prod.fst).map fun k => (k, q k)) := by
    intro row hr dep hd
    simpa only [ranks] using decreasing row hr dep hd
  refine ⟨(g.map Prod.fst).map (fun k => (k, q k)), ?_⟩
  simp only [certificate, hc, bind, Option.bind_some, ite_eq_left ranked]

private theorem fold_max_bound (xs : List Nat) (bound base : Nat)
    (members : ∀ x ∈ xs, x ≤ bound) (initial : base ≤ bound) :
    xs.foldl max base ≤ bound := by
  induction xs generalizing base with
  | nil => exact initial
  | cons n ns ih =>
    apply ih _ (fun x hx => members x (by simp [hx]))
    exact Nat.max_le.mpr ⟨initial, members n (by simp)⟩

private theorem rank_bound (g : Graph) (hn : (g.map Prod.fst).Nodup) (fuel : Nat)
    (n : Deps.Node) : rank (graphRanks g fuel) n ≤ fuel := by
  induction fuel generalizing n with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    by_cases hm : n ∈ g.map Prod.fst
    · obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
      rw [rank_succ_row g hn row hr]
      have hb := fold_max_bound (row.2.map (rank (graphRanks g fuel))) fuel 0
        (by intro x hx; obtain ⟨dep, _, rfl⟩ := List.mem_map.mp hx; exact ih dep)
        (Nat.zero_le _)
      omega
    · rw [rank_absent g n hm]
      omega

theorem certificate_complete (g : Graph) (hn : (g.map Prod.fst).Nodup)
    (h : ∃ r, Ranked g r) : ∃ r, certificate g = some r := by
  obtain ⟨r, hr⟩ := h
  let q := rank (graphRanks g g.length)
  have stable (n : Deps.Node) : rank (graphRanks g (g.length + 1)) n = q n :=
    ranks_stable g hn (compressed g r) (compressed_pos g r)
      (compressed_edges g r hr) g.length n (compressed_bound g r n)
  apply certificate_of_height g q
  · intro n
    cases hl : g.lookup n with
    | none =>
      have ha : n ∉ g.map Prod.fst := by
        intro hm
        obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
        have hz := (List.lookup_eq_none_iff.mp hl) row hr
        simp only [bne_iff_ne] at hz
        exact hz he.symm
      simpa only [hl] using rank_absent g n ha g.length
    | some edges =>
      have hm : (n, edges) ∈ g := by
        obtain ⟨before, after, hg, _⟩ := List.lookup_eq_some_iff.mp hl
        simp [hg]
      simpa only [hl, stable] using rank_succ_row g hn (n, edges) hm g.length
  · exact rank_bound g hn g.length
  · exact graphRanks_complete g hn ⟨r, hr⟩

theorem certificate_iff (g : Graph) (hn : (g.map Prod.fst).Nodup) :
    (∃ r, certificate g = some r) ↔ ∃ r, Ranked g r :=
  ⟨fun ⟨r, h⟩ => ⟨r, certificate_sound g r h⟩, certificate_complete g hn⟩

end FastRanks

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
      (Item.name i, deps)

def designDeps (d : Core.Design) (fuel : Nat) : String → Option Deps :=
  let table := dependencyTable d fuel
  fun name => table.lookup name

/-!
A typed module is meaningful only inside a `Design`.
Its `Design.environments` proof ties its interfaces and children to the design.
Module semantics must therefore use that enclosing design.
-/
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
  context_eq : ctx = contextFromPorts interfaces ⟨pos, name, ports, equationsErase body⟩

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
def assembleDesign (top : String) (itemNames : List String) (externs : List Extern)
    (bodies : List Module) (topPos : Pos) : Core.Design :=
  let items := itemNames.filterMap fun n =>
    match bodies.find? (·.name == n) with
    | some m => some (.module m.erase)
    | none => (externs.find? (·.name == n)).map Item.extern
  ⟨top, items, topPos⟩

structure Design where
  top : String
  itemNames : List String
  externs : List Extern
  bodies : List Module
  topPos : Pos
  hierarchy : ordered (externs.map (·.name)) (bodies.map Module.erase) = true
  environments : ∀ m ∈ bodies,
    let d := assembleDesign top itemNames externs bodies topPos
    m.interfaces = portsOf d ∧ m.children = designDeps d d.depsFuel ∧
      Core.Item.module m.erase ∈ d.items

def Design.erase (d : Design) : Core.Design :=
  assembleDesign d.top d.itemNames d.externs d.bodies d.topPos

/-! Each module uses the interfaces and dependency contracts of its enclosing design. -/
theorem Design.module_context (d : Design) (m : Module) (hm : m ∈ d.bodies) :
    m.ctx = context d.erase m.erase := by
  have env := d.environments m hm
  exact m.context_eq.trans (congrArg (fun ps => contextFromPorts ps m.erase) env.1)


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
    let body ← statements d (context d m) m.body
    let dependencies := dependencyTable d d.depsFuel
    let children := fun name => dependencies.lookup name
    let graph := Deps.graph m children
    match hcert : FastRanks.certificate graph with
    | none => none
    | some ranks => do
      have h := FastRanks.certificate_sound graph ranks hcert
      let groups ← groupStatements (context d m) (portsOf d) body
      if hg : equationsErase groups = m.body then
        let typed : Module := ⟨m.pos, m.name, m.ports, context d m, portsOf d, groups,
          children, ranks, by simpa [graph, hg] using h,
          by rw [hg]; rfl⟩
        let rest ← elaborateModules d rest
        return typed :: rest
      else none

theorem elaborateModules_erase (d : Core.Design) (raw : List Core.Module) (ts : List Module)
    (h : elaborateModules d raw = some ts) : ts.map Module.erase = raw := by
  induction raw generalizing ts with
  | nil => cases h; rfl
  | cons m raw ih =>
    simp only [elaborateModules, statements, bind, Option.bind_eq_some_iff] at h
    obtain ⟨body, _, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨groups, _, h⟩ := h
    split at h <;> try contradiction
    next he =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨rest, hr, h⟩ := h
      cases h
      simp only [List.map_cons, Module.erase, he, ih _ hr]

theorem elaborateModules_environment (d : Core.Design) (raw : List Core.Module) (ts : List Module)
    (h : elaborateModules d raw = some ts) :
    ∀ m ∈ ts, m.interfaces = portsOf d ∧ m.children = designDeps d d.depsFuel := by
  induction raw generalizing ts with
  | nil => cases h; simp
  | cons m raw ih =>
    simp only [elaborateModules, statements, bind, Option.bind_eq_some_iff] at h
    obtain ⟨body, _, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨groups, _, h⟩ := h
    split at h <;> try contradiction
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨rest, hr, h⟩ := h
    cases h
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨trivial, rfl⟩, ih _ hr⟩

def elaborateDesign (d : Core.Design) : Option Design := do
  let sorted ← orderModules (modules d).length (externNames d) (modules d)
  if hc : sorted.Perm (modules d) then
    match hb : elaborateModules d sorted with
    | none => none
    | some bodies => do
      let externs := d.items.filterMap fun i => match i with
        | .extern e => some e | _ => none
      if hh : ordered (externs.map (·.name)) (bodies.map Module.erase) = true then
        let raw := assembleDesign d.top (d.items.map Item.name) externs bodies d.topPos
        if he : raw = d then
          have environment : ∀ m ∈ bodies,
              m.interfaces = portsOf raw ∧ m.children = designDeps raw raw.depsFuel ∧
                Core.Item.module m.erase ∈ raw.items := by
            intro m hm
            rw [he]
            obtain ⟨hi, hd⟩ := elaborateModules_environment d sorted bodies hb m hm
            refine ⟨hi, hd, ?_⟩
            have mem : m.erase ∈ modules d := hc.mem_iff.mp (by
              rw [← elaborateModules_erase d sorted bodies hb]
              exact List.mem_map.mpr ⟨m, hm, rfl⟩)
            obtain ⟨item, mem, eq⟩ := List.mem_filterMap.mp mem
            cases item <;> cases eq
            exact mem
          some ⟨d.top, d.items.map Item.name, externs, bodies, d.topPos, hh, environment⟩
        else none
      else none
  else none

theorem elaborateDesign_erase (d : Core.Design) (t : Design)
    (h : elaborateDesign d = some t) : t.erase = d := by
  simp only [elaborateDesign, bind, Option.bind_eq_some_iff] at h
  obtain ⟨sorted, _, h⟩ := h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  next he => cases h; exact he

end Silicon.Core.Typed
