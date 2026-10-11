-- SPDX-License-Identifier: Apache-2.0
/-!
Silicon reserves no name. A core name is a list of fields, joined by one `$`.
A backend name joins its parts with `$$`, so it never equals a core name.
-/
namespace Silicon.Core

def nameStart (c : Char) : Bool := c.isAlpha || c == '_'

def fieldChar (c : Char) : Bool := nameStart c || c.isDigit

/-! After the first character, a `$` separates two fields. A field character must follow it. -/
def fieldsRest : List Char → Bool
  | [] => true
  | c :: cs =>
    (if c == '$' then (match cs with | d :: _ => fieldChar d | [] => false) else fieldChar c) &&
      fieldsRest cs

/-! The name pattern of the core IR spec, section 3, without the keyword rule. -/
def namePattern (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => nameStart c && fieldsRest cs

/-! The parts of a backend name follow its kind, each after `$$`. -/
def joinParts : String → List String → String
  | first, [] => first
  | first, next :: rest => first ++ "$$" ++ joinParts next rest

def backendName (kind : String) (args : List String) : String := joinParts kind args

/-! A register gets the backend name `reg$$<n>`. A memory model calls its register `mem`. -/
def regName (n : String) : String := backendName "reg" [n]

/-! A part of a backend name matches the name pattern or contains no `$`. -/
def BackendPart (p : String) : Prop := namePattern p = true ∨ '$' ∉ p.toList

private def NoPair (l : List Char) : Prop := ∀ a b, l ≠ a ++ '$' :: '$' :: b

private def NoTrail (l : List Char) : Prop := ∀ a, l ≠ a ++ ['$']

private theorem fieldsRest_pair (a b : List Char) :
    fieldsRest (a ++ '$' :: '$' :: b) = false := by
  induction a with
  | nil => simp [fieldsRest, fieldChar, nameStart]
  | cons c cs ih => simp [fieldsRest, ih]

private theorem fieldsRest_trail (a : List Char) : fieldsRest (a ++ ['$']) = false := by
  induction a with
  | nil => simp [fieldsRest]
  | cons c cs ih => simp [fieldsRest, ih]

private theorem fieldsRest_chars (l : List Char) (h : fieldsRest l = true) :
    ∀ c ∈ l, c = '$' ∨ fieldChar c = true := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    simp only [fieldsRest, Bool.and_eq_true] at h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · by_cases hd : x = '$'
      · exact .inl hd
      · simp [hd] at h
        exact .inr h.1
    · exact ih h.2 x hx

theorem namePattern_head (s : String) (h : namePattern s = true) :
    ∃ c cs, s.toList = c :: cs ∧ nameStart c = true := by
  unfold namePattern at h
  cases hs : s.toList with
  | nil => simp [hs] at h
  | cons c cs =>
    simp only [hs, Bool.and_eq_true] at h
    exact ⟨c, cs, rfl, h.1⟩

theorem namePattern_chars (s : String) (h : namePattern s = true) :
    ∀ c ∈ s.toList, c = '$' ∨ fieldChar c = true := by
  unfold namePattern at h
  cases hs : s.toList with
  | nil => simp
  | cons c cs =>
    simp only [hs, Bool.and_eq_true] at h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact .inr (by simp [fieldChar, h.1])
    · exact fieldsRest_chars cs h.2 x hx

theorem namePattern_no_dot (s : String) (h : namePattern s = true) : '.' ∉ s.toList := by
  intro hd
  rcases namePattern_chars s h '.' hd with hc | hc
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)

private theorem namePattern_noPair (s : String) (h : namePattern s = true) : NoPair s.toList := by
  intro a b hs
  unfold namePattern at h
  rw [hs] at h
  cases a with
  | nil => simp [nameStart] at h
  | cons c cs => simp [fieldsRest_pair] at h

private theorem namePattern_noTrail (s : String) (h : namePattern s = true) :
    NoTrail s.toList := by
  intro a hs
  unfold namePattern at h
  rw [hs] at h
  cases a with
  | nil => simp [nameStart] at h
  | cons c cs => simp [fieldsRest_trail] at h

private theorem part_noPair (p : String) (h : BackendPart p) : NoPair p.toList := by
  rcases h with h | h
  · exact namePattern_noPair p h
  · intro a b hs
    exact h (by simp [hs])

private theorem part_noTrail (p : String) (h : BackendPart p) : NoTrail p.toList := by
  rcases h with h | h
  · exact namePattern_noTrail p h
  · intro a hs
    exact h (by simp [hs])

/-! The first part ends at the first `$$`. A longer first part would contain `$$` or end in `$`. -/
private theorem prefix_eq {x y r s : List Char}
    (px : NoPair x) (tx : NoTrail x) (py : NoPair y) (ty : NoTrail y)
    (hr : r = [] ∨ ∃ r', r = '$' :: '$' :: r') (hs : s = [] ∨ ∃ s', s = '$' :: '$' :: s')
    (h : x ++ r = y ++ s) : x = y := by
  rcases List.append_eq_append_iff.mp h with ⟨t, hy, hr'⟩ | ⟨t, hx, hs'⟩
  · cases t with
    | nil => simpa using hy.symm
    | cons c t =>
      rcases hr with rfl | ⟨r', rfl⟩
      · simp at hr'
      · simp only [List.cons_append, List.cons.injEq] at hr'
        obtain ⟨rfl, hr'⟩ := hr'
        cases t with
        | nil => exact absurd hy (ty x)
        | cons d t =>
          simp only [List.cons_append, List.cons.injEq] at hr'
          obtain ⟨rfl, -⟩ := hr'
          exact absurd hy (py x t)
  · cases t with
    | nil => simpa using hx
    | cons c t =>
      rcases hs with rfl | ⟨s', rfl⟩
      · simp at hs'
      · simp only [List.cons_append, List.cons.injEq] at hs'
        obtain ⟨rfl, hs'⟩ := hs'
        cases t with
        | nil => exact absurd hx (tx y)
        | cons d t =>
          simp only [List.cons_append, List.cons.injEq] at hs'
          obtain ⟨rfl, -⟩ := hs'
          exact absurd hx (px y t)

private def encode : List Char → List (List Char) → List Char
  | first, [] => first
  | first, next :: rest => first ++ '$' :: '$' :: encode next rest

private theorem joinParts_toList (first : String) (rest : List String) :
    (joinParts first rest).toList = encode first.toList (rest.map String.toList) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    simp only [joinParts, String.toList_append, ih, List.map_cons, encode, List.append_assoc]
    rfl

private theorem encode_injective (first first' : List Char) (rest rest' : List (List Char))
    (parts : ∀ p ∈ first :: rest, NoPair p ∧ NoTrail p)
    (parts' : ∀ p ∈ first' :: rest', NoPair p ∧ NoTrail p)
    (h : encode first rest = encode first' rest') : first = first' ∧ rest = rest' := by
  induction rest generalizing first first' rest' with
  | nil =>
    cases rest' with
    | nil => exact ⟨h, rfl⟩
    | cons next' tail' =>
      have hp := parts first (by simp)
      have hp' := parts' first' (by simp)
      have same := prefix_eq (r := []) hp.1 hp.2 hp'.1 hp'.2 (.inl rfl) (.inr ⟨_, rfl⟩)
        (by simpa [encode] using h)
      subst same
      simp [encode] at h
  | cons next tail ih =>
    have hp := parts first (by simp)
    have hp' := parts' first' (by simp)
    cases rest' with
    | nil =>
      have same := prefix_eq (s := []) hp.1 hp.2 hp'.1 hp'.2 (.inr ⟨_, rfl⟩) (.inl rfl)
        (by simpa [encode] using h)
      subst same
      simp [encode] at h
    | cons next' tail' =>
      have same := prefix_eq hp.1 hp.2 hp'.1 hp'.2 (.inr ⟨_, rfl⟩) (.inr ⟨_, rfl⟩) h
      subst same
      simp only [encode, List.append_cancel_left_eq, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih next next' tail'
        (fun p hp => parts p (List.mem_cons_of_mem _ hp))
        (fun p hp => parts' p (List.mem_cons_of_mem _ hp)) h
      exact ⟨rfl, by rw [h1, h2]⟩

/-! A backend name contains `$$`, so no backend name matches the name pattern. -/
theorem backend_name_not_core (kind : String) (args : List String) (h : args ≠ []) :
    namePattern (backendName kind args) = false := by
  cases args with
  | nil => exact absurd rfl h
  | cons next rest =>
    cases hp : namePattern (backendName kind (next :: rest)) with
    | false => rfl
    | true =>
      refine absurd ?_ (namePattern_noPair _ hp kind.toList (joinParts next rest).toList)
      simp [backendName, joinParts, String.toList_append]

/-! A split at each `$$` gives back the kind and the arguments. -/
theorem backend_name_injective {kind kind' : String} {args args' : List String}
    (parts : ∀ p ∈ kind :: args, BackendPart p) (parts' : ∀ p ∈ kind' :: args', BackendPart p)
    (h : backendName kind args = backendName kind' args') : kind = kind' ∧ args = args' := by
  have chars := congrArg String.toList h
  simp only [backendName, joinParts_toList] at chars
  have good : ∀ {k : String} {as : List String}, (∀ p ∈ k :: as, BackendPart p) →
      ∀ p ∈ k.toList :: as.map String.toList, NoPair p ∧ NoTrail p := by
    intro k as hk p hp
    simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact ⟨part_noPair k (hk k (by simp)), part_noTrail k (hk k (by simp))⟩
    · exact ⟨part_noPair q (hk q (by simp [hq])), part_noTrail q (hk q (by simp [hq]))⟩
  obtain ⟨h1, h2⟩ := encode_injective _ _ _ _ (good parts) (good parts') chars
  refine ⟨String.toList_inj.mp h1, ?_⟩
  simpa [List.map_map] using congrArg (List.map String.ofList) h2

theorem regName_eq (n : String) : regName n = "reg" ++ "$$" ++ n := rfl

theorem regName_injective {a b : String} (h : regName a = regName b) : a = b :=
  String.append_right_inj ("reg" ++ "$$") |>.mp h

theorem regName_not_core (n : String) : namePattern (regName n) = false :=
  backend_name_not_core "reg" [n] (by simp)

private theorem nameStart_digit (c : Char) (h : c.isDigit = true) : nameStart c = false := by
  have hv : c.toNat ≥ 48 ∧ c.toNat ≤ 57 := by
    simp [Char.isDigit, UInt32.le_iff_toNat_le] at h; exact h
  have hu : c ≠ '_' := by intro e; subst e; simp at hv
  simp [nameStart, Char.isAlpha, Char.isUpper, Char.isLower, UInt32.le_iff_toNat_le, hu]
  omega

/-! A temporary of the lowering has a decimal number as its name. It starts with a digit. -/
theorem decimal_not_core (i : Nat) : namePattern (toString i) = false := by
  unfold namePattern
  cases hs : (toString i).toList with
  | nil => rfl
  | cons c cs =>
    have digits : (toString i).toList = Nat.toDigits 10 i := Nat.toList_repr
    have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10)
      (show c ∈ Nat.toDigits 10 i by rw [← digits, hs]; simp)
    simp [nameStart_digit c digit]

end Silicon.Core
