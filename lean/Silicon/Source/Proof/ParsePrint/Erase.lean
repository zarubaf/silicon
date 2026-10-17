-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Print
import Silicon.Source.Lex

/-!
The position erasure and the precondition of `parse_print` (section 10.3 of the front-end
spec).

The erasure sets each source position to line 0 and column 0. It also erases the position in
each `Ident` and each `Param`. Two ASTs are equal up to positions if their erasures are equal.

`Printable` is the precondition of the spec, as a `Bool` check. Each clause of the spec maps to
a check here:

- A name, a field, or a binder is a source identifier that is not a keyword: `validName`. A
  binder of a pattern is also not `_`, because the parser reads `_` as no binder: `binderOk`.
  The enum name and the variant name of a variant pattern are not `_`: `Pattern.printable`.
- No index is empty: `Expr.printable` and `TypeExpr.printable` at `index`.
- No tuple is empty: `Expr.printable` and `TypeExpr.printable` at `tuple`. The printer writes an
  empty tuple as `()`, which is the unit value or the unit type.
- Each module parameter and each struct parameter has `comptime`: `Param.printable true`.
- A `domains` declaration has at most one name: `Item.printable` at `module`.
- Each assignment and connection target is a place: `Expr.place`.
- No resource statement is in a `fn` without `comptime`: the flag `plain` of `Stmt.printable`.
- Each body has only the statement kinds that the parser accepts in that body. The parser
  accepts each statement kind in each body, except a resource in a `fn` without `comptime`.
  Thus the flag `plain` also covers this clause.
- No string has a control character other than LF, CR, and tab: `printableChar`.
- Each number is below 2^65536: `Expr.printable` at `num` and at `select`, and
  `Pattern.printable` at `int`.

A method name is a name in the sense of the first clause: `Expr.printable` at `method`.

The proof covers the container forms of slice 2. These are the unit value, the unit type, a
tuple, an array, an array type `[T; N]` in a type and in an expression, and a selector `.N`. It
also covers the type forms of phase 3: a `struct` item, and a `type` item or statement. It
covers the forms of phase 4: a `mut` parameter of a function, and a receiver call `x.m(args)`.
It covers the function types of phase 5, in a type and in an expression. It covers the enums,
the variant paths, and the `match` expressions with their patterns of slice 3. The first name of
a variant pattern is not `_`, because `_` starts the pattern `_`.
-/
namespace Silicon.Source

/-! The erased position. -/
def Pos.zero : Pos := ⟨0, 0⟩

def Ident.erase (i : Ident) : Ident := ⟨Pos.zero, i.name⟩

def Pattern.erase : Pattern → Pattern
  | .wild _ => .wild Pos.zero
  | .int _ neg v => .int Pos.zero neg v
  | .bool _ v => .bool Pos.zero v
  | .variant _ t v bs => .variant Pos.zero t.erase v.erase (bs.map (·.map Ident.erase))

mutual
def Expr.erase : Expr → Expr
  | .num _ v => .num Pos.zero v
  | .bool _ v => .bool Pos.zero v
  | .str _ v => .str Pos.zero v
  | .name _ n => .name Pos.zero n
  | .unary _ op a => .unary Pos.zero op a.erase
  | .binary _ op l r => .binary Pos.zero op l.erase r.erase
  | .cond _ c y n => .cond Pos.zero c.erase y.erase n.erase
  | .call _ f xs => .call Pos.zero f.erase (xs.map Expr.erase)
  | .index _ b xs => .index Pos.zero b.erase (xs.map Expr.erase)
  | .field _ b f => .field Pos.zero b.erase f.erase
  | .unit _ => .unit Pos.zero
  | .tuple _ xs => .tuple Pos.zero (xs.map Expr.erase)
  | .array _ xs => .array Pos.zero (xs.map Expr.erase)
  | .select _ b _ i => .select Pos.zero b.erase Pos.zero i
  | .arrayType _ t n => .arrayType Pos.zero t.erase n.erase
  | .method _ r m xs => .method Pos.zero r.erase m.erase (xs.map Expr.erase)
  | .fnType _ ps r => .fnType Pos.zero (ps.map FnParam.erase) r.erase
  | .path _ t v => .path Pos.zero t.erase v.erase
  | .«match» _ s arms => .«match» Pos.zero s.erase (arms.map Arm.erase)

def TypeExpr.erase : TypeExpr → TypeExpr
  | .name _ n => .name Pos.zero n
  | .index _ b xs => .index Pos.zero b.erase (xs.map Expr.erase)
  | .unit _ => .unit Pos.zero
  | .tuple _ ts => .tuple Pos.zero (ts.map TypeExpr.erase)
  | .array _ t n => .array Pos.zero t.erase n.erase
  | .fn _ ps r => .fn Pos.zero (ps.map FnParam.erase) r.erase

def FnParam.erase : FnParam → FnParam
  | .mk m t => .mk m t.erase

def Arm.erase : Arm → Arm
  | .mk p v => .mk p.erase v.erase
end

def Stmt.erase : Stmt → Stmt
  | .local _ m n ty v => .local Pos.zero m n.erase (ty.map TypeExpr.erase) v.erase
  | .assign _ t v => .assign Pos.zero t.erase v.erase
  | .connect _ t v => .connect Pos.zero t.erase v.erase
  | .reg _ n ty i => .reg Pos.zero n.erase ty.erase i.erase
  | .wire _ n ty => .wire Pos.zero n.erase ty.erase
  | .mem _ n ty d => .mem Pos.zero n.erase ty.erase d.erase
  | .input _ n ty => .input Pos.zero n.erase ty.erase
  | .output _ n ty => .output Pos.zero n.erase ty.erase
  | .inst _ n m xs => .inst Pos.zero n.erase m.erase (xs.map Expr.erase)
  | .ret _ v => .ret Pos.zero (v.map Expr.erase)
  | .ctIf _ c y none => .ctIf Pos.zero c.erase (y.map Stmt.erase) none
  | .ctIf _ c y (some n) => .ctIf Pos.zero c.erase (y.map Stmt.erase) (some (n.map Stmt.erase))
  | .ctFor _ i lo hi b => .ctFor Pos.zero i.erase lo.erase hi.erase (b.map Stmt.erase)
  | .block _ b => .block Pos.zero (b.map Stmt.erase)
  | .expr _ v => .expr Pos.zero v.erase
  | .alias _ n ty => .alias Pos.zero n.erase ty.erase

def Param.erase (p : Param) : Param := ⟨Pos.zero, p.mode, p.name.erase, p.ty.erase⟩

def StructField.erase (f : StructField) : StructField := ⟨f.name.erase, f.ty.erase⟩

def Variant.erase (v : Variant) : Variant :=
  ⟨v.name.erase, v.payload.map TypeExpr.erase, v.tag.erase⟩

def Item.erase : Item → Item
  | .const _ n ty v => .const Pos.zero n.erase ty.erase v.erase
  | .fn _ c n ps r b =>
    .fn Pos.zero c n.erase (ps.map Param.erase) r.erase (b.map Stmt.erase)
  | .module _ n ps ds b =>
    .module Pos.zero n.erase (ps.map Param.erase) (ds.map (·.map Ident.erase))
      (b.map Stmt.erase)
  | .struct _ n ps fs => .struct Pos.zero n.erase (ps.map Param.erase) (fs.map StructField.erase)
  | .alias _ n ty => .alias Pos.zero n.erase ty.erase
  | .enum _ n ty vs => .enum Pos.zero n.erase ty.erase (vs.map Variant.erase)

namespace ParsePrint

/-! A source identifier that is not a keyword. -/
def validName (s : String) : Bool :=
  match s.toList with
  | c :: cs => Lex.identStart c && cs.all Lex.identChar && !Lex.keywords.contains s
  | [] => false

/-!
A number literal is below this bound. It is irreducible, so that no elaboration step
computes the power.
-/
@[irreducible]
def numberBound : Nat := 2 ^ 65536

/-! A character that a string can hold: no control character except LF, CR, and tab. -/
def printableChar (c : Char) : Bool :=
  !Lex.control c || c == '\n' || c == '\r' || c == '\t'

end ParsePrint

open ParsePrint

/-!
A binder of a pattern: a name that is not `_`. The parser reads `_` as no binder, so a binder
`_` has the AST `none`.
-/
def binderOk : Option Ident → Bool
  | none => true
  | some i => validName i.name && i.name != "_"

/-!
A pattern. A literal is below 2^65536. The first name of a variant pattern is not `_`, because
`_` starts the pattern `_`. The variant name is not `_`, because `E::_` is `S001`.
-/
def Pattern.printable : Pattern → Bool
  | .wild _ | .bool .. => true
  | .int _ _ v => v < numberBound
  | .variant _ t v bs =>
    validName t.name && t.name != "_" && validName v.name && v.name != "_" && bs.all binderOk

/-! A place: a name, or a field, an index, or a selector of a place. -/
def Expr.place : Expr → Bool
  | .name .. => true
  | .field _ b _ | .index _ b _ | .select _ b .. => b.place
  | _ => false

mutual
  def Expr.printable : Expr → Bool
    | .num _ v => v < numberBound
    | .bool .. => true
    | .str _ s => s.toList.all printableChar
    | .name _ n => validName n
    | .unary _ _ a => a.printable
    | .binary _ _ l r => l.printable && r.printable
    | .cond _ c y n => c.printable && y.printable && n.printable
    | .call _ f xs => f.printable && Expr.printableAll xs
    | .index _ b xs => b.printable && !xs.isEmpty && Expr.printableAll xs
    | .field _ b f => b.printable && validName f.name
    | .unit _ => true
    | .tuple _ xs => !xs.isEmpty && Expr.printableAll xs
    | .array _ xs => Expr.printableAll xs
    | .select _ b _ i => b.printable && i < numberBound
    | .arrayType _ t n => t.printable && n.printable
    | .method _ r m xs => r.printable && validName m.name && Expr.printableAll xs
    | .fnType _ ps r => FnParam.printableAll ps && r.printable
    | .path _ t v => validName t.name && validName v.name
    | .«match» _ s arms => s.printable && Arm.printableAll arms

  def Expr.printableAll : List Expr → Bool
    | [] => true
    | x :: xs => x.printable && Expr.printableAll xs

  def TypeExpr.printable : TypeExpr → Bool
    | .name _ n => validName n
    | .index _ b xs => b.printable && !xs.isEmpty && Expr.printableAll xs
    | .unit _ => true
    | .tuple _ ts => !ts.isEmpty && TypeExpr.printableAll ts
    | .array _ t n => t.printable && n.printable
    | .fn _ ps r => FnParam.printableAll ps && r.printable

  def TypeExpr.printableAll : List TypeExpr → Bool
    | [] => true
    | t :: ts => t.printable && TypeExpr.printableAll ts

  def FnParam.printable : FnParam → Bool
    | .mk _ t => t.printable

  def FnParam.printableAll : List FnParam → Bool
    | [] => true
    | p :: ps => p.printable && FnParam.printableAll ps

  def Arm.printable : Arm → Bool
    | .mk p v => p.printable && v.printable

  def Arm.printableAll : List Arm → Bool
    | [] => true
    | a :: as => a.printable && Arm.printableAll as
end

mutual
  /-- A statement in a body. `plain` holds in the body of a `fn` without `comptime`. -/
  def Stmt.printable (plain : Bool) : Stmt → Bool
    | .local _ _ n ty v => validName n.name && ty.all TypeExpr.printable && v.printable
    | .assign _ t v => t.place && t.printable && v.printable
    | .connect _ t v => t.place && t.printable && v.printable
    | .reg _ n ty i => !plain && validName n.name && ty.printable && i.printable
    | .wire _ n ty => !plain && validName n.name && ty.printable
    | .mem _ n ty d => !plain && validName n.name && ty.printable && d.printable
    | .input _ n ty => !plain && validName n.name && ty.printable
    | .output _ n ty => !plain && validName n.name && ty.printable
    | .inst _ n m xs =>
      !plain && validName n.name && validName m.name && Expr.printableAll xs
    | .ret _ v => v.all Expr.printable
    | .ctIf _ c y none => c.printable && Stmt.printableAll plain y
    | .ctIf _ c y (some n) =>
      c.printable && Stmt.printableAll plain y && Stmt.printableAll plain n
    | .ctFor _ i lo hi b =>
      validName i.name && lo.printable && hi.printable && Stmt.printableAll plain b
    | .block _ b => Stmt.printableAll plain b
    | .expr _ v => v.printable
    | .alias _ n ty => validName n.name && ty.printable

  def Stmt.printableAll (plain : Bool) : List Stmt → Bool
    | [] => true
    | s :: ss => s.printable plain && Stmt.printableAll plain ss
end

/-!
A parameter mode. A module parameter or a struct parameter (`static`) has `comptime`. A function
parameter has at most one mark, `comptime` or `mut`.
-/
def ParamMode.printable (static : Bool) : ParamMode → Bool
  | .none => !static
  | .comptime => true
  | .mut => !static

def Param.printable (static : Bool) (p : Param) : Bool :=
  p.mode.printable static && validName p.name.name && p.ty.printable

def Variant.printable (v : Variant) : Bool :=
  validName v.name.name && v.payload.all TypeExpr.printable && v.tag.printable

def Item.printable : Item → Bool
  | .const _ n ty v => validName n.name && ty.printable && v.printable
  | .fn _ c n ps r b => validName n.name && ps.all (Param.printable false) && r.printable
      && Stmt.printableAll (!c) b
  | .module _ n ps ds b => validName n.name && ps.all (Param.printable true)
      && ds.all (fun ds => ds.length ≤ 1 && ds.all (validName ·.name))
      && Stmt.printableAll false b
  | .struct _ n ps fs => validName n.name && ps.all (Param.printable true)
      && fs.all (fun f => validName f.name.name && f.ty.printable)
  | .alias _ n ty => validName n.name && ty.printable
  | .enum _ n ty vs => validName n.name && ty.printable && vs.all Variant.printable

namespace ParsePrint

/-! The precondition of `parse_print`: an AST that the parser can give. -/
def Printable (items : List Item) : Prop := items.all Item.printable = true

instance (items : List Item) : Decidable (Printable items) :=
  inferInstanceAs (Decidable (_ = true))

end ParsePrint

/-!
These two induction principles follow the cases of `Expr.erase` and `TypeExpr.erase`. The
principle for an expression has no hypothesis for a type expression in it. The principle for a
type expression has no hypothesis for an expression in it. A proof that needs both hypotheses
uses `Expr.erase.mutual_induct`, or an induction on the number of tokens.
-/

theorem Expr.ind (motive : Expr → Prop)
    (case1 : ∀ pos v, motive (.num pos v))
    (case2 : ∀ pos v, motive (.bool pos v))
    (case3 : ∀ pos v, motive (.str pos v))
    (case4 : ∀ pos n, motive (.name pos n))
    (case5 : ∀ pos op a, motive a → motive (.unary pos op a))
    (case6 : ∀ pos op l r, motive l → motive r → motive (.binary pos op l r))
    (case7 : ∀ pos c y n, motive c → motive y → motive n → motive (.cond pos c y n))
    (case8 : ∀ pos f xs, motive f → (∀ x ∈ xs, motive x) → motive (.call pos f xs))
    (case9 : ∀ pos b xs, motive b → (∀ x ∈ xs, motive x) → motive (.index pos b xs))
    (case10 : ∀ pos b f, motive b → motive (.field pos b f))
    (case11 : ∀ pos, motive (.unit pos))
    (case12 : ∀ pos xs, (∀ x ∈ xs, motive x) → motive (.tuple pos xs))
    (case13 : ∀ pos xs, (∀ x ∈ xs, motive x) → motive (.array pos xs))
    (case14 : ∀ pos b litPos i, motive b → motive (.select pos b litPos i))
    (case15 : ∀ pos t n, motive n → motive (.arrayType pos t n))
    (case16 : ∀ pos r m xs, motive r → (∀ x ∈ xs, motive x) → motive (.method pos r m xs))
    (case17 : ∀ pos ps r, motive (.fnType pos ps r))
    (case18 : ∀ pos t v, motive (.path pos t v))
    (case19 : ∀ pos s arms, motive s → (∀ q v, Arm.mk q v ∈ arms → motive v) →
      motive (.match pos s arms))
    (e : Expr) : motive e :=
  Expr.erase.induct motive (fun a => ∀ q v, a = .mk q v → motive v) (fun _ => True)
    (fun _ => True) case1 case2 case3 case4 case5 case6
    case7 case8 case9 case10 case11 case12 case13 case14 (fun p t n _ ih => case15 p t n ih)
    case16 (fun p ps r _ _ => case17 p ps r) case18
    (fun p s arms ihs ih => case19 p s arms ihs fun q v h => ih _ h q v rfl)
    (fun _ _ ih _ _ h => by cases h; exact ih) (fun _ _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) e

theorem TypeExpr.ind (motive : TypeExpr → Prop)
    (case1 : ∀ pos n, motive (.name pos n))
    (case2 : ∀ pos b xs, motive b → motive (.index pos b xs))
    (case3 : ∀ pos, motive (.unit pos))
    (case4 : ∀ pos ts, (∀ x ∈ ts, motive x) → motive (.tuple pos ts))
    (case5 : ∀ pos t n, motive t → motive (.array pos t n))
    (case6 : ∀ pos ps r, (∀ m t, FnParam.mk m t ∈ ps → motive t) → motive r →
      motive (.fn pos ps r)) (t : TypeExpr) : motive t :=
  TypeExpr.erase.induct (fun _ => True) (fun _ => True) (fun p => ∀ m t, p = .mk m t → motive t)
    motive
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun _ _ ih _ _ h => by cases h; exact ih)
    case1 (fun p b xs ih _ => case2 p b xs ih) case3 case4 (fun p t n ih _ => case5 p t n ih)
    (fun p ps r ih ihr => case6 p ps r (fun m t h => ih _ h m t rfl) ihr) t

/-! The erasure is idempotent. -/

@[simp] theorem Ident.erase_name (i : Ident) : i.erase.name = i.name := rfl
@[simp] theorem Ident.erase_erase (i : Ident) : i.erase.erase = i.erase := rfl

@[simp] theorem Pattern.erase_erase (q : Pattern) : q.erase.erase = q.erase := by
  cases q <;> simp [Pattern.erase, List.map_map, Function.comp_def, Option.map_map]

private theorem erase_erase_all :
    (∀ e : Expr, e.erase.erase = e.erase) ∧ (∀ a : Arm, a.erase.erase = a.erase) ∧
      (∀ p : FnParam, p.erase.erase = p.erase) ∧ ∀ t : TypeExpr, t.erase.erase = t.erase := by
  apply Expr.erase.mutual_induct <;> intros <;>
    simp_all [Expr.erase, TypeExpr.erase, FnParam.erase, Arm.erase, List.map_map]

@[simp] theorem Expr.erase_erase (e : Expr) : e.erase.erase = e.erase := erase_erase_all.1 e

@[simp] theorem TypeExpr.erase_erase (t : TypeExpr) : t.erase.erase = t.erase :=
  erase_erase_all.2.2.2 t

@[simp] theorem Stmt.erase_erase (s : Stmt) : s.erase.erase = s.erase := by
  induction s using Stmt.erase.induct <;>
    simp_all [Stmt.erase, List.map_map, Option.map_map, Function.comp_def]

@[simp] theorem Param.erase_erase (p : Param) : p.erase.erase = p.erase := by
  simp [Param.erase]

@[simp] theorem StructField.erase_erase (f : StructField) : f.erase.erase = f.erase := by
  simp [StructField.erase]

@[simp] theorem Variant.erase_erase (v : Variant) : v.erase.erase = v.erase := by
  simp [Variant.erase, List.map_map, Function.comp_def]

@[simp] theorem Item.erase_erase (i : Item) : i.erase.erase = i.erase := by
  cases i <;> simp [Item.erase, List.map_map, Option.map_map, Function.comp_def]

/-! The printer ignores positions, so the text of an AST is the text of its erasure. -/

@[simp] theorem Expr.level_erase (e : Expr) : e.erase.level = e.level := by
  cases e <;> simp [Expr.erase, Expr.level]

theorem Pattern.binderText_erase (o : Option Ident) :
    Pattern.binderText (o.map Ident.erase) = Pattern.binderText o := by
  cases o <;> rfl

theorem Pattern.print_erase (q : Pattern) : q.erase.print = q.print := by
  cases q <;> simp [Pattern.erase, Pattern.print, List.map_map, Function.comp_def,
    Pattern.binderText_erase]

private theorem print_erase_all :
    (∀ e : Expr, ∀ c, e.erase.print c = e.print c) ∧ (∀ a : Arm, a.erase.print = a.print) ∧
      (∀ p : FnParam, p.erase.print = p.print) ∧ ∀ t : TypeExpr, t.erase.print = t.print := by
  apply Expr.erase.mutual_induct
  case case19 =>
    intro p s arms ihs ih c
    have hm : List.map (fun x => x.erase.print) arms = List.map Arm.print arms :=
      List.map_congr_left fun x hx => ih x hx
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, ihs, List.map_map, Function.comp_def, hm] <;> rfl
  case case20 =>
    intro q v ih
    simp [Arm.erase, Arm.print, ih, Pattern.print_erase]
  case case8 =>
    intro p f xs ihf ih c
    have hm : List.map (fun x => Expr.print 0 x.erase) xs = List.map (Expr.print 0) xs :=
      List.map_congr_left fun x hx => ih x hx 0
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, ihf, List.map_map, Function.comp_def, hm]
    cases f <;> simp only [Expr.erase] <;> rfl
  case case9 =>
    intro p f xs ihf ih c
    have hm : List.map (fun x => Expr.print 0 x.erase) xs = List.map (Expr.print 0) xs :=
      List.map_congr_left fun x hx => ih x hx 0
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, ihf, List.map_map, Function.comp_def, hm] <;> rfl
  case case16 =>
    intro p r m xs ihr ih c
    have hm : List.map (fun x => Expr.print 0 x.erase) xs = List.map (Expr.print 0) xs :=
      List.map_congr_left fun x hx => ih x hx 0
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, ihr, List.map_map, Function.comp_def, hm, Ident.erase_name] <;> rfl
  case case12 | case13 =>
    intro p xs ih c
    have hm : List.map (fun x => Expr.print 0 x.erase) xs = List.map (Expr.print 0) xs :=
      List.map_congr_left fun x hx => ih x hx 0
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, List.map_map, Function.comp_def, hm, List.length_map] <;> rfl
  case case17 =>
    intro p ps r ih ihr c
    have hm : List.map (fun x => x.erase.print) ps = List.map FnParam.print ps :=
      List.map_congr_left fun x hx => ih x hx
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, ihr, List.map_map, Function.comp_def, hm] <;> rfl
  case case21 =>
    intro m t ih
    simp [FnParam.erase, FnParam.print, ih]
  case case23 =>
    intro p b xs ihb ih
    have hm : List.map (fun x => Expr.print 0 x.erase) xs = List.map (Expr.print 0) xs :=
      List.map_congr_left fun x hx => ih x hx 0
    simp only [TypeExpr.erase]
    conv => lhs; rw [TypeExpr.print.eq_def]
    conv => rhs; rw [TypeExpr.print.eq_def]
    simp only [List.map_map, Function.comp_def, hm, ihb]
    cases b <;> simp only [TypeExpr.erase] <;> rfl
  case case25 =>
    intro p ts ih
    have hm : List.map (fun t => t.erase.print) ts = List.map TypeExpr.print ts :=
      List.map_congr_left fun t ht => ih t ht
    simp [TypeExpr.erase, TypeExpr.print, List.map_map, Function.comp_def, hm]
  case case27 =>
    intro p ps r ih ihr
    have hm : List.map (fun x => x.erase.print) ps = List.map FnParam.print ps :=
      List.map_congr_left fun x hx => ih x hx
    simp [TypeExpr.erase, TypeExpr.print, List.map_map, Function.comp_def, hm, ihr]
  case case22 | case24 | case26 =>
    intros
    simp_all [TypeExpr.erase, TypeExpr.print]
  all_goals
    intros
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp_all [Expr.level] <;> rfl

theorem Expr.print_erase (e : Expr) : ∀ c, e.erase.print c = e.print c :=
  print_erase_all.1 e

theorem TypeExpr.print_erase (t : TypeExpr) : t.erase.print = t.print :=
  print_erase_all.2.2.2 t

theorem Stmt.lines_erase (l : List Stmt) (h : ∀ s ∈ l, ∀ d, s.erase.print d = s.print d) :
    ∀ d, Stmt.lines d (l.map Stmt.erase) = Stmt.lines d l := by
  induction l with
  | nil => intro d; rfl
  | cons s ss ih =>
    intro d
    simp only [List.map, Stmt.lines]
    rw [h s (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem Stmt.body_erase (l : List Stmt) (h : ∀ s ∈ l, ∀ d, s.erase.print d = s.print d) :
    ∀ d, Stmt.body d (l.map Stmt.erase) = Stmt.body d l := by
  intro d
  cases l with
  | nil => rfl
  | cons s ss =>
    simp only [List.map, Stmt.body]
    rw [← List.map_cons, Stmt.lines_erase _ h]

theorem Stmt.print_erase (s : Stmt) : ∀ d, s.erase.print d = s.print d := by
  induction s using Stmt.erase.induct with
  | case10 _ v => intro d; cases v <;> simp [Stmt.erase, Stmt.print, Expr.print_erase]
  | _ => intro d; simp_all [Stmt.erase, Stmt.print, Expr.print_erase, TypeExpr.print_erase,
      List.map_map, Function.comp_def, Stmt.body_erase]

theorem Param.print_erase (p : Param) : p.erase.print = p.print := by
  simp only [Param.erase, Param.print, TypeExpr.print_erase, Ident.erase_name]

theorem StructField.print_erase (f : StructField) : f.erase.print = f.print := by
  simp only [StructField.erase, StructField.print, TypeExpr.print_erase, Ident.erase_name]

theorem Variant.print_erase (v : Variant) : v.erase.print = v.print := by
  simp [Variant.erase, Variant.print, Expr.print_erase, TypeExpr.print_erase, List.map_map,
    Function.comp_def]

theorem Item.print_erase (i : Item) : i.erase.print = i.print := by
  rcases i with _ | _ | ⟨_, _, _, _ | _, _⟩ | _ | _ | _ <;>
    simp [Item.erase, Item.print, Expr.print_erase, TypeExpr.print_erase,
      Param.print_erase, StructField.print_erase, Variant.print_erase, List.map_map,
      Function.comp_def, Stmt.body_erase, Stmt.print_erase]

theorem Print.print_erase (items : List Item) :
    Print.print (items.map Item.erase) = Print.print items := by
  simp [Print.print, List.map_map, Function.comp_def, Item.print_erase]

/-! `Printable` ignores positions. -/

@[simp] theorem Expr.place_erase (e : Expr) : e.erase.place = e.place := by
  induction e using Expr.ind <;> simp_all [Expr.erase, Expr.place]

private theorem all_congr_mem {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l <;> simp_all

theorem Expr.printableAll_eq (xs : List Expr) :
    Expr.printableAll xs = xs.all Expr.printable := by
  induction xs <;> simp_all [Expr.printableAll]

theorem TypeExpr.printableAll_eq (ts : List TypeExpr) :
    TypeExpr.printableAll ts = ts.all TypeExpr.printable := by
  induction ts <;> simp_all [TypeExpr.printableAll]

theorem FnParam.printableAll_eq (ps : List FnParam) :
    FnParam.printableAll ps = ps.all FnParam.printable := by
  induction ps <;> simp_all [FnParam.printableAll]

theorem Arm.printableAll_eq (as : List Arm) :
    Arm.printableAll as = as.all Arm.printable := by
  induction as <;> simp_all [Arm.printableAll]

@[simp] theorem Pattern.printable_erase (q : Pattern) : q.erase.printable = q.printable := by
  cases q with
  | variant _ t v bs =>
    have : ∀ o : Option Ident, binderOk (o.map Ident.erase) = binderOk o := by
      intro o; cases o <;> rfl
    simp [Pattern.erase, Pattern.printable, List.all_map, Function.comp_def, this]
  | _ => rfl

theorem Stmt.printableAll_eq (plain : Bool) (ss : List Stmt) :
    Stmt.printableAll plain ss = ss.all (Stmt.printable plain) := by
  induction ss <;> simp_all [Stmt.printableAll]

private theorem printable_erase_all :
    (∀ e : Expr, e.erase.printable = e.printable) ∧
      ∀ t : TypeExpr, t.erase.printable = t.printable := by
  suffices h : (∀ e : Expr, e.erase.printable = e.printable) ∧
      (∀ a : Arm, a.erase.printable = a.printable) ∧
      (∀ p : FnParam, p.erase.printable = p.printable) ∧
      ∀ t : TypeExpr, t.erase.printable = t.printable from ⟨h.1, h.2.2.2⟩
  apply Expr.erase.mutual_induct
  case case19 =>
    intro p s arms ihs ih
    simp only [Expr.erase, Expr.printable, ihs, Arm.printableAll_eq, List.all_map,
      Function.comp_def]
    rw [all_congr_mem ih]
  case case20 =>
    intro q v ih
    simp only [Arm.erase, Arm.printable, ih, Pattern.printable_erase]
  case case17 =>
    intro p ps r ih ihr
    simp only [Expr.erase, Expr.printable, ihr, FnParam.printableAll_eq, List.all_map,
      Function.comp_def]
    rw [all_congr_mem ih]
  case case21 =>
    intro m t ih
    simp only [FnParam.erase, FnParam.printable, ih]
  case case27 =>
    intro p ps r ih ihr
    simp only [TypeExpr.erase, TypeExpr.printable, ihr, FnParam.printableAll_eq, List.all_map,
      Function.comp_def]
    rw [all_congr_mem ih]
  case case8 | case9 =>
    intro p f xs ihf ih
    simp only [Expr.erase, Expr.printable, ihf, Expr.printableAll_eq, List.all_map,
      Function.comp_def, List.isEmpty_map]
    rw [all_congr_mem ih]
  case case16 =>
    intro p r m xs ihr ih
    simp only [Expr.erase, Expr.printable, ihr, Expr.printableAll_eq, List.all_map,
      Function.comp_def, Ident.erase_name]
    rw [all_congr_mem ih]
  case case12 | case13 =>
    intro p xs ih
    simp only [Expr.erase, Expr.printable, Expr.printableAll_eq, List.all_map,
      Function.comp_def, List.isEmpty_map]
    rw [all_congr_mem ih]
  case case23 =>
    intro p b xs ihb ih
    simp only [TypeExpr.erase, TypeExpr.printable, ihb, Expr.printableAll_eq, List.all_map,
      Function.comp_def, List.isEmpty_map]
    rw [all_congr_mem ih]
  case case25 =>
    intro p ts ih
    simp only [TypeExpr.erase, TypeExpr.printable, TypeExpr.printableAll_eq, List.all_map,
      Function.comp_def, List.isEmpty_map]
    rw [all_congr_mem ih]
  all_goals intros; simp_all [Expr.erase, Expr.printable, TypeExpr.erase, TypeExpr.printable]

@[simp] theorem Expr.printable_erase (e : Expr) : e.erase.printable = e.printable :=
  printable_erase_all.1 e

@[simp] theorem TypeExpr.printable_erase (t : TypeExpr) : t.erase.printable = t.printable :=
  printable_erase_all.2 t

@[simp] theorem Stmt.printable_erase (plain : Bool) (s : Stmt) :
    s.erase.printable plain = s.printable plain := by
  induction s using Stmt.erase.induct with
  | case11 _ c y ih =>
    simp only [Stmt.erase, Stmt.printable, Expr.printable_erase, Stmt.printableAll_eq,
      List.all_map, Function.comp_def]
    rw [all_congr_mem ih]
  | case12 _ c y n ihy ihn =>
    simp only [Stmt.erase, Stmt.printable, Expr.printable_erase, Stmt.printableAll_eq,
      List.all_map, Function.comp_def]
    rw [all_congr_mem ihy, all_congr_mem ihn]
  | case13 _ i lo hi b ih =>
    simp only [Stmt.erase, Stmt.printable, Expr.printable_erase, Stmt.printableAll_eq,
      List.all_map, Function.comp_def, Ident.erase_name]
    rw [all_congr_mem ih]
  | case14 _ b ih =>
    simp only [Stmt.erase, Stmt.printable, Stmt.printableAll_eq, List.all_map,
      Function.comp_def]
    rw [all_congr_mem ih]
  | case1 _ _ _ ty _ => cases ty <;> simp [Stmt.erase, Stmt.printable]
  | case10 _ v => cases v <;> simp [Stmt.erase, Stmt.printable]
  | _ => simp [Stmt.erase, Stmt.printable, Expr.printableAll_eq, List.all_map,
      Function.comp_def]

@[simp] theorem Param.printable_erase (static : Bool) (p : Param) :
    p.erase.printable static = p.printable static := by
  simp [Param.erase, Param.printable]

@[simp] theorem Variant.printable_erase (v : Variant) : v.erase.printable = v.printable := by
  simp [Variant.erase, Variant.printable, List.all_map, Function.comp_def]

@[simp] theorem Item.printable_erase (i : Item) : i.erase.printable = i.printable := by
  rcases i with _ | _ | ⟨_, _, _, _ | _, _⟩ | _ | _ | _ <;>
    simp [Item.erase, Item.printable, Stmt.printableAll_eq, List.all_map, Function.comp_def,
      StructField.erase]

theorem ParsePrint.printable_erase (items : List Item) :
    ParsePrint.Printable (items.map Item.erase) ↔ ParsePrint.Printable items := by
  simp [ParsePrint.Printable, Function.comp_def]

end Silicon.Source
