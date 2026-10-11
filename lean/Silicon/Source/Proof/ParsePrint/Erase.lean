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

- A name, a field, or a binder is a source identifier that is not a keyword: `validName`.
- No index is empty: `Expr.printable` and `TypeExpr.printable` at `index`.
- Each module parameter has `comptime`: `Param.printable true`. The AST has no `mut` flag at a
  parameter, so no check is necessary for `mut` at a `fn` parameter.
- A `domains` declaration has at most one name: `Item.printable` at `module`.
- Each assignment and connection target is a place: `Expr.place`.
- No resource statement is in a `fn` without `comptime`: the flag `plain` of `Stmt.printable`.
- Each body has only the statement kinds that the parser accepts in that body. The parser
  accepts each statement kind in each body, except a resource in a `fn` without `comptime`.
  Thus the flag `plain` also covers this clause.
- No string has a control character other than LF, CR, and tab: `printableChar`.
- Each number is below 2^65536: `Expr.printable` at `num`.
-/
namespace Silicon.Source

/-! The erased position. -/
def Pos.zero : Pos := ⟨0, 0⟩

def Ident.erase (i : Ident) : Ident := ⟨Pos.zero, i.name⟩

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

def TypeExpr.erase : TypeExpr → TypeExpr
  | .name _ n => .name Pos.zero n
  | .index _ b xs => .index Pos.zero b.erase (xs.map Expr.erase)

def Stmt.erase : Stmt → Stmt
  | .local _ m n ty v => .local Pos.zero m n.erase (ty.map TypeExpr.erase) v.erase
  | .assign _ t v => .assign Pos.zero t.erase v.erase
  | .connect _ t v => .connect Pos.zero t.erase v.erase
  | .reg _ n ty i => .reg Pos.zero n.erase ty.erase i.erase
  | .wire _ n ty => .wire Pos.zero n.erase ty.erase
  | .input _ n ty => .input Pos.zero n.erase ty.erase
  | .output _ n ty => .output Pos.zero n.erase ty.erase
  | .inst _ n m xs => .inst Pos.zero n.erase m.erase (xs.map Expr.erase)
  | .ret _ v => .ret Pos.zero (v.map Expr.erase)
  | .ctIf _ c y none => .ctIf Pos.zero c.erase (y.map Stmt.erase) none
  | .ctIf _ c y (some n) => .ctIf Pos.zero c.erase (y.map Stmt.erase) (some (n.map Stmt.erase))
  | .ctFor _ i lo hi b => .ctFor Pos.zero i.erase lo.erase hi.erase (b.map Stmt.erase)
  | .block _ b => .block Pos.zero (b.map Stmt.erase)
  | .expr _ v => .expr Pos.zero v.erase

def Param.erase (p : Param) : Param := ⟨Pos.zero, p.comptime, p.name.erase, p.ty.erase⟩

def Item.erase : Item → Item
  | .const _ n ty v => .const Pos.zero n.erase ty.erase v.erase
  | .fn _ c n ps r b =>
    .fn Pos.zero c n.erase (ps.map Param.erase) r.erase (b.map Stmt.erase)
  | .module _ n ps ds b =>
    .module Pos.zero n.erase (ps.map Param.erase) (ds.map (·.map Ident.erase))
      (b.map Stmt.erase)

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

/-! A place of slice 1: a name, or a field of a place. -/
def Expr.place : Expr → Bool
  | .name .. => true
  | .field _ b _ => b.place
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

  def Expr.printableAll : List Expr → Bool
    | [] => true
    | x :: xs => x.printable && Expr.printableAll xs
end

def TypeExpr.printable : TypeExpr → Bool
  | .name _ n => validName n
  | .index _ b xs => b.printable && !xs.isEmpty && Expr.printableAll xs

mutual
  /-- A statement in a body. `plain` holds in the body of a `fn` without `comptime`. -/
  def Stmt.printable (plain : Bool) : Stmt → Bool
    | .local _ _ n ty v => validName n.name && ty.all TypeExpr.printable && v.printable
    | .assign _ t v => t.place && t.printable && v.printable
    | .connect _ t v => t.place && t.printable && v.printable
    | .reg _ n ty i => !plain && validName n.name && ty.printable && i.printable
    | .wire _ n ty => !plain && validName n.name && ty.printable
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

  def Stmt.printableAll (plain : Bool) : List Stmt → Bool
    | [] => true
    | s :: ss => s.printable plain && Stmt.printableAll plain ss
end

/-! A parameter. A module parameter (`static`) has `comptime`. -/
def Param.printable (static : Bool) (p : Param) : Bool :=
  (!static || p.comptime) && validName p.name.name && p.ty.printable

def Item.printable : Item → Bool
  | .const _ n ty v => validName n.name && ty.printable && v.printable
  | .fn _ c n ps r b => validName n.name && ps.all (Param.printable false) && r.printable
      && Stmt.printableAll (!c) b
  | .module _ n ps ds b => validName n.name && ps.all (Param.printable true)
      && ds.all (fun ds => ds.length ≤ 1 && ds.all (validName ·.name))
      && Stmt.printableAll false b

namespace ParsePrint

/-! The precondition of `parse_print`: an AST that the parser can give. -/
def Printable (items : List Item) : Prop := items.all Item.printable = true

instance (items : List Item) : Decidable (Printable items) :=
  inferInstanceAs (Decidable (_ = true))

end ParsePrint

/-! The erasure is idempotent. -/

@[simp] theorem Ident.erase_name (i : Ident) : i.erase.name = i.name := rfl
@[simp] theorem Ident.erase_erase (i : Ident) : i.erase.erase = i.erase := rfl

@[simp] theorem Expr.erase_erase (e : Expr) : e.erase.erase = e.erase := by
  induction e using Expr.erase.induct <;> simp_all [Expr.erase, List.map_map]

@[simp] theorem TypeExpr.erase_erase (t : TypeExpr) : t.erase.erase = t.erase := by
  induction t <;> simp_all [TypeExpr.erase, List.map_map]

@[simp] theorem Stmt.erase_erase (s : Stmt) : s.erase.erase = s.erase := by
  induction s using Stmt.erase.induct <;>
    simp_all [Stmt.erase, List.map_map, Option.map_map, Function.comp_def]

@[simp] theorem Param.erase_erase (p : Param) : p.erase.erase = p.erase := by
  simp [Param.erase]

@[simp] theorem Item.erase_erase (i : Item) : i.erase.erase = i.erase := by
  cases i <;> simp [Item.erase, List.map_map, Option.map_map, Function.comp_def]

/-! The printer ignores positions, so the text of an AST is the text of its erasure. -/

@[simp] theorem Expr.level_erase (e : Expr) : e.erase.level = e.level := by
  cases e <;> simp [Expr.erase, Expr.level]

theorem Expr.print_erase (e : Expr) : ∀ c, e.erase.print c = e.print c := by
  induction e using Expr.erase.induct with
  | case8 p f xs ihf ih =>
    intro c
    have hm : List.map (fun x => print 0 x.erase) xs = List.map (print 0) xs :=
      List.map_congr_left fun x hx => ih x hx 0
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, ihf, List.map_map, Function.comp_def, hm]
    cases f <;> simp only [Expr.erase] <;> rfl
  | case9 p f xs ihf ih =>
    intro c
    have hm : List.map (fun x => print 0 x.erase) xs = List.map (print 0) xs :=
      List.map_congr_left fun x hx => ih x hx 0
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp only [Expr.level, ihf, List.map_map, Function.comp_def, hm] <;> rfl
  | _ =>
    intro c
    simp only [Expr.erase]
    conv => lhs; rw [Expr.print.eq_def]
    conv => rhs; rw [Expr.print.eq_def]
    simp_all [Expr.level] <;> rfl

theorem TypeExpr.print_erase (t : TypeExpr) : t.erase.print = t.print := by
  induction t with
  | name => rfl
  | index p b xs ih =>
    simp [TypeExpr.erase, TypeExpr.print, ih, List.map_map, Function.comp_def,
      Expr.print_erase]

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
  | case9 _ v => intro d; cases v <;> simp [Stmt.erase, Stmt.print, Expr.print_erase]
  | _ => intro d; simp_all [Stmt.erase, Stmt.print, Expr.print_erase, TypeExpr.print_erase,
      List.map_map, Function.comp_def, Stmt.body_erase]

theorem Param.print_erase (p : Param) : p.erase.print = p.print := by
  simp only [Param.erase, Param.print, TypeExpr.print_erase, Ident.erase_name]; rfl

theorem Item.print_erase (i : Item) : i.erase.print = i.print := by
  rcases i with _ | _ | ⟨_, _, _, _ | _, _⟩ <;>
    simp [Item.erase, Item.print, Expr.print_erase, TypeExpr.print_erase,
      Param.print_erase, List.map_map, Function.comp_def, Stmt.body_erase, Stmt.print_erase]

theorem Print.print_erase (items : List Item) :
    Print.print (items.map Item.erase) = Print.print items := by
  simp [Print.print, List.map_map, Function.comp_def, Item.print_erase]

/-! `Printable` ignores positions. -/

@[simp] theorem Expr.place_erase (e : Expr) : e.erase.place = e.place := by
  induction e using Expr.erase.induct <;> simp_all [Expr.erase, Expr.place]

private theorem all_congr_mem {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l <;> simp_all

theorem Expr.printableAll_eq (xs : List Expr) :
    Expr.printableAll xs = xs.all Expr.printable := by
  induction xs <;> simp_all [Expr.printableAll]

theorem Stmt.printableAll_eq (plain : Bool) (ss : List Stmt) :
    Stmt.printableAll plain ss = ss.all (Stmt.printable plain) := by
  induction ss <;> simp_all [Stmt.printableAll]

@[simp] theorem Expr.printable_erase (e : Expr) : e.erase.printable = e.printable := by
  induction e using Expr.erase.induct with
  | case8 _ f xs ihf ih =>
    simp only [Expr.erase, Expr.printable, ihf, Expr.printableAll_eq, List.all_map,
      Function.comp_def]
    rw [all_congr_mem ih]
  | case9 _ f xs ihf ih =>
    simp only [Expr.erase, Expr.printable, ihf, Expr.printableAll_eq, List.all_map,
      Function.comp_def, List.isEmpty_map]
    rw [all_congr_mem ih]
  | _ => simp_all [Expr.erase, Expr.printable]

@[simp] theorem TypeExpr.printable_erase (t : TypeExpr) : t.erase.printable = t.printable := by
  induction t <;> simp_all [TypeExpr.erase, TypeExpr.printable, Expr.printableAll_eq,
    List.all_map, Function.comp_def]

@[simp] theorem Stmt.printable_erase (plain : Bool) (s : Stmt) :
    s.erase.printable plain = s.printable plain := by
  induction s using Stmt.erase.induct with
  | case10 _ c y ih =>
    simp only [Stmt.erase, Stmt.printable, Expr.printable_erase, Stmt.printableAll_eq,
      List.all_map, Function.comp_def]
    rw [all_congr_mem ih]
  | case11 _ c y n ihy ihn =>
    simp only [Stmt.erase, Stmt.printable, Expr.printable_erase, Stmt.printableAll_eq,
      List.all_map, Function.comp_def]
    rw [all_congr_mem ihy, all_congr_mem ihn]
  | case12 _ i lo hi b ih =>
    simp only [Stmt.erase, Stmt.printable, Expr.printable_erase, Stmt.printableAll_eq,
      List.all_map, Function.comp_def, Ident.erase_name]
    rw [all_congr_mem ih]
  | case13 _ b ih =>
    simp only [Stmt.erase, Stmt.printable, Stmt.printableAll_eq, List.all_map,
      Function.comp_def]
    rw [all_congr_mem ih]
  | case1 _ _ _ ty _ => cases ty <;> simp [Stmt.erase, Stmt.printable]
  | case9 _ v => cases v <;> simp [Stmt.erase, Stmt.printable]
  | _ => simp [Stmt.erase, Stmt.printable, Expr.printableAll_eq, List.all_map,
      Function.comp_def]

@[simp] theorem Param.printable_erase (static : Bool) (p : Param) :
    p.erase.printable static = p.printable static := by
  simp [Param.erase, Param.printable]

@[simp] theorem Item.printable_erase (i : Item) : i.erase.printable = i.printable := by
  rcases i with _ | _ | ⟨_, _, _, _ | _, _⟩ <;>
    simp [Item.erase, Item.printable, Stmt.printableAll_eq, List.all_map, Function.comp_def]

theorem ParsePrint.printable_erase (items : List Item) :
    ParsePrint.Printable (items.map Item.erase) ↔ ParsePrint.Printable items := by
  simp [ParsePrint.Printable, Function.comp_def]

end Silicon.Source
