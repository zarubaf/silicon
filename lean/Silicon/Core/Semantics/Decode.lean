import Silicon.Core.Semantics.Driver
import Silicon.Core.Semantics.MemoryOwner
import Silicon.Core.Semantics.Drivers

/-! Checked names and output coverage make driver decoding total. -/
namespace Silicon.Core.Semantics

open Typed

theorem valueDriver_exists (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (node : Deps.Node) (width : Nat)
    (found : m.ctx.lookup node = some (.value (.bits width))) :
    Nonempty (ValueDriver m node width) := by
  rcases Ownership.value_origin m node width found with hp | hl | hr | hi
  · obtain ⟨port, member, rfl, bits⟩ := hp
    cases hd : port.dir with
    | input => exact ⟨.input port member hd bits⟩
    | output =>
      obtain ⟨pos, raw, member, _⟩ := output_assignment d.erase wf m.erase
        (module_mem d m hm) port member hd
      obtain ⟨index, w, target, value, member, _⟩ :=
        Ownership.assign_equation m.body pos port.name raw member
      have hw : w = width := by
        have targetWidth : valueTy m.ctx port.name = some (.bits width) := by
          simp [valueTy, found]
        rw [targetWidth] at target
        exact Ty.bits.inj (Option.some.inj target).symm
      subst w
      exact ⟨.assign index pos port.name width target value member⟩
  · obtain ⟨pos, name, raw, member, rfl⟩ := hl
    obtain ⟨index, value, member, _⟩ := Ownership.let_equation m.body pos name width raw member
    exact ⟨.let_ index pos name width value member⟩
  · obtain ⟨pos, name, clock, raw, member, rfl⟩ := hr
    obtain ⟨index, target, reset, nextIndex, nextPos, next, member, _⟩ :=
      Ownership.reg_equation m.body pos name width clock raw member
    exact ⟨.reg index pos name width clock target reset nextIndex nextPos next member⟩
  · obtain ⟨pos, name, child, raw, port, member, portMember, dir, bits, rfl⟩ := hi
    obtain ⟨index, inputs, member, _⟩ := Ownership.inst_equation m.body pos name child raw member
    exact ⟨.inst index pos name child inputs member port portMember dir bits⟩

theorem memoryDriver_exists (m : Typed.Module) (name : String) (width depth : Nat)
    (found : m.ctx.lookup (.name name) = some (.memory width depth)) :
    Nonempty (MemoryDriver m name width depth) := by
  obtain ⟨index, pos, clock, target, writes, member⟩ :=
    Ownership.memory_equation m name width depth found
  exact ⟨.mem index pos name width depth clock target writes member⟩

noncomputable def decodeValue (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (node : Deps.Node) (width : Nat)
    (found : m.ctx.lookup node = some (.value (.bits width))) : ValueDriver m node width :=
  Classical.choice (valueDriver_exists d wf m hm node width found)

noncomputable def decodeMemory (m : Typed.Module) (name : String) (width depth : Nat)
    (found : m.ctx.lookup (.name name) = some (.memory width depth)) :
    MemoryDriver m name width depth :=
  Classical.choice (memoryDriver_exists m name width depth found)

end Silicon.Core.Semantics
