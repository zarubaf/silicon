-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Semantics.Driver
import Silicon.Core.Semantics.Drivers
import Silicon.Core.Semantics.Ownership

/-! A decoded value or memory has one typed source in a well-formed design. -/
namespace Silicon.Core.Semantics

private theorem equation_source (m : Typed.Module) (e : Typed.Equation m.ctx m.interfaces)
    (he : e ∈ m.body) :
    ∃ stmt ∈ m.erase.body, Core.Stmt.driverName stmt = some (equationName e) := by
  cases e <;> (refine ⟨_, (Ownership.mem_equationsErase m.body _).mpr
    ⟨_, he, _, _, List.mem_cons_self .., rfl⟩, rfl⟩)

theorem input_not_equation (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (port : Port) (hp : port ∈ m.ports)
    (hi : port.dir = .input) (e : Typed.Equation m.ctx m.interfaces) (he : e ∈ m.body) :
    equationName e ≠ port.name := by
  intro hn
  obtain ⟨stmt, hs, hl⟩ := equation_source m e he
  exact Check.input_not_driver d.erase wf m.erase (module_mem d m hm) port hp hi stmt hs
    (hl.trans (congrArg some hn))

private theorem valueDriver_heq (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (a : ValueDriver m node width)
    (b : ValueDriver m other otherWidth) (hn : node = other) (hw : width = otherWidth) :
    HEq a b := by
  cases hw
  cases a <;> cases b
  all_goals try cases hn
  all_goals try
    exact False.elim (input_not_equation d wf m hm _ (by assumption)
      (by assumption) _ (by assumption) rfl)
  case refl.let_.let_.refl i p n expr mem j q expr' mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
    rfl
  case refl.let_.reg.refl i p n expr mem j q clock ni np reset next target mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
  case refl.let_.assign.refl i p n expr mem j q expr' target mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
  case refl.reg.let_.refl i p n clock ni np target reset next mem j q expr mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
  case refl.reg.reg.refl i p n clock ni np target reset next mem
      j q clock' ni' np' reset' next' target' mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
    rfl
  case refl.reg.assign.refl i p n clock ni np target reset next mem j q expr target' mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
  case refl.assign.let_.refl i p n target expr mem j q expr' mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
  case refl.assign.reg.refl i p n target expr mem j q clock ni np reset next target' mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
  case refl.assign.assign.refl i p n target expr mem j q expr' target' mem' =>
    have he := equation_unique d wf m hm _ _ mem mem' rfl
    cases he
    rfl
  case refl.input.input p hp hd ht q hq qd qt =>
    have ports := Check.module_ports_nodup d.erase m.erase wf (module_mem d m hm)
    have he := Check.named_port_eq m.ports p q ports hp hq (Deps.Node.name.inj hn)
    cases he
    rfl
  case refl.inst.inst i p n child inputs mem port portmem dir bits
      j q n' child' inputs' mem' port' portmem' dir' bits' =>
    have he := equation_unique d wf m hm _ _ mem mem' (Deps.Node.port.inj hn).1
    cases he
    have ports := Check.interface_unique d.erase wf.1 child
    have interfaces : m.interfaces = Typed.portsOf d.erase := (d.environments m hm).1
    rw [← interfaces] at ports
    have he := ports port portmem port' portmem' (Deps.Node.port.inj hn).2
    cases he
    rfl

theorem ValueDriver.unique (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (a b : ValueDriver m node width) : a = b :=
  eq_of_heq (valueDriver_heq d wf m hm a b rfl rfl)

theorem MemoryDriver.unique (d : Typed.Design) (wf : WellFormed d.erase)
    (m : Typed.Module) (hm : m ∈ d.bodies) (a b : MemoryDriver m name width depth) :
    a = b := by
  cases a with
  | mem i p n w dep clock target writes member =>
    cases b with
    | mem j q _ _ _ clock' target' writes' member' =>
      have he := equation_unique d wf m hm _ _ member member' rfl
      cases he
      rfl

end Silicon.Core.Semantics
