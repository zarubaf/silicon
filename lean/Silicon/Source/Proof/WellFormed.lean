-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Cli

/-!
The well-formedness of the elaboration (section 7 of the front-end spec). A `Cli.Checked`
carries the proof that the core check accepts its design, so `check_sound` gives `WellFormed`.
-/
namespace Silicon.Source.Proof

open Silicon.Core

/-! A successful checked elaboration gives a design that the core check accepts. -/
theorem elab_wellFormed (o : Cli.Opts) (src t : String) (dg : String → String)
    (c : Cli.Checked) (_h : Cli.elabChecked o src t dg = .ok c) :
    ∃ t, Core.check c.design = .ok t ∧ Core.WellFormed c.design :=
  ⟨c.typed, c.accepted, (check_sound c.design c.typed c.accepted).1⟩

end Silicon.Source.Proof
