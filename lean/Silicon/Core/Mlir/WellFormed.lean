-- SPDX-License-Identifier: Apache-2.0
import Silicon.Core.Mlir.Semantics

/-!
Types constrain equations without imposing an order on their operands.
Module ranks constrain only the instance hierarchy, so sibling feedback remains valid.
-/
namespace Silicon.Core.Mlir

def Op.resultTypes : Op → List Ty
  | .constant w _ | .comb _ _ _ w => [.int w]
  | .icmp .. => [.int 1]
  | .mux _ _ _ ty | .compreg _ _ _ ty => [ty]
  | .extract _ _ _ wo | .replicate _ _ wo => [.int wo]
  | .concat _ _ wa wb => [.int (wa + wb)]
  | .arrayGet _ _ _ w _ => [.int w]
  | .arrayInject _ _ _ n w _ => [.array n w]
  | .instance _ _ _ results => results.map Prod.snd

def Op.operands : Op → List (String × Ty)
  | .constant .. => []
  | .comb _ a b w | .icmp _ a b w => [(a, .int w), (b, .int w)]
  | .mux c a b ty => [(c, .int 1), (a, ty), (b, ty)]
  | .extract a _ wi _ | .replicate a wi _ => [(a, .int wi)]
  | .concat a b wa wb => [(a, .int wa), (b, .int wb)]
  | .compreg next clk reset ty => [(next, ty), (clk, .clock)] ++
      (reset.toList.flatMap fun (s, v) => [(s, .int 1), (v, ty)])
  | .arrayGet arr idx n w a => [(arr, .array n w), (idx, .int a)]
  | .arrayInject arr idx v n w a => [(arr, .array n w), (idx, .int a), (v, .int w)]
  | .instance _ _ args _ => args.map fun (_, value, ty) => (value, ty)

def Op.Valid : Op → Prop
  | .constant w value => value < 2 ^ w
  | .extract _ lo wi wo => lo + wo ≤ wi
  | .replicate _ wi wo => wi * (wo / wi) = wo ∧ 0 < wi
  | .arrayGet _ _ n _ a | .arrayInject _ _ _ n _ a => n = 2 ^ a
  | _ => True

def Module.definitions (m : Module) : List (String × Ty) :=
  (m.inputPorts.map fun p => (p.name, p.ty)) ++
    m.body.flatMap (fun (names, op) => names.zip op.resultTypes)

def Item.name : Item → String
  | .module m => m.name
  | .extern name _ => name

def Item.ports : Item → List Port
  | .module m => m.ports
  | .extern _ ports => ports

def Design.signature (d : Design) (name : String) : Option (List Port) :=
  (d.items.find? (·.name == name)).map Item.ports

def Module.WellFormed (d : Design) (m : Module) : Prop :=
  (m.ports.map Port.name).Nodup ∧
  (m.definitions.map Prod.fst).Nodup ∧
  (m.body.filterMap (fun (_, op) => match op with
    | .instance name .. => some name | _ => none)).Nodup ∧
  (∀ entry ∈ m.body,
    entry.1.length = entry.2.resultTypes.length ∧ entry.2.Valid ∧
    (∀ operand ∈ entry.2.operands, m.definitions.lookup operand.1 = some operand.2) ∧
    (match entry.2 with
    | .instance _ callee args results => ∃ ports, d.signature callee = some ports ∧
        args.map (fun (pin, _, ty) => (pin, ty)) =
          ((ports.filter (·.dir == .input)).map fun p => (p.name, p.ty)) ∧
        results = ((ports.filter (·.dir == .output)).map fun p => (p.name, p.ty))
    | _ => True)) ∧
  m.outputs.length = m.outputPorts.length ∧
  (∀ pair ∈ m.outputs.zip m.outputPorts,
    m.definitions.lookup pair.1 = some pair.2.ty)

def WellFormed (d : Design) : Prop :=
  (d.items.map Item.name).Nodup ∧
  (∀ item ∈ d.items, (item.ports.map Port.name).Nodup) ∧
  (∀ m, .module m ∈ d.items → m.WellFormed d) ∧
  ∃ rank : String → Nat, ∀ m, .module m ∈ d.items →
    ∀ names inst callee args results,
      (names, .instance inst callee args results) ∈ m.body → rank callee < rank m.name

end Silicon.Core.Mlir
