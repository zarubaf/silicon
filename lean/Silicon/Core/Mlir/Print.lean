import Silicon.Core.Mlir.Syntax

namespace Silicon.Core.Mlir

private def tyText : Ty → String
  | .int w => s!"i{w}"
  | .clock => "!seq.clock"
  | .array n w => s!"!hw.array<{n}xi{w}>"

private def predText : Pred → String
  | .eq => "eq"
  | .ne => "ne"
  | .ult => "ult"
  | .ule => "ule"
  | .ugt => "ugt"
  | .uge => "uge"
  | .slt => "slt"
  | .sle => "sle"
  | .sgt => "sgt"
  | .sge => "sge"

private def values (names : List String) : String :=
  String.intercalate ", " (names.map ("%" ++ ·))

private def muxText (c a b : String) (ty : Ty) : String :=
  s!"comb.mux %{c}, %{a}, %{b} : {tyText ty}"

private def opText : Op → String
  | .constant w value => s!"hw.constant {value} : i{w}"
  | .comb name args w => s!"comb.{name} {values args} : i{w}"
  | .icmp p a b w => s!"comb.icmp {predText p} %{a}, %{b} : i{w}"
  | .mux c a b w => muxText c a b (.int w)
  | .arrayMux c a b n w => muxText c a b (.array n w)
  | .extract a lo wi wo => s!"comb.extract %{a} from {lo} : (i{wi}) -> i{wo}"
  | .concat a b wa wb => s!"comb.concat %{a}, %{b} : i{wa}, i{wb}"
  | .replicate a wi wo => s!"comb.replicate %{a} : (i{wi}) -> i{wo}"
  | .compreg next clk reset ty =>
    let suffix := match reset with
      | none => ""
      | some (signal, value) => s!" reset %{signal}, %{value}"
    s!"seq.compreg %{next}, %{clk}{suffix} : {tyText ty}"
  | .arrayGet arr idx n w a =>
    s!"hw.array_get %{arr}[%{idx}] : {tyText (.array n w)}, i{a}"
  | .arrayInject arr idx v n w a =>
    s!"hw.array_inject %{arr}[%{idx}], %{v} : {tyText (.array n w)}, i{a}"
  | .instance inst callee args results =>
    let inputs := String.intercalate ", " (args.map fun (pin, value, ty) =>
      s!"{pin}: %{value}: {tyText ty}")
    let outputs := String.intercalate ", " (results.map fun (pin, ty) => s!"{pin}: {tyText ty}")
    s!"hw.instance \"{inst}\" @{callee}({inputs}) -> ({outputs})"

private def signature (ports : List Port) : String :=
  "(" ++ String.intercalate ", " (ports.map fun p => match p.dir with
    | .input => s!"in %{p.name} : {tyText p.ty}"
    | .output => s!"out {p.name} : {tyText p.ty}") ++ ")"

private def outputText (outputs : List (String × Ty)) : String :=
  match outputs with
  | [] => "hw.output"
  | _ => "hw.output " ++ values (outputs.map Prod.fst) ++ " : " ++
      String.intercalate ", " (outputs.map fun (_, ty) => tyText ty)

private def itemText : Item → String
  | .extern name ports => s!"hw.module.extern @{name}{signature ports}\n"
  | .module m =>
    let body := String.join (m.body.map fun (results, op) =>
      let lhs := if results.isEmpty then "" else values results ++ " = "
      "  " ++ lhs ++ opText op ++ "\n")
    "hw.module @" ++ m.name ++ signature m.ports ++ " {\n" ++ body ++
      "  " ++ outputText m.outputs ++ "\n}\n"

def print (d : Design) : String := String.join (d.items.map itemText)

end Silicon.Core.Mlir
