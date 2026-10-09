import Silicon.Core.Typed

/-! Vectors keep port order. Only spaces and tabs separate input tokens. -/
namespace Silicon.Core

private def vectorSpace (c : Char) : Bool := c == ' ' || c == '\t'

private def parsePairs : List Port → List String → Except String (List (String × Nat))
  | [], [] => .ok []
  | [], _ => .error "extra input tokens"
  | p :: ps, tokens => do
    if p.dir != .input then return ← parsePairs ps tokens
    match p.ty with
    | .clock => parsePairs ps tokens
    | .bits width =>
      let name :: value :: rest := tokens | .error "missing input"
      if name != p.name then throw s!"expected input {p.name}"
      if value.isEmpty || !value.toList.all Char.isDigit then
        throw "expected a decimal natural number"
      let some n := value.toNat? | .error "expected a decimal natural number"
      if n >= 2 ^ width then throw s!"input {name} exceeds its width"
      return (name, n) :: (← parsePairs ps rest)

def parseInputLine (m : Typed.Module) (line : String) : Except String (List (String × Nat)) := do
  let chars := line.toList
  if chars.any (fun c => c == '\r' || c == '\n') then throw "invalid input line ending"
  let text := String.ofList ((chars.dropWhile vectorSpace).reverse.dropWhile vectorSpace).reverse
  if !text.startsWith "in=(" || !text.endsWith ")" then throw "expected in=(...)"
  let body := ((text.drop 4).toString.dropEnd 1).toString
  let tokens := ((body.map fun c => if c == '\t' then ' ' else c).splitOn " ").filter
    (fun s => !s.isEmpty)
  parsePairs m.ports tokens

def printOutputLine (values : List (String × Nat)) : String :=
  "out=(" ++ String.intercalate " " (values.map fun (n, v) => s!"{n} {v}") ++ ")\n"

def errorLine (e : Error) : String :=
  s!"error[{e.code}]: {e.pos.line}:{e.pos.col}: {e.msg}"

end Silicon.Core
