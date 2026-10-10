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

/-! The name and value tokens of an input line `in=(...)`. -/
def inputTokens (line : String) : Except String (List String) := do
  let chars := line.toList
  if chars.any (fun c => c == '\r' || c == '\n') then throw "invalid input line ending"
  let text := String.ofList ((chars.dropWhile vectorSpace).reverse.dropWhile vectorSpace).reverse
  if !text.startsWith "in=(" || !text.endsWith ")" then throw "expected in=(...)"
  let body := ((text.drop 4).toString.dropEnd 1).toString
  return ((body.map fun c => if c == '\t' then ' ' else c).splitOn " ").filter
    (fun s => !s.isEmpty)

def parseInputLine (m : Typed.Module) (line : String) : Except String (List (String × Nat)) := do
  parsePairs m.ports (← inputTokens line)

/-! An output line from the names and the printed values of the outputs. -/
def outputLine (values : List (String × String)) : String :=
  "out=(" ++ String.intercalate " " (values.map fun (n, v) => s!"{n} {v}") ++ ")\n"

def printOutputLine (values : List (String × Nat)) : String :=
  outputLine (values.map fun (n, v) => (n, toString v))

def errorLine (e : Error) : String :=
  s!"error[{e.code}]: {e.pos.line}:{e.pos.col}: {e.msg}"

end Silicon.Core
