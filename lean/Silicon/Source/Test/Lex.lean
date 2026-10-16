-- SPDX-License-Identifier: Apache-2.0
import Silicon.Source.Lex

/-!
These tests check the lexer at its public boundary: the token kinds, the positions, and
the position of each lexical error.
-/

namespace Silicon.Source.Test

open Lex

def kinds (s : String) : List Kind := (lex defaultSyntaxDepth s).map (·.kind)

def positions (s : String) : List (Nat × Nat) :=
  (lex defaultSyntaxDepth s).map fun t => (t.pos.line, t.pos.col)

def failsAt (s : String) (line col : Nat) (depth : Nat := defaultSyntaxDepth) : Bool :=
  match error? (lex depth s) with
  | some e => e.code == .S001 && e.pos == ⟨line, col⟩
  | none => false

/-! Each token class. -/
#guard kinds "" == [.eof]
#guard kinds "abc _x A1_b" == [.ident "abc", .ident "_x", .ident "A1_b", .eof]
#guard kinds "module modules" == [.keyword "module", .ident "modules", .eof]
#guard keywords.all fun k => kinds k == [.keyword k, .eof]
#guard kinds "static_assert error resize" ==
  [.ident "static_assert", .ident "error", .ident "resize", .eof]
#guard kinds "0 42 007 0x1F 0xff 0b101" ==
  [.number 0, .number 42, .number 7, .number 31, .number 255, .number 5, .eof]
#guard kinds "\"hi there\"" == [.string "hi there", .eof]
#guard kinds "@TypeOf(x)" ==
  [.symbol "@", .ident "TypeOf", .symbol "(", .ident "x", .symbol ")", .eof]
#guard kinds "( ) [ ] { } , ; : . = + - * / % < > ! ~ & | ^ @" ==
  ["(", ")", "[", "]", "{", "}", ",", ";", ":", ".", "=", "+", "-", "*", "/", "%", "<", ">",
   "!", "~", "&", "|", "^", "@"].map Kind.symbol ++ [.eof]
#guard longSymbols.all fun s => kinds s == [.symbol s, .eof]

/-! Longest match: the two-character operator wins, also without spaces. -/
#guard kinds "a>>b" == [.ident "a", .symbol ">>", .ident "b", .eof]
#guard kinds "x:=y" == [.ident "x", .symbol ":=", .ident "y", .eof]
#guard kinds "a+%1" == [.ident "a", .symbol "+%", .number 1, .eof]
#guard kinds "a- -b" == [.ident "a", .symbol "-", .symbol "-", .ident "b", .eof]
#guard kinds ">>>" == [.symbol ">>", .symbol ">", .eof]
#guard kinds "0..N" == [.number 0, .symbol "..", .ident "N", .eof]
#guard kinds "u.q x.0" ==
  [.ident "u", .symbol ".", .ident "q", .ident "x", .symbol ".", .number 0, .eof]

/-! Each token takes the longest match. A rule between tokens is a parser rule. -/
#guard kinds "12ab" == [.number 12, .ident "ab", .eof]
#guard kinds "0x" == [.number 0, .ident "x", .eof]
#guard kinds "0xg" == [.number 0, .ident "xg", .eof]
#guard kinds "0b2" == [.number 0, .ident "b2", .eof]
#guard kinds "0b102" == [.number 2, .number 2, .eof]
#guard kinds "1_000" == [.number 1, .ident "_000", .eof]
#guard kinds "@foo" == [.symbol "@", .ident "foo", .eof]
#guard kinds "fn()->UInt" ==
  [.keyword "fn", .symbol "(", .symbol ")", .symbol "->", .ident "UInt", .eof]
#guard kinds "x=>y Op::Add" ==
  [.ident "x", .symbol "=>", .ident "y", .ident "Op", .symbol "::", .ident "Add", .eof]
#guard kinds "a==>b" == [.ident "a", .symbol "==", .symbol ">", .ident "b", .eof]
#guard kinds "enum match matches" == [.keyword "enum", .keyword "match", .ident "matches", .eof]

/-! Comments separate tokens and produce none. A block comment does not nest. -/
#guard kinds "a // b c\nd" == [.ident "a", .ident "d", .eof]
#guard kinds "a // to the end" == [.ident "a", .eof]
#guard kinds "a/* b\n c */d" == [.ident "a", .ident "d", .eof]
#guard kinds "/* /* */ x" == [.ident "x", .eof]
#guard kinds "/**/x/***/y" == [.ident "x", .ident "y", .eof]
#guard kinds "a/b" == [.ident "a", .symbol "/", .ident "b", .eof]
#guard kinds "\"// no comment\"" == [.string "// no comment", .eof]

/-! The five escapes. Other Unicode characters stand for themselves. -/
#guard kinds "\"\\\" \\\\ \\n \\r \\t\"" == [.string "\" \\ \n \r \t", .eof]
#guard kinds "\"größe\"" == [.string "größe", .eof]

/-! Positions start at 1. LF starts a new line. CR and tab count as one column. -/
#guard positions "let x\n  = 1;" == [(1, 1), (1, 5), (2, 3), (2, 5), (2, 6), (2, 7)]
#guard positions "a\r\n\tb" == [(1, 1), (2, 2), (2, 3)]
#guard positions "/* x\ny */ z" == [(2, 6), (2, 7)]
#guard positions "\"ä\" b" == [(1, 1), (1, 5), (1, 6)]
#guard positions "x\n" == [(1, 1), (2, 1)]

/-! A lexical error is `S001` at the first character of the bad token. -/
#guard failsAt "a \"open" 1 3
#guard failsAt "a\n  \"open\nb\"" 2 3
#guard failsAt "x /* open" 1 3
#guard failsAt "x /* open *" 1 3
#guard failsAt "\"bad \\q\"" 1 1
#guard failsAt "\"tab\there\"" 1 1
#guard failsAt "a $ b" 1 3
#guard failsAt "a # b" 1 3
#guard failsAt "ä" 1 1
#guard failsAt "x \"a\x01b\" y" 1 3
#guard error? (lex defaultSyntaxDepth "a b") == none

/-! The tokens before an error stay, so the parser can report an earlier error first. -/
#guard kinds "import x $" == [.keyword "import", .ident "x", .error "unexpected character"]

/-! A number literal is below 2^65536 in each radix. Leading zeros do not count. -/
def top : Nat := 2 ^ 65536 - 1
#guard kinds ("x " ++ toString top) == [.ident "x", .number top, .eof]
#guard kinds ("0x" ++ "".pushn 'f' 16384) == [.number top, .eof]
#guard kinds ("0b" ++ "".pushn '1' 65536) == [.number top, .eof]
#guard kinds ("000" ++ toString top) == [.number top, .eof]
#guard kinds ("0x00" ++ "".pushn 'f' 16384) == [.number top, .eof]
#guard kinds ("0b00" ++ "".pushn '1' 65536) == [.number top, .eof]
#guard failsAt ("x " ++ toString (top + 1)) 1 3
#guard failsAt ("x 0x1" ++ "".pushn '0' 16384) 1 3
#guard failsAt ("x 0b1" ++ "".pushn '0' 65536) 1 3

/-! A long literal fails before its conversion, so it fails fast. -/
#guard failsAt ("x " ++ "".pushn '9' 1000000 ++ " y") 1 3

/-!
The three kinds of brackets nest together at most the syntax depth. The first opening bracket
above it is `S001`. A closing bracket at the depth 0 keeps the depth at 0.
-/
#guard error? (lex 4 "([{(x)}])") == none
#guard failsAt "([{((x))}])" 1 5 4
#guard failsAt "{{{{{" 1 5 4
#guard failsAt "[[[[[" 1 5 4
#guard error? (lex 2 "(())(())[{}]") == none
#guard failsAt ")]}(((" 1 6 2
#guard failsAt "((\n  {x" 2 3 2
#guard failsAt "$(((" 1 1 2
#guard failsAt "((( \"open" 1 3 2
#guard error? (lex defaultSyntaxDepth ("".pushn '(' 4096)) == none
#guard failsAt ("".pushn '(' 4097) 1 4097
#guard failsAt ("".pushn '{' 1000000) 1 4097

end Silicon.Source.Test
