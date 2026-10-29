import Diag
import Lang.Compile.Lower

/-! # `Test/Diag.lean` — the registry, and what a diagnostic looks like

Rationale: `docs/diagnostics.md`. -/

namespace Paralever.Test.Diag
open Paralever

/-! ## The registry

A code must be findable and unique, or `explain` cannot answer for it. -/

#guard Diag.codes.length == 20
#guard (Diag.codes.map Diag.Code.id) == (Diag.codes.map Diag.Code.id).eraseDups
#guard Diag.codes.all fun c => (Diag.find? c.id).isSome
#guard Diag.codes.all fun c => (Diag.find? c.id.toLower).isSome
-- every code carries a rule and a reason, so none can be issued without an explanation
#guard Diag.codes.all fun c => !c.title.isEmpty && 80 ≤ c.why.length
#guard (Diag.find? "P999").isNone

/-! ## Positions

Resolved against the source, once. Both are 1-based. -/

private def three : Diag.Source := Diag.Source.of "t.prl" "one\ntwo\nthree\n"

#guard three.posAt 0 == ⟨1, 1⟩
-- the newline itself, at the end of line 1
#guard three.posAt 3 == ⟨1, 4⟩
#guard three.posAt 4 == ⟨2, 1⟩
#guard three.posAt 8 == ⟨3, 1⟩
#guard three.lineAt 2 == "two"
#guard three.lineAt 9 == ""

/-! ## Rendering

The caret covers the span and no more, and a diagnostic with no span still names the file. -/

/--
info: error[P002]: 'buf' is a reserved word
 --> t.prl:2:5
  |
2 | reg buf
  |     ^^^
-/
#guard_msgs in
#eval IO.println (Diag.render (Diag.Source.of "t.prl" "buf A[4]\nreg buf\n")
  { code := some Diag.p002, msg := "'buf' is a reserved word", span := some (Diag.Span.of 13 3) })

-- a point span marks one character
#guard Diag.render (Diag.Source.of "t.prl" "abc\n")
    { code := some Diag.p001, msg := "x", span := some (Diag.Span.at 1) }
  == "error[P001]: x\n --> t.prl:1:2\n  |\n1 | abc\n  |  ^"

-- no span: the file, and the hints, with nothing to point at
#guard Diag.render (Diag.Source.of "t.prl" "abc\n")
    { code := some Diag.p101, msg := "undeclared buffer 'B'", hints := ["declare it"] }
  == "error[P101]: undeclared buffer 'B'\n --> t.prl\n = help: declare it"

-- a span running past the end of its line is clipped to the line
#guard Diag.render (Diag.Source.of "t.prl" "ab\ncd\n")
    { msg := "x", span := some (Diag.Span.of 0 9) }
  == "error: x\n --> t.prl:1:1\n  |\n1 | ab\n  | ^^"

#guard Diag.wrap 10 "one two three four" == "one two\nthree four"

/-! ## The front end issues them

Every code is reachable from a `.prl` file, which is what keeps the table honest. -/

private def codeOf (src : String) (stdin : String := "") : Option String :=
  match Lang.ofString src stdin with
  | .error d => d.code.map Diag.Code.id
  | .ok _    => none

#guard codeOf "reg buf" == some "P002"
#guard codeOf "parallel { } :: \"x" == some "P003"
#guard codeOf "buf A[4]\n}" == some "P004"
#guard codeOf "reg t\nbuf A[4]\n%t := A[0] + 1" == some "P005"
#guard codeOf "let a = zeros" == some "P006"
#guard codeOf "buf A[4]\nB[0] := 1" == some "P101"
#guard codeOf "buf A[4]\nbuf A[4]" == some "P102"
#guard codeOf "buf A[4]\nbuf B[4] at 2" == some "P103"
#guard codeOf "buf A[4] = 1, 2, 3, 4, 5" == some "P104"
#guard codeOf "reg t\nbuf A[4]\n%t := 1\n[%t] := 2" == some "P105"
#guard codeOf "parallel { buf A[4] } | { }" == some "P106"
#guard codeOf "reg t\nbuf A[4]\n%t := 4 % 3" == some "P107"
#guard codeOf "reg t\nparfor i in 2 { %t := input }" "1 2" == some "P108"
#guard codeOf "reg t\n%t := input" == some "P109"
#guard codeOf "reg t\nbuf A[4]\n%t := A[0..9][0]" == some "P110"
#guard codeOf "buf A[4]\nslice h = A[1..3]\n\nprint h" == some "P111"
#guard codeOf "def f(A, i) { A[i] := 1 }\nbuf A[4]\nf(A)" == some "P112"
#guard codeOf "def f(x) { f(x) }\nf(0)" == some "P113"
-- the three a `def` shares with the rest of the language: a misplaced statement, a name twice,
-- and a call to a name nothing defines
#guard codeOf "def f(n) { buf B[n] }\nf(4)" == some "P106"
#guard codeOf "def f(A) { A[0] := 1 }\ndef f(A) { A[1] := 1 }\nbuf A[4]\nf(A)" == some "P102"
#guard codeOf "buf A[4]\ng(A)" == some "P101"
#guard codeOf "def f(A) { A[0] := 1 }\nbuf A[4]\nassert f(A) == f(A)\nassert f(A) == f(A)"
         == some "P114"
-- and the three an `assert` shares: the claim out of place, a side that is not a call, and an
-- `on` naming what is not a buffer
#guard codeOf "def f(A) { A[0] := 1 }\nbuf A[4]\nfor i in 2 { assert f(A) == f(A) }"
         == some "P106"
#guard codeOf "buf A[4]\nassert A[0] == A[1] on A" == some "P001"
#guard codeOf "def f(A) { A[0] := 1 }\nbuf A[4]\nassert f(A) == f(A) on T" == some "P101"

-- unexpected tokens are one code, not twenty-one: the message says what was expected
#guard codeOf "buf A[4]\nA[0] 1" == some "P001"
#guard codeOf "reg t\n%t :=" == some "P001"
#guard codeOf "parallel {" == some "P001"

end Paralever.Test.Diag
