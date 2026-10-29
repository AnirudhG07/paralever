import Lang.Smt.Report

/-! # The SMT verification condition, as build gates

What is decided in Lean, what is left for a solver, and that the two agree with `wfB` where `wfB`
has an opinion. No guard here runs a solver: a build must be green on a machine with none.
-- ref: `docs/smt-vc.md` -/

namespace Test.Smt
open Paralever Paralever.Lang Paralever.Smt

private def compile (src : String) : Option Compiled := (ofString src).toOption

private def statusOf (src : String) : Option (List Vc) :=
  (compile src).map (fun c => obligations c.prog)

/-- The one-fork verdict, as a word, so a guard reads as the report does. -/
private def verdict (src : String) : Option String :=
  match statusOf src with
  | some [v] => some (match v.status with
      | .independent => "independent"
      | .collides _  => "racy"
      | .query _ _   => "query")
  | some []  => some "none"
  | _        => none

/-! ## Symbolic evaluation decides what it can

A thread's index is an expression, and an unrolled `parfor` leaves it closed — so it folds to a
literal and the address becomes a known cell. That is the whole over-approximation gap for a
determined index, closed without a solver. -/

#guard Sym.fold (.add (.lit 2) (.mul (.lit 3) (.lit 4))) == Sym.lit 14
#guard Sym.fold (.add (.opaque 0) (.lit 0)) == Sym.add (.opaque 0) (.lit 0)
#guard SAddr.norm (.at ⟨10, 4⟩ (.add (.lit 1) (.lit 1))) == SAddr.fixed 12
-- the wrap is reproduced, not assumed away: index 5 of a 4-cell buffer is its second cell
#guard SAddr.norm (.at ⟨10, 4⟩ (.lit 5)) == SAddr.fixed 11
-- and a negative index clamps to the first, which is why `--assume nonneg` exists
#guard SAddr.norm (.at ⟨10, 4⟩ (.lit (-3))) == SAddr.fixed 10

/-- A computed index that folds: `wfB` refuses, and the obligation is discharged in Lean. -/
def folds : String :=
  "buf s[8]\nparfor t in 4 {\n  %p := t\n  s[%p] := 65\n}"

#guard (compile folds).map (fun c => ParProg.wfB c.prog) == some false
#guard verdict folds == some "independent"

/-! A static index: `wfB` accepts, and so does this, by the same route. -/
#guard verdict "buf s[4]\nparfor t in 4 {\n  s[t] := 65\n}" == some "independent"

/-! Two threads on one known cell is a race, not a gap, and needs no solver. -/
#guard verdict "buf A[1]\nparfor t in 2 {\n  A[0] := t\n}" == some "racy"

/-! Nothing to discharge when there is no fork. -/
#guard verdict "buf A[2]\nA[0] := 1\nA[1] := 2" == some "none"

/-! ## What is left for a solver

An index read from memory is the one thing substitution cannot remove. -/

def scatter : String := include_str "../Examples/Language/scatter.prl"
def stripe  : String := include_str "../Examples/Language/stripe.prl"

#guard verdict scatter == some "query"
#guard verdict stripe  == some "query"

/-! **The gap the VC path exists to close.** Both files are refused by `wfB`, and in both the
refusal is the over-approximated footprint rather than a race — so there is something for a solver
to add. Without this pair the feature could be vacuous. -- ref: `CLAUDE.md` § Anti-vacuity -/
#guard (compile stripe).map (fun c => ParProg.wfB c.prog) == some false
#guard (compile scatter).map (fun c => ParProg.wfB c.prog) == some false

/-! One unknown per load, numbered across the whole program: three loads, three unknowns. -/
#guard (statusOf scatter).map (fun vs => vs.map (fun v => v.origins.length)) == some [3]
#guard (statusOf stripe).map (fun vs => vs.map (fun v => v.origins.length)) == some [2]

/-! Each unknown says which cell it came from, or a query cannot be read. -/
#guard ((compile scatter).map fun c =>
  ((obligations c.prog).head?.map (fun v => v.origins.map (originLine c))).getD [])
  == some [ "  u0  the value read from idx[0]"
          , "  u1  the value read from idx[1]"
          , "  u2  the value read from idx[2]" ]

/-! ## The query itself -/

private def queryOf (src : String) : Option Query :=
  match statusOf src with
  | some [⟨_, _, .query q _, _, _⟩] => some q
  | _ => none

#guard (queryOf stripe).map (fun q => q.unknowns) == some 2
#guard (queryOf stripe).map (fun q => (q.render.splitOn "(set-logic QF_LIA)").length) == some 2
#guard (queryOf stripe).map (fun q => (q.render.splitOn "(check-sat)").length) == some 2
-- a model is asked for only when one exists, because `(get-value …)` after `unsat` is an error
#guard (queryOf stripe).map (fun q => q.render.splitOn "(get-value" |>.length) == some 1
#guard (queryOf stripe).map (fun q => q.render (model := true) |>.splitOn "(get-value" |>.length)
         == some 2

/-! `--assume nonneg` adds one hypothesis per unknown and nothing else. -/
#guard ((statusOf stripe).map fun vs => (vs.map assumeNonneg).map fun v =>
  match v.status with | .query q _ => q.assume.length | _ => 0) == some [2]

/-- A product of two computed values leaves the decidable fragment, and the logic says so. -/
def nlin : String :=
  "buf A[8]\nbuf k[2] = 1, 1\nparallel {\n  %p := k[0]\n  %q := k[1]\n  A[%p * %q] := 1\n} | {\n  A[7] := 2\n}"
#guard (queryOf nlin).map (fun q => q.goal.nonlinear) == some true
#guard (queryOf nlin).map (fun q => (q.render.splitOn "(set-logic QF_NIA)").length) == some 2

/-! ## A widened footprint cannot yield a race

Both branches of an `ifElse` contribute, but only one runs, so two threads "touching" one cell may
be two branches that never both happen. The flag is per fork, so a branch elsewhere does not taint
one that has none. -- ref: `docs/cli.md` § The three verdicts -/

private def approxOf (src : String) : Option (List Bool) :=
  (statusOf src).map (fun vs => vs.map (fun v => v.approx))

#guard approxOf stripe == some [false]
#guard approxOf "buf A[1]\nparfor t in 2 {\n  A[0] := t\n}" == some [false]

/-! Two threads write `A[0]`, but each from inside a branch, so the collision is a possibility. -/
def branched : String :=
  "buf A[2]\nbuf g[1] = 1\nparallel {\n  %c := g[0]\n  if %c { A[0] := 1 } else { A[1] := 1 }\n} | {\n  %d := g[0]\n  if %d { A[1] := 2 } else { A[0] := 2 }\n}"

#guard approxOf branched == some [true]
#guard verdict branched == some "racy"

/-! A branch *outside* a fork leaves that fork's own answer alone. -/
#guard approxOf "buf A[2]\nbuf g[1] = 1\n%c := g[0]\nif %c { A[0] := 1 } else { A[1] := 1 }\nparfor t in 2 {\n  A[t] := 3\n}" == some [false]

/-! ## The solver's command line

`--timeout` has to reach the solver, and each spells it differently. -/

#guard (z3.argsFor "q.smt2") == #["-smt2", "q.smt2"]
#guard ({ z3 with timeout := 60000 }.argsFor "q.smt2") == #["-smt2", "-t:60000", "q.smt2"]
#guard ({ cvc5 with timeout := 500 }.argsFor "q.smt2")
         == #["--lang=smt2", "--produce-models", "--tlimit=500", "q.smt2"]
-- `0` is no limit, and the flag is left off rather than passed as zero
#guard ({ z3 with timeout := 0 }.argsFor "q.smt2") == #["-smt2", "q.smt2"]
/-! A name decides the argument shape, so `--solver cvc5` is not handed z3's flags. -/
#guard (named "cvc5").timeFlag == "--tlimit="
#guard (named "/opt/z3/bin/z3").timeFlag == "-t:"
#guard (named "/usr/local/bin/cvc5-1.2.0").timeFlag == "--tlimit="

/-! ## Reading a solver's answer, and checking it

A `sat` answer is a claim about two cells. `witness` recomputes it, so the guard below is the same
check the tool performs on a live solver's model. -/

#guard parseModel ["u0", "u1"] "sat\n((u0 3)\n (u1 (- 1)))\n" == [(0, 3), (1, -1)]
#guard parseModel ["u0"] "sat\n((u0 0))" == [(0, 0)]

/-- `dst` at base 3, three cells: indices 0 and 3 are the same cell, 0 and 1 are not. -/
private def dst : ArrRef := ⟨3, 3⟩

#guard (witness [(.at dst (.opaque 0), .at dst (.opaque 1))] [(0, 0), (1, 3)]).map
         (fun w => w.2.2) == some 3
#guard witness [(.at dst (.opaque 0), .at dst (.opaque 1))] [(0, 0), (1, 1)] == none

/-! ## The arithmetic, decided in Lean

`ArrRef.addr_ne` is the obligation the solver was being handed: distinct in-range indices address
distinct cells. The guards beneath it are the hypotheses being load-bearing — out of range the clamp
aliases, and `-1`, `0` and `3` are one cell of `dst`. -- ref: `docs/smt-vc.md` -/

example (i j : Int) (hi : 0 ≤ i) (hi' : i < 3) (hj : 0 ≤ j) (hj' : j < 3) (h : i ≠ j) :
    dst.addr i ≠ dst.addr j := ArrRef.addr_ne dst hi hi' hj hj' h

example (i j : Int) (hi : 0 ≤ i) (hi' : i < 3) (hj : 0 ≤ j) (hj' : j < 3)
    (h : dst.addr i = dst.addr j) : i = j := ArrRef.eq_of_addr_eq dst hi hi' hj hj' h

#guard dst.addr (-1) == dst.addr 0
#guard dst.addr 3 == dst.addr 0

/-! ## The file `-o` writes -/

#guard ((compile stripe).map fun c => (smtFile c (obligations c.prog)).splitOn "u0  the value read from k[0]" |>.length) == some 2
#guard ((compile "buf A[2]\nA[0] := 1").map fun c =>
  smtFile c (obligations c.prog)) == some "; every fork was decided without a solver\n"

end Test.Smt
