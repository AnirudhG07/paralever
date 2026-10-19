import Paralever.Search.ExplainHtml
import Paralever.Lang.Imp

/-! # Reading a counterexample

What `wellFormedB p σ = false` actually *is*: the interleaving that realizes the race, and the heap
the sequential run would have left. `explainProg` replays the found schedule against the real
`step`, so nothing here is a claim the semantics does not make. -- ref: `docs/race-search.md` -/

namespace Examples.RaceReport
open Paralever Paralever.Prog

/-- Everything starts at `0`. -/
def σ0 : State := fun _ => .int 0

/-! ### 1 · Two threads, one cell

The smallest failure: sequential work, then a fork whose sides both write `[5]`. -/

def racy : Prog :=
  .seq (.wr 0 1) (.seq (.rd 0) (.seq (.par (.wr 5 7) (.wr 5 9)) (.wr 1 2)))

example : wellFormedB racy.toParM σ0 = false := by decide
#eval IO.println (explainProg racy σ0)

/-! ### 2 · The race is late — both sides work before colliding on `[9]` -/

def late : Prog :=
  .par (.seq (.wr 10 1) (.seq (.wr 11 1) (.wr 9 1)))
       (.seq (.wr 20 1) (.seq (.wr 21 1) (.wr 9 2)))

#eval IO.println (explainProg late σ0)

/-! ### 3 · The race is nested — thread names are paths, so `T1.0`/`T1.1` say which fork -/

def nested : Prog :=
  .seq (.wr 1 1) (.par (.wr 2 2) (.par (.seq (.rd 3) (.wr 7 1)) (.seq (.rd 4) (.wr 7 2))))

#eval IO.println (explainProg nested σ0)

/-! ### 4 · Three children, two of them racing

The middle child is innocent; the report names the pair that is not. -/

def triple : Prog :=
  .par (.seq (.rd 0) (.wr 6 1)) (.par (.wr 3 1) (.seq (.rd 0) (.wr 6 2)))

#eval IO.println (explainProg triple σ0)

/-! ### 5 · The other direction

Shared reads are not a race, so phase 1 finds nothing and phase 2 is not run — `raceSites_nil_iff`
makes that a theorem, not a timeout. -/

def clean : Prog :=
  .par (.seq (.rd 0) (.wr 1 1)) (.seq (.rd 0) (.wr 2 2))

example : wellFormedB clean.toParM σ0 = true := by decide
#eval IO.println (explainProg clean σ0)

/-! ### 6 · A program written in the DSL

`explainParM` takes any `ParM`, so a `ParProg` explains itself through `execPar`/`execSeq`. -/

open Paralever.Lang

def ρ0 : Regs := fun _ => 0

/-- Two threads of a `parallel` block writing the same cell. -/
def badDSL : ParProg := ParProg.block
  [ ParProg.store 0 (.lit 1)
  , ParProg.par [ ParProg.store 5 (.lit 7), ParProg.store 5 (.lit 9) ]
  , ParProg.store 1 (.lit 2) ]

example : badDSL.wfB = false := by decide
#eval IO.println
  (explainParM rawName 12 (badDSL.execPar ρ0) (badDSL.execSeq ρ0) σ0 [0, 1, 5])

/-! ### 7 · Three threads, and a long run

`wide` forks three; only the outer two collide, so the middle one sits idle. -/

def side (base : Loc) (m : Nat) : Prog :=
  (List.range m).foldl (fun acc i => .seq acc (.wr (base + i) 1)) (.wr base 1)

/-- Three threads; `T0` and `T1.1` collide on `[9]`, `T1.0` does not. -/
def wide : Prog :=
  .par (.seq (side 1000 4) (.wr 9 1))
    (.par (side 50000 4) (.seq (side 90000 4) (.wr 9 2)))

#eval IO.println (explainProg wide σ0)

/-- 123 steps: the middle of the trace is collapsed, and the footprints are clipped. -/
def long : Prog :=
  .par (.seq (side 1000 60) (.wr 9 1)) (.seq (side 90000 60) (.wr 9 2))

#eval IO.println (explainProg long σ0)

/-! ### 8 · The same, as a widget

Both renderers consume the same `Report`, so nothing is computed differently. -/

#race wide σ0
#race long σ0

/-! ### 9 · Named locations

`explainParM` takes a `LocName`, so a layout's `show` prints the cell rather than the address.
`Search/` never learns what a layout is. -/

def mem : Layout := Layout.of
  [ buf "X" [6]    arange
  , buf "W" [2, 3] (rows [[1, 0, -1], [0, 1, 0]])
  , buf "Y" [2] ]

/-- Two threads reducing into `Y[0]` — the second one's index is wrong. -/
def dup : ParProg := ParProg.par
  [ ParProg.store (mem.at "Y" [0]) (.lit 7), ParProg.store (mem.at "Y" [0]) (.lit 9) ]

example : dup.wfB = false := by decide

#eval IO.println (explainParM mem.show 8 (dup.execPar ρ0) (dup.execSeq ρ0) mem.state
  (List.range mem.size))

end Examples.RaceReport
