import Paralever.Search.Explain
import Lang.Core.Imp


namespace Paralever.Examples.ControlFlow
open Paralever Paralever.Lang

def ρ0 : Regs := fun _ => 0
def σ0 : State := fun l => if l == 0 then .int 5 else .int 0

/-! ## 1. A conditional inside a parallel block -/

def clamp : ParProg := paralever {
  %0 := [0];
  parallel { if (%0) { [1] := 1 } else { [1] := 0 } }
    | { if (%0) { [2] := 2 } else { [2] := 0 } }
}

/-- The path is dynamic, so the footprint is a bound. -/
example : ParProg.footprintExact clamp = false := by decide

/-- Still precise: each thread's two branches write the same cell, so Bernstein holds. -/
example : ParProg.footprintOf clamp = ⟨[0], [1, 1, 2, 2]⟩ := rfl

example : ParProg.wfB clamp = true := by decide

/-- **The theorem, with no extra hypothesis.** -/
example : ParSeqEq (clamp.execPar ρ0) (clamp.execSeq ρ0) σ0 :=
  ParProg.par_seq_eq (by decide) ρ0 σ0

/-- `[0] = 5`, so both `then` branches fire. -/
example : (runSeq (clamp.execPar ρ0) σ0).2.window 0 3
    = [(0, .int 5), (1, .int 1), (2, .int 2)] := rfl

/-! ## 2. A guarded loop: `while e in n` tests `e` before each of at most `n` rounds -/

def drain : ParProg := paralever {
  while (%9) in 5 { %0 := [0]; [0] := %0 - 1; %9 := %0 }
}

/-- Runs while `[0]` is non-zero: `5 → 4 → 3 → 2 → 1 → 0`. -/
example : (runSeq (drain.execPar (fun r => if r == 9 then 1 else 0)) σ0).2 0 = .int 0 := rfl

/-- An ordinary `ifElse`/`seq` tree, so nothing new has to hold. -/
example : ParProg.hasPar drain = false := by decide
example : ParProg.wfB drain = true := by decide

/-! ## 3. Where it costs the check

Branches writing *different* cells give overlapping bounds, so `wfB` rejects what no run can make
collide. `wellFormedB` still accepts it at a heap. -/

def crossed : ParProg := paralever {
  %0 := [0];
  parallel { if (%0) { [1] := 1 } else { [2] := 1 } }
    | { if (%0) { [2] := 2 } else { [1] := 2 } }
}

example : ParProg.wfB crossed = false := by decide

/-- …yet at this heap the branches taken are `[1]` and `[2]`, which never meet. -/
example : wellFormedB (crossed.execPar ρ0) σ0 = true := by decide

end Paralever.Examples.ControlFlow
