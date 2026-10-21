import Paralever.Search.Explain
import Lang.Core.Imp


namespace Paralever.Examples.Scatter
open Paralever Paralever.Lang

-- `decide` on `wellFormedB` reduces a lowered program against a concrete heap
set_option maxRecDepth 4000

/-- Four data cells, then two indices into them. -/
def A : ArrRef := ⟨0, 4⟩
def B : ArrRef := ⟨10, 2⟩

def ρ0 : Regs := fun _ => 0

/-- `B = [1, 3]` — the two scatters miss each other. -/
def σdisjoint : State := fun l => if l == 10 then .int 1 else if l == 11 then .int 3 else .int 0

/-- `B = [2, 2]` — both scatters land on `A[2]`. -/
def σalias : State := fun l => if l == 10 || l == 11 then .int 2 else .int 0

/-- `t0 := B[i] ; A[t0] := v`. The store's address is a register expression, which is the whole
point: separating the index into a register is what keeps `AExp` the only address arithmetic. -/
def scatter (i : Nat) (v : Int) : ParProg :=
  ParProg.block [ ParProg.loadAt 0 B (.lit i), ParProg.storeAt A (.reg 0) (.lit v) ]

def prog : ParProg := ParProg.par [ scatter 0 1, scatter 1 2 ]

/-! ## 1. The syntactic footprint is a bound — all of `A`, since the index is unknown -/

example : ParProg.footprintOf (scatter 0 1) = ⟨[10, 11], [0, 1, 2, 3]⟩ := rfl

/-- Computed addresses, so the bound is not exact. -/
example : ParProg.footprintExact prog = false := by decide

/-- So `wfB` rejects: both bounds cover all of `A`. Imprecision, not unsoundness. -/
example : ParProg.wfB prog = false := by decide

/-! ## 2. The exact check accepts it, at a heap where the indices miss -/

example : wellFormedB (prog.execPar ρ0) σdisjoint = true := by decide

/-- The equivalence itself, at the heap where the indices miss. `wfB` cannot deliver it, so the
two `WellFormed` hypotheses come from the exact check; the canonical runs agree unconditionally. -/
theorem par_seq_eq_disjoint : ParSeqEq (prog.execPar ρ0) (prog.execSeq ρ0) σdisjoint :=
  parSeqEq_of_runSeq_eq _ _ _
    ((wellFormedB_iff _ _).1 (by decide))
    ((wellFormedB_iff _ _).1 (by decide))
    (ParProg.execPar_runSeq_all.1 prog ρ0 σdisjoint)

/-! ## 3. …and refuses it where they collide, with a counterexample -/

example : wellFormedB (prog.execPar ρ0) σalias = false := by decide

#eval IO.println
  (explainParM rawName 10 (prog.execPar ρ0) (prog.execSeq ρ0) σalias [0, 1, 2, 3, 10, 11])

/-! ## 4. It prints, with the computed address as a subscript -/

#eval IO.println (ParProg.reportProg prog)

end Paralever.Examples.Scatter
