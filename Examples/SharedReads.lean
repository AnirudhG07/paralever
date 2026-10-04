import Paralever.Lib.Notation
import Paralever.Pragma.ParallelFor

/-! # Example: shared reads, disjoint writes — why Bernstein, not `∗`

`Core/Access.lean`'s `Indep` deliberately has no `Disjoint f₁.reads f₂.reads` clause. This is the
one example built specifically to exercise that: `findMin`/`findMax` both read the *same* three
locations (the input array) and write to *different* locations (their own output). A naive
separation-logic treatment (`P ∗ Q` = exclusive heap split, e.g. `Logic/BIInstance.lean`'s imported
instance) would reject this outright — both sides touch the shared input, so no heap split exists.
Bernstein's conditions accept it immediately: nothing about read/read overlap is even checked.

Marked `#parallel[ findMin, findMax ]` (`Pragma/ParallelFor.lean`) rather than a raw `parPair` —
the general, non-loop pragma, for "these specific named tasks are independent" rather than "this
range of iterations is." -/

namespace Paralever.Examples.SharedReads
open ParM Paralever.Pragma.ParallelFor

/-- Read the three input locations and write their minimum to `10`. -/
def findMin : ParM Unit :=
  .read 0 (fun v0 => .read 1 (fun v1 => .read 2 (fun v2 =>
    match v0, v1, v2 with
    | .int a, .int b, .int c => .write 10 (.int (min a (min b c))) .pure
    | _, _, _ => .pure ())))

/-- Read the *same* three input locations and write their maximum to `11`. -/
def findMax : ParM Unit :=
  .read 0 (fun v0 => .read 1 (fun v1 => .read 2 (fun v2 =>
    match v0, v1, v2 with
    | .int a, .int b, .int c => .write 11 (.int (max a (max b c))) .pure
    | _, _, _ => .pure ())))

def σ0 : State
  | 0 => .int 5 | 1 => .int (-2) | 2 => .int 9 | _ => .int 0

example : accesses findMin σ0 = ⟨[0, 1, 2], [10]⟩ := rfl
example : accesses findMax σ0 = ⟨[0, 1, 2], [11]⟩ := rfl

/-- The reads overlap completely — `[0,1,2]` on both sides — yet the footprints are still
Bernstein-independent, because only the writes (`10` vs `11`) are checked against anything. -/
example : indepB (accesses findMin σ0) (accesses findMax σ0) = true := rfl

/-- Both `findMin` and `findMax`, marked parallel via the general pragma. -/
def minmaxPar : ParM (List Unit) := #parallel[ findMin, findMax ]

example : minmaxPar = ParM.parAll [findMin, findMax] := rfl

theorem wellFormed_minmax : WellFormed minmaxPar σ0 := by
  apply WellFormed_parAll_cons
  · trivial
  · exact (indepB_iff _ _).mp (by decide)
  · apply WellFormed_parAll_cons
    · trivial
    · exact (indepB_iff _ _).mp (by decide)
    · exact WellFormed_parAll_nil _

/-- The payoff: computing min and max of the same data in parallel reaches exactly the outcomes
computing them one after another does — despite both reading every input location. -/
theorem minmaxPar_par_seq_eq : minmaxPar ∥≡ ParM.seqAll [findMin, findMax] from σ0 :=
  parAll_par_seq_eq _ σ0 wellFormed_minmax

example : (runSeq minmaxPar σ0).2 10 = .int (-2) := rfl
example : (runSeq minmaxPar σ0).2 11 = .int 9 := rfl

/-! ### Anti-vacuity: a write into the shared input, and independence breaks -/

/-- Not "min/max of shared data" anymore — writes location `0`, one of `findMin`'s inputs. -/
def racer : ParM Unit := .write 0 (.int 99) .pure

example : indepB (accesses findMin σ0) (accesses racer σ0) = false := rfl

def isWrong {α : Type} : Conf α → Bool
  | .wrong => true
  | _      => false

/-- Read vs. write on the same location races immediately — parallel execution can step straight
to `wrong`, something the sequential composition never does. -/
example : (step (#parallel[ findMin, racer ] : ParM (List Unit)) σ0).map isWrong = [true] := rfl

end Paralever.Examples.SharedReads
