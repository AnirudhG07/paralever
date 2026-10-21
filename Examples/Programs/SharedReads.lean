import Paralever.Lib.Cost
import Paralever.Lib.Notation
import Paralever.Lib.Loop


namespace Paralever.Examples.SharedReads
open ParM Paralever.Loop

/-! ### pure -/

/-- Minimum of locations `0,1,2` into `10`, maximum into `11`. -/
def minmaxPure (σ : State) : State :=
  match σ 0, σ 1, σ 2 with
  | .int a, .int b, .int c =>
      (σ.update 10 (.int (min a (min b c)))).update 11 (.int (max a (max b c)))
  | _, _, _ => σ

/-! ### seq -/

/-- Read the three input locations and write their minimum to `10`. -/
def findMin : ParM Unit :=
  .read 0 (fun v0 => .read 1 (fun v1 => .read 2 (fun v2 =>
    match v0, v1, v2 with
    | .int a, .int b, .int c => .write 10 (.int (min a (min b c))) .pure
    | _, _, _ => .pure ())))

/-- Read the *same* three locations and write their maximum to `11`. -/
def findMax : ParM Unit :=
  .read 0 (fun v0 => .read 1 (fun v1 => .read 2 (fun v2 =>
    match v0, v1, v2 with
    | .int a, .int b, .int c => .write 11 (.int (max a (max b c))) .pure
    | _, _, _ => .pure ())))

def minmaxSeq : ParM (List Unit) := ParM.seqAll [findMin, findMax]

/-! ### par -/

/-- The general, non-loop pragma: "these specific named tasks are independent." -/
def minmaxPar : ParM (List Unit) := #parallel[ findMin, findMax ]

example : minmaxPar = ParM.parAll [findMin, findMax] := rfl

/-! ### pure = seq -/

theorem pure_eq_seq (σ : State) : (runSeq minmaxSeq σ).2 = minmaxPure σ := by
  rcases h0 : σ 0 with a | _ | _ <;> rcases h1 : σ 1 with b | _ | _ <;>
    rcases h2 : σ 2 with c | _ | _ <;>
    simp [minmaxSeq, minmaxPure, findMin, findMax, ParM.seqPair, h0, h1, h2]

/-! ### seq = par -/

theorem wellFormed_findMin (σ : State) : WellFormed findMin σ := by
  simp only [findMin, WellFormed]
  rcases σ 0 with a | _ | _ <;> rcases σ 1 with b | _ | _ <;> rcases σ 2 with c | _ | _ <;>
    simp only [] <;> trivial

theorem wellFormed_findMax (σ : State) : WellFormed findMax σ := by
  simp only [findMax, WellFormed]
  rcases σ 0 with a | _ | _ <;> rcases σ 1 with b | _ | _ <;> rcases σ 2 with c | _ | _ <;>
    simp only [] <;> trivial

theorem wellFormed_findMax_all (σ : State) : WellFormed (ParM.parAll [findMax]) σ := by
  apply WellFormed_parAll_cons
  · exact wellFormed_findMax σ
  · simp [accesses_parAll_nil, Footprint.empty]
  · exact WellFormed_parAll_nil _

/-- The payoff. Both branches read every input location, and the footprints are still independent:
only the writes (`10` vs `11`) are checked against anything. -/
theorem wellFormed_minmax (σ : State) : WellFormed minmaxPar σ := by
  apply WellFormed_parAll_cons
  · exact wellFormed_findMin σ
  · rcases h0 : σ 0 with a | _ | _ <;> rcases h1 : σ 1 with b | _ | _ <;>
      rcases h2 : σ 2 with c | _ | _ <;>
      simp +decide [findMin, findMax, accesses_parAll_cons, accesses_parAll_nil,
        Footprint.union, Footprint.empty, h0, h1, h2]
  · exact wellFormed_findMax_all _

theorem seq_eq_par (σ : State) : minmaxPar ∥≡ minmaxSeq from σ :=
  parAll_par_seq_eq _ σ (wellFormed_minmax σ)

/-! ### time par < time seq -/

theorem time_lt (σ : State) : time minmaxPar σ < time minmaxSeq σ := by
  refine time_parAll_lt_seqAll findMin [findMax] σ (wellFormed_minmax σ)
    (time_pos findMin σ rfl) ?_
  exact time_parAll_pos findMax [] σ (wellFormed_findMax_all σ) (time_pos findMax σ rfl)

/-- Same work either way — only the rounds shrink. -/
theorem work_eq (σ : State) : work minmaxPar σ = work minmaxSeq σ :=
  work_parAll_eq_seqAll _ σ

/-! ### A concrete instance -/

def σ0 : State
  | 0 => .int 5 | 1 => .int (-2) | 2 => .int 9 | _ => .int 0

example : accesses findMin σ0 = ⟨[0, 1, 2], [10]⟩ := rfl
example : accesses findMax σ0 = ⟨[0, 1, 2], [11]⟩ := rfl
example : (runSeq minmaxPar σ0).2 10 = .int (-2) := rfl
example : (runSeq minmaxPar σ0).2 11 = .int 9 := rfl

/-! ### Anti-vacuity: a write into the shared input breaks independence -/

/-- Writes location `0`, one of `findMin`'s inputs. -/
def racer : ParM Unit := .write 0 (.int 99) .pure

example : indepB (accesses findMin σ0) (accesses racer σ0) = false := rfl

def isWrong {α : Type} : Conf α → Bool
  | .wrong => true
  | _      => false

/-- Read against write on the same location: parallel execution steps straight to `wrong`, which
the sequential composition never does. -/
example : (step (#parallel[ findMin, racer ] : ParM (List Unit)) σ0).map isWrong = [true] := rfl

end Paralever.Examples.SharedReads
