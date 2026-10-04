import Paralever.Lib.Pure

/-! # Example: write the algorithm purely, get the `ParM` program and both proofs

The question this answers: *"I have a pure function. Do I have to rewrite it as a `ParM` program by
hand, and if so how do I know the rewrite is faithful?"*

Answer: you write the pure fold, pick the locations, and `Lib/Pure.lean` supplies

1. the `ParM` program (`readsCombine` / `reduceArrayPureP`),
2. **a proof it computes your pure function** (`reduceFold_eq_foldPure`), and
3. `ParSeqEq` from three arithmetic hypotheses (`reduceArrayPure_par_seq_eq`).

Worked here on row sums: `Out[i] = Σ_j A[i,j]`, `A` at `[0,n²)`, `Out` at `[n²,n²+n)`. -/

namespace Paralever.Examples.PureToParM
open Paralever

/-! ### Step 1 — the algorithm, purely. No monad, no `ParM`, no locations yet.

This is the part a user actually writes: how to combine values. -/

/-- Add a `Val` into an `Int` accumulator, ignoring non-integers. The whole algorithm. -/
def addVals (vs : List Val) (acc : Int) : Int :=
  vs.foldl (fun a v => match v with | .int n => a + n | _ => a) acc

/-! ### Step 2 — the layout. Which cells does row `i`, step `j` read? -/

/-- Row `i` of an `n × n` matrix based at 0: step `j` reads the single cell `A[i,j]`. -/
def rowLoc (n : Nat) (i j : Nat) : List Loc := [i * n + j]

/-- `Out[i]` lives at `n² + i`. -/
def outLoc (n : Nat) (i : Nat) : Loc := n * n + i

/-- Reads stay inside `A`. -/
def InA (n : Nat) (l : Loc) : Prop := l < n * n

/-! ### Step 3 — the `ParM` program, assembled by the library -/

def rowSumsPar (n : Nat) : ParM (List Unit) :=
  reduceArrayPureP n n (rowLoc n) addVals 0 Val.int (outLoc n)

def rowSumsSeq (n : Nat) : ParM (List Unit) :=
  reduceArrayPureS n n (rowLoc n) addVals 0 Val.int (outLoc n)

/-! ### Step 4 — faithfulness: the `ParM` fold computes the pure fold

`foldPure` is the pure specification; `reduceFold_eq_foldPure` is generic, so this is a one-liner
rather than `SumArray.lean`'s hand-written induction. -/

theorem rowFold_faithful (n i : Nat) (σ : State) :
    (runSeq (reduceFold (readsCombine (rowLoc n i) addVals) n 0 (0 : Int)) σ).1
      = foldPure σ (rowLoc n i) addVals n 0 0 :=
  reduceFold_eq_foldPure (rowLoc n i) addVals σ n 0 0

/-! ### Step 5 — `ParSeqEq`, from three arithmetic facts -/

/-- **The payoff.** All three hypotheses are `omega`/`grind` on index arithmetic. -/
theorem rowSums_par_seq_eq (n : Nat) (σ : State) :
    rowSumsPar n ∥≡ rowSumsSeq n from σ := by
  unfold rowSumsPar rowSumsSeq
  apply reduceArrayPure_par_seq_eq n n (rowLoc n) addVals 0 Val.int (outLoc n) (InA n)
  · -- reads land in A: i*n + j < n*n when i < n and j < n
    intro p hp k hk l hl
    simp only [rowLoc, List.mem_singleton] at hl
    subst hl
    have h1 : p * n + k < (p + 1) * n := by rw [Nat.succ_mul]; omega
    have h2 : (p + 1) * n ≤ n * n := Nat.mul_le_mul_right n hp
    simp only [InA]
    exact Nat.lt_of_lt_of_le h1 h2
  · intro p q hp hq hpq; grind [outLoc]
  · intro p hp; grind [outLoc, InA]

/-! ### Concrete check: row sums of `[[1,2],[3,4]]` are `3` and `7` -/

def σ2 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | _ => .int 0

example : (runSeq (rowSumsPar 2) σ2).2 4 = .int 3 := rfl
example : (runSeq (rowSumsPar 2) σ2).2 5 = .int 7 := rfl

end Paralever.Examples.PureToParM
