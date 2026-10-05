import Paralever.Lib.Pure

/-! # `Out[i] := Σ_j A[i,j]` written purely, then lifted

The algorithm is an ordinary fold; `Lib/Pure.lean` builds the `ParM` program from it and proves the
lift faithful. Rationale: `docs/pure-bridge.md`, `docs/reductions.md`, `docs/cost.md`. -/

namespace Paralever.Examples.PureToParM
open Paralever

/-! ### Layout: `A` at `[0,n²)`, `Out` at `[n², n²+n)` -/

/-- Row `p` of an `n × n` matrix based at 0: step `k` reads the single cell `A[p,k]`. -/
def rowLoc (n : Nat) (p k : Nat) : List Loc := [p * n + k]

def outLoc (n : Nat) (p : Nat) : Loc := n * n + p

/-- The read region: everything a row sum touches lies in `A`. -/
def InA (n : Nat) (l : Loc) : Prop := l < n * n

private theorem hlocs (n : Nat) : ∀ p, p < n → ∀ k, k < n → ∀ l ∈ rowLoc n p k, InA n l := by
  intro p hp k hk l hl
  simp only [rowLoc, List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl
  have h1 : p * n + k < (p + 1) * n := by rw [Nat.succ_mul]; omega
  have h2 : (p + 1) * n ≤ n * n := Nat.mul_le_mul_right n hp
  exact Nat.lt_of_lt_of_le h1 h2

private theorem hdstinj (n : Nat) : ∀ p q, p < n → q < n → p ≠ q → outLoc n p ≠ outLoc n q := by
  intro p q hp hq hpq; grind [outLoc]

private theorem hdstout (n : Nat) : ∀ p, p < n → ¬ InA n (outLoc n p) := by
  intro p hp; grind [outLoc, InA]

/-! ### pure -/

/-- Add a `Val` into an `Int` accumulator, ignoring non-integers. The whole algorithm. -/
def addVals (vs : List Val) (acc : Int) : Int :=
  vs.foldl (fun a v => match v with | .int n => a + n | _ => a) acc

/-- Row `p`'s sum as a function of the heap: no monad, no locations threaded through a program. -/
def rowSumsPure (n : Nat) (σ : State) (p : Nat) : Int := foldPure σ (rowLoc n p) addVals n 0 0

/-! ### seq -/

def rowSumsSeq (n : Nat) : ParM (List Unit) :=
  reduceArrayPureS n n (rowLoc n) addVals 0 Val.int (outLoc n)

/-! ### par -/

def rowSumsPar (n : Nat) : ParM (List Unit) :=
  reduceArrayPureP n n (rowLoc n) addVals 0 Val.int (outLoc n)

/-! ### pure = seq

`reduceFold (readsCombine ...) n 0 0` is the fold `rowSumsSeq` runs for row `p`; it returns exactly
what `rowSumsPure` computes. -/

theorem pure_eq_seq (n p : Nat) (σ : State) :
    (runSeq (reduceFold (readsCombine (rowLoc n p) addVals) n 0 (0 : Int)) σ).1
      = rowSumsPure n σ p :=
  reduceFold_eq_foldPure (rowLoc n p) addVals σ n 0 0

/-! ### seq = par -/

theorem seq_eq_par (n : Nat) (σ : State) : rowSumsPar n ∥≡ rowSumsSeq n from σ :=
  reduceArrayPure_par_seq_eq n n (rowLoc n) addVals 0 Val.int (outLoc n) (InA n)
    (hlocs n) (hdstinj n) (hdstout n) σ

/-! ### time par < time seq -/

theorem time_lt (n : Nat) (h2 : 2 ≤ n) (σ : State) :
    time (rowSumsPar n) σ < time (rowSumsSeq n) σ := by
  unfold rowSumsPar rowSumsSeq reduceArrayPureP reduceArrayPureS
  exact reduceArray_time_lt n n (fun p => readsCombine (rowLoc n p) addVals) 0 Val.int
    (outLoc n) (InA n)
    (fun p k acc σ' => readsCombine_wellformed _ _ k acc σ')
    (fun p hp k hk acc σ' => readsCombine_readsWithin _ _ k acc σ' (InA n) (hlocs n p hp k hk))
    (fun p k acc σ' => readsCombine_no_writes _ _ k acc σ')
    (hdstinj n) (hdstout n) h2 σ

/-! ### Concrete check: row sums of `[[1,2],[3,4]]` are `3` and `7` -/

def σ2 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | _ => .int 0

example : (runSeq (rowSumsPar 2) σ2).2 4 = .int 3 := rfl
example : (runSeq (rowSumsPar 2) σ2).2 5 = .int 7 := rfl

end Paralever.Examples.PureToParM
