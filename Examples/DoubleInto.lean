import Paralever.Pragma.MapArray
import Paralever.Lib.Notation

/-! # `Out[i] := 2 * In[i]`

The five standard steps: **pure**, **seq**, **par**, then `pure = seq`, `seq = par`,
`time par < time seq`. Rationale: `docs/pure-bridge.md`, `docs/cost.md`. -/

namespace Paralever.Examples.DoubleInto
open Paralever

def inp (n : Nat) : ArrRef := Array[0, n]
def out (n : Nat) : ArrRef := Array[n, 2 * n]

private theorem hlen (n : Nat) : (inp n).len = (out n).len := by
  show n - 0 = 2 * n - n; omega

private theorem hdisj (n : Nat) :
    (inp n).base + (inp n).len ≤ (out n).base ∨ (out n).base + (out n).len ≤ (inp n).base :=
  Or.inl (by show 0 + (n - 0) ≤ n; omega)

/-! ### pure -/

def double : Val → Val
  | .int x => .int (2 * x)
  | v      => v

def doublePure (n : Nat) : State → State := mapArrayPure (inp n) (out n) double

/-! ### seq -/

def doubleSeq (n : Nat) : ParM (List Unit) := mapArraySeq (inp n) (out n) double

/-! ### par -/

def doublePar (n : Nat) : ParM (List Unit) := mapArrayPar (inp n) (out n) double

/-! ### pure = seq -/

theorem pure_eq_seq (n : Nat) (σ : State) : (runSeq (doubleSeq n) σ).2 = doublePure n σ :=
  mapArraySeq_eq_pure (inp n) (out n) double σ

/-- The same fact read off pointwise: `Out[i]` holds twice `In[i]`. -/
theorem seq_spec (n i : Nat) (hi : i < n) (σ : State) :
    (runSeq (doubleSeq n) σ).2 ((out n).loc i) = double (σ ((inp n).loc i)) :=
  mapArraySeq_spec (inp n) (out n) double (hlen n) (hdisj n) σ i (by show i < n - 0; omega)

/-! ### seq = par -/

theorem seq_eq_par (n : Nat) (σ : State) : doublePar n ∥≡ doubleSeq n from σ :=
  mapArray_par_seq_eq (inp n) (out n) double (hlen n) (hdisj n) σ

/-! ### time par < time seq -/

theorem time_lt (n : Nat) (h2 : 2 ≤ n) (σ : State) :
    time (doublePar n) σ < time (doubleSeq n) σ :=
  mapArray_time_lt (inp n) (out n) double (hlen n) (hdisj n) (by show 2 ≤ n - 0; omega) σ

/-- Same work either way — only the rounds shrink. -/
theorem work_eq (n : Nat) (σ : State) : work (doublePar n) σ = work (doubleSeq n) σ := by
  simp [doublePar, doubleSeq, mapArrayPar, mapArraySeq, work_parAll_eq_seqAll]

/-! ### Anti-vacuity: the loop that must be rejected

`A[i] := A[i-1] + 1` — iteration 2 reads what iteration 1 writes, so `Indep` fails and none of the
theorems above apply. -/

def incFromPrev (i : Nat) : ParM Unit :=
  .read (i - 1) (fun v => match v with
    | .int x => .write i (.int (x + 1)) .pure
    | _      => .pure ())

def σ0 : State := fun _ => .int 0

example : indepB (accesses (incFromPrev 1) σ0) (accesses (incFromPrev 2) σ0) = false := rfl

end Paralever.Examples.DoubleInto
