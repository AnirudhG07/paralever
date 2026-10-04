import Paralever.Pragma.MapArray
import Paralever.Lib.Notation

/-! # Example: `mapArrayPar` on a genuine elementwise loop, and the loop it must reject

`doubleInto`: `Out[i] := 2 * In[i]`, `In` at `[0,n)`, `Out` at `[n,2n)` — the textbook
parallelizable loop. With `Pragma/MapArray.lean`, the entire independence obligation for *any* `n`
is one call to `mapArray_par_seq_eq`: supply array bounds + disjointness, done.

`incFromPrev` is the contrast — `CLAUDE.md`'s flagged loop-carried-dependence case
(`A[i] := A[i-1] + 1`). It cannot go through the same recipe. -/

namespace Paralever.Examples.DoubleInto
open Paralever

/-! ### The loop a pragma should accept -/

def inp (n : Nat) : ArrRef := Array[0, n]
def out (n : Nat) : ArrRef := Array[n, n]

def double : Val → Val
  | .int x => .int (2 * x)
  | v      => v

def doublePar (n : Nat) := mapArrayPar (inp n) (out n) double
def doubleSeq (n : Nat) := mapArraySeq (inp n) (out n) double

/-- **The payoff, for any `n`**: one line. -/
theorem doublePar_par_seq_eq (n : Nat) (σ : State) :
    doublePar n ∥≡ doubleSeq n from σ :=
  mapArray_par_seq_eq (inp n) (out n) double rfl (Or.inl (by show 0 + n ≤ n; omega)) σ

/-! ### Anti-vacuity: the loop a pragma must reject -/

def incFromPrev (i : Nat) : ParM Unit :=
  .read (i - 1) (fun v => match v with
    | .int x => .write i (.int (x + 1)) .pure
    | _      => .pure ())

def σ0 : State := fun _ => .int 0

/-- Iteration `2` reads location `1`, which iteration `1` writes — a genuine conflict. -/
example : indepB (accesses (incFromPrev 1) σ0) (accesses (incFromPrev 2) σ0) = false := rfl

end Paralever.Examples.DoubleInto
