import Paralever.Pragma.ParallelFor

/-! # Example: `#parallel_for` on a genuine elementwise loop, and the loop it must reject

`doubleInto`: `Out[i] := 2 * In[i]`, `In` at `[0,n)`, `Out` at `[n,2n)` — the textbook parallelizable
loop, no cross-iteration dependence. `doublePar_par_seq_eq` discharges the whole obligation, for
*any* `n`, via `Pragma/ParallelFor.lean`'s validator: one footprint bound per iteration, one `omega`
call for pairwise disjointness. No per-`n` proof, no induction written here at all.

`incFromPrev` is the contrast — `CLAUDE.md`'s own flagged loop-carried-dependence case
(`A[i] := A[i-1] + 1`). It cannot go through the same recipe: iteration `i` reads what iteration
`i-1` writes, so no disjointness fact exists to supply. `§ Anti-vacuity` below confirms this is a
real conflict, not a proof-engineering gap. -/

namespace Paralever.Examples.DoubleInto
open Paralever ParM Paralever.Pragma.ParallelFor

/-! ### The loop a pragma should accept -/

/-- `Out[i] := 2 * In[i]`, where `In` is `[0,n)` and `Out` is `[n,2n)` — disjoint arrays, one
value read per iteration, one written. -/
def doubleInto (n i : Nat) : ParM Unit :=
  .read i (fun v => match v with
    | .int x => .write (n + i) (.int (2 * x)) .pure
    | _      => .pure ())

def doublePar (n : Nat) : ParM (List Unit) := #parallel_for n, (doubleInto n)
def doubleSeq (n : Nat) : ParM (List Unit) := ParM.seqAll ((List.range n).map (doubleInto n))

example : doublePar 3 = ParM.parAll ((List.range 3).map (doubleInto 3)) := rfl

theorem doubleInto_wellformed (n i : Nat) (σ : State) : WellFormed (doubleInto n i) σ := by
  simp only [doubleInto, WellFormed]; cases σ i <;> trivial

/-- Each iteration touches exactly its own input cell `i` and its own output cell `n+i` — nothing
else, for any state. -/
theorem doubleInto_footprint (n i : Nat) (σ : State) :
    FootprintWithin (accesses (doubleInto n i) σ) (fun l => l = i ∨ l = n + i) := by
  simp only [doubleInto, accesses]
  have hread : FootprintWithin (Footprint.mk [i] []) (fun l => l = i ∨ l = n + i) :=
    FootprintWithin.read i _ (Or.inl rfl)
  cases σ i with
  | int x =>
      exact FootprintWithin.union hread (FootprintWithin.write (n + i) _ (Or.inr rfl))
  | bool b => exact FootprintWithin.union hread (FootprintWithin.empty _)
  | unit   => exact FootprintWithin.union hread (FootprintWithin.empty _)

/-- **The check**: two distinct in-range iterations never touch the same cell — one `omega` call,
the entire independence obligation for a loop of *any* size `n`. -/
theorem doubleInto_disjoint (n i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ∀ l, (l = i ∨ l = n + i) → (l = j ∨ l = n + j) → False := by
  intro l h1 h2; omega

/-- **The payoff, for any `n`**: the pragma-marked loop equals its sequential counterpart. -/
theorem doublePar_par_seq_eq (n : Nat) (σ : State) : ParSeqEq (doublePar n) (doubleSeq n) σ :=
  parAll_par_seq_eq_of_indexed_footprint (List.range n) (doubleInto n)
    (fun i l => l = i ∨ l = n + i) List.nodup_range
    (fun i _ => doubleInto_wellformed n i) (fun i _ => doubleInto_footprint n i)
    (fun i j hi hj => doubleInto_disjoint n i j (List.mem_range.mp hi) (List.mem_range.mp hj)) σ

/-! ### Anti-vacuity: the loop a pragma must reject -/

def incFromPrev (i : Nat) : ParM Unit :=
  .read (i - 1) (fun v => match v with
    | .int x => .write i (.int (x + 1)) .pure
    | _      => .pure ())

def σ0 : State := fun _ => .int 0

/-- Iteration `2` reads location `1`, which iteration `1` writes — a genuine conflict, so no
`hdisj` proof of the shape `doubleInto_disjoint` used exists for this loop. -/
example : indepB (accesses (incFromPrev 1) σ0) (accesses (incFromPrev 2) σ0) = false := rfl

end Paralever.Examples.DoubleInto
