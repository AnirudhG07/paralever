import Paralever.Lib.TouchesOnly
import Paralever.Lib.Notation

/-! # Example: real recursive parallel mergesort

The flagship example `PLAN.md`/`M7-M9` calls for: genuine divide-and-conquer, nested `.par` (each
recursive call itself contains further `.par` nodes, not just one flat level like `SumArray`'s
chunking or `Sort`'s compare-swap rounds), and — unlike those two — recursion whose depth depends
on the *size* of the input, not a fixed list handed in up front.

**Why this doesn't need Tier-2 (data-dependent footprints, `Logic/`).** Quicksort's partition
*index* is data-dependent (it depends on comparisons against the pivot's value), which is exactly
why a real quicksort needs ownership-transfer reasoning. Mergesort's split point is not data
dependent at all — `mid := lo + (hi - lo) / 2` is pure arithmetic, fixed before any array access
happens. So at every level of the recursion the two recursive calls' footprints are *statically
known, disjoint, contiguous index ranges* — `omega` territory, exactly `SumArray.lean`'s own
"§3: arbitrary chunking" argument, just applied at every recursion depth instead of once. That
argument predicted this is where a real divide-and-conquer example would land; this file confirms
it.

**Layout.** One array of size `N`, plus a same-size scratch array right after it: locations
`[0, N)` are the data, `[N, 2N)` are scratch. `mergeSortPar N lo hi` sorts data `[lo, hi)` in
place, using scratch `[lo, hi)` (shifted by `N`) to merge into, then copying the merged range back.
Since every recursive call keeps `hi ≤ N`, the data and scratch channels never overlap regardless
of the specific `lo`/`hi`/`mid` — no cross-channel disjointness check is ever needed, only
data-range-vs-data-range and scratch-range-vs-scratch-range, both by `omega`.

`mergeStep`/`copyBack` are fuel-bounded (`docs/program-model.md`'s allowance for structural-or-
fuel-bounded recursion), fuel supplied as the range length so it's always exactly enough.
-/

namespace Paralever.Examples.MergeSort

open ParM

/-! ### Pure spec

Documentation only: what `mergeStep`/`mergeSortPar` below are supposed to compute, in the shape
`SumArray.lean`'s "pure first, then convert" discipline calls for. **Not connected to the `ParM`
code by a correctness proof** — that would be an ordinary sequential-sorting-algorithm correctness
result, orthogonal to this project's actual claim (`docs/program-model.md`, `PLAN.md`: independent
⇒ `par` ≡ `seq`). Nothing below depends on this section. -/

def mergePure : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x ≤ y then x :: mergePure xs (y :: ys) else y :: mergePure (x :: xs) ys
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

def mergeSortPure : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      let xs := x :: y :: rest
      let mid := xs.length / 2
      mergePure (mergeSortPure (xs.take mid)) (mergeSortPure (xs.drop mid))
termination_by xs => xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

/-! ### The `ParM` merge step and copy-back — sequential, fuel-bounded -/

/-- Merge sorted `[i, mid)` and `[j, hi)` (both in the data channel) into the scratch channel
starting at `auxBase + k`, advancing `k` alongside whichever of `i`/`j` moves. `fuel` is consumed
one-for-one with every `i`/`j` advance, so `fuel := (mid - i) + (hi - j)` is always exactly
enough — never runs out early, never needed beyond the merge's real length. -/
@[simp, grind .]
def mergeStep (mid hi auxBase : Nat) : Nat → Nat → Nat → Nat → ParM Unit
  | 0, _, _, _ => .pure ()
  | fuel + 1, i, j, k =>
      if i ≥ mid then
        if j ≥ hi then .pure ()
        else .read j (fun v => .write (auxBase + k) v
          (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1)))
      else if j ≥ hi then
        .read i (fun v => .write (auxBase + k) v
          (fun _ => mergeStep mid hi auxBase fuel (i + 1) j (k + 1)))
      else
        .read i (fun vi => .read j (fun vj =>
          match vi, vj with
          | .int x, .int y =>
              if x ≤ y then
                .write (auxBase + k) vi (fun _ => mergeStep mid hi auxBase fuel (i + 1) j (k + 1))
              else
                .write (auxBase + k) vj (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1))
          | _, _ => .pure ()))

/-- Copy `fuel` values from `auxBase + i` back to `j`, advancing both together. -/
@[simp, grind .]
def copyBack (auxBase : Nat) : Nat → Nat → Nat → ParM Unit
  | 0, _, _ => .pure ()
  | fuel + 1, i, j =>
      .read (auxBase + i) (fun v => .write j v (fun _ => copyBack auxBase fuel (i + 1) (j + 1)))

/-! ### The recursive parallel sort -/

@[simp, grind .]
def mergeSortPar (N : Nat) : Nat → Nat → ParM Unit
  | lo, hi =>
      if _h : hi - lo ≤ 1 then .pure ()
      else
        let mid := lo + (hi - lo) / 2
        ParM.bind (ParM.parPair (mergeSortPar N lo mid) (mergeSortPar N mid hi)) (fun _ =>
          ParM.bind (mergeStep mid hi N (hi - lo) lo mid lo) (fun _ =>
            copyBack N (hi - lo) lo lo))
termination_by lo hi => hi - lo
decreasing_by all_goals omega

/-! ### Independence — "different memory ⇒ done," via `Theory/Intervals.lean`

`mergeStep`/`copyBack` contain no `.par` node — a fuel-recursive loop has no independence obligation
of its own to discharge, so `WellFormed` for either is unconditionally true (`_wellformed` below).

`mergeSortPar` is different: it *does* contain a `.par` node (once per recursion level, combining
the two recursive sub-sorts), and that is the one and only place `Indep` is ever invoked in this
file. The obligation is discharged by `Theory/Intervals.lean`'s generic machinery: bound each side's
*entire* footprint (reads and writes, across its whole recursive sub-computation) to a location
predicate, show the two predicates are never true of the same location (one `omega` call), get
`Indep` for free from `indep_of_footprint_within` — no Bernstein-condition case analysis, ever,
for any depth of nesting. `TouchesOnly` is exactly that predicate: "in the data range being sorted,
or its matching scratch range." -/

/-! `TouchesOnly lo hi N` — "in the data channel `[lo,hi)` or the matching scratch channel
`[N+lo,N+hi)`" — is the one predicate every footprint bound below targets. It and its two lemmas
(`.mono`, `.disjoint`) come from `Lib/TouchesOnly.lean`; two sort calls over disjoint `[lo,hi)`
ranges (with `hi ≤ N`) are `TouchesOnly`-disjoint, which is the entire independence argument
`mergeSortPar`'s `.par` node needs. -/

/-- `mergeStep`'s full footprint (reads *and* writes): reads stay in the data range `[i,mid)∪[j,hi)`,
writes stay in the scratch range `[auxBase+k, auxBase+k+fuel)` — both `TouchesOnly lo hi N` once
`i,j,mid,hi ⊆ [lo,hi)` and `auxBase = N` (checked where this is used, by `omega`). -/
theorem mergeStep_within (mid hi auxBase : Nat) :
    ∀ (fuel i j k : Nat) (σ : State),
      FootprintWithin (accesses (mergeStep mid hi auxBase fuel i j k) σ)
        (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase + k ≤ l ∧ l < auxBase + k + fuel)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i j k σ
      have heq : mergeStep mid hi auxBase 0 i j k = .pure () := rfl
      rw [heq]; simp only [accesses]; exact FootprintWithin.empty _
  | succ fuel ih =>
      intro i j k σ
      by_cases hc1 : i ≥ mid
      · by_cases hc2 : j ≥ hi
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k = .pure () := by
            simp only [mergeStep]; rw [if_pos hc1, if_pos hc2]
          rw [heq]; simp only [accesses]; exact FootprintWithin.empty _
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read j (fun v => .write (auxBase + k) v
                  (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1))) := by
            simp only [mergeStep]; rw [if_pos hc1, if_neg hc2]
          rw [heq]
          simp only [accesses]
          have hmono : ∀ l, ((i ≤ l ∧ l < mid) ∨ (j+1 ≤ l ∧ l < hi) ∨ (auxBase+(k+1) ≤ l ∧ l < auxBase+(k+1)+fuel))
              → ((i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) := by
            intro l hl; omega
          have hj1 : (i ≤ j ∧ j < mid) ∨ (j ≤ j ∧ j < hi) ∨ (auxBase+k ≤ j ∧ j < auxBase+k+(fuel+1)) :=
            Or.inr (Or.inl (by omega))
          have hk1 : (i ≤ auxBase+k ∧ auxBase+k < mid) ∨ (j ≤ auxBase+k ∧ auxBase+k < hi)
              ∨ (auxBase+k ≤ auxBase+k ∧ auxBase+k < auxBase+k+(fuel+1)) := Or.inr (Or.inr (by omega))
          have hb1 : FootprintWithin (Footprint.mk [j] [])
              (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
            FootprintWithin.read j _ hj1
          have hb2 : FootprintWithin (Footprint.mk [] [auxBase+k])
              (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
            FootprintWithin.write (auxBase+k) _ hk1
          have hb3 := FootprintWithin.mono hmono (ih i (j+1) (k+1) (σ.update (auxBase+k) (σ j)))
          exact FootprintWithin.union hb1 (FootprintWithin.union hb2 hb3)
      · by_cases hc2 : j ≥ hi
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read i (fun v => .write (auxBase + k) v
                  (fun _ => mergeStep mid hi auxBase fuel (i + 1) j (k + 1))) := by
            simp only [mergeStep]; rw [if_neg hc1, if_pos hc2]
          rw [heq]
          simp only [accesses]
          have hmono : ∀ l, ((i+1 ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+(k+1) ≤ l ∧ l < auxBase+(k+1)+fuel))
              → ((i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) := by
            intro l hl; omega
          have hi1 : (i ≤ i ∧ i < mid) ∨ (j ≤ i ∧ i < hi) ∨ (auxBase+k ≤ i ∧ i < auxBase+k+(fuel+1)) :=
            Or.inl (by omega)
          have hk1 : (i ≤ auxBase+k ∧ auxBase+k < mid) ∨ (j ≤ auxBase+k ∧ auxBase+k < hi)
              ∨ (auxBase+k ≤ auxBase+k ∧ auxBase+k < auxBase+k+(fuel+1)) := Or.inr (Or.inr (by omega))
          have hb1 : FootprintWithin (Footprint.mk [i] [])
              (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
            FootprintWithin.read i _ hi1
          have hb2 : FootprintWithin (Footprint.mk [] [auxBase+k])
              (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
            FootprintWithin.write (auxBase+k) _ hk1
          have hb3 := FootprintWithin.mono hmono (ih (i+1) j (k+1) (σ.update (auxBase+k) (σ i)))
          exact FootprintWithin.union hb1 (FootprintWithin.union hb2 hb3)
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read i (fun vi => .read j (fun vj =>
                  match vi, vj with
                  | .int x, .int y =>
                      if x ≤ y then
                        .write (auxBase + k) vi (fun _ => mergeStep mid hi auxBase fuel (i + 1) j (k + 1))
                      else
                        .write (auxBase + k) vj (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1))
                  | _, _ => .pure ())) := by
            simp only [mergeStep]; rw [if_neg hc1, if_neg hc2]
          rw [heq]
          simp only [accesses]
          have hi1 : (i ≤ i ∧ i < mid) ∨ (j ≤ i ∧ i < hi) ∨ (auxBase+k ≤ i ∧ i < auxBase+k+(fuel+1)) :=
            Or.inl (by omega)
          have hj1 : (i ≤ j ∧ j < mid) ∨ (j ≤ j ∧ j < hi) ∨ (auxBase+k ≤ j ∧ j < auxBase+k+(fuel+1)) :=
            Or.inr (Or.inl (by omega))
          have hb1 : FootprintWithin (Footprint.mk [i] [])
              (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
            FootprintWithin.read i _ hi1
          have hb2 : FootprintWithin (Footprint.mk [j] [])
              (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
            FootprintWithin.read j _ hj1
          apply FootprintWithin.union hb1
          apply FootprintWithin.union hb2
          have hmonoR : ∀ l, ((i+1 ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+(k+1) ≤ l ∧ l < auxBase+(k+1)+fuel))
              → ((i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) := by
            intro l hl; omega
          have hmonoL : ∀ l, ((i ≤ l ∧ l < mid) ∨ (j+1 ≤ l ∧ l < hi) ∨ (auxBase+(k+1) ≤ l ∧ l < auxBase+(k+1)+fuel))
              → ((i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) := by
            intro l hl; omega
          have hk1 : (i ≤ auxBase+k ∧ auxBase+k < mid) ∨ (j ≤ auxBase+k ∧ auxBase+k < hi)
              ∨ (auxBase+k ≤ auxBase+k ∧ auxBase+k < auxBase+k+(fuel+1)) := Or.inr (Or.inr (by omega))
          cases σ i with
          | int x =>
              cases σ j with
              | int y =>
                  by_cases hxy : x ≤ y
                  · simp only [hxy, if_true]
                    simp only [accesses]
                    have hb3 : FootprintWithin (Footprint.mk [] [auxBase+k])
                        (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
                      FootprintWithin.write (auxBase+k) _ hk1
                    have hb4 := FootprintWithin.mono hmonoR (ih (i+1) j (k+1) (σ.update (auxBase+k) (Val.int x)))
                    exact FootprintWithin.union hb3 hb4
                  · simp only [hxy, if_false]
                    simp only [accesses]
                    have hb3 : FootprintWithin (Footprint.mk [] [auxBase+k])
                        (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
                      FootprintWithin.write (auxBase+k) _ hk1
                    have hb4 := FootprintWithin.mono hmonoL (ih i (j+1) (k+1) (σ.update (auxBase+k) (Val.int y)))
                    exact FootprintWithin.union hb3 hb4
              | bool b => simp only [accesses]; exact FootprintWithin.empty _
              | unit => simp only [accesses]; exact FootprintWithin.empty _
          | bool b => simp only [accesses]; exact FootprintWithin.empty _
          | unit => simp only [accesses]; exact FootprintWithin.empty _

/-- `copyBack`'s full footprint: reads stay in `[auxBase+i, auxBase+i+fuel)` (scratch), writes stay
in `[j, j+fuel)` (data). -/
theorem copyBack_within (auxBase : Nat) :
    ∀ (fuel i j : Nat) (σ : State),
      FootprintWithin (accesses (copyBack auxBase fuel i j) σ)
        (fun l => (auxBase+i ≤ l ∧ l < auxBase+i+fuel) ∨ (j ≤ l ∧ l < j+fuel)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i j σ
      have heq : copyBack auxBase 0 i j = .pure () := rfl
      rw [heq]; simp only [accesses]; exact FootprintWithin.empty _
  | succ fuel ih =>
      intro i j σ
      have heq : copyBack auxBase (fuel+1) i j
          = .read (auxBase+i) (fun v => .write j v (fun _ => copyBack auxBase fuel (i+1) (j+1))) := rfl
      rw [heq]
      simp only [accesses]
      have hmono : ∀ l, ((auxBase+(i+1) ≤ l ∧ l < auxBase+(i+1)+fuel) ∨ (j+1 ≤ l ∧ l < (j+1)+fuel))
          → ((auxBase+i ≤ l ∧ l < auxBase+i+(fuel+1)) ∨ (j ≤ l ∧ l < j+(fuel+1))) := by
        intro l hl; omega
      have hread : (auxBase+i ≤ auxBase+i ∧ auxBase+i < auxBase+i+(fuel+1))
          ∨ (j ≤ auxBase+i ∧ auxBase+i < j+(fuel+1)) := Or.inl (by omega)
      have hwrite : (auxBase+i ≤ j ∧ j < auxBase+i+(fuel+1)) ∨ (j ≤ j ∧ j < j+(fuel+1)) :=
        Or.inr (by omega)
      have hb1 : FootprintWithin (Footprint.mk [auxBase+i] [])
          (fun l => (auxBase+i ≤ l ∧ l < auxBase+i+(fuel+1)) ∨ (j ≤ l ∧ l < j+(fuel+1))) :=
        FootprintWithin.read (auxBase+i) _ hread
      have hb2 : FootprintWithin (Footprint.mk [] [j])
          (fun l => (auxBase+i ≤ l ∧ l < auxBase+i+(fuel+1)) ∨ (j ≤ l ∧ l < j+(fuel+1))) :=
        FootprintWithin.write j _ hwrite
      have hb3 := FootprintWithin.mono hmono (ih (i+1) (j+1) (σ.update j (σ (auxBase+i))))
      exact FootprintWithin.union hb1 (FootprintWithin.union hb2 hb3)

/-- `mergeStep` contains no `.par` node, so it is unconditionally well-formed — no independence
obligation ever arises inside a straight-line fuel loop. -/
theorem mergeStep_wellformed (mid hi auxBase : Nat) :
    ∀ (fuel i j k : Nat) (σ : State), WellFormed (mergeStep mid hi auxBase fuel i j k) σ := by
  intro fuel
  induction fuel with
  | zero => intro i j k σ; trivial
  | succ fuel ih =>
      intro i j k σ
      by_cases hc1 : i ≥ mid
      · by_cases hc2 : j ≥ hi
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k = .pure () := by
            simp only [mergeStep]; rw [if_pos hc1, if_pos hc2]
          rw [heq]; trivial
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read j (fun v => .write (auxBase + k) v
                  (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1))) := by
            simp only [mergeStep]; rw [if_pos hc1, if_neg hc2]
          rw [heq]; simp only [WellFormed]; exact ih i (j+1) (k+1) _
      · by_cases hc2 : j ≥ hi
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read i (fun v => .write (auxBase + k) v
                  (fun _ => mergeStep mid hi auxBase fuel (i + 1) j (k + 1))) := by
            simp only [mergeStep]; rw [if_neg hc1, if_pos hc2]
          rw [heq]; simp only [WellFormed]; exact ih (i+1) j (k+1) _
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read i (fun vi => .read j (fun vj =>
                  match vi, vj with
                  | .int x, .int y =>
                      if x ≤ y then
                        .write (auxBase + k) vi (fun _ => mergeStep mid hi auxBase fuel (i + 1) j (k + 1))
                      else
                        .write (auxBase + k) vj (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1))
                  | _, _ => .pure ())) := by
            simp only [mergeStep]; rw [if_neg hc1, if_neg hc2]
          rw [heq]
          simp only [WellFormed]
          cases σ i with
          | int x =>
              cases σ j with
              | int y =>
                  by_cases hxy : x ≤ y
                  · simp only [hxy, if_true, WellFormed]; exact ih (i+1) j (k+1) _
                  · simp only [hxy, if_false, WellFormed]; exact ih i (j+1) (k+1) _
              | bool b => trivial
              | unit => trivial
          | bool b => trivial
          | unit => trivial

/-- Same reason as `mergeStep_wellformed`: no `.par` node, unconditionally well-formed. -/
theorem copyBack_wellformed (auxBase : Nat) :
    ∀ (fuel i j : Nat) (σ : State), WellFormed (copyBack auxBase fuel i j) σ := by
  intro fuel
  induction fuel with
  | zero => intro i j σ; trivial
  | succ fuel ih =>
      intro i j σ
      have heq : copyBack auxBase (fuel+1) i j
          = .read (auxBase+i) (fun v => .write j v (fun _ => copyBack auxBase fuel (i+1) (j+1))) := rfl
      rw [heq]; simp only [WellFormed]; exact ih (i+1) (j+1) _

/-- **The payoff.** Both the footprint bound and `WellFormed` for the whole recursive sort, in one
induction on an explicit bound `n ≥ hi - lo` (so the recursive calls' smaller ranges are available
by `ih`, mirroring `mergeSortPar`'s own `termination_by hi - lo`). The `.par` node's independence
obligation — the only place `Indep` is ever invoked in this entire file — is discharged by
`indep_of_footprint_within` plus `TouchesOnly.disjoint`: two ranges, one `omega` call, done.
Everything else here is bookkeeping that assembles that one fact into the whole recursive tree. -/
theorem mergeSortPar_spec (N : Nat) :
    ∀ (n lo hi : Nat), hi - lo ≤ n → hi ≤ N → ∀ σ : State,
      FootprintWithin (accesses (mergeSortPar N lo hi) σ) (TouchesOnly lo hi N) ∧
      WellFormed (mergeSortPar N lo hi) σ := by
  intro n
  induction n with
  | zero =>
      intro lo hi hn hN σ
      have hle1 : hi - lo ≤ 1 := by omega
      have heq : mergeSortPar N lo hi = .pure () := by
        rw [mergeSortPar.eq_1]; rw [dif_pos hle1]
      rw [heq]
      refine ⟨?_, trivial⟩
      simp only [accesses]; exact FootprintWithin.empty _
  | succ n ih =>
      intro lo hi hn hN σ
      by_cases hle1 : hi - lo ≤ 1
      · have heq : mergeSortPar N lo hi = .pure () := by
          rw [mergeSortPar.eq_1]; rw [dif_pos hle1]
        rw [heq]
        refine ⟨?_, trivial⟩
        simp only [accesses]; exact FootprintWithin.empty _
      · have hmn : lo + (hi - lo) / 2 - lo ≤ n := by omega
        have hhn : hi - (lo + (hi - lo) / 2) ≤ n := by omega
        have hlomid : lo ≤ lo + (hi - lo) / 2 := by omega
        have hmidhi : lo + (hi - lo) / 2 ≤ hi := by omega
        have hmidN : lo + (hi - lo) / 2 ≤ N := by omega
        have hlorefl : lo ≤ lo := by omega
        have hhirefl : hi ≤ hi := by omega
        have heq : mergeSortPar N lo hi
            = ParM.bind (ParM.parPair (mergeSortPar N lo (lo+(hi-lo)/2)) (mergeSortPar N (lo+(hi-lo)/2) hi))
                (fun _ => ParM.bind (mergeStep (lo+(hi-lo)/2) hi N (hi - lo) lo (lo+(hi-lo)/2) lo) (fun _ =>
                  copyBack N (hi - lo) lo lo)) := by
          rw [mergeSortPar.eq_1]; rw [dif_neg hle1]
        rw [heq]
        obtain ⟨hFL, hWL⟩ := ih lo (lo+(hi-lo)/2) hmn hmidN σ
        obtain ⟨hFR, hWR⟩ := ih (lo+(hi-lo)/2) hi hhn hN (runSeq (mergeSortPar N lo (lo+(hi-lo)/2)) σ).2
        have hFL' : FootprintWithin (accesses (mergeSortPar N lo (lo+(hi-lo)/2)) σ) (TouchesOnly lo hi N) :=
          FootprintWithin.mono (fun l => TouchesOnly.mono hlorefl hmidhi) hFL
        have hFR' : FootprintWithin
            (accesses (mergeSortPar N (lo+(hi-lo)/2) hi) (runSeq (mergeSortPar N lo (lo+(hi-lo)/2)) σ).2)
            (TouchesOnly lo hi N) :=
          FootprintWithin.mono (fun l => TouchesOnly.mono hlomid hhirefl) hFR
        have hdisj : ∀ l, TouchesOnly lo (lo+(hi-lo)/2) N l → TouchesOnly (lo+(hi-lo)/2) hi N l → False :=
          fun l => TouchesOnly.disjoint hN
        have hindep : Indep (accesses (mergeSortPar N lo (lo+(hi-lo)/2)) σ)
            (accesses (mergeSortPar N (lo+(hi-lo)/2) hi) (runSeq (mergeSortPar N lo (lo+(hi-lo)/2)) σ).2) :=
          indep_of_footprint_within hFL hFR hdisj
        have hWpar : WellFormed
            (ParM.parPair (mergeSortPar N lo (lo+(hi-lo)/2)) (mergeSortPar N (lo+(hi-lo)/2) hi)) σ :=
          WellFormed_par_intro hindep hWL hWR
        have hFpar : FootprintWithin
            (accesses (ParM.parPair (mergeSortPar N lo (lo+(hi-lo)/2)) (mergeSortPar N (lo+(hi-lo)/2) hi)) σ)
            (TouchesOnly lo hi N) := by
          simp only [accesses, ParM.parPair]
          exact FootprintWithin.union hFL' (FootprintWithin.union hFR' (FootprintWithin.empty _))
        refine ⟨?_, ?_⟩
        · rw [accesses_bind]
          apply FootprintWithin.union hFpar
          rw [accesses_bind]
          have hmonoM : ∀ l, ((lo ≤ l ∧ l < lo+(hi-lo)/2) ∨ (lo+(hi-lo)/2 ≤ l ∧ l < hi)
              ∨ (N+lo ≤ l ∧ l < N+lo+(hi-lo))) → TouchesOnly lo hi N l := by
            intro l hl; grind [TouchesOnly, InRange]
          have hmergeF : FootprintWithin
              (accesses (mergeStep (lo+(hi-lo)/2) hi N (hi-lo) lo (lo+(hi-lo)/2) lo)
                (runSeq (ParM.parPair (mergeSortPar N lo (lo+(hi-lo)/2))
                  (mergeSortPar N (lo+(hi-lo)/2) hi)) σ).2)
              (TouchesOnly lo hi N) :=
            FootprintWithin.mono hmonoM
              (mergeStep_within (lo+(hi-lo)/2) hi N (hi-lo) lo (lo+(hi-lo)/2) lo _)
          apply FootprintWithin.union hmergeF
          have hmonoC : ∀ l, ((N+lo ≤ l ∧ l < N+lo+(hi-lo)) ∨ (lo ≤ l ∧ l < lo+(hi-lo))) → TouchesOnly lo hi N l := by
            intro l hl; grind [TouchesOnly, InRange]
          exact FootprintWithin.mono hmonoC (copyBack_within N (hi-lo) lo lo _)
        · rw [WellFormed_bind]
          refine ⟨hWpar, ?_⟩
          rw [WellFormed_bind]
          have hstepWF := mergeStep_wellformed (lo+(hi-lo)/2) hi N (hi-lo) lo (lo+(hi-lo)/2) lo
              (runSeq (ParM.parPair (mergeSortPar N lo (lo+(hi-lo)/2))
                (mergeSortPar N (lo+(hi-lo)/2) hi)) σ).2
          have hcopyWF := copyBack_wellformed N (hi-lo) lo lo
              (runSeq (mergeStep (lo+(hi-lo)/2) hi N (hi-lo) lo (lo+(hi-lo)/2) lo)
                (runSeq (ParM.parPair (mergeSortPar N lo (lo+(hi-lo)/2))
                  (mergeSortPar N (lo+(hi-lo)/2) hi)) σ).2).2
          exact ⟨hstepWF, hcopyWF⟩

/-- **The headline theorem.** `mergeSortPar N lo hi` is well-formed against any state, for any
in-bounds range — independence checked once, structurally, at every nested `.par` node via
`TouchesOnly` disjointness, not per-call. -/
theorem mergeSortPar_wellformed (N lo hi : Nat) (hhiN : hi ≤ N) (σ : State) :
    WellFormed (mergeSortPar N lo hi) σ :=
  (mergeSortPar_spec N (hi - lo) lo hi (by omega) hhiN σ).2

/-- The concrete payoff at the top split: sorting `[lo,mid)` and `[mid,hi)` in parallel reaches
exactly the outcomes sorting them one after another does. Every other `.par` node in the recursion
(both halves' own internal splits, all the way down) gets the identical corollary for free from the
same `WellFormed` fact, via the same two lines — `WellFormed_bind` to peel off the obligation for
that node, `par_seq_eq` to discharge it. -/
theorem mergeSortPar_split_par_seq_eq (N lo hi : Nat) (hhiN : hi ≤ N) (hgt : ¬ hi - lo ≤ 1)
    (σ : State) :
    ParM.parPair (mergeSortPar N lo (lo + (hi - lo) / 2)) (mergeSortPar N (lo + (hi - lo) / 2) hi)
      ∥≡ ParM.seqPair (mergeSortPar N lo (lo + (hi - lo) / 2)) (mergeSortPar N (lo + (hi - lo) / 2) hi)
      from σ := by
  have hwf := mergeSortPar_wellformed N lo hi hhiN σ
  have heq : mergeSortPar N lo hi
      = ParM.bind (ParM.parPair (mergeSortPar N lo (lo+(hi-lo)/2)) (mergeSortPar N (lo+(hi-lo)/2) hi))
          (fun _ => ParM.bind (mergeStep (lo+(hi-lo)/2) hi N (hi - lo) lo (lo+(hi-lo)/2) lo) (fun _ =>
            copyBack N (hi - lo) lo lo)) := by
    rw [mergeSortPar.eq_1]; rw [dif_neg hgt]
  rw [heq, WellFormed_bind] at hwf
  exact par_seq_eq _ _ σ hwf.1

end Paralever.Examples.MergeSort
