import Paralever.Lib.TouchesOnly
import Paralever.Lib.Notation
import Paralever.Lib.Cost
import Prl.Lang.Imp


namespace Paralever.Examples.MergeSort

open ParM

/-! ### pure

The algorithm on plain lists, no monad. -/

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

/-! ### The merge and copy-back loops

Shared verbatim by both versions below; neither contains a `.par` node. -/

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

/-! ### par -/

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

/-! ### seq -/

/-- The sequential counterpart: identical recursion, `seqPair` in place of `parPair`. -/
def mergeSortSeq (N : Nat) : Nat → Nat → ParM Unit
  | lo, hi =>
      if _h : hi - lo ≤ 1 then .pure ()
      else
        let mid := lo + (hi - lo) / 2
        ParM.bind (ParM.seqPair (mergeSortSeq N lo mid) (mergeSortSeq N mid hi)) (fun _ =>
          ParM.bind (mergeStep mid hi N (hi - lo) lo mid lo) (fun _ =>
            copyBack N (hi - lo) lo lo))
termination_by lo hi => hi - lo
decreasing_by all_goals omega

/-! ### Independence — "different memory ⇒ done," via `Theory/Intervals.lean`

`mergeStep`/`copyBack` have no `.par` node, so `WellFormed` for either is unconditional. The one
`.par` node is `mergeSortPar`'s, and `Theory/Intervals.lean` discharges it: bound each side's entire
footprint to a predicate, show the two are never true of the same location (one `omega`), read
`Indep` off `indep_of_footprint_within` — no Bernstein case analysis at any depth. `TouchesOnly` is
that predicate: "in the data range being sorted, or its matching scratch range." -/

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
            simp only [mergeStep]; rw [ite_eq_left hc1, ite_eq_left hc2]
          rw [heq]; simp only [accesses]; exact FootprintWithin.empty _
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read j (fun v => .write (auxBase + k) v
                  (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1))) := by
            simp only [mergeStep]; rw [ite_eq_left hc1, ite_eq_right hc2]
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
            simp only [mergeStep]; rw [ite_eq_right hc1, ite_eq_left hc2]
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
            simp only [mergeStep]; rw [ite_eq_right hc1, ite_eq_right hc2]
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
                  · simp only [hxy, ite_true]
                    simp only [accesses]
                    have hb3 : FootprintWithin (Footprint.mk [] [auxBase+k])
                        (fun l => (i ≤ l ∧ l < mid) ∨ (j ≤ l ∧ l < hi) ∨ (auxBase+k ≤ l ∧ l < auxBase+k+(fuel+1))) :=
                      FootprintWithin.write (auxBase+k) _ hk1
                    have hb4 := FootprintWithin.mono hmonoR (ih (i+1) j (k+1) (σ.update (auxBase+k) (Val.int x)))
                    exact FootprintWithin.union hb3 hb4
                  · simp only [hxy, ite_false]
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
            simp only [mergeStep]; rw [ite_eq_left hc1, ite_eq_left hc2]
          rw [heq]; trivial
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read j (fun v => .write (auxBase + k) v
                  (fun _ => mergeStep mid hi auxBase fuel i (j + 1) (k + 1))) := by
            simp only [mergeStep]; rw [ite_eq_left hc1, ite_eq_right hc2]
          rw [heq]; simp only [WellFormed]; exact ih i (j+1) (k+1) _
      · by_cases hc2 : j ≥ hi
        · have heq : mergeStep mid hi auxBase (fuel+1) i j k
              = .read i (fun v => .write (auxBase + k) v
                  (fun _ => mergeStep mid hi auxBase fuel (i + 1) j (k + 1))) := by
            simp only [mergeStep]; rw [ite_eq_right hc1, ite_eq_left hc2]
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
            simp only [mergeStep]; rw [ite_eq_right hc1, ite_eq_right hc2]
          grind

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
          rw [accesses_parPair]
          exact FootprintWithin.union hFL' hFR'
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

/-! ### pure = seq

The general array-to-list refinement (`mergeSortPar` sorts iff `mergeSortPure` does) is an ordinary
sequential-sorting correctness proof, orthogonal to this project's claim and not attempted here —
link ③ of `docs/pure-bridge.md`. What is checked is the instance: -/

def σ4 : State
  | 0 => .int 5 | 1 => .int 3 | 2 => .int 8 | 3 => .int 1
  | _ => .int 0

/-- info: true -/
#guard_msgs in
#eval ((List.range 4).map (runSeq (mergeSortPar 4 0 4) σ4).2)
  == (mergeSortPure [5, 3, 8, 1]).map Val.int

/-! ### seq = par -/

/-- Both versions compute the same canonical run, at every depth. -/
theorem runSeq_eq (N : Nat) : ∀ (n lo hi : Nat), hi - lo ≤ n → ∀ σ : State,
    runSeq (mergeSortPar N lo hi) σ = runSeq (mergeSortSeq N lo hi) σ := by
  intro n
  induction n with
  | zero =>
      intro lo hi hn σ
      have h1 : hi - lo ≤ 1 := by omega
      rw [mergeSortPar.eq_1, dite_eq_left h1, mergeSortSeq.eq_1, dite_eq_left h1]
  | succ n ih =>
      intro lo hi hn σ
      by_cases h1 : hi - lo ≤ 1
      · rw [mergeSortPar.eq_1, dite_eq_left h1, mergeSortSeq.eq_1, dite_eq_left h1]
      · rw [mergeSortPar.eq_1, dite_eq_right h1, mergeSortSeq.eq_1, dite_eq_right h1]
        have hl : lo + (hi - lo) / 2 - lo ≤ n := by omega
        have hr : hi - (lo + (hi - lo) / 2) ≤ n := by omega
        simp only [runSeq_bind, runSeq_parPair, ParM.seqPair, runSeq,
          ih lo (lo + (hi - lo) / 2) hl σ]
        rw [ih (lo + (hi - lo) / 2) hi hr (runSeq (mergeSortSeq N lo (lo + (hi - lo) / 2)) σ).2]

/-- `mergeSortSeq` has no `par` node anywhere, so it is well-formed unconditionally. -/
theorem seq_wellformed (N : Nat) : ∀ (n lo hi : Nat), hi - lo ≤ n → ∀ σ : State,
    WellFormed (mergeSortSeq N lo hi) σ := by
  intro n
  induction n with
  | zero =>
      intro lo hi hn σ
      have h1 : hi - lo ≤ 1 := by omega
      rw [mergeSortSeq.eq_1, dite_eq_left h1]; trivial
  | succ n ih =>
      intro lo hi hn σ
      by_cases h1 : hi - lo ≤ 1
      · rw [mergeSortSeq.eq_1, dite_eq_left h1]; trivial
      · rw [mergeSortSeq.eq_1, dite_eq_right h1]
        have hl : lo + (hi - lo) / 2 - lo ≤ n := by omega
        have hr : hi - (lo + (hi - lo) / 2) ≤ n := by omega
        rw [WellFormed_bind, ParM.seqPair, WellFormed_bind]
        refine ⟨⟨ih lo _ hl σ, ?_⟩, ?_⟩
        · rw [WellFormed_bind]; exact ⟨ih _ hi hr _, trivial⟩
        · rw [WellFormed_bind]
          exact ⟨mergeStep_wellformed _ _ _ _ _ _ _ _, copyBack_wellformed _ _ _ _ _⟩

/-- **seq = par**, for the whole recursion, not just the top split. -/
theorem seq_eq_par (N lo hi : Nat) (hhiN : hi ≤ N) (σ : State) :
    mergeSortPar N lo hi ∥≡ mergeSortSeq N lo hi from σ := by
  intro r σ'
  rw [wellFormed_canonical _ σ r σ' (mergeSortPar_wellformed N lo hi hhiN σ),
    wellFormed_canonical _ σ r σ' (seq_wellformed N (hi - lo) lo hi (by omega) σ),
    runSeq_eq N (hi - lo) lo hi (by omega) σ]

/-! ### time par < time seq -/

theorem copyBack_time_pos (auxBase fuel i j : Nat) (hf : 0 < fuel) (σ : State) :
    0 < time (copyBack auxBase fuel i j) σ := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  exact time_pos _ σ rfl

/-- A range of two or more always ends with a copy-back, so it costs at least one round. -/
theorem seq_time_pos (N lo hi : Nat) (h2 : 2 ≤ hi - lo) (σ : State) :
    0 < time (mergeSortSeq N lo hi) σ := by
  have h1 : ¬ hi - lo ≤ 1 := by omega
  rw [mergeSortSeq.eq_1, dite_eq_right h1]
  have hwf := seq_wellformed N (hi - lo) lo hi (by omega) σ
  rw [mergeSortSeq.eq_1, dite_eq_right h1] at hwf
  rw [time_bind_add _ _ σ hwf]
  have hwf2 := ((WellFormed_bind _ _ σ).mp hwf).2
  rw [time_bind_add _ _ _ hwf2]
  have := copyBack_time_pos N (hi - lo) lo lo (by omega)
    (runSeq (mergeStep (lo + (hi - lo) / 2) hi N (hi - lo) lo (lo + (hi - lo) / 2) lo)
      (runSeq (ParM.seqPair (mergeSortSeq N lo (lo + (hi - lo) / 2))
        (mergeSortSeq N (lo + (hi - lo) / 2) hi)) σ).2).2
  omega

/-- **`time par ≤ time seq`** at every depth: `max` at each fork instead of `+`. -/
theorem time_le (N : Nat) : ∀ (n lo hi : Nat), hi - lo ≤ n → hi ≤ N → ∀ σ : State,
    time (mergeSortPar N lo hi) σ ≤ time (mergeSortSeq N lo hi) σ := by
  intro n
  induction n with
  | zero =>
      intro lo hi hn _ σ
      have h1 : hi - lo ≤ 1 := by omega
      rw [mergeSortPar.eq_1, dite_eq_left h1, mergeSortSeq.eq_1, dite_eq_left h1]; omega
  | succ n ih =>
      intro lo hi hn hN σ
      by_cases h1 : hi - lo ≤ 1
      · rw [mergeSortPar.eq_1, dite_eq_left h1, mergeSortSeq.eq_1, dite_eq_left h1]; omega
      · have hl : lo + (hi - lo) / 2 - lo ≤ n := by omega
        have hr : hi - (lo + (hi - lo) / 2) ≤ n := by omega
        have hmid : lo + (hi - lo) / 2 ≤ N := by omega
        rw [mergeSortPar.eq_1, dite_eq_right h1, mergeSortSeq.eq_1, dite_eq_right h1]
        have hwfP := mergeSortPar_wellformed N lo hi hN σ
        have hwfS := seq_wellformed N (hi - lo) lo hi (by omega) σ
        rw [mergeSortPar.eq_1, dite_eq_right h1] at hwfP
        rw [mergeSortSeq.eq_1, dite_eq_right h1] at hwfS
        have hpair : runSeq (ParM.parPair (mergeSortPar N lo (lo + (hi - lo) / 2))
              (mergeSortPar N (lo + (hi - lo) / 2) hi)) σ
            = runSeq (ParM.seqPair (mergeSortSeq N lo (lo + (hi - lo) / 2))
              (mergeSortSeq N (lo + (hi - lo) / 2) hi)) σ := by
          simp only [runSeq_parPair, ParM.seqPair, runSeq, runSeq_bind,
            runSeq_eq N n lo (lo + (hi - lo) / 2) hl σ]
          rw [runSeq_eq N n (lo + (hi - lo) / 2) hi hr _]
        have hePl : runSeq (mergeSortPar N lo (lo + (hi - lo) / 2)) σ
            = runSeq (mergeSortSeq N lo (lo + (hi - lo) / 2)) σ :=
          runSeq_eq N n lo _ hl σ
        have hwfPP := ((WellFormed_bind _ _ σ).mp hwfP).1
        rw [time_bind_add _ _ σ hwfP, time_bind_add _ _ σ hwfS, hpair,
          time_parPair_eq_max _ _ σ hwfPP,
          time_seqPair_eq_add _ _ σ ((WellFormed_bind _ _ σ).mp hwfS).1]
        -- the right half does not see the left half's writes, so its rounds are the same either way
        have hC : time (mergeSortPar N (lo + (hi - lo) / 2) hi)
              (runSeq (mergeSortPar N lo (lo + (hi - lo) / 2)) σ).2
            = time (mergeSortPar N (lo + (hi - lo) / 2) hi) σ :=
          time_locality _ _ σ (accesses (mergeSortPar N lo (lo + (hi - lo) / 2)) σ).writes
            (wellFormed_parPair_parts _ _ σ hwfPP).2.2
            ⟨(wellFormed_parPair_parts _ _ σ hwfPP).1.2.1,
             (wellFormed_parPair_parts _ _ σ hwfPP).1.1⟩ (runSeq_frame _ σ)
        rw [hePl] at hC
        have h2l := ih lo (lo + (hi - lo) / 2) hl hmid σ
        have h2r := ih (lo + (hi - lo) / 2) hi hr hN
          (runSeq (mergeSortSeq N lo (lo + (hi - lo) / 2)) σ).2
        omega

/-- **`time par < time seq`** once both halves have real work, i.e. from four elements up. -/
theorem time_lt (N lo hi : Nat) (hhiN : hi ≤ N) (h4 : 4 ≤ hi - lo) (σ : State) :
    time (mergeSortPar N lo hi) σ < time (mergeSortSeq N lo hi) σ := by
  have h1 : ¬ hi - lo ≤ 1 := by omega
  have hl : lo + (hi - lo) / 2 - lo ≤ hi - lo := by omega
  have hr : hi - (lo + (hi - lo) / 2) ≤ hi - lo := by omega
  have hmid : lo + (hi - lo) / 2 ≤ N := by omega
  rw [mergeSortPar.eq_1, dite_eq_right h1, mergeSortSeq.eq_1, dite_eq_right h1]
  have hwfP := mergeSortPar_wellformed N lo hi hhiN σ
  have hwfS := seq_wellformed N (hi - lo) lo hi (by omega) σ
  rw [mergeSortPar.eq_1, dite_eq_right h1] at hwfP
  rw [mergeSortSeq.eq_1, dite_eq_right h1] at hwfS
  have hpair : runSeq (ParM.parPair (mergeSortPar N lo (lo + (hi - lo) / 2))
        (mergeSortPar N (lo + (hi - lo) / 2) hi)) σ
      = runSeq (ParM.seqPair (mergeSortSeq N lo (lo + (hi - lo) / 2))
        (mergeSortSeq N (lo + (hi - lo) / 2) hi)) σ := by
    simp only [runSeq_parPair, ParM.seqPair, runSeq, runSeq_bind,
      runSeq_eq N (hi - lo) lo (lo + (hi - lo) / 2) hl σ]
    rw [runSeq_eq N (hi - lo) (lo + (hi - lo) / 2) hi hr _]
  have hePl : runSeq (mergeSortPar N lo (lo + (hi - lo) / 2)) σ
      = runSeq (mergeSortSeq N lo (lo + (hi - lo) / 2)) σ :=
    runSeq_eq N (hi - lo) lo _ hl σ
  have hwfPP := ((WellFormed_bind _ _ σ).mp hwfP).1
  rw [time_bind_add _ _ σ hwfP, time_bind_add _ _ σ hwfS, hpair,
    time_parPair_eq_max _ _ σ hwfPP,
    time_seqPair_eq_add _ _ σ ((WellFormed_bind _ _ σ).mp hwfS).1]
  -- the right half does not see the left half's writes, so its rounds are the same either way
  have hC : time (mergeSortPar N (lo + (hi - lo) / 2) hi)
        (runSeq (mergeSortPar N lo (lo + (hi - lo) / 2)) σ).2
      = time (mergeSortPar N (lo + (hi - lo) / 2) hi) σ :=
    time_locality _ _ σ (accesses (mergeSortPar N lo (lo + (hi - lo) / 2)) σ).writes
      (wellFormed_parPair_parts _ _ σ hwfPP).2.2
      ⟨(wellFormed_parPair_parts _ _ σ hwfPP).1.2.1,
       (wellFormed_parPair_parts _ _ σ hwfPP).1.1⟩ (runSeq_frame _ σ)
  rw [hePl] at hC
  have h2l := time_le N (hi - lo) lo (lo + (hi - lo) / 2) hl hmid σ
  have h2r := time_le N (hi - lo) (lo + (hi - lo) / 2) hi hr hhiN
    (runSeq (mergeSortSeq N lo (lo + (hi - lo) / 2)) σ).2
  have hposl := seq_time_pos N lo (lo + (hi - lo) / 2) (by omega) σ
  have hposr := seq_time_pos N (lo + (hi - lo) / 2) hi (by omega)
    (runSeq (mergeSortSeq N lo (lo + (hi - lo) / 2)) σ).2
  omega

/-- Same operations either way, with no hypothesis. -/
theorem work_eq (lo hi : Nat) (σ : State) :
    work (ParM.parPair (mergeSortPar hi lo (lo + (hi - lo) / 2))
        (mergeSortPar hi (lo + (hi - lo) / 2) hi)) σ
      = work (ParM.seqPair (mergeSortPar hi lo (lo + (hi - lo) / 2))
        (mergeSortPar hi (lo + (hi - lo) / 2) hi)) σ := work_par_eq_seq _ _ σ

-- At the top split of a four-element range: eighteen operations either way, nine rounds
-- against eighteen.
/-- info: (18, 18, 9, 18) -/
#guard_msgs in
#eval (work (ParM.parPair (mergeSortPar 4 0 2) (mergeSortPar 4 2 4)) σ4,
       work (ParM.seqPair (mergeSortPar 4 0 2) (mergeSortPar 4 2 4)) σ4,
       time (ParM.parPair (mergeSortPar 4 0 2) (mergeSortPar 4 2 4)) σ4,
       time (ParM.seqPair (mergeSortPar 4 0 2) (mergeSortPar 4 2 4)) σ4)

/-! ## 4. The same algorithm, written in the surface language

`AExp` has no comparison, so §1's `mergeStep` — which branches on `x ≤ y` — is not expressible, and
patching it with a conditional would make the footprint a union of branches and lose exactness.
Batcher's odd-even merge sort takes the route hardware takes instead: its merge is a fixed network
of compare-exchanges, branch-free given `min` and `max`, so the footprint stays exact and the
obligation stays a `Bool`. The parallelism is nested — `wfB` checks Bernstein at every `parallel`
block of the recursion tree, at every depth. -/

namespace Surface
open Paralever.Prl

/-- A no-op. -/
def skipP : ParProg := ParProg.block []

/-- Branch-free compare-exchange: the smaller value to `i`, the larger to `j`. Both registers hold
the original values when the stores run, so no temporary is needed. -/
def cmpEx (i j : Loc) : ParProg :=
  paralever { %0 := [i]; %1 := [j];
        [i] := AExp.min (%0) (%1);
        [j] := AExp.max (%0) (%1) }

/-- Batcher's odd-even merge of two sorted halves, at comparator distance `r`. The two sub-merges
run in parallel, and so does the whole row of comparators after them. -/
def oeMerge : Nat → Nat → Nat → Nat → ParProg
  | 0,        _,  _, _ => skipP
  | fuel + 1, lo, n, r =>
      let m := r * 2
      if m < n then
        ParProg.block
          [ .par [ oeMerge fuel lo n m, oeMerge fuel (lo + r) n m ]
          , .par ((List.range ((n - r) / m)).map (fun t =>
              let i := lo + r + t * m; cmpEx i (i + r))) ]
      else cmpEx lo (lo + r)

/-- Sort `[lo, lo+n)` for `n` a power of two: **sort the two halves in parallel**, then merge. The
recursion builds a tree of `parallel` blocks, each thread containing more of them. -/
def oeSort : Nat → Nat → Nat → ParProg
  | 0,        _,  _ => skipP
  | fuel + 1, lo, n =>
      if n ≤ 1 then skipP
      else
        let m := n / 2
        ParProg.block
          [ .par [ oeSort fuel lo m, oeSort fuel (lo + m) m ]
          , oeMerge (fuel + 1) lo n 1 ]

/-! ### The obligation, at every depth

One `decide` covers the whole tree: `wfB` on a `parallel` block checks its own threads pairwise
*and* recurses into each of them, so a race nested three levels down is caught here. -/

example : ParProg.wfB (oeSort 4 0 4) = true := by decide
example : ParProg.wfB (oeSort 8 0 8) = true := by decide

/-- Nesting is checked, not assumed: an inner block that races is rejected even when the outer
threads are disjoint. -/
example : ParProg.wfB (.par [cmpEx 0 1, cmpEx 2 3]) = true  := by decide
example : ParProg.wfB (.par [cmpEx 0 1, cmpEx 1 2]) = false := by decide

/-! ### Par = Seq, cost, and execution -/

theorem par_seq_eq_8 (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (oeSort 8 0 8) ρ) (ParProg.execSeq (oeSort 8 0 8) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- **Par ≤ Seq in rounds** — §3's `time_le` is the hand-built version of this. -/
theorem time_le_8 (ρ : Regs) (σ : State) :
    time (ParProg.execPar (oeSort 8 0 8) ρ) σ ≤ time (ParProg.execSeq (oeSort 8 0 8) ρ) σ :=
  ParProg.time_le (by decide) ρ σ

/-- The threaded and single-threaded runs agree, so a benchmark of the two is fair. -/
theorem runTask_eq_seq (ρ : Regs) (σ : State) :
    ParProg.runTask (oeSort 8 0 8) ρ σ = ParProg.runTaskSeq (oeSort 8 0 8) ρ σ :=
  ParProg.runTask_eq_runTaskSeq (by decide) ρ σ

/-- And it sorts. `#eval` spawns a `Task` per thread of every block, at every depth. -/
def σ8 : State
  | 0 => .int 8 | 1 => .int 3 | 2 => .int 6 | 3 => .int 1
  | 4 => .int 7 | 5 => .int 2 | 6 => .int 5 | 7 => .int 4
  | _ => .int 0

-- #eval ParProg.evalTask (oeSort 8 0 8) σ8 [0,1,2,3,4,5,6,7]
-- ⇒ [1, 2, 3, 4, 5, 6, 7, 8]

example : (runSeq (ParProg.execPar (oeSort 8 0 8) (fun _ => 0)) σ8).2 0 = .int 1 := rfl
example : (runSeq (ParProg.execPar (oeSort 8 0 8) (fun _ => 0)) σ8).2 7 = .int 8 := rfl

end Surface

end Paralever.Examples.MergeSort
