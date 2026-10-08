import Paralever.Lib.Cost
import Paralever.Lib.Notation

/-! # Independent compare-swap rounds

`compareSwap i j` both reads *and* writes `i` and `j`, so independence is a real obligation here —
unlike a read-only chunked sum. A whole round of swaps is described by a `SwapPlan`, and the single
side condition is `plan.locs.Nodup`: no location is touched by two pairs. Rationale:
`docs/access.md`, `docs/cost.md`. A `Task`-based compiled variant is in `SortTask.lean`. -/

namespace Paralever.Examples.Sort

open ParM

/-- A parallelization plan: one index pair per swap, any number of pairs, any indices — the
odd-even-transposition-sort building block. -/
abbrev SwapPlan := List (Loc × Loc)

/-- All locations touched by the whole plan. -/
def SwapPlan.locs (plan : SwapPlan) : List Loc := plan.flatMap (fun (i, j) => [i, j])

theorem SwapPlan.locs_cons (p : Loc × Loc) (ps : SwapPlan) :
    SwapPlan.locs (p :: ps) = [p.1, p.2] ++ SwapPlan.locs ps := rfl

/-! ### pure -/

/-- One compare-swap as an ordinary state transformer. -/
def swapPure (i j : Loc) (σ : State) : State :=
  match σ i, σ j with
  | .int x, .int y => if y < x then (σ.update i (.int y)).update j (.int x) else σ
  | _, _ => σ

def swapRoundPure (plan : SwapPlan) (σ : State) : State :=
  plan.foldl (fun σ p => swapPure p.1 p.2 σ) σ

/-! ### seq -/

/-- Written in raw `ParM` constructors rather than `do`-notation so the inductions below unfold by
`simp`/`rfl` without fighting the `Monad` instance. -/
def compareSwap (i j : Loc) : ParM Unit :=
  .read i (fun a => .read j (fun b =>
    match a, b with
    | .int x, .int y =>
        if y < x then .write i (.int y) (fun _ => .write j (.int x) (fun _ => .pure ()))
        else .pure ()
    | _, _ => .pure ()))

def swapRoundSeq (plan : SwapPlan) : ParM (List Unit) :=
  ParM.seqAll (plan.map (fun (i, j) => compareSwap i j))

/-! ### par -/

def swapRoundPar (plan : SwapPlan) : ParM (List Unit) :=
  ParM.parAll (plan.map (fun (i, j) => compareSwap i j))

/-! ### pure = seq -/

theorem compareSwap_runSeq (i j : Loc) (σ : State) :
    (runSeq (compareSwap i j) σ).2 = swapPure i j σ := by
  simp only [compareSwap, swapPure, runSeq]
  rcases hi : σ i with x | b | u <;> rcases hj : σ j with y | b' | u' <;>
    simp only [runSeq] <;> (try split) <;> rfl

theorem pure_eq_seq (plan : SwapPlan) (σ : State) :
    (runSeq (swapRoundSeq plan) σ).2 = swapRoundPure plan σ := by
  induction plan generalizing σ with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      simp only [swapRoundSeq] at ih
      simp only [swapRoundSeq, swapRoundPure, List.map_cons, List.foldl_cons, ParM.seqAll,
        ParM.seqPair, runSeq_bind, runSeq, compareSwap_runSeq]
      exact ih (swapPure i j σ)

/-! ### seq = par -/

/-- List subset is monotone under append — local building block for the inductions below. -/
theorem List.append_subset_append {α : Type} {l1 l2 l1' l2' : List α}
    (h1 : l1 ⊆ l1') (h2 : l2 ⊆ l2') : l1 ++ l2 ⊆ l1' ++ l2' := by
  grind only [= List.subset_def, = List.mem_append]

theorem compareSwap_footprint (i j : Loc) (σ : State) :
    (accesses (compareSwap i j) σ).reads ⊆ [i, j] ∧
    (accesses (compareSwap i j) σ).writes ⊆ [i, j] := by
  simp only [compareSwap, accesses]
  rcases hσi : σ i with x | b | u <;> rcases hσj : σ j with y | b' | u' <;>
    simp only [] <;>
    (try split) <;>
    simp only [accesses, Footprint.union, Footprint.empty] <;>
    constructor <;> intro l hl <;> simp_all

theorem compareSwap_wellformed (i j : Loc) (σ : State) : WellFormed (compareSwap i j) σ := by
  simp only [compareSwap, WellFormed]
  rcases hσi : σ i with x | b | u <;> rcases hσj : σ j with y | b' | u' <;>
    simp only [] <;> (try split) <;> trivial

theorem swapRoundPar_footprint (plan : SwapPlan) (σ : State) :
    (accesses (swapRoundPar plan) σ).reads ⊆ plan.locs ∧
    (accesses (swapRoundPar plan) σ).writes ⊆ plan.locs := by
  induction plan generalizing σ with
  | nil => simp [swapRoundPar, accesses_parAll_nil, Footprint.empty, SwapPlan.locs]
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      simp only [swapRoundPar] at ih
      simp only [swapRoundPar, List.map_cons, accesses_parAll_cons, Footprint.union,
        SwapPlan.locs_cons]
      obtain ⟨hr, hw⟩ := compareSwap_footprint i j σ
      obtain ⟨hr', hw'⟩ := ih (runSeq (compareSwap i j) σ).2
      constructor <;> (try simp only [List.append_nil, Footprint.empty]) <;>
        first
          | exact List.append_subset_append hr hr'
          | exact List.append_subset_append hw hw'

theorem wellFormed_swapRoundPar (plan : SwapPlan) (σ : State) (h : plan.locs.Nodup) :
    WellFormed (swapRoundPar plan) σ := by
  induction plan generalizing σ with
  | nil => exact WellFormed_parAll_nil σ
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      rw [SwapPlan.locs_cons] at h
      obtain ⟨_, hpsNodup, hdisj⟩ := List.nodup_append.mp h
      simp only [swapRoundPar, List.map_cons] at ih ⊢
      apply WellFormed_parAll_cons
      · exact compareSwap_wellformed i j σ
      · obtain ⟨hr, hw⟩ := compareSwap_footprint i j σ
        obtain ⟨hr', hw'⟩ := swapRoundPar_footprint ps (runSeq (compareSwap i j) σ).2
        refine indep_of_footprint_subset hr hw hr' hw' ?_
        grind
      · exact ih (runSeq (compareSwap i j) σ).2 hpsNodup

theorem seq_eq_par (plan : SwapPlan) (σ : State) (h : plan.locs.Nodup) :
    swapRoundPar plan ∥≡ swapRoundSeq plan from σ :=
  parAll_par_seq_eq _ σ (wellFormed_swapRoundPar plan σ h)

/-! ### time par < time seq -/

theorem time_compareSwap_pos (i j : Loc) (σ : State) : 0 < time (compareSwap i j) σ :=
  time_pos (compareSwap i j) σ rfl

theorem time_swapRoundPar_pos (a : Loc × Loc) (plan : SwapPlan) (σ : State)
    (h : (SwapPlan.locs (a :: plan)).Nodup) : 0 < time (swapRoundPar (a :: plan)) σ := by
  obtain ⟨i, j⟩ := a
  have hwf := wellFormed_swapRoundPar ((i, j) :: plan) σ h
  simp only [swapRoundPar, List.map_cons] at hwf ⊢
  exact time_parAll_pos _ _ σ hwf (time_compareSwap_pos i j σ)

/-- Two or more disjoint swaps: strictly fewer rounds in parallel. Both branches of the top `par`
must do real work, which is why the plan needs at least two pairs. -/
theorem time_lt (a b : Loc × Loc) (rest : SwapPlan) (σ : State)
    (h : (SwapPlan.locs (a :: b :: rest)).Nodup) :
    time (swapRoundPar (a :: b :: rest)) σ < time (swapRoundSeq (a :: b :: rest)) σ := by
  obtain ⟨i, j⟩ := a
  obtain ⟨i', j'⟩ := b
  have hwf := wellFormed_swapRoundPar ((i, j) :: (i', j') :: rest) σ h
  rw [SwapPlan.locs_cons] at h
  have htail := time_swapRoundPar_pos (i', j') rest σ (List.nodup_append.mp h).2.1
  simp only [swapRoundPar, swapRoundSeq, List.map_cons] at hwf htail ⊢
  exact time_parAll_lt_seqAll _ _ σ hwf (time_compareSwap_pos i j σ) htail

/-- Same work either way — only the rounds shrink. -/
theorem work_eq (plan : SwapPlan) (σ : State) :
    work (swapRoundPar plan) σ = work (swapRoundSeq plan) σ :=
  work_parAll_eq_seqAll _ σ

/-! ### A concrete instance

Three disjoint pairs at uneven indices, over the array `[5, 3, 8, 1, 9, 2]` at locations 0–5. The
same fixture `SortTask.lean` benchmarks. -/

def σ6 : State
  | 0 => .int 5 | 1 => .int 3 | 2 => .int 8 | 3 => .int 1 | 4 => .int 9 | 5 => .int 2 | _ => .int 0

def plan3 : SwapPlan := [(0, 1), (2, 3), (4, 5)]

example : plan3.locs.Nodup := by decide

example : (runSeq (swapRoundPar plan3) σ6).2 0 = .int 3 := rfl
example : (runSeq (swapRoundPar plan3) σ6).2 3 = .int 8 := rfl

/-! ### Anti-vacuity: a plan that reuses a location

`[(0,1), (1,2)]` shares location `1`, so `plan.locs.Nodup` fails and none of the theorems above
apply — exactly the overlapping-swap case a round must not contain. -/

example : ¬ (SwapPlan.locs [(0, 1), (1, 2)]).Nodup := by decide

example : indepB (accesses (compareSwap 0 1) σ6) (accesses (compareSwap 1 2) σ6) = false := rfl

end Paralever.Examples.Sort
