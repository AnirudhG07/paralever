import Paralever.Lib.Compose
import Paralever.Lib.Notation

/-! # Example: independent compare-swap rounds

`compareSwap i j` reads and writes both `i` and `j`, so — unlike `SumArray.lean`'s `sumRange`,
which never writes — independence here is not free: two swaps `(i,j)` and `(i',j')` are Bernstein-
independent iff `{i,j}` and `{i',j'}` are disjoint, and that has to be checked, not assumed. This
file is the contrasting case `SumArray.lean`'s docstring points at.

**§1**: the original two-half warm-up (`sortLeftHalf`/`sortRightHalf`), independence by `decide`.

**§2 (variation)**: `SwapPlan := List (Loc × Loc)` generalizes to *any number* of independent
swaps, not just two fixed halves — the odd-even-transposition-sort building block. Independence
is discharged by one hypothesis, `plan.locs.Nodup` (no location used by more than one pair in the
whole plan), via the general Bernstein-from-subsets lemma `indep_of_footprint_subset`.

`swapRound_par_seq_eq`/`sort_par_seq_eq` carry the one open dependency tracked as a TODO in
`Theory/Decomposition.lean` (`wellFormed_canonical`'s `par` case) — see `docs/decomposition.md`.
Everything else in this file is sorry-free. A real `Task`-based compiled variant with an actual
wall-clock benchmark is in `SortTask.lean`.
-/

namespace Paralever.Examples.Sort

open ParM

/-- Compare-and-swap two locations into ascending order. Written in raw `ParM` constructors (not
`do`-notation), same reason as `SumArray.sumRange`: keeps the inductive proofs below unfolding by
`simp`/`rfl` without fighting the `Monad` instance. -/
def compareSwap (i j : Loc) : ParM Unit :=
  .read i (fun a => .read j (fun b =>
    match a, b with
    | .int x, .int y =>
        if y < x then .write i (.int y) (fun _ => .write j (.int x) (fun _ => .pure ()))
        else .pure ()
    | _, _ => .pure ()))

/-! ### §1 — the original two-half warm-up -/

/-- "Sorting" a 2-element range is exactly one compare-swap. -/
def sortLeftHalf : ParM Unit := compareSwap 0 1
def sortRightHalf : ParM Unit := compareSwap 2 3

/-- Array `[5, 3, 8, 1]` at locations 0–3. -/
def σ0 : State
  | 0 => .int 5 | 1 => .int 3 | 2 => .int 8 | 3 => .int 1 | _ => .int 0

example : accesses sortLeftHalf σ0 = ⟨[0, 1], [0, 1]⟩ := rfl
example : accesses sortRightHalf σ0 = ⟨[2, 3], [2, 3]⟩ := rfl

/-- The two halves' footprints are disjoint in both directions — Bernstein holds trivially since
they don't even share reads. -/
example : indepB (accesses sortLeftHalf σ0) (accesses sortRightHalf σ0) = true := rfl

/-- Neither half contains a nested `par`, so each is trivially well-formed on its own — `apply
WellFormed_par_intro` turns the goal into exactly the three things worth checking: independence,
then each side's own well-formedness. -/
theorem wellFormed_sort : WellFormed (parPair sortLeftHalf sortRightHalf) σ0 := by
  apply WellFormed_par_intro
  · exact (indepB_iff _ _).mp (by decide)
  · trivial
  · trivial

/-- The metatheorem, instantiated: running both sub-sorts in parallel reaches exactly the outcomes
running them in sequence does. -/
theorem sort_par_seq_eq :
    parPair sortLeftHalf sortRightHalf ∥≡ seqPair sortLeftHalf sortRightHalf from σ0 :=
  par_seq_eq sortLeftHalf sortRightHalf σ0 wellFormed_sort

example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 0 = .int 3 := rfl
example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 1 = .int 5 := rfl
example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 2 = .int 1 := rfl
example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 3 = .int 8 := rfl

/-! ### §2 (variation) — any number of independent swaps -/

/-- A parallelization plan for compare-swap: one pair per swap, any number of pairs, any indices
— the odd-even-transposition-sort building block, generalizing §1's fixed two halves. -/
abbrev SwapPlan := List (Loc × Loc)

/-- All locations touched by the whole plan. -/
def SwapPlan.locs (plan : SwapPlan) : List Loc := plan.flatMap (fun (i, j) => [i, j])

theorem SwapPlan.locs_cons (p : Loc × Loc) (ps : SwapPlan) :
    SwapPlan.locs (p :: ps) = [p.1, p.2] ++ SwapPlan.locs ps := rfl

/-- List subset is monotone under append — local building block for the induction below; not
worth upstreaming on its own. -/
theorem List.append_subset_append {α : Type} {l1 l2 l1' l2' : List α}
    (h1 : l1 ⊆ l1') (h2 : l2 ⊆ l2') : l1 ++ l2 ⊆ l1' ++ l2' := by
  grind only [= List.subset_def, = List.mem_append]

def swapRoundPar (plan : SwapPlan) : ParM (List Unit) :=
  ParM.parAll (plan.map (fun (i, j) => compareSwap i j))
def swapRoundSeq (plan : SwapPlan) : ParM (List Unit) :=
  ParM.seqAll (plan.map (fun (i, j) => compareSwap i j))

theorem compareSwap_footprint (i j : Loc) (σ : State) :
    (accesses (compareSwap i j) σ).reads ⊆ [i, j] ∧ (accesses (compareSwap i j) σ).writes ⊆ [i, j] := by
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
  | nil => simp [swapRoundPar, ParM.parAll, accesses, Footprint.empty, SwapPlan.locs]
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      simp only [swapRoundPar] at ih
      simp only [swapRoundPar, List.map_cons, ParM.parAll, ParM.parPair, accesses_bind, accesses,
        Footprint.union, SwapPlan.locs_cons]
      obtain ⟨hr, hw⟩ := compareSwap_footprint i j σ
      obtain ⟨hr', hw'⟩ := ih (runSeq (compareSwap i j) σ).2
      constructor <;> (try simp only [List.append_nil, Footprint.empty]) <;>
        first
          | exact List.append_subset_append hr hr'
          | exact List.append_subset_append hw hw'

/-- Bernstein via subset-of-disjoint-sets: if `f`'s reads/writes ⊆ `A`, `g`'s reads/writes ⊆ `B`,
and `A`, `B` are disjoint, `f` and `g` are independent. The general shape needed whenever writes
are present — contrast `SumArray.indep_of_no_writes`, which needed no disjointness at all because
there were no writes to protect. -/
theorem indep_of_footprint_subset {f g : Footprint} {A B : List Loc}
    (hfr : f.reads ⊆ A) (hfw : f.writes ⊆ A) (hgr : g.reads ⊆ B) (hgw : g.writes ⊆ B)
    (hAB : Disjoint A B) : Indep f g := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl1 hl2; exact hAB l (hfw hl1) (hgw hl2)
  · intro l hl1 hl2; exact hAB l (hfw hl1) (hgr hl2)
  · intro l hl1 hl2; exact hAB l (hfr hl2) (hgw hl1)

/-- **General**, for any number of swaps, any indices — the only real condition is
`plan.locs.Nodup`: no location is touched by more than one pair in the whole plan. Contrast
`SumArray.wellFormed_sumRangePar`, which needed *no* side condition at all: here writes are real,
so a genuine disjointness check is unavoidable, and this is exactly it. -/
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

/-- The metatheorem, for any independent set of swaps. -/
theorem swapRound_par_seq_eq (plan : SwapPlan) (σ : State) (h : plan.locs.Nodup) :
    swapRoundPar plan ∥≡ swapRoundSeq plan from σ := by
  exact parAll_par_seq_eq _ σ (wellFormed_swapRoundPar plan σ h)

/-! A genuinely uneven-in-*index* instance — three disjoint pairs, not two contiguous halves: -/

def σ6 : State
  | 0 => .int 5 | 1 => .int 3 | 2 => .int 8 | 3 => .int 1 | 4 => .int 9 | 5 => .int 2 | _ => .int 0

def plan3 : SwapPlan := [(0, 1), (2, 3), (4, 5)]

example : plan3.locs.Nodup := by decide

example : WellFormed (swapRoundPar plan3) σ6 := wellFormed_swapRoundPar plan3 σ6 (by decide)

example : (runSeq (swapRoundPar plan3) σ6).2 0 = .int 3 := rfl
example : (runSeq (swapRoundPar plan3) σ6).2 1 = .int 5 := rfl
example : (runSeq (swapRoundPar plan3) σ6).2 2 = .int 1 := rfl
example : (runSeq (swapRoundPar plan3) σ6).2 3 = .int 8 := rfl
example : (runSeq (swapRoundPar plan3) σ6).2 4 = .int 2 := rfl
example : (runSeq (swapRoundPar plan3) σ6).2 5 = .int 9 := rfl

end Paralever.Examples.Sort
