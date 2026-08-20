import Paralever.Theory.Sequentialize

/-! # Example: independent sub-sorts

A 4-element array split into two halves; each half is "sorted" by one compare-swap. The two
halves touch disjoint locations, so `par_seq_eq` applies directly — no new proof technique, just
an instance of the metatheorem.

Deliberately stops at the two sub-sorts. Merging the results back together reads *across* both
halves and is therefore not independent — merging is inherently sequential and outside this
example's scope; see `docs/theory.md` §11 for the general pattern (sort/merge is example 2 of
`PLAN.md`'s flagship set).

`par_seq_eq` here still carries the one open dependency tracked as a TODO in
`Theory/Decomposition.lean` (`wellFormed_canonical`'s `par` case) — see `docs/decomposition.md`.
Everything else in this file is sorry-free.
-/

namespace Paralever.Examples.Sort

open ParM

/-- Compare-and-swap two locations into ascending order. -/
def compareSwap (i j : Loc) : ParM Unit := do
  let a ← rd i
  let b ← rd j
  match a, b with
  | .int x, .int y =>
      if y < x then do wr i (.int y); wr j (.int x)
      else return ()
  | _, _ => return ()

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
theorem sort_par_seq_eq : ParSeqEq (parPair sortLeftHalf sortRightHalf) (seqPair sortLeftHalf sortRightHalf) σ0 :=
  par_seq_eq sortLeftHalf sortRightHalf σ0 wellFormed_sort

/-! The canonical outcome (`runSeq`, sorry-free — see `docs/decomposition.md` for why this is
what both sides funnel through under well-formedness): each half ends up sorted independently. -/

example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 0 = .int 3 := rfl
example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 1 = .int 5 := rfl
example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 2 = .int 1 := rfl
example : (runSeq (parPair sortLeftHalf sortRightHalf) σ0).2 3 = .int 8 := rfl

end Paralever.Examples.Sort
