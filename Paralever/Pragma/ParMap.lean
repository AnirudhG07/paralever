import Paralever.Theory.Sequentialize

/-! # `parMap` — parallelize an existing pure function, zero footprint-marking

The direct answer to "I already have a pure function, I don't want to redefine `State`s or mark
locations, I just want `par_seq_eq` about running it on independent chunks in parallel." Every
other example in this project (`SumArray`, `Sort`, `MergeSort`, `MatMul`) parallelizes code that
*reads and writes a shared heap* — that's exactly the case that needs a footprint bound. `parMap`
is the other, much more common case: the function is applied to a plain value (`c : List α`) that
each parallel branch already owns outright, so there is no heap access to bound at all.
`parMap_wellformed` is unconditional — no `omega`, no disjointness fact, no per-call proof,
because every branch of the parallel tree is a bare `.pure`. -/

namespace Paralever.Pragma.ParMap
open Paralever

/-- `Indep` never needs to know anything about `g` when the other side touches nothing —
`Disjoint [] _` is vacuous for all three of `Indep`'s conditions. -/
@[simp, grind .]
theorem indep_empty_left (g : Footprint) : Indep Footprint.empty g := by
  simp [Indep, Footprint.empty]

/-- Apply `f` to each chunk, in parallel. `f` is a plain `List α → β`, evaluated directly — no
`ParM` rewrite of the caller's function required. -/
def parMap {α β : Type} (f : List α → β) (chunks : List (List α)) : ParM (List β) :=
  ParM.parAll (chunks.map (fun c => ParM.pure (f c)))

/-- The sequential counterpart, same shape as every other example's `_Seq` pairing. -/
def seqMap {α β : Type} (f : List α → β) (chunks : List (List α)) : ParM (List β) :=
  ParM.seqAll (chunks.map (fun c => ParM.pure (f c)))

/-- **Unconditional.** No hypothesis on `f`, `chunks`, or `σ` — every branch is a `.pure`, so there
is nothing to check. -/
theorem parMap_wellformed {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    WellFormed (parMap f chunks) σ := by
  unfold parMap
  induction chunks generalizing σ with
  | nil => exact WellFormed_parAll_nil σ
  | cons c cs ih =>
      grind only [= List.map_cons, WellFormed_parAll_cons, = WellFormed.eq_1, = accesses.eq_1,
        indep_empty_left]

/-- **The payoff.** Running `f` over every chunk in parallel reaches exactly the outcome running
it in sequence does — for *any* pure `f` and *any* chunking, no proof obligation left for the
caller. -/
theorem parMap_par_seq_eq {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    ParSeqEq (parMap f chunks) (seqMap f chunks) σ :=
  parAll_par_seq_eq _ σ (parMap_wellformed f chunks σ)

end Paralever.Pragma.ParMap
