import Paralever.Theory.Sequentialize
import Paralever.Lib.Cost

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

/-- Anything is independent of a computation that touches nothing: all three of `Indep`'s conditions
are `Disjoint []`-shaped, hence vacuous. The only fact `parMap_wellformed` needs. -/
@[simp, grind .]
theorem indep_empty_left (g : Footprint) : Indep Footprint.empty g := by
  simp [Indep, Footprint.empty]

/-- Apply `f` to each chunk, in parallel. `f` stays a plain `List α → β` and is evaluated directly
inside a `ParM.pure`, so nothing about the caller's function has to be rewritten into `ParM` — and
nothing about it reaches the heap, which is why every theorem below is unconditional. -/
def parMap {α β : Type} (f : List α → β) (chunks : List (List α)) : ParM (List β) :=
  ParM.parAll (chunks.map (fun c => ParM.pure (f c)))

/-- The sequential counterpart: the same chunks, one after another. Same `_Par`/`_Seq` pairing as
every other example. -/
def seqMap {α β : Type} (f : List α → β) (chunks : List (List α)) : ParM (List β) :=
  ParM.seqAll (chunks.map (fun c => ParM.pure (f c)))

/-- **`parMap` is well-formed, always.** No hypothesis on `f`, `chunks`, or `σ`: every branch is a
`.pure`, so every footprint in sight is empty and the Bernstein check at each `par` node is vacuous. -/
theorem parMap_wellformed {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    WellFormed (parMap f chunks) σ := by
  unfold parMap
  induction chunks generalizing σ with
  | nil => exact WellFormed_parAll_nil σ
  | cons c cs ih =>
      grind only [= List.map_cons, WellFormed_parAll_cons, = WellFormed.eq_1, = accesses.eq_1,
        indep_empty_left]

/-- **Chunked parallel application of a pure function needs no side condition.** Running `f` over
every chunk in parallel reaches exactly the outcomes running it in sequence does, for *any* `f` and
*any* chunking, with nothing left for the caller to discharge.

The price is visible in `work_parMap_zero`/`time_parMap_zero`: with no heap access there is no memory
traffic to overlap, so this route buys correctness for free and shows no speedup in a cost model that
counts memory rounds. Real speedup comes from the examples that do touch the heap. -/
theorem parMap_par_seq_eq {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    ParSeqEq (parMap f chunks) (seqMap f chunks) σ :=
  parAll_par_seq_eq _ σ (parMap_wellformed f chunks σ)

/-! ### Pure counterpart and cost

Every branch is a `ParM.pure`, so there is no memory traffic at all: `work = 0`, hence `time = 0` for
both versions. A speedup from pure parallel work is invisible to this cost model, which counts
memory rounds — see `docs/cost.md`. -/

/-- `seqMap` computes `chunks.map f` and leaves the heap exactly as it found it. -/
@[simp, grind .]
theorem seqMap_eq_map {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    runSeq (seqMap f chunks) σ = (chunks.map f, σ) := by
  induction chunks generalizing σ with
  | nil => rfl
  | cons c cs ih =>
      simp only [seqMap] at ih
      simp only [seqMap, List.map_cons, ParM.seqAll, ParM.seqPair, runSeq, runSeq_bind, ih]

/-- `parMap`'s canonical run computes the same `chunks.map f`, heap untouched — the pure counterpart
of `parMap_par_seq_eq`, by computation rather than through the metatheorem. -/
@[simp, grind .]
theorem parMap_eq_map {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    runSeq (parMap f chunks) σ = (chunks.map f, σ) := by
  -- `parAll` is one `par` node now, so route through its canonical-run bridge to `seqAll`
  show runSeq (ParM.parAll (chunks.map (fun c => ParM.pure (f c)))) σ = _
  rw [runSeq_parAll_eq_seqAll]
  exact seqMap_eq_map f chunks σ

/-- Zero memory operations, for any chunking — `work` counts reads and writes, and there are none.
-- ref: `docs/cost.md` -/
theorem work_parMap_zero {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    work (parMap f chunks) σ = 0 := by
  show work (ParM.parAll (chunks.map (fun c => ParM.pure (f c)))) σ = 0
  rw [work_parAll_eq_seqAll]
  induction chunks generalizing σ with
  | nil => rfl
  | cons c cs ih =>
      rw [List.map_cons, ParM.seqAll, work_bind, work_seqPair, ih (runSeq (ParM.pure (f c)) σ).2]
      simp [work]

/-- Zero parallel rounds, hence no measurable speedup: this cost model counts memory rounds, and
`parMap` performs no memory operations at all. Honest rather than flattering — the result is the point
of the section header above. -/
theorem time_parMap_zero {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    time (parMap f chunks) σ = 0 :=
  time_zero_of_work_zero _ σ (parMap_wellformed f chunks σ) (work_parMap_zero f chunks σ)

end Paralever.Pragma.ParMap
