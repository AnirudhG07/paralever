import Paralever.Core.Access

/-! # `runSeq`/`WellFormed` through `bind` — general supporting facts

Reused by `Theory/WellFormedCanonical.lean` (the hard theorem) and by `Theory/Sequentialize.lean`
(the assembly). Kept separate because these are genuinely general — not specific to the
decomposition proof. Rationale: `docs/decomposition.md`.
-/

namespace Paralever

@[simp, grind .]
theorem runSeq_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    runSeq (ParM.bind p f) σ = runSeq (f (runSeq p σ).1) (runSeq p σ).2 := by
  induction p generalizing σ with
  | pure a => rfl
  | read l k ih => exact ih (σ l) f σ
  | write l v k ih => exact ih () f (σ.update l v)
  | par p q k ihp ihq ihk => exact ihk _ f _

/-- `WellFormed` respects `bind`: well-formedness of the whole is well-formedness of the first
part plus well-formedness of the continuation *at the canonical outcome*. General and reusable —
this is what makes `wellFormed_of_seqPair` (and its N-ary generalization) mechanical rather than a
repeat of the `par` case's difficulty. -/
@[simp, grind .]
theorem WellFormed_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    WellFormed (ParM.bind p f) σ ↔
    WellFormed p σ ∧ WellFormed (f (runSeq p σ).1) (runSeq p σ).2 := by
  induction p generalizing σ with
  | pure a => simp [ParM.bind, WellFormed, runSeq]
  | read l k ih => exact ih (σ l) f σ
  | write l v k ih => exact ih () f (σ.update l v)
  | par p q k ihp ihq ihk =>
      grind only [ParM.bind, WellFormed, runSeq]

/-- The canonical reference value does not distinguish `parPair` from `seqPair` — `runSeq` was
already defined by running `par`'s branches sequentially. No `Indep` needed for this fact; the
difference between parallel and sequential only shows up operationally, in `Reaches`. -/
@[simp, grind .]
theorem runSeq_par_eq_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    runSeq (ParM.parPair p q) σ = runSeq (ParM.seqPair p q) σ := by
  unfold ParM.seqPair
  rw [runSeq_bind, runSeq_bind]
  rfl

end Paralever
