import Paralever.Core.Access

/-! # `runSeq`/`WellFormed`/`accesses` through `bind` — general supporting facts

Reused by `Theory/WellFormedCanonical.lean` (the hard theorem) and by `Theory/Sequentialize.lean`
(the assembly). Kept separate because these are genuinely general — not specific to the
decomposition proof. Rationale: `docs/decomposition.md`.
-/

namespace Paralever

/-- The canonical run of `bind p f` is `p`'s run followed by `f`'s, started at `p`'s result and
post-state. Every `do`-block footprint or value computation in the project reduces through this. -/
@[simp, grind .]
theorem runSeq_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    runSeq (ParM.bind p f) σ = runSeq (f (runSeq p σ).1) (runSeq p σ).2 := by
  induction p generalizing σ with
  | pure a => rfl
  | read l k ih => exact ih (σ l) f σ
  | write l v k ih => exact ih () f (σ.update l v)
  | par p q k ihp ihq ihk => exact ihk _ f _

/-- `bind p f` is well-formed exactly when `p` is and `f`'s continuation is — the latter checked at
`p`'s canonical outcome, since that is the state the continuation actually starts from. Splitting a
`WellFormed` obligation along a `do` block is this lemma, and it is what makes
`wellFormed_of_seqPair` and its N-ary version mechanical rather than a repeat of the `par` case's
difficulty. -/
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

/-- The footprint of `bind p f` is `p`'s united with the continuation's, the latter measured from
`p`'s canonical outcome. Mirrors `runSeq_bind`, and is how every array-style example (`SumArray`,
`MergeSort`) bounds the footprint of a `do` block. -/
@[simp, grind .]
theorem accesses_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    accesses (ParM.bind p f) σ =
    Footprint.union (accesses p σ) (accesses (f (runSeq p σ).1) (runSeq p σ).2) := by
  induction p generalizing σ with
  | pure a => rfl
  | read l k ih => grind
  | write l v k ih => grind
  | par p q k ihp ihq ihk => grind

/-- `parPair p q` and `seqPair p q` have the *same* canonical run — unconditionally, with no `Indep`
hypothesis, because `runSeq` was defined to treat a `par` node by running its branches left to right.
The whole difference between parallel and sequential lives in `Reaches`, not here; this is the purely
definitional bridge `par_seq_eq` rewrites along once both sides have been reduced to their canonical
outcomes. -/
@[simp, grind .]
theorem runSeq_par_eq_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    runSeq (ParM.parPair p q) σ = runSeq (ParM.seqPair p q) σ := by
  unfold ParM.seqPair
  rw [runSeq_bind, runSeq_bind]
  rfl

end Paralever
