import Paralever.Core.Access

/-! # `runSeq`/`WellFormed`/`accesses` through `bind` — general supporting facts

Reused by `Theory/WellFormedCanonical.lean` (the hard theorem) and by `Theory/Sequentialize.lean`
(the assembly). Kept separate because these are genuinely general — not specific to the
decomposition proof. Rationale: `docs/decomposition.md`.

Each proof here inducts with `ParM.inductionOn` (`Core/ParM.lean`): Lean's `induction` tactic refuses
a nested inductive. The motive has to quantify over the continuation's type and the state, because the
induction descends into a fork's children, which have types of their own.
-/

namespace Paralever

/-- The canonical run of `bind p f` is `p`'s run followed by `f`'s, started at `p`'s result and
post-state. Every `do`-block footprint or value computation in the project reduces through this. -/
@[simp, grind .]
theorem runSeq_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    runSeq (ParM.bind p f) σ = runSeq (f (runSeq p σ).1) (runSeq p σ).2 := by
  have H : ∀ {α : Type} (p : ParM α) (β : Type) (f : α → ParM β) (σ : State),
      runSeq (ParM.bind p f) σ = runSeq (f (runSeq p σ).1) (runSeq p σ).2 := by
    intro α p
    induction p using ParM.inductionOn with
    | hpure a => intro β f σ; rfl
    | hread l k ih => intro β f σ; exact ih (σ l) β f σ
    | hwrite l v k ih => intro β f σ; exact ih () β f (σ.update l v)
    | hpar cs k _ ihk => intro β f σ; exact ihk _ β f _
  exact H p β f σ

/-- `bind p f` is well-formed exactly when `p` is and `f`'s continuation is — the latter checked at
`p`'s canonical outcome, since that is the state the continuation actually starts from. Splitting a
`WellFormed` obligation along a `do` block is this lemma, and it is what makes
`wellFormed_of_seqPair` and its N-ary version mechanical rather than a repeat of the `par` case's
difficulty. -/
@[simp, grind .]
theorem WellFormed_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    WellFormed (ParM.bind p f) σ ↔
    WellFormed p σ ∧ WellFormed (f (runSeq p σ).1) (runSeq p σ).2 := by
  have H : ∀ {α : Type} (p : ParM α) (β : Type) (f : α → ParM β) (σ : State),
      WellFormed (ParM.bind p f) σ ↔
      WellFormed p σ ∧ WellFormed (f (runSeq p σ).1) (runSeq p σ).2 := by
    intro α p
    induction p using ParM.inductionOn with
    | hpure a => intro β f σ; simp [ParM.bind, WellFormed, runSeq]
    | hread l k ih => intro β f σ; exact ih (σ l) β f σ
    | hwrite l v k ih => intro β f σ; exact ih () β f (σ.update l v)
    | hpar cs k _ ihk =>
        intro β f σ
        show WellFormed (.par cs (fun vs => ParM.bind (k vs) f)) σ ↔ _
        rw [WellFormed, WellFormed, ihk _ β f _]
        exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩,
               fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  exact H p β f σ

/-- The footprint of `bind p f` is `p`'s united with the continuation's, the latter measured from
`p`'s canonical outcome. Mirrors `runSeq_bind`, and is how every array-style example (`SumArray`,
`MergeSort`) bounds the footprint of a `do` block. -/
@[simp, grind .]
theorem accesses_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    accesses (ParM.bind p f) σ =
    Footprint.union (accesses p σ) (accesses (f (runSeq p σ).1) (runSeq p σ).2) := by
  have H : ∀ {α : Type} (p : ParM α) (β : Type) (f : α → ParM β) (σ : State),
      accesses (ParM.bind p f) σ =
      Footprint.union (accesses p σ) (accesses (f (runSeq p σ).1) (runSeq p σ).2) := by
    intro α p
    induction p using ParM.inductionOn with
    | hpure a => intro β f σ; rfl
    | hread l k ih => intro β f σ; grind
    | hwrite l v k ih => intro β f σ; grind
    | hpar cs k _ ihk => intro β f σ; grind
  exact H p β f σ

/-- `parPair p q` and `seqPair p q` have the *same* canonical run — unconditionally, with no `Indep`
hypothesis, because `runSeq` was defined to treat a `par` node by running its children left to right.
The whole difference between parallel and sequential lives in `Reaches`, not here; this is the purely
definitional bridge `par_seq_eq` rewrites along once both sides have been reduced to their canonical
outcomes. -/
@[simp, grind .]
theorem runSeq_par_eq_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    runSeq (ParM.parPair p q) σ = runSeq (ParM.seqPair p q) σ := by
  unfold ParM.seqPair ParM.parPair
  rw [runSeq_bind, runSeq_bind]
  rfl

end Paralever
