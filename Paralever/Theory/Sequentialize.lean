import Paralever.Theory.WellFormedCanonical

/-! # The sequentialization theorem

Assembly only. Each headline theorem here is `wellFormed_canonical`
(`Theory/WellFormedCanonical.lean`) applied to both sides, plus a purely definitional bridge
(`runSeq_par_eq_seq`, `runSeq_parAll_eq_seqAll`) saying the two sides have the same canonical run.
All the difficulty is in that one lemma. Rationale: `docs/decomposition.md`.
-/

namespace Paralever

/-- `p` and `q` reach exactly the same outcomes from `σ` — the same reachable
`(result, final-state)` pairs, regardless of which one actually runs. This is what "parallel and
sequential agree" *means* in this project: every headline theorem below is stated in this
vocabulary rather than spelling out `Reaches`/`Conf.run`/`ParM.pure` directly. -/
def ParSeqEq {α : Type} (p q : ParM α) (σ : State) : Prop :=
  ∀ r σ', Reaches (.run p σ) (.run (.pure r) σ') ↔ Reaches (.run q σ) (.run (.pure r) σ')

/-- Well-formedness transfers from the parallel composition to the sequential one. The `Indep`
conjunct is not needed: `seqPair` has no top-level `par` node to check, only `p`'s and `q`'s own
internal structure, which `WellFormed (parPair p q) σ` already supplies. A `WellFormed_bind`
rearrangement, not an interleaving argument. -/
theorem wellFormed_of_seqPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) : WellFormed (ParM.seqPair p q) σ := by
  grind [ParM.seqPair, ParM.parPair]

/-- **The metatheorem.** `p ∥ q` and `p; q` reach exactly the same outcomes from `σ`, under every
schedule, whenever the program is well-formed.

"Well-formed" is Bernstein independence checked at *every* `par` node in the term, not only the
outermost one — nothing weaker would do, since a branch can race with itself while the two branches'
total footprints stay disjoint. That obligation is the only thing left for a user to discharge per
program; everything above it has been proved once, here. -- ref: `docs/decomposition.md` -/
theorem par_seq_eq {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) : ParSeqEq (ParM.parPair p q) (ParM.seqPair p q) σ := by
  intro r σ'
  rw [wellFormed_canonical _ σ r σ' h,
      wellFormed_canonical _ σ r σ' (wellFormed_of_seqPair p q σ h),
      runSeq_par_eq_seq]

/-! ### N-ary generalization

A corollary of the binary case, not a second theorem. `parAll`/`seqAll` are binary `par`/`seqPair`
nested over a list, so the same assembly goes through by induction on the list and no new proof
technique appears — which is why `ParM` has no `parN` constructor to prove this about (`List (ParM α)`
would be an illegal nested inductive; see `docs/program-model.md`). -/

/-- The two sides of the N-ary equivalence have the same canonical run — the definitional bridge for
`parAll_par_seq_eq`, `runSeq_par_eq_seq` lifted along the list. No `Indep` needed. -/
theorem runSeq_parAll_eq_seqAll {τ : Type} (ps : List (ParM τ)) (σ : State) :
    runSeq (ParM.parAll ps) σ = runSeq (ParM.seqAll ps) σ := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih =>
      simp only [ParM.parAll, ParM.seqAll, runSeq_bind]
      rw [runSeq_par_eq_seq p (ParM.parAll ps) σ]
      simp only [ParM.seqPair, runSeq_bind, ih]

/-- Well-formedness transfers from `parAll` to `seqAll`, by induction on the list — the N-ary
`wellFormed_of_seqPair`. -/
theorem wellFormed_of_seqAll {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) : WellFormed (ParM.seqAll ps) σ := by
  induction ps generalizing σ with
  | nil => trivial
  | cons p ps ih =>
      simp only [ParM.parAll, WellFormed_bind] at h
      simp only [ParM.seqAll, WellFormed_bind, ParM.seqPair]
      refine ⟨?_, trivial⟩
      have hp := h.1
      unfold ParM.parPair WellFormed at hp
      simp_all only [WellFormed, and_true, Indep, Disjoint, imp_false, and_self]

/-- `WellFormed (parAll (p :: ps)) σ` from the three facts about the head and tail that need proving.
`apply` this to peel one element off a `parAll` well-formedness goal; note the tail's independence and
well-formedness are checked at `(runSeq p σ).2`, the state after the head's canonical run. -/
@[simp, grind .]
theorem WellFormed_parAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (h1 : WellFormed p σ)
    (h2 : Indep (accesses p σ) (accesses (ParM.parAll ps) (runSeq p σ).2))
    (h3 : WellFormed (ParM.parAll ps) (runSeq p σ).2) :
    WellFormed (ParM.parAll (p :: ps)) σ := by
  simp only [ParM.parAll, WellFormed_bind, ParM.parPair, WellFormed]
  exact ⟨⟨h2, h1, h3, trivial⟩, trivial⟩

/-- An empty `parAll` is well-formed — the base case, nothing to check. -/
@[simp, grind .]
theorem WellFormed_parAll_nil {τ : Type} (σ : State) :
    WellFormed (ParM.parAll ([] : List (ParM τ))) σ := trivial

/-- **The metatheorem for a list of branches**: running `ps` all in parallel reaches exactly the
outcomes running them one after another does, under every schedule, given well-formedness. This is
what `#parallel_for` and every chunked example ultimately appeals to. -/
@[simp, grind .]
theorem parAll_par_seq_eq {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) : ParSeqEq (ParM.parAll ps) (ParM.seqAll ps) σ := by
  intro r σ'
  rw [wellFormed_canonical _ σ r σ' h,
      wellFormed_canonical _ σ r σ' (wellFormed_of_seqAll ps σ h),
      runSeq_parAll_eq_seqAll]

end Paralever
