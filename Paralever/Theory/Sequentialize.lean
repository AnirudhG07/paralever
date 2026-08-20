import Paralever.Theory.Decomposition

/-! # The sequentialization theorem

Assembly only — the content is in `wellFormed_canonical` (`Theory/Decomposition.lean`), whose
`par` case is not yet proved (TODO there). This file is complete *given* that lemma; nothing here
is a shortcut. Rationale: `docs/decomposition.md`.
-/

namespace Paralever

/-- `p` and `q` reach exactly the same outcomes from `σ` — the same reachable
`(result, final-state)` pairs, regardless of which one actually runs. This is what "parallel and
sequential agree" *means* in this project: every headline theorem below is stated in this
vocabulary rather than spelling out `Reaches`/`Conf.run`/`ParM.pure` directly. -/
def ParSeqEq {α : Type} (p q : ParM α) (σ : State) : Prop :=
  ∀ r σ', Reaches (.run p σ) (.run (.pure r) σ') ↔ Reaches (.run q σ) (.run (.pure r) σ')

/-- `WellFormed (parPair p q) σ` needs no `Indep` to transfer to `seqPair p q` — there is no
top-level `par` node in `seqPair` to check, only `p`'s and `q`'s own internal structure, which
`WellFormed (parPair p q) σ` already supplies via its second and third conjuncts. Proved via
`WellFormed_bind`, not the `par` case's interleaving argument. -/
theorem wellFormed_of_seqPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) : WellFormed (ParM.seqPair p q) σ := by
  grind [WellFormed_bind, ParM.seqPair, ParM.parPair]

/-- The metatheorem. Parallel and sequential composition reach exactly the same outcomes,
whenever the program is well-formed (independent at every nesting level, not just the top). -/
theorem par_seq_eq {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) : ParSeqEq (ParM.parPair p q) (ParM.seqPair p q) σ := by
  intro r σ'
  rw [wellFormed_canonical _ σ r σ' h,
      wellFormed_canonical _ σ r σ' (wellFormed_of_seqPair p q σ h),
      runSeq_par_eq_seq]

/-! ### N-ary generalization

Corollary of the binary case, exactly as `docs/decomposition.md` predicted: `parAll`/`seqAll` are
built from binary `par`/`seqPair` nested over a list, so the same three-piece assembly
(`wellFormed_canonical` on each side, plus a purely-definitional bridge) goes through by induction
on the list — no new proof technique. Both supporting lemmas below are fully proved (no `sorry`);
the metatheorem itself inherits the *same* open dependency as `par_eq_seq` — the `par` case of
`wellFormed_canonical` — and nothing more. -/

theorem runSeq_parAll_eq_seqAll {τ : Type} (ps : List (ParM τ)) (σ : State) :
    runSeq (ParM.parAll ps) σ = runSeq (ParM.seqAll ps) σ := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih =>
      simp only [ParM.parAll, ParM.seqAll, runSeq_bind]
      rw [runSeq_par_eq_seq p (ParM.parAll ps) σ]
      simp only [ParM.seqPair, runSeq_bind, ih]

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

/-- `WellFormed (parAll (p :: ps)) σ` unfolded once — `apply WellFormed_parAll_cons` to start a
`WellFormed` proof for a `parAll` list one element at a time. -/
theorem WellFormed_parAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (h1 : WellFormed p σ)
    (h2 : Indep (accesses p σ) (accesses (ParM.parAll ps) (runSeq p σ).2))
    (h3 : WellFormed (ParM.parAll ps) (runSeq p σ).2) :
    WellFormed (ParM.parAll (p :: ps)) σ := by
  simp only [ParM.parAll, WellFormed_bind, ParM.parPair, WellFormed]
  exact ⟨⟨h2, h1, h3, trivial⟩, trivial⟩

theorem WellFormed_parAll_nil {τ : Type} (σ : State) :
    WellFormed (ParM.parAll ([] : List (ParM τ))) σ := trivial

/-- The metatheorem for a list of branches — "break the work into a few pieces" in its literal
form. Same statement shape as `par_seq_eq`, generalized from a pair to a list. -/
theorem parAll_par_seq_eq {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) : ParSeqEq (ParM.parAll ps) (ParM.seqAll ps) σ := by
  intro r σ'
  rw [wellFormed_canonical _ σ r σ' h,
      wellFormed_canonical _ σ r σ' (wellFormed_of_seqAll ps σ h),
      runSeq_parAll_eq_seqAll]

end Paralever
