import Paralever.Theory.Decomposition

/-! # The sequentialization theorem

Assembly only — the content is in `wellFormed_canonical` (`Theory/Decomposition.lean`), whose
`par` case is not yet proved (TODO there). This file is complete *given* that lemma; nothing here
is a shortcut. Rationale: `docs/decomposition.md`.
-/

namespace Paralever

/-- `WellFormed (parPair p q) σ` needs no `Indep` to transfer to `seqPair p q` — there is no
top-level `par` node in `seqPair` to check, only `p`'s and `q`'s own internal structure, which
`WellFormed (parPair p q) σ` already supplies via its second and third conjuncts. Proved via
`WellFormed_bind`, not the `par` case's interleaving argument. -/
theorem wellFormed_of_seqPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) : WellFormed (ParM.seqPair p q) σ := by
  unfold ParM.parPair WellFormed at h
  unfold ParM.seqPair
  rw [WellFormed_bind]
  refine ⟨h.2.1, ?_⟩
  rw [WellFormed_bind]
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- The metatheorem. Parallel and sequential composition reach exactly the same outcomes,
whenever the program is well-formed (independent at every nesting level, not just the top). -/
theorem par_eq_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) (r : α × β) (σ' : State) :
    Reaches (.run (ParM.parPair p q) σ) (.run (.pure r) σ')
  ↔ Reaches (.run (ParM.seqPair p q) σ) (.run (.pure r) σ') := by
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
      exact ⟨hp.2.1, ih _ hp.2.2.1, trivial⟩

/-- The metatheorem for a list of branches — "break the work into a few pieces" in its literal
form. Same statement shape as `par_eq_seq`, generalized from a pair to a list. -/
theorem parAll_eq_seqAll {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) (r : List τ) (σ' : State) :
    Reaches (.run (ParM.parAll ps) σ) (.run (.pure r) σ')
  ↔ Reaches (.run (ParM.seqAll ps) σ) (.run (.pure r) σ') := by
  rw [wellFormed_canonical _ σ r σ' h,
      wellFormed_canonical _ σ r σ' (wellFormed_of_seqAll ps σ h),
      runSeq_parAll_eq_seqAll]

end Paralever
