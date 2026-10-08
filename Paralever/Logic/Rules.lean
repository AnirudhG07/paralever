import Paralever.Theory.Sequentialize

/-! # Hoare triples over `ParM` — the parallel composition rule

Hoare-triple validity defined directly against the real operational semantics (`Reaches`), no
trace model, no domain theory — Vafeiadis' style (*Concurrent Separation Logic and Operational
Semantics*, MFPS'11), already `CLAUDE.md`'s stated reference for Tier-2. The parallel rule itself
(`{P}C{Q} {P'}C'{Q'} / {P∗P'} C∥C' {Q∗Q'}`, disjointness side condition) is O'Hearn's, *Resources,
Concurrency, and Local Reasoning* (CONCUR'04 / TCS'07) — the paper that introduces Concurrent
Separation Logic. Its classical soundness proof decomposes an interleaved execution into two
independent per-thread executions (Brookes' Parallel Decomposition Lemma, Theorem 21, same
CONCUR'04/TCS'07 paper already cited in `Theory/WellFormedCanonical.lean`) — but that theorem, read
directly (see `docs/decomposition.md`'s account, from having actually read the paper), is a
*per-computation projection* lemma, not the trace-set equality `[[c1‖c2]] = [[c1;c2]]` this file's
proof actually needs. That equality is `par_seq_eq` (`Theory/Sequentialize.lean`) — Paralever's own
theorem, best described as Brookes' Theorem 21 specialized to no shared resources and strengthened
to full outcome equivalence, not a restatement of something already on the page there. Everything
below is built on `par_seq_eq`, not confirmed by it: no separate soundness paper of ours is cited
here beyond that theorem itself.

Uses plain `∧` for framing, not the separating `∗` from `Logic/BIInstance.lean` — see that file's
header for why (that instance's `∗` is exclusive/disjoint-heap only, narrower than this project's
own `Indep`, which permits shared reads). `Local` below plays `∗`'s locality role directly against
`Core/Access.lean`'s own footprint vocabulary, so the parallel rule proved here is fully general
(shared reads included) without waiting on that design question. Graduating framing itself to `∗`
is future work; nothing here is blocked on it.
-/

namespace Paralever.Logic

open Paralever

/-- Hoare-triple validity: partial correctness against the real, nondeterministic `Reaches`
relation. No safety clause (a triple says nothing about executions that race) — matches how this
project already separates "does it reach a race" from "what does it reach if it doesn't"
(`docs/decomposition.md`'s own `wellFormed_canonical`, which is exactly this same split for the
canonical-outcome side). -/
def Triple {τ : Type} (P : State → Prop) (c : ParM τ) (Q : τ → State → Prop) : Prop :=
  ∀ σ, P σ → ∀ r σ', Reaches (.run c σ) (.run (.pure r) σ') → Q r σ'

/-- `P` depends only on locations in `L` — the side condition framing needs when assertions are
plain `State → Prop` rather than footprint-carrying `∗`-assertions. -/
def Local (L : List Loc) (P : State → Prop) : Prop :=
  ∀ σ σ', (∀ l ∈ L, σ l = σ' l) → (P σ ↔ P σ')

/-- The state agreement a frame argument needs, lifted from `runSeq_frame` to the *real*
`Reaches` relation via `wellFormed_canonical`: under `WellFormed`, wherever a real execution ends
up is exactly the canonical `runSeq` outcome, so `runSeq_frame`'s locality applies to it directly. -/
theorem reaches_frame {τ : Type} (c : ParM τ) (σ : State) (hwf : WellFormed c σ)
    (r : τ) (σ' : State) (h : Reaches (.run c σ) (.run (.pure r) σ')) :
    ∀ l ∉ (accesses c σ).writes, σ l = σ' l := by
  have heq : (r, σ') = runSeq c σ := (wellFormed_canonical c σ r σ' hwf).mp h
  intro l hl
  have := runSeq_frame c σ l hl
  rw [← heq] at this
  exact this.symm

/-- **The frame rule.** `R`, local to some `L` disjoint from what `c` writes (whenever `P` holds),
survives `c`'s execution untouched. -/
theorem Triple.frame {τ : Type} {P : State → Prop} {c : ParM τ} {Q : τ → State → Prop}
    (h : Triple P c Q) (R : State → Prop) (L : List Loc) (hLocal : Local L R)
    (hwf : ∀ σ, P σ → WellFormed c σ)
    (hDisjoint : ∀ σ, P σ → Disjoint L (accesses c σ).writes) :
    Triple (fun σ => P σ ∧ R σ) c (fun r σ => Q r σ ∧ R σ) := by
  intro σ ⟨hP, hR⟩ r σ' hReach
  refine ⟨h σ hP r σ' hReach, (hLocal σ σ' ?_).mp hR⟩
  intro l hl
  exact reaches_frame c σ (hwf σ hP) r σ' hReach l (fun hmem => hDisjoint σ hP l hl hmem)

/-- **The parallel composition rule.** `WellFormed (parPair c c') σ` is doing double duty: it is
*both* the classical CSL disjointness side condition *and* (via `par_seq_eq`) the reason the rule
is sound at all, rather than two separate obligations. -/
theorem Triple.par {α β : Type} {P : State → Prop} {c : ParM α} {Q : α → State → Prop}
    {P' : State → Prop} {c' : ParM β} {Q' : β → State → Prop}
    (h : Triple P c Q) (h' : Triple P' c' Q')
    (LP' LQ : List Loc)
    (hLocalP' : Local LP' P') (hLocalQ : ∀ r, Local LQ (Q r))
    (hwf : ∀ σ, P σ → P' σ → WellFormed (ParM.parPair c c') σ)
    (hDisjP' : ∀ σ, P σ → P' σ → Disjoint LP' (accesses c σ).writes)
    (hDisjQ : ∀ σ, P σ → P' σ → Disjoint LQ (accesses c' (runSeq c σ).2).writes) :
    Triple (fun σ => P σ ∧ P' σ) (ParM.parPair c c') (fun r σ => Q r.1 σ ∧ Q' r.2 σ) := by
  intro σ ⟨hP, hP'⟩ r σ' hReach
  have hwf' := hwf σ hP hP'
  have heq : (r, σ') = runSeq (ParM.parPair c c') σ := (wellFormed_canonical _ σ r σ' hwf').mp hReach
  obtain ⟨_, ⟨hwfc, hwfc', _⟩, _⟩ := hwf'
  have hunfold : runSeq (ParM.parPair c c') σ =
      (((runSeq c σ).1, (runSeq c' (runSeq c σ).2).1), (runSeq c' (runSeq c σ).2).2) := rfl
  rw [hunfold] at heq
  obtain ⟨hr, hσ'eq⟩ := Prod.mk.injEq .. ▸ heq
  have hReachC : Reaches (.run c σ) (.run (.pure (runSeq c σ).1) (runSeq c σ).2) :=
    (wellFormed_canonical c σ (runSeq c σ).1 (runSeq c σ).2 hwfc).mpr rfl
  have hQa : Q (runSeq c σ).1 (runSeq c σ).2 := h σ hP (runSeq c σ).1 (runSeq c σ).2 hReachC
  have hReachC' : Reaches (.run c' (runSeq c σ).2)
      (.run (.pure (runSeq c' (runSeq c σ).2).1) (runSeq c' (runSeq c σ).2).2) :=
    (wellFormed_canonical c' (runSeq c σ).2 (runSeq c' (runSeq c σ).2).1
      (runSeq c' (runSeq c σ).2).2 hwfc').mpr rfl
  have hP'σ1 : P' (runSeq c σ).2 := by
    apply (hLocalP' σ (runSeq c σ).2 ?_).mp hP'
    intro l hl
    exact reaches_frame c σ hwfc (runSeq c σ).1 (runSeq c σ).2 hReachC l
      (fun hmem => hDisjP' σ hP hP' l hl hmem)
  have hQ'b : Q' (runSeq c' (runSeq c σ).2).1 (runSeq c' (runSeq c σ).2).2 :=
    h' (runSeq c σ).2 hP'σ1 (runSeq c' (runSeq c σ).2).1 (runSeq c' (runSeq c σ).2).2 hReachC'
  have hQaσ2 : Q (runSeq c σ).1 (runSeq c' (runSeq c σ).2).2 := by
    apply (hLocalQ (runSeq c σ).1 (runSeq c σ).2 (runSeq c' (runSeq c σ).2).2 ?_).mp hQa
    intro l hl
    exact reaches_frame c' (runSeq c σ).2 hwfc' (runSeq c' (runSeq c σ).2).1
      (runSeq c' (runSeq c σ).2).2 hReachC' l (fun hmem => hDisjQ σ hP hP' l hl hmem)
  rw [hr, hσ'eq]
  exact ⟨hQaσ2, hQ'b⟩

end Paralever.Logic
