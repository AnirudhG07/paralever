import Paralever.Core.Access

/-! # Decomposition — the sequentialization theorem

`par_eq_seq` reduces to `wellFormed_canonical` (every well-formed program's *only* reachable
outcome, under real interleaving, is its canonical `runSeq` value) plus `runSeq_par_eq_seq`
(the canonical value doesn't distinguish `.par` from sequential composition). Rationale and the
full proof plan for the remaining case: `docs/decomposition.md`.
-/

namespace Paralever

/-! ### Supporting facts about `runSeq` (pure definitions, no operational semantics) -/

/-- Locations `p` doesn't write are untouched by its canonical run. The base fact the locality
lemma builds on. -/
theorem runSeq_frame {τ : Type} (p : ParM τ) (σ : State) :
    ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l := by
  induction p generalizing σ with
  | pure a => intro l _; rfl
  | read l' k ih =>
      intro l hl
      simp only [accesses] at hl
      simp only [runSeq]
      exact ih (σ l') σ l hl
  | write l' v k ih =>
      intro l hl
      simp only [accesses, Footprint.union] at hl
      have hne : l ≠ l' := by intro h; apply hl; subst h; simp
      have hl' : l ∉ (accesses (k ()) (σ.update l' v)).writes := by
        intro hmem; exact hl (by right; exact hmem)
      simp only [runSeq]
      rw [ih () (σ.update l' v) l hl', State.update_other]
      exact hne
  | par p q k ihp ihq ihk =>
      intro l hl
      simp only [accesses, Footprint.union, List.mem_append, not_or] at hl
      obtain ⟨h1, h2, h3⟩ := hl
      simp only [runSeq]
      rw [ihk _ _ l h3, ihq _ l h2, ihp σ l h1]

/-- Both components disjoint from `F`, as a conjunction rather than one combined `reads++writes`
list — this is what actually projects cleanly through `Footprint.union`'s nesting; the combined
form fights every `par`-case proof because `union` interleaves reads and writes separately. -/
def FDisjoint (F : List Loc) (f : Footprint) : Prop := Disjoint F f.reads ∧ Disjoint F f.writes

theorem FDisjoint.left {F : List Loc} {a b : Footprint} (h : FDisjoint F (Footprint.union a b)) :
    FDisjoint F a :=
  ⟨fun l hl hmem => h.1 l hl (by simp [Footprint.union, hmem]),
   fun l hl hmem => h.2 l hl (by simp [Footprint.union, hmem])⟩

theorem FDisjoint.right {F : List Loc} {a b : Footprint} (h : FDisjoint F (Footprint.union a b)) :
    FDisjoint F b :=
  ⟨fun l hl hmem => h.1 l hl (by simp [Footprint.union, hmem]),
   fun l hl hmem => h.2 l hl (by simp [Footprint.union, hmem])⟩

/-- Locality/frame: if `σ`, `σ'` agree outside a set `F` disjoint from `p`'s footprint (computed
against `σ`), `p`'s canonical run agrees on `σ`, `σ'` in value, footprint, and everywhere outside
`F`. The proof of the whole project's decomposition lemma routes through this: it is what lets a
branch's behaviour mid-interleaving (starting from some state reached so far) agree with its
behaviour computed by `accesses`'s reference convention (starting from a different but
agreeing-outside-`F` state), whenever `F` is that branch's own footprint. -/
theorem accesses_runSeq_locality {τ : Type} (p : ParM τ) (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accesses p σ)) (hagree : ∀ l, l ∉ F → σ l = σ' l) :
    accesses p σ = accesses p σ' ∧ (runSeq p σ).1 = (runSeq p σ').1 ∧
    ∀ l, l ∉ F → (runSeq p σ).2 l = (runSeq p σ').2 l := by
  induction p generalizing σ σ' with
  | pure a => exact ⟨rfl, rfl, fun l _ => hagree l ‹_›⟩
  | read l k ih =>
      have hlF : l ∉ F := fun hl => hF.1 l hl (by simp [accesses, Footprint.union])
      have hlv : σ l = σ' l := hagree l hlF
      have hF' : FDisjoint F (accesses (k (σ' l)) σ) := by
        constructor
        · intro x hx hmem; exact hF.1 x hx (by simp [accesses, Footprint.union, hlv, hmem])
        · intro x hx hmem; exact hF.2 x hx (by simp [accesses, Footprint.union, hlv, hmem])
      obtain ⟨e1, e2, e3⟩ := ih (σ' l) σ σ' hF' hagree
      simp only [accesses, runSeq, hlv]
      exact ⟨by rw [e1], e2, e3⟩
  | write l v k ih =>
      have hF' : FDisjoint F (accesses (k ()) (σ.update l v)) := by
        constructor
        · intro x hx hmem; exact hF.1 x hx (by simp [accesses, Footprint.union, hmem])
        · intro x hx hmem; exact hF.2 x hx (by simp [accesses, Footprint.union, hmem])
      have hagree' : ∀ l', l' ∉ F → (σ.update l v) l' = (σ'.update l v) l' := by
        intro l' hl'
        by_cases heq : l' = l
        · simp [State.update, heq]
        · rw [State.update_other σ v heq, State.update_other σ' v heq]
          exact hagree l' hl'
      obtain ⟨e1, e2, e3⟩ := ih () (σ.update l v) (σ'.update l v) hF' hagree'
      simp only [accesses, runSeq]
      exact ⟨by rw [e1], e2, e3⟩
  | par p q k ihp ihq ihk =>
      have hFp : FDisjoint F (accesses p σ) := hF.left
      obtain ⟨ep1, ep2, ep3⟩ := ihp σ σ' hFp hagree
      have hFq : FDisjoint F (accesses q (runSeq p σ).2) := hF.right.left
      obtain ⟨eq1, eq2, eq3⟩ := ihq (runSeq p σ).2 (runSeq p σ').2 hFq ep3
      have hFk : FDisjoint F
          (accesses (k ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1)) (runSeq q (runSeq p σ).2).2) :=
        hF.right.right
      obtain ⟨ek1, ek2, ek3⟩ := ihk _ _ _ hFk eq3
      rw [ep2, eq2] at ek1 ek2 ek3
      simp only [accesses, runSeq, ep2, eq2]
      exact ⟨by rw [ep1, eq1, ek1], ek2, ek3⟩

/-- What `accesses`'s definition asymmetrically assumed (`docs/access.md`) is now a theorem, not
a hand-wave: under `Indep`, `q`'s canonical run from the post-`p` state `σ₁` agrees with its run
from the original `σ` — i.e. `q` really is computed in isolation, matching Brookes' `s₁ ∗ s₂`
splitting. `Indep`'s write-disjointness components are exactly `FDisjoint` at `F := p`'s writes;
`runSeq_frame` is exactly the agreement hypothesis `accesses_runSeq_locality` needs. -/
theorem accesses_runSeq_isolated {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : Indep (accesses p σ) (accesses q (runSeq p σ).2)) :
    accesses q (runSeq p σ).2 = accesses q σ ∧
    (runSeq q (runSeq p σ).2).1 = (runSeq q σ).1 := by
  have hF : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) := ⟨h.2.1, h.1⟩
  have hagree : ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l := runSeq_frame p σ
  obtain ⟨e1, e2, _⟩ := accesses_runSeq_locality q (runSeq p σ).2 σ (accesses p σ).writes hF hagree
  exact ⟨e1, e2⟩

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
theorem WellFormed_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    WellFormed (ParM.bind p f) σ ↔
    WellFormed p σ ∧ WellFormed (f (runSeq p σ).1) (runSeq p σ).2 := by
  induction p generalizing σ with
  | pure a => simp [ParM.bind, WellFormed, runSeq]
  | read l k ih => exact ih (σ l) f σ
  | write l v k ih => exact ih () f (σ.update l v)
  | par p q k ihp ihq ihk =>
      simp only [ParM.bind, WellFormed, runSeq]
      rw [ihk _ f _]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, h2, h3, h4⟩, h5⟩
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩

/-- The canonical reference value does not distinguish `parPair` from `seqPair` — `runSeq` was
already defined by running `par`'s branches sequentially. No `Indep` needed for this fact; the
difference between parallel and sequential only shows up operationally, in `Reaches`. -/
theorem runSeq_par_eq_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    runSeq (ParM.parPair p q) σ = runSeq (ParM.seqPair p q) σ := by
  unfold ParM.seqPair
  rw [runSeq_bind, runSeq_bind]
  rfl

/-! ### The canonical-outcome theorem

Under `WellFormed`, real interleaved execution reaches *only* the canonical `runSeq` outcome.
`pure`/`read`/`write` are proved; `par` is the content of Brookes' decomposition lemma and is not
yet proved — see `docs/decomposition.md` for the three-lemma plan (locality of `runSeq`, the
join-point decomposition of `Reaches` at a `par` node, and the diamond step via
`State.update_comm`). This is the one place in the project where the real difficulty lives; it is
deliberately left open rather than forced. -/
theorem wellFormed_canonical {τ : Type} (p : ParM τ) :
    ∀ σ r σ', WellFormed p σ → (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ) := by
  induction p with
  | pure a =>
      intro σ r σ' _
      constructor
      · intro h
        have h2 := Reaches.terminal (c := Conf.run (ParM.pure a) σ) rfl h
        simp only [Conf.run.injEq, ParM.pure.injEq] at h2
        simp [runSeq, h2.1, h2.2]
      · intro h
        simp only [runSeq, Prod.mk.injEq] at h
        obtain ⟨h5, h4⟩ := h
        subst h5; subst h4
        exact Reaches.refl
  | read l k ih =>
      intro σ r σ' hwf
      have hstep : stepC (Conf.run (ParM.read l k) σ) = [Conf.run (k (σ l)) σ] := rfl
      constructor
      · intro h
        rcases Reaches.single_step hstep h with heq | h'
        · exact absurd heq (by simp)
        · exact (ih (σ l) σ r σ' hwf).mp h'
      · intro h
        refine Reaches.trans ?_ ((ih (σ l) σ r σ' hwf).mpr h)
        exact Reaches.tail Reaches.refl (by rw [hstep]; exact List.mem_singleton_self _)
  | write l v k ih =>
      intro σ r σ' hwf
      have hstep : stepC (Conf.run (ParM.write l v k) σ) = [Conf.run (k ()) (σ.update l v)] := rfl
      constructor
      · intro h
        rcases Reaches.single_step hstep h with heq | h'
        · exact absurd heq (by simp)
        · exact (ih () (σ.update l v) r σ' hwf).mp h'
      · intro h
        refine Reaches.trans ?_ ((ih () (σ.update l v) r σ' hwf).mpr h)
        exact Reaches.tail Reaches.refl (by rw [hstep]; exact List.mem_singleton_self _)
  | par p q k ihp ihq ihk =>
      intro σ r σ' hwf
      -- TODO(decomposition): Brookes' decomposition lemma, operational half.
      -- (1) locality — DONE, accesses_runSeq_isolated above.
      -- (2) join-point decomposition of Reaches at `par` (any interleaved run factors into a
      --     p-prefix and a q-prefix up to the point both finish) — OPEN.
      -- (3) the diamond step via State.update_comm (already proved, Core/Semantics.lean) — the
      --     lemma exists but isn't yet wired into an interleaving argument.
      -- See docs/decomposition.md for the full account. This is the one place in the project
      -- where real difficulty remains; deliberately not forced.
      sorry

end Paralever
