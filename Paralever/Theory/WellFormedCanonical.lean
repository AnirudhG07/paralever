import Paralever.Theory.Decomposition

/-! # `wellFormed_canonical` — the sequentialization theorem's hard case

Dedicated file: every lemma here exists to support this one theorem's `par` case, Brookes'
Parallel Decomposition Lemma (CONCUR'04 §5–7) mechanized via Vafeiadis' operational style
(MFPS'11). Nothing here is reused elsewhere in the project — general facts about `runSeq`/
`WellFormed` through `bind` live in `Theory/Decomposition.lean` instead.

-/


namespace Paralever

/-! ### Locality of `accesses`/`runSeq` — done -/

/-- Locations `p` doesn't write are untouched by its canonical run. The base fact the locality
lemma builds on. -/
@[simp, grind .]
theorem runSeq_frame {τ : Type} (p : ParM τ) (σ : State) :
    ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l := by
  induction p generalizing σ with
  | pure a => intro l _; rfl
  | read l' k ih => grind
  | write l' v k ih => grind
  | par p q k ihp ihq ihk => grind

/-- Both components disjoint from `F`, as a conjunction rather than one combined `reads++writes`
list — this is what actually projects cleanly through `Footprint.union`'s nesting; the combined
form fights every `par`-case proof because `union` interleaves reads and writes separately. -/
@[simp, grind .]
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
      grind only [FDisjoint, = accesses.eq_2, = runSeq.eq_2, = Disjoint.eq_1,
        = Footprint.union.eq_1, = List.cons_append, = List.mem_cons, = List.mem_append]
  | write l v k ih =>
      grind only [accesses, FDisjoint, runSeq, Footprint.union, = Disjoint.eq_1, = List.cons_append,
        State.update_other, State.update_same, = List.mem_append, ← List.not_mem_nil]
  | par p q k ihp ihq ihk =>
      have hFp : FDisjoint F (accesses p σ) := hF.left
      obtain ⟨ep1, ep2, ep3⟩ := ihp σ σ' hFp hagree
      have hFq : FDisjoint F (accesses q (runSeq p σ).2) := hF.right.left
      grind only [accesses, runSeq, FDisjoint, Footprint.union, = Disjoint.eq_1,
        usr List.append_assoc, = List.mem_append]

/-- What `accesses`'s definition asymmetrically assumed (`docs/access.md`) is now a theorem, not
a hand-wave: under `Indep`, `q`'s canonical run from the post-`p` state `σ₁` agrees with its run
from the original `σ` — i.e. `q` really is computed in isolation, matching Brookes' `s₁ ∗ s₂`
splitting. `Indep`'s write-disjointness components are exactly `FDisjoint` at `F := p`'s writes;
`runSeq_frame` is exactly the agreement hypothesis `accesses_runSeq_locality` needs. -/
@[simp, grind .]
theorem accesses_runSeq_isolated {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : Indep (accesses p σ) (accesses q (runSeq p σ).2)) :
    accesses q (runSeq p σ).2 = accesses q σ ∧
    (runSeq q (runSeq p σ).2).1 = (runSeq q σ).1 := by
  have hF : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) := ⟨h.2.1, h.1⟩
  have hagree : ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l := runSeq_frame p σ
  obtain ⟨e1, e2, _⟩ := accesses_runSeq_locality q (runSeq p σ).2 σ (accesses p σ).writes hF hagree
  exact ⟨e1, e2⟩

/-! ### Join-point decomposition of `Reaches` at a `par` node — done

Any real interleaved run out of a `.par p q k` config is, at every point, either still in `par`
form (both branches mid-flight), has passed through the join into `k`'s continuation, or has
crashed. Forced by `step`'s own shape: a `.par p' q' k` config only ever steps to another `.par`
config (via `Conf.inL`/`Conf.inR`, whichever branch moves), to `.wrong` (on a race), or — the one
case that actually leaves `par` form — to `k (a, b)` once *both* sides are already `.pure`. -/
theorem par_dichotomy {α β γ : Type} (p : ParM α) (q : ParM β) (k : α × β → ParM γ)
    (σ : State) (C : Conf γ) (h : Reaches (.run (.par p q k) σ) C) :
    (∃ p' q' σ'', C = .run (.par p' q' k) σ'') ∨
    (∃ a b σ'', Reaches (.run (.par p q k) σ) (.run (k (a, b)) σ'') ∧ Reaches (.run (k (a, b)) σ'') C) ∨
    C = .wrong := by
  induction h with
  | refl => left; exact ⟨p, q, σ, rfl⟩
  | @tail c c' hc hmem ih =>
      rcases ih with ⟨p', q', σ'', heq⟩ | hjoin | hwrong
      · subst heq
        simp only [stepC, step] at hmem
        split at hmem
        · grind
        · split at hmem
          all_goals grind
      all_goals grind

/-- `nextAccs`'s head label(s) are always already accounted for in `accesses` computed at the
*same* state — the "zero-step" case of containment (`docs/decomposition.md`'s still-open
operational-containment piece). Purely structural: no `WellFormed`, no `Reaches`. -/
theorem nextAccs_subset_accesses {τ : Type} (P : ParM τ) (σ : State) :
    ∀ lbl ∈ nextAccs P, (lbl.isWrite = true → lbl.loc ∈ (accesses P σ).writes) ∧
                          (lbl.isWrite = false → lbl.loc ∈ (accesses P σ).reads) := by
  induction P generalizing σ with
  | pure a => simp
  | read l k _ =>
      grind [nextAccs, accesses, Footprint.union, Label.isWrite, Label.loc]
  | write l v k _ =>
      grind [nextAccs, accesses, Footprint.union, Label.isWrite, Label.loc]
  | par p q k ihp ihq _ =>
      grind only [nextAccs, accesses, = List.mem_append, Footprint.union, usr List.append_assoc]

/-- Two programs' *total* footprints being `Indep` (checked against the *same* state) already
rules out their *immediate* next actions conflicting — via `nextAccs_subset_accesses` bounding each
side's head label inside its own total footprint, then reading off Bernstein's conditions directly.
This is the easy half of "`Indep` prevents racing"; the hard, still-open half is that it keeps
preventing racing at *every later* point of a real interleaved execution, not just the first step —
see the `TODO(decomposition)` below. -/
theorem no_race_of_indep {α β : Type} (P : ParM α) (Q : ParM β) (σ : State)
    (hindep : Indep (accesses P σ) (accesses Q σ)) :
    ¬ racing (nextAccs P) (nextAccs Q) = true := by
  intro hrace
  simp only [racing, List.any_eq_true] at hrace
  obtain ⟨a, ha, hexb⟩ := hrace
  obtain ⟨b, hb, hconf⟩ := hexb
  simp only [Label.conflicts, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hconf
  have hA := nextAccs_subset_accesses P σ a ha
  have hB := nextAccs_subset_accesses Q σ b hb
  grind only [= Indep.eq_1, = Disjoint.eq_1]

/-- Peel the first layer off an `Indep` hypothesis stated against a `Footprint.union` — needed
every time a `read`/`write` node's own label is consumed and the proof must continue with `Indep`
for just the continuation's footprint. -/
theorem Indep.right_union {A B C : Footprint} (h : Indep (Footprint.union A B) C) : Indep B C :=
  ⟨fun l hl hc => h.1 l (List.mem_append_right _ hl) hc,
   fun l hl hc => h.2.1 l (List.mem_append_right _ hl) hc,
   fun l hl hb => h.2.2 l hl (List.mem_append_right _ hb)⟩

/-- If `p`'s own accumulated writes never touch a location `q` reads or writes (the piece of
`WellFormed` that constrains `q`), then `q`'s well-formedness transfers between any two states that
agree outside `p`'s footprint. State-level only — no `Reaches` involved. Bridges `WellFormed q σ₁`
(what `WellFormed (par p q k) σ` actually supplies, `σ₁` being `p`'s canonical post-state) and
`WellFormed q σ` (what's needed to invoke `q`'s own `wellFormed_canonical` from the *real* start
state `σ`, where `q`'s real execution genuinely begins). -/
theorem WellFormed_locality {τ : Type} (P : ParM τ) (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accesses P σ)) (hagree : ∀ l ∉ F, σ l = σ' l) :
    WellFormed P σ ↔ WellFormed P σ' := by
  induction P generalizing σ σ' with
  | pure a => simp [WellFormed]
  | read l k ih => grind
  | write l v k ih => grind
  | par p q k ihp ihq ihk =>
      have hFp : FDisjoint F (accesses p σ) := hF.left
      obtain ⟨eacc_p, eval_p, eagree1⟩ := accesses_runSeq_locality p σ σ' F hFp hagree
      have hFq : FDisjoint F (accesses q (runSeq p σ).2) := hF.right.left
      obtain ⟨eacc_q, eval_q, eagree2⟩ :=
        accesses_runSeq_locality q (runSeq p σ).2 (runSeq p σ').2 F hFq eagree1
      have hFk : FDisjoint F (accesses (k ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1))
                    (runSeq q (runSeq p σ).2).2) := hF.right.right
      grind only [WellFormed]

/-- If every real step `p` takes from `σ` avoids racing with `q` (checked against `q` as it stood
at `σ`, since this lemma runs `p` alone and `q` never moves), any real run of `p` lifts, unchanged,
into the `.par p q k` context via `Conf.inL` — "run `p` to completion first" is always a legal
schedule when `p`'s moves don't conflict with `q`. Half of the ← direction's witness schedule; the
other half is `reaches_par_right`. -/
theorem reaches_par_left {α β γ : Type} (p : ParM α) (q : ParM β) (k : α × β → ParM γ) (σ : State)
    (C : Conf α) (h : Reaches (.run p σ) C)
    (hnr : ∀ p'' σ'', Reaches (.run p σ) (.run p'' σ'') → ¬ racing (nextAccs p'') (nextAccs q) = true) :
    (∃ p' σ', C = .run p' σ' ∧ Reaches (.run (.par p q k) σ) (.run (.par p' q k) σ')) ∨ C = .wrong := by
  induction h with
  | refl => left; exact ⟨p, σ, rfl, Reaches.refl⟩
  | @tail c c' hc hmem ih =>
      rcases ih with ⟨p'', σ'', heq, hlift⟩ | hwrong
      · subst heq
        have hnr'' := hnr p'' σ'' hc
        have hstep : c' ∈ step p'' σ'' := hmem
        have hcompound : Conf.inL q k c' ∈ stepC (Conf.run (ParM.par p'' q k) σ'') := by grind
        grind
      · grind

/-- Symmetric to `reaches_par_left`: runs `q` to completion with `p` held fixed. Used with
`p := .pure a` (so `nextAccs p = []` and the non-racing side condition is trivial), lifting `q`'s
completion into the `.par` context after `p` is already done. -/
theorem reaches_par_right {α β γ : Type} (p : ParM α) (q : ParM β) (k : α × β → ParM γ) (σ : State)
    (C : Conf β) (h : Reaches (.run q σ) C)
    (hnr : ∀ q'' σ'', Reaches (.run q σ) (.run q'' σ'') → ¬ racing (nextAccs p) (nextAccs q'') = true) :
    (∃ q' σ', C = .run q' σ' ∧ Reaches (.run (.par p q k) σ) (.run (.par p q' k) σ')) ∨ C = .wrong := by
  induction h with
  | refl => left; exact ⟨q, σ, rfl, Reaches.refl⟩
  | @tail c c' hc hmem ih =>
      rcases ih with ⟨q'', σ'', heq, hlift⟩ | hwrong
      · subst heq
        have hnr'' := hnr q'' σ'' hc
        have hstep : c' ∈ step q'' σ'' := hmem
        have hcompound : Conf.inR p k c' ∈ stepC (Conf.run (ParM.par p q'' k) σ'') := by grind
        grind
      · grind


/-! ### Operational locality and the single-step canonical invariant

The piece that closes the `par` case. Discovered by re-examining *why* the theorem needs
`WellFormed` at all: `step`'s racing check is re-evaluated fresh at every single step (not once at
the top), so a real step that *doesn't* crash is automatically non-racing *at that instant* — no
extra argument needed for that part. What genuinely needs independence is different: when the
*right* branch moves first (before the left), its real starting state is the raw joint state, not
the left-first canonical reference point `σ₁` the whole theorem is stated against — and only
`Indep` guarantees replaying it against `σ₁` gives the same outcome. `step_combined` below is the
single-step version of exactly that fact, proved by induction on the moving program with no
appeal to an arbitrary-depth "general containment" argument — the earlier, harder approach (see
`docs/decomposition.md`'s history) needed containment relative to the *original* top-level
footprint at *every* reachable depth; this needs it for exactly one step at a time, which turns
out to be enough. -/

/-- Operational (step-level) analogue of `accesses_runSeq_locality`: if `σ`, `σ'` agree outside a
footprint-disjoint set `F`, `P` takes "the same" real step from either — same resulting program,
and resulting states that still agree outside `F`. -/
theorem step_locality {τ : Type} (P : ParM τ) (σ σ' : State) (F : List Loc)
    (hwf : WellFormed P σ)
    (hF : FDisjoint F (accesses P σ)) (hagree : ∀ l ∉ F, σ l = σ' l)
    (P3 : ParM τ) (σ3 : State) (hstep : Conf.run P3 σ3 ∈ stepC (Conf.run P σ)) :
    ∃ σ3', Conf.run P3 σ3' ∈ stepC (Conf.run P σ') ∧ (∀ l ∉ F, σ3 l = σ3' l) := by
  induction P generalizing σ σ' σ3 with
  | pure a => simp [stepC, step] at hstep
  | read l k ih =>
      grind
  | write l v k ih =>
      simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
      obtain ⟨hP3, hσ3⟩ := hstep
      have hl : l ∉ F := fun hmem => hF.2 l hmem (by simp [accesses])
      refine ⟨σ'.update l v, ?_, ?_⟩
      · simp only [stepC, step, hP3, List.mem_singleton]
      · intro l' hl'
        rw [hσ3]
        grind
  | par p q k ihp ihq _ =>
      simp only [stepC, step] at hstep
      split at hstep
      · simp at hstep
      · rename_i hnr
        split at hstep
        · grind
        · rename_i hnp
          simp only [List.mem_append, List.mem_map] at hstep
          rcases hstep with ⟨cx, hcx, heq⟩ | ⟨cx, hcx, heq⟩
          · cases cx with
            | run p3 σ3x =>
                simp only [Conf.inL, Conf.run.injEq] at heq
                obtain ⟨hP3, hσ3⟩ := heq
                have hFp : FDisjoint F (accesses p σ) := hF.left
                have hwfp : WellFormed p σ := hwf.2.1
                obtain ⟨σ3', hstep', hag'⟩ := ihp σ σ' hwfp hFp hagree p3 σ3x hcx
                refine ⟨σ3', ?_, ?_⟩
                all_goals grind
            | wrong => simp [Conf.inL] at heq
          · cases cx with
            | run q3 σ3x =>
                simp only [Conf.inR, Conf.run.injEq] at heq
                obtain ⟨hP3, hσ3⟩ := heq
                have hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2) := hwf.1
                have hFq : FDisjoint F (accesses q (runSeq p σ).2) := hF.right.left
                have hwfq1 : WellFormed q (runSeq p σ).2 := hwf.2.2.1
                have hiso := accesses_runSeq_isolated p q σ hindep
                have hFq0 : FDisjoint F (accesses q σ) := hiso.1 ▸ hFq
                have hwfq0 : WellFormed q σ := (WellFormed_locality q (runSeq p σ).2 σ
                  (accesses p σ).writes ⟨hindep.2.1, hindep.1⟩
                  (fun l hl => runSeq_frame p σ l hl)).mp hwfq1
                obtain ⟨σ3', hstep', hag'⟩ := ihq σ σ' hwfq0 hFq0 hagree q3 σ3x hcx
                refine ⟨σ3', ?_, ?_⟩
                all_goals grind
            | wrong => simp [Conf.inR] at heq

/-- Locations outside a real step's own write-footprint are untouched by it — the operational
(single-step) analogue of `runSeq_frame`. -/
theorem step_frame {τ : Type} (P : ParM τ) (σ σ3 : State) (hwf : WellFormed P σ) (P3 : ParM τ)
    (hstep : Conf.run P3 σ3 ∈ stepC (Conf.run P σ)) :
    ∀ l ∉ (accesses P σ).writes, σ l = σ3 l := by
  induction P generalizing σ σ3 with
  | pure a => simp [stepC, step] at hstep
  | read l k _ => grind
  | write l v k ih =>
      simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
      intro l' hl'
      have hl : l ∈ (accesses (ParM.write l v k) σ).writes := by simp [accesses]
      have hne : l' ≠ l := fun h => hl' (h ▸ hl)
      rw [hstep.2, State.update_other σ v hne]
  | par p q k ihp ihq _ =>
      have hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2) := hwf.1
      have hwfq1 : WellFormed q (runSeq p σ).2 := hwf.2.2.1
      have hwfq0 : WellFormed q σ := (WellFormed_locality q (runSeq p σ).2 σ
        (accesses p σ).writes ⟨hindep.2.1, hindep.1⟩
        (fun l hl => runSeq_frame p σ l hl)).mp hwfq1
      simp only [stepC, step] at hstep
      grind



/-- **The single-step canonical invariant.** Under `WellFormed`, one real step never changes the
*canonical outcome* `runSeq` computes, and never lets a fresh location outside the original
footprint leak into `accesses` — no matter which of the two `.par` branches moved, and no matter
how deeply either is itself `.par`-structured. This is proved and used as one combined statement
(not two separate lemmas) because the harder half — the branch that moves *second*, replayed
against its canonical reference state via `step_locality` — needs the footprint half of its own
conclusion, applied one level down through `ihq`, to pin the replayed state down exactly (not just
up to agreement outside some set). Iterating this lemma along a whole `Reaches` chain still needs
`WellFormed` preserved at every step to invoke it again — that remaining piece is `TODO` at the
bottom of this file. -/
theorem step_combined {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
      runSeq P3 σ3 = runSeq P σ ∧
      (∀ F, FDisjoint F (accesses P σ) → FDisjoint F (accesses P3 σ3)) := by
  induction P with
  | pure a => intro σ _ P3 σ3 hstep; simp [stepC, step] at hstep
  | read l k _ =>
      intro σ _ P3 σ3 hstep
      simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨rfl, fun F hF => hF.right⟩
  | write l v k _ =>
      intro σ _ P3 σ3 hstep
      simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨rfl, fun F hF => hF.right⟩
  | par p q k ihp ihq _ =>
      intro σ hwf P3 σ3 hstep
      have hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2) := hwf.1
      have hwfp0 : WellFormed p σ := hwf.2.1
      have hwfq1 : WellFormed q (runSeq p σ).2 := hwf.2.2.1
      have hiso := accesses_runSeq_isolated p q σ hindep
      have hwfq0 : WellFormed q σ := (WellFormed_locality q (runSeq p σ).2 σ
        (accesses p σ).writes ⟨hindep.2.1, hindep.1⟩ (fun l hl => runSeq_frame p σ l hl)).mp hwfq1
      have hindep0 : Indep (accesses p σ) (accesses q σ) := hiso.1 ▸ hindep
      simp only [stepC, step] at hstep
      split at hstep
      · simp at hstep
      · rename_i hnr
        split at hstep
        · grind
        · simp only [List.mem_append, List.mem_map] at hstep
          rcases hstep with ⟨cx, hcx, heq⟩ | ⟨cx, hcx, heq⟩
          · cases cx with
            | run p3 σ3x =>
                simp only [Conf.inL, Conf.run.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                obtain ⟨heqR, hFsub⟩ := ihp σ hwfp0 p3 σ3x hcx
                constructor
                · simp only [runSeq, heqR]
                · intro F hF
                  have hFp3 := hFsub F hF.left
                  grind
            | wrong => simp [Conf.inL] at heq
          · cases cx with
            | run q3 σ3x =>
                simp only [Conf.inR, Conf.run.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                have hFp_q : FDisjoint (accesses q σ).writes (accesses p σ) :=
                  ⟨(Indep.symm hindep0).2.1, (Indep.symm hindep0).1⟩
                have hagree_pq : ∀ l ∉ (accesses q σ).writes, σ l = σ3x l :=
                  step_frame q σ σ3x hwfq0 q3 hcx
                obtain ⟨heqAccP, heqA, agree1⟩ :=
                  accesses_runSeq_locality p σ σ3x (accesses q σ).writes hFp_q hagree_pq
                have hFq_p : FDisjoint (accesses p σ).writes (accesses q σ) :=
                  ⟨hindep0.2.1, hindep0.1⟩
                have hagree_σσ1 : ∀ l ∉ (accesses p σ).writes, σ l = (runSeq p σ).2 l :=
                  fun l hl => (runSeq_frame p σ l hl).symm
                obtain ⟨σ3x', hstep1, hagree2⟩ :=
                  step_locality q σ (runSeq p σ).2 (accesses p σ).writes hwfq0 hFq_p hagree_σσ1
                    q3 σ3x hcx
                obtain ⟨EQ_q_shifted, FSUB_shifted⟩ := ihq (runSeq p σ).2 hwf.2.2.1 q3 σ3x' hstep1
                have hFq1 : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) :=
                  ⟨hwf.1.2.1, hwf.1.1⟩
                have heq_full : σ3x' = (runSeq p σ3x).2 := by
                  funext l
                  by_cases hl : l ∈ (accesses p σ).writes
                  · have h1 : σ3x' l = (runSeq p σ).2 l :=
                      (step_frame q (runSeq p σ).2 σ3x' hwf.2.2.1 q3 hstep1 l
                        (fun hmem => hFq1.2 l hl hmem)).symm
                    have h2 : (runSeq p σ3x).2 l = (runSeq p σ).2 l := by
                      have hl' : l ∉ (accesses q σ).writes := fun hmem => hFq_p.2 l hl hmem
                      exact (agree1 l hl').symm
                    rw [h1, h2]
                  · have h1 : σ3x' l = σ3x l := (hagree2 l hl).symm
                    grind
                have EQ_final : runSeq q3 (runSeq p σ3x).2 = runSeq q (runSeq p σ).2 := by
                  rw [← heq_full]; exact EQ_q_shifted
                constructor
                · show runSeq (k ((runSeq p σ3x).1, (runSeq q3 (runSeq p σ3x).2).1))
                      (runSeq q3 (runSeq p σ3x).2).2 =
                    runSeq (k ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1)) (runSeq q (runSeq p σ).2).2
                  rw [heqA, EQ_final]
                · intro F hF
                  have hFq3 : FDisjoint F (accesses q3 (runSeq p σ3x).2) := by
                    rw [← heq_full]; exact FSUB_shifted F hF.right.left
                  grind
            | wrong => simp [Conf.inR] at heq

/-! ### Preservation — closing the `sorry`

`step_combined` gives the invariant for *one* step; using it again on the *next* step needs
`WellFormed` re-established at that point, which needs `Indep`'s three Bernstein conditions
individually — `step_combined`'s own containment conjunct bundles reads and writes together via
one `FDisjoint`, which isn't fine-grained enough to reconstruct them. `step_subset_rw` is the
finer version (same proof shape as `step_combined`'s footprint half, `.reads`/`.writes` tracked as
separate `List.Subset` facts), and `WellFormed_preserved` is what actually chains: it doesn't
re-derive containment for a compound moved branch from scratch — `ihp`/`ihq` (the *same*
`WellFormed_preserved`, structurally smaller) already give `WellFormed` for that branch directly,
so the only new content per step is checking `Indep` monotonically shrinks via `step_subset_rw`. -/
theorem step_subset_rw {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
      runSeq P3 σ3 = runSeq P σ ∧
      (accesses P3 σ3).reads ⊆ (accesses P σ).reads ∧
      (accesses P3 σ3).writes ⊆ (accesses P σ).writes := by
  induction P with
  | pure a => intro σ _ P3 σ3 hstep; simp [stepC, step] at hstep
  | read l k _ => grind
  | write l v k _ => grind
  | par p q k ihp ihq _ =>
      intro σ hwf P3 σ3 hstep
      have hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2) := hwf.1
      have hwfp0 : WellFormed p σ := hwf.2.1
      have hwfq1 : WellFormed q (runSeq p σ).2 := hwf.2.2.1
      have hiso := accesses_runSeq_isolated p q σ hindep
      have hwfq0 : WellFormed q σ := (WellFormed_locality q (runSeq p σ).2 σ
        (accesses p σ).writes ⟨hindep.2.1, hindep.1⟩ (fun l hl => runSeq_frame p σ l hl)).mp hwfq1
      have hindep0 : Indep (accesses p σ) (accesses q σ) := hiso.1 ▸ hindep
      simp only [stepC, step] at hstep
      split at hstep
      · simp at hstep
      · rename_i hnr
        split at hstep
        · grind
        · simp only [List.mem_append, List.mem_map] at hstep
          rcases hstep with ⟨cx, hcx, heq⟩ | ⟨cx, hcx, heq⟩
          · grind
          · cases cx with
            | run q3 σ3x =>
                simp only [Conf.inR, Conf.run.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                have hFp_q : FDisjoint (accesses q σ).writes (accesses p σ) :=
                  ⟨(Indep.symm hindep0).2.1, (Indep.symm hindep0).1⟩
                have hagree_pq : ∀ l ∉ (accesses q σ).writes, σ l = σ3x l :=
                  step_frame q σ σ3x hwfq0 q3 hcx
                obtain ⟨heqAccP, heqA, agree1⟩ :=
                  accesses_runSeq_locality p σ σ3x (accesses q σ).writes hFp_q hagree_pq
                have hFq_p : FDisjoint (accesses p σ).writes (accesses q σ) :=
                  ⟨hindep0.2.1, hindep0.1⟩
                have hagree_σσ1 : ∀ l ∉ (accesses p σ).writes, σ l = (runSeq p σ).2 l :=
                  fun l hl => (runSeq_frame p σ l hl).symm
                obtain ⟨σ3x', hstep1, hagree2⟩ :=
                  step_locality q σ (runSeq p σ).2 (accesses p σ).writes hwfq0 hFq_p hagree_σσ1
                    q3 σ3x hcx
                have hFq1 : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) :=
                  ⟨hwf.1.2.1, hwf.1.1⟩
                have heq_full : σ3x' = (runSeq p σ3x).2 := by
                  funext l
                  by_cases hl : l ∈ (accesses p σ).writes
                  · have h1 : σ3x' l = (runSeq p σ).2 l :=
                      (step_frame q (runSeq p σ).2 σ3x' hwf.2.2.1 q3 hstep1 l
                        (fun hmem => hFq1.2 l hl hmem)).symm
                    have h2 : (runSeq p σ3x).2 l = (runSeq p σ).2 l := by grind
                    rw [h1, h2]
                  · grind
                grind
            | wrong => simp [Conf.inR] at heq



/-- Disjointness is monotone under shrinking either side — how `step_subset_rw`'s containment
turns into `Indep` for a moved branch. -/
theorem Disjoint.mono_left {a a' b : List Loc} (hsub : a ⊆ a')
    (h : Disjoint a' b) : Disjoint a b :=
  fun l hl hb => h l (hsub hl) hb

theorem Disjoint.mono_right {a b b' : List Loc} (hsub : b ⊆ b')
    (h : Disjoint a b') : Disjoint a b :=
  fun l ha hl => h l ha (hsub hl)

/-- **Subject reduction.** `WellFormed` is preserved by a single real step, no matter which branch
moved or how deep its own structure is. Combined with `step_combined`, this is what lets the
canonical-value invariant survive an entire `Reaches` derivation, not just one step of it. -/
theorem WellFormed_preserved {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) → WellFormed P3 σ3 := by
  induction P with
  | pure a => intro σ _ P3 σ3 hstep; simp [stepC, step] at hstep
  | read l k _ => grind
  | write l v k _ => grind
  | par p q k ihp ihq _ =>
      intro σ hwf P3 σ3 hstep
      have hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2) := hwf.1
      have hwfp0 : WellFormed p σ := hwf.2.1
      have hwfq1 : WellFormed q (runSeq p σ).2 := hwf.2.2.1
      have hwfk : WellFormed (k ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1)) (runSeq q (runSeq p σ).2).2 :=
        hwf.2.2.2
      have hiso := accesses_runSeq_isolated p q σ hindep
      have hwfq0 : WellFormed q σ := (WellFormed_locality q (runSeq p σ).2 σ
        (accesses p σ).writes ⟨hindep.2.1, hindep.1⟩ (fun l hl => runSeq_frame p σ l hl)).mp hwfq1
      have hindep0 : Indep (accesses p σ) (accesses q σ) := hiso.1 ▸ hindep
      simp only [stepC, step] at hstep
      split at hstep
      · simp at hstep
      · rename_i hnr
        split at hstep
        · rename_i a b
          simp only [List.mem_singleton, Conf.run.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          simpa using hwfk
        · simp only [List.mem_append, List.mem_map] at hstep
          rcases hstep with ⟨cx, hcx, heq⟩ | ⟨cx, hcx, heq⟩
          · cases cx with
            | run p3 σ3x =>
                simp only [Conf.inL, Conf.run.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                have hwfp3 := ihp σ hwfp0 p3 σ3x hcx
                obtain ⟨heqR, hsubR, hsubW⟩ := step_subset_rw p σ hwfp0 p3 σ3x hcx
                have hindep3 : Indep (accesses p3 σ3x) (accesses q (runSeq p σ).2) :=
                  ⟨Disjoint.mono_left hsubW hindep.1, Disjoint.mono_left hsubW hindep.2.1,
                   Disjoint.mono_right hsubR hindep.2.2⟩
                show Indep (accesses p3 σ3x) (accesses q (runSeq p3 σ3x).2) ∧ WellFormed p3 σ3x ∧
                    WellFormed q (runSeq p3 σ3x).2 ∧
                    WellFormed (k ((runSeq p3 σ3x).1, (runSeq q (runSeq p3 σ3x).2).1))
                      (runSeq q (runSeq p3 σ3x).2).2
                rw [heqR]
                exact ⟨hindep3, hwfp3, hwfq1, hwfk⟩
            | wrong => simp [Conf.inL] at heq
          · cases cx with
            | run q3 σ3x =>
                simp only [Conf.inR, Conf.run.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                have hFp_q : FDisjoint (accesses q σ).writes (accesses p σ) :=
                  ⟨(Indep.symm hindep0).2.1, (Indep.symm hindep0).1⟩
                have hagree_pq : ∀ l ∉ (accesses q σ).writes, σ l = σ3x l :=
                  step_frame q σ σ3x hwfq0 q3 hcx
                obtain ⟨heqAccP, heqA, agree1⟩ :=
                  accesses_runSeq_locality p σ σ3x (accesses q σ).writes hFp_q hagree_pq
                have hwfpσ3x : WellFormed p σ3x :=
                  (WellFormed_locality p σ σ3x (accesses q σ).writes hFp_q hagree_pq).mp hwfp0
                have hFq_p : FDisjoint (accesses p σ).writes (accesses q σ) :=
                  ⟨hindep0.2.1, hindep0.1⟩
                have hagree_σσ1 : ∀ l ∉ (accesses p σ).writes, σ l = (runSeq p σ).2 l :=
                  fun l hl => (runSeq_frame p σ l hl).symm
                obtain ⟨σ3x', hstep1, hagree2⟩ :=
                  step_locality q σ (runSeq p σ).2 (accesses p σ).writes hwfq0 hFq_p hagree_σσ1
                    q3 σ3x hcx
                have hwfq3 := ihq (runSeq p σ).2 hwf.2.2.1 q3 σ3x' hstep1
                obtain ⟨EQ_q_shifted, hsubR_q, hsubW_q⟩ :=
                  step_subset_rw q (runSeq p σ).2 hwf.2.2.1 q3 σ3x' hstep1
                have hFq1 : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) :=
                  ⟨hwf.1.2.1, hwf.1.1⟩
                have heq_full : σ3x' = (runSeq p σ3x).2 := by
                  funext l
                  by_cases hl : l ∈ (accesses p σ).writes
                  · have h1 : σ3x' l = (runSeq p σ).2 l :=
                      (step_frame q (runSeq p σ).2 σ3x' hwf.2.2.1 q3 hstep1 l
                        (fun hmem => hFq1.2 l hl hmem)).symm
                    have h2 : (runSeq p σ3x).2 l = (runSeq p σ).2 l := by
                      have hl' : l ∉ (accesses q σ).writes := fun hmem => hFq_p.2 l hl hmem
                      exact (agree1 l hl').symm
                    rw [h1, h2]
                  · have h1 : σ3x' l = σ3x l := (hagree2 l hl).symm
                    have h2 : (runSeq p σ3x).2 l = σ3x l := by
                      have hl' : l ∉ (accesses p σ3x).writes := heqAccP ▸ hl
                      exact runSeq_frame p σ3x l hl'
                    rw [h1, h2]
                grind
            | wrong => simp [Conf.inR] at heq


/-- `step_combined` + `WellFormed_preserved`, iterated along a whole `Reaches` chain: any real,
non-crashing execution reaches a config whose canonical value matches the start's — the uniqueness
direction of `wellFormed_canonical`, in general (not yet restricted to a `.pure` endpoint). -/
theorem runSeq_invariant_chain {τ : Type} (P : ParM τ) (σ : State) (hwf : WellFormed P σ)
    (C : Conf τ) (h : Reaches (.run P σ) C) :
    ∀ P' σ', C = .run P' σ' → WellFormed P' σ' ∧ runSeq P' σ' = runSeq P σ := by
  induction h with
  | refl => grind
  | @tail c c' hc hmem ih =>
      intro P' σ' heq
      subst heq
      cases c with
      | run P'' σ'' =>
          obtain ⟨hwf'', heqR''⟩ := ih P'' σ'' rfl
          have hwf3 := WellFormed_preserved P'' σ'' hwf'' P' σ' hmem
          obtain ⟨heqR3, _, _⟩ := step_subset_rw P'' σ'' hwf'' P' σ' hmem
          exact ⟨hwf3, heqR3.trans heqR''⟩
      | wrong => simp only [stepC, List.not_mem_nil] at hmem


/-- `step_subset_rw` iterated along a whole chain: everything a real execution touches, however
many steps in, is still bounded by the *original* footprint. This is what lets `reaches_par_left`/
`reaches_par_right`'s non-racing side condition be discharged for the ← direction's witness
schedule, for a branch of *any* nesting depth — no separate "general containment" development
needed, since it falls out of the already-proved one-step facts plus this chaining. -/
theorem subset_chain {τ : Type} (P : ParM τ) (σ : State) (hwf : WellFormed P σ)
    (C : Conf τ) (h : Reaches (.run P σ) C) :
    ∀ P' σ', C = .run P' σ' →
      (accesses P' σ').reads ⊆ (accesses P σ).reads ∧ (accesses P' σ').writes ⊆ (accesses P σ).writes := by
  induction h with
  | refl => grind
  | @tail c c' hc hmem ih =>
      intro P' σ' heq
      subst heq
      cases c with
      | run P'' σ'' =>
          have hwf'' := (runSeq_invariant_chain P σ hwf (.run P'' σ'') hc P'' σ'' rfl).1
          obtain ⟨hsubR'', hsubW''⟩ := ih P'' σ'' rfl
          obtain ⟨_, hsubR3, hsubW3⟩ := step_subset_rw P'' σ'' hwf'' P' σ' hmem
          exact ⟨fun l h => hsubR'' (hsubR3 h), fun l h => hsubW'' (hsubW3 h)⟩
      | wrong => simp only [stepC, List.not_mem_nil] at hmem

/-- `no_race_of_indep`, generalized: the containment facts it needs (labels land inside a
footprint) supplied as explicit hypotheses instead of derived internally via
`nextAccs_subset_accesses` at a fixed state — needed once labels are bounded by an *original*
footprint several steps back (`subset_chain`) rather than their own current one. -/
theorem no_race_contained (labP labQ : List Label) (fP fQ : Footprint)
    (hindep : Indep fP fQ)
    (hP : ∀ lbl ∈ labP, (lbl.isWrite = true → lbl.loc ∈ fP.writes) ∧ (lbl.isWrite = false → lbl.loc ∈ fP.reads))
    (hQ : ∀ lbl ∈ labQ, (lbl.isWrite = true → lbl.loc ∈ fQ.writes) ∧ (lbl.isWrite = false → lbl.loc ∈ fQ.reads)) :
    ¬ racing labP labQ = true := by
  grind only [= Indep.eq_1, = racing.eq_1, = Disjoint.eq_1, = List.any_eq, = Label.conflicts.eq_1]

/-! ### The canonical-outcome theorem -/

theorem wellFormed_canonical {τ : Type} (p : ParM τ) :
    ∀ σ r σ', WellFormed p σ → (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ) := by
  induction p with
  | pure a =>
      intro σ r σ' _
      constructor
      · intro h
        have h2 := Reaches.terminal (c := Conf.run (ParM.pure a) σ) rfl h
        simp_all
      · grind [Reaches]
  | read l k ih =>
      intro σ r σ' hwf
      have hstep : stepC (Conf.run (ParM.read l k) σ) = [Conf.run (k (σ l)) σ] := rfl
      constructor
      · grind [Reaches.single_step]
      · intro h
        refine Reaches.trans ?_ ((ih (σ l) σ r σ' hwf).mpr h)
        exact Reaches.tail Reaches.refl (by rw [hstep]; exact List.mem_singleton_self _)
  | write l v k ih =>
      intro σ r σ' hwf
      have hstep : stepC (Conf.run (ParM.write l v k) σ) = [Conf.run (k ()) (σ.update l v)] := rfl
      constructor
      · grind [Reaches.single_step]
      · intro h
        refine Reaches.trans ?_ ((ih () (σ.update l v) r σ' hwf).mpr h)
        exact Reaches.tail Reaches.refl (by rw [hstep]; exact List.mem_singleton_self _)
  | par p q k ihp ihq ihk =>
      intro σ r σ' hwf
      obtain ⟨hindep, hwfp0, hwfq1, hwfk⟩ := hwf
      constructor
      · intro h
        obtain ⟨_, heqR⟩ := runSeq_invariant_chain (p.par q k) σ ⟨hindep, hwfp0, hwfq1, hwfk⟩
          (.run (ParM.pure r) σ') h (ParM.pure r) σ' rfl
        have hru : runSeq (ParM.pure r) σ' = (r, σ') := rfl
        rw [← hru]
        exact heqR
      · intro heq
        have hRp : Reaches (.run p σ) (.run (ParM.pure (runSeq p σ).1) (runSeq p σ).2) :=
          (ihp σ (runSeq p σ).1 (runSeq p σ).2 hwfp0).mpr rfl
        generalize ha_def : (runSeq p σ).1 = a at hRp heq hindep hwfp0 hwfq1 hwfk ⊢
        generalize hσ1_def : (runSeq p σ).2 = σ1 at hRp heq hindep hwfq1 hwfk ⊢
        generalize hb_def : (runSeq q σ1).1 = b at heq hwfk ⊢
        generalize hσ2_def : (runSeq q σ1).2 = σ2 at heq hwfk ⊢
        have hnr1 : ∀ p'' σ'', Reaches (.run p σ) (.run p'' σ'') →
            ¬ racing (nextAccs p'') (nextAccs q) = true := by
          intro p'' σ'' hR
          have hcontP := subset_chain p σ hwfp0 (.run p'' σ'') hR p'' σ'' rfl
          have hcP : ∀ lbl ∈ nextAccs p'', (lbl.isWrite = true → lbl.loc ∈ (accesses p σ).writes) ∧
              (lbl.isWrite = false → lbl.loc ∈ (accesses p σ).reads) := by
            intro lbl hlbl
            have h0 := nextAccs_subset_accesses p'' σ'' lbl hlbl
            exact ⟨fun hw => hcontP.2 (h0.1 hw), fun hr => hcontP.1 (h0.2 hr)⟩
          exact no_race_contained (nextAccs p'') (nextAccs q) (accesses p σ) (accesses q σ1)
            hindep hcP (nextAccs_subset_accesses q σ1)
        rcases reaches_par_left p q k σ (.run (ParM.pure a) σ1) hRp hnr1 with
          ⟨p', σ'', heq1, hR1⟩ | hcontra
        case inr => simp at hcontra
        simp only [Conf.run.injEq] at heq1
        obtain ⟨rfl, rfl⟩ := heq1
        have hRq : Reaches (.run q σ1) (.run (ParM.pure b) σ2) :=
          (ihq σ1 b σ2 hwfq1).mpr (by rw [← hb_def, ← hσ2_def])
        have hnr2 : ∀ q'' σ'', Reaches (.run q σ1) (.run q'' σ'') →
            ¬ racing (nextAccs (ParM.pure a)) (nextAccs q'') = true := by
          intro q'' σ'' _
          simp [nextAccs, racing]
        rcases reaches_par_right (ParM.pure a) q k σ1 (.run (ParM.pure b) σ2) hRq hnr2 with
          ⟨q', σ3, heq2, hR2⟩ | hcontra2
        case inr => simp at hcontra2
        simp only [Conf.run.injEq] at heq2
        obtain ⟨rfl, rfl⟩ := heq2
        have hRfull : Reaches (.run (p.par q k) σ) (.run ((ParM.pure a).par (ParM.pure b) k) σ2) :=
          hR1.trans hR2
        have hstepJoin : Conf.run (k (a, b)) σ2 ∈
            stepC (Conf.run ((ParM.pure a).par (ParM.pure b) k) σ2) := by
          simp [stepC, step]
        have hRjoin : Reaches (.run (p.par q k) σ) (.run (k (a, b)) σ2) :=
          hRfull.tail hstepJoin
        refine Reaches.trans hRjoin ((ihk (a, b) σ2 r σ' hwfk).mpr ?_)
        grind only [= runSeq.eq_4]

end Paralever
