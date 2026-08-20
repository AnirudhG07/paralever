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
@[simp, grind .]
theorem runSeq_frame {τ : Type} (p : ParM τ) (σ : State) :
    ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l := by
  induction p generalizing σ with
  | pure a => intro l _; rfl
  | read l' k ih => grind
  | write l' v k ih =>  grind
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
      · grind[Reaches.single_step]
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
