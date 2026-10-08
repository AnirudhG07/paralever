import Paralever.Theory.Decomposition

/-! # `wellFormed_canonical` — the sequentialization theorem's hard case

Dedicated file: every lemma here exists to support this one theorem's `par` case, Brookes'
Parallel Decomposition Lemma (CONCUR'04 §5–7) mechanized via Vafeiadis' operational style
(MFPS'11). Nothing here is reused elsewhere in the project — general facts about `runSeq`/
`WellFormed` through `bind` live in `Theory/Decomposition.lean` instead.

-/


namespace Paralever

/-! ### Locality of `accesses`/`runSeq` -/

/-- Locations `p` doesn't write are untouched by its canonical run — the frame property for the
reference execution, and the base fact `accesses_runSeq_locality` builds on. -/
theorem runSeq_frame_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ l,
       l ∉ (accessesChilds cs σ).writes → (runChilds cs σ).2 l = σ l) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ l _; rfl
  · intro α l' k ih σ l hl; grind
  · intro α l' v k ih σ l hl; grind
  · intro β αs cs k ih2 ihk σ l hl
    -- the fork writes nothing outside the children's writes, then the continuation's
    simp only [accesses, Footprint.union, List.mem_append, not_or] at hl
    exact (ihk _ (runChilds cs σ).2 l hl.2).trans (ih2 σ l hl.1)
  · intro σ l _; rfl
  · -- **the 2-to-N step**: `l` is outside the head's writes and outside the tail's, so neither
    -- touches it, and the tail starts from a state that already agrees with `σ` at `l`
    intro α αs p ps ihp ihps σ l hl
    simp only [accessesChilds, Footprint.union, List.mem_append, not_or] at hl
    exact (ihps (runSeq p σ).2 l hl.2).trans (ihp σ l hl.1)

@[simp, grind .]
theorem runSeq_frame {τ : Type} (p : ParM τ) (σ : State) :
    ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l :=
  runSeq_frame_all.1 p σ

@[simp, grind .]
theorem runChilds_frame {αs : List Type} (cs : Childs ParM αs) (σ : State) :
    ∀ l, l ∉ (accessesChilds cs σ).writes → (runChilds cs σ).2 l = σ l :=
  runSeq_frame_all.2 cs σ

/-- `F` shares no location with anything `f` touches. Stated as reads and writes disjoint from `F`
*separately* rather than as one `Disjoint F (reads ++ writes)`: `Footprint.union` interleaves all the
reads and then all the writes, so the combined form does not project through a nested union without
fragile `Or`-shuffling, while this one projects in a line each way (`.left`/`.right`).
-- ref: `docs/decomposition.md` -/
@[simp, grind .]
def FDisjoint (F : List Loc) (f : Footprint) : Prop := Disjoint F f.reads ∧ Disjoint F f.writes

/-- Project a union's disjointness onto its left summand. -/
theorem FDisjoint.left {F : List Loc} {a b : Footprint} (h : FDisjoint F (Footprint.union a b)) :
    FDisjoint F a :=
  ⟨fun l hl hmem => h.1 l hl (by simp [Footprint.union, hmem]),
   fun l hl hmem => h.2 l hl (by simp [Footprint.union, hmem])⟩

/-- Project a union's disjointness onto its right summand; chain `.right.left` to reach the middle
component of `accesses`'s three-way `par` union. -/
theorem FDisjoint.right {F : List Loc} {a b : Footprint} (h : FDisjoint F (Footprint.union a b)) :
    FDisjoint F b :=
  ⟨fun l hl hmem => h.1 l hl (by simp [Footprint.union, hmem]),
   fun l hl hmem => h.2 l hl (by simp [Footprint.union, hmem])⟩

/-- Build disjointness from a union's two halves — the converse of `.left`/`.right`. -/
theorem FDisjoint.union_of {F : List Loc} {a b : Footprint}
    (ha : FDisjoint F a) (hb : FDisjoint F b) : FDisjoint F (Footprint.union a b) := by
  refine ⟨?_, ?_⟩
  · intro l hl hmem
    rcases List.mem_append.mp hmem with h | h
    · exact ha.1 l hl h
    · exact hb.1 l hl h
  · intro l hl hmem
    rcases List.mem_append.mp hmem with h | h
    · exact ha.2 l hl h
    · exact hb.2 l hl h

/-- **A program cannot tell apart two states that differ only where it never looks.** If `σ` and `σ'`
agree outside a set `F` that `p`'s footprint avoids, then `p`'s canonical run from the two agrees in
value, in footprint, and on every location outside `F`.

Piece 1 of the decomposition proof, and the reason it works at all: it lets a branch's behaviour
mid-interleaving (from whatever state has been reached so far) be identified with its behaviour under
`accesses`'s reference convention (from a different but `F`-agreeing state), taking `F` to be the
other branch's writes. -/
theorem accesses_runSeq_locality_all :
    (∀ {τ : Type} (p : ParM τ), ∀ (σ σ' : State) (F : List Loc),
        FDisjoint F (accesses p σ) → (∀ l, l ∉ F → σ l = σ' l) →
        accesses p σ = accesses p σ' ∧ (runSeq p σ).1 = (runSeq p σ').1 ∧
        ∀ l, l ∉ F → (runSeq p σ).2 l = (runSeq p σ').2 l) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ (σ σ' : State) (F : List Loc),
        FDisjoint F (accessesChilds cs σ) → (∀ l, l ∉ F → σ l = σ' l) →
        accessesChilds cs σ = accessesChilds cs σ' ∧ (runChilds cs σ).1 = (runChilds cs σ').1 ∧
        ∀ l, l ∉ F → (runChilds cs σ).2 l = (runChilds cs σ').2 l) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ σ' F _ hagree; exact ⟨rfl, rfl, fun l hl => hagree l hl⟩
  · intro α l k ih σ σ' F hF hagree
    have hl : l ∉ F := fun hmem => hF.1 l hmem (by simp [accesses, Footprint.union])
    have hv : σ l = σ' l := hagree l hl
    have hFk : FDisjoint F (accesses (k (σ l)) σ) :=
      ⟨fun x hx hmem => hF.1 x hx (by simp [accesses, Footprint.union, hmem]),
       fun x hx hmem => hF.2 x hx (by simp [accesses, Footprint.union, hmem])⟩
    obtain ⟨e1, e2, e3⟩ := ih (σ l) σ σ' F hFk hagree
    refine ⟨?_, ?_, ?_⟩
    · show Footprint.union _ _ = Footprint.union _ _
      rw [← hv, e1]
    · show (runSeq (k (σ l)) σ).1 = (runSeq (k (σ' l)) σ').1
      rw [← hv]; exact e2
    · intro x hx
      show (runSeq (k (σ l)) σ).2 x = (runSeq (k (σ' l)) σ').2 x
      rw [← hv]; exact e3 x hx
  · intro α l v k ih σ σ' F hF hagree
    have hFk : FDisjoint F (accesses (k ()) (σ.update l v)) :=
      ⟨fun x hx hmem => hF.1 x hx (by simp [accesses, Footprint.union, hmem]),
       fun x hx hmem => hF.2 x hx (by simp [accesses, Footprint.union, hmem])⟩
    have hagree' : ∀ x, x ∉ F → (σ.update l v) x = (σ'.update l v) x := by
      intro x hx
      by_cases hxl : x = l
      · subst hxl; simp [State.update]
      · simpa [State.update, hxl] using hagree x hx
    obtain ⟨e1, e2, e3⟩ := ih () (σ.update l v) (σ'.update l v) F hFk hagree'
    refine ⟨?_, e2, e3⟩
    show Footprint.union _ _ = Footprint.union _ _
    rw [e1]
  · -- a fork: the children as a block, then the continuation from where they left off
    intro β αs cs k ih2 ihk σ σ' F hF hagree
    have hFcs : FDisjoint F (accessesChilds cs σ) := hF.left
    obtain ⟨e1, e2, e3⟩ := ih2 σ σ' F hFcs hagree
    have hFk : FDisjoint F (accesses (k (runChilds cs σ).1) (runChilds cs σ).2) := hF.right
    obtain ⟨f1, f2, f3⟩ := ihk (runChilds cs σ).1 (runChilds cs σ).2 (runChilds cs σ').2 F hFk e3
    refine ⟨?_, ?_, ?_⟩
    · show Footprint.union _ _ = Footprint.union _ _
      rw [e1, e2] at *; rw [e1]; congr 1
    · show (runSeq (k (runChilds cs σ).1) _).1 = (runSeq (k (runChilds cs σ').1) _).1
      rw [← e2]; exact f2
    · intro l hl
      show (runSeq (k (runChilds cs σ).1) _).2 l = (runSeq (k (runChilds cs σ').1) _).2 l
      rw [← e2]; exact f3 l hl
  · intro σ σ' F _ hagree; exact ⟨rfl, rfl, fun l hl => hagree l hl⟩
  · -- **the 2-to-N step**: the head is local by its own IH, and the tail is local from the state
    -- the head left — which the head's own locality says still agrees outside `F`
    intro α αs p ps ihp ihps σ σ' F hF hagree
    have hFp : FDisjoint F (accesses p σ) := hF.left
    obtain ⟨e1, e2, e3⟩ := ihp σ σ' F hFp hagree
    have hFps : FDisjoint F (accessesChilds ps (runSeq p σ).2) := hF.right
    obtain ⟨f1, f2, f3⟩ := ihps (runSeq p σ).2 (runSeq p σ').2 F hFps e3
    refine ⟨?_, ?_, ?_⟩
    · show Footprint.union _ _ = Footprint.union _ _; rw [e1, f1]
    · show ((runSeq p σ).1, _) = ((runSeq p σ').1, _); rw [e2, f2]
    · exact f3

theorem accesses_runSeq_locality {τ : Type} (p : ParM τ) (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accesses p σ)) (hagree : ∀ l, l ∉ F → σ l = σ' l) :
    accesses p σ = accesses p σ' ∧ (runSeq p σ).1 = (runSeq p σ').1 ∧
    ∀ l, l ∉ F → (runSeq p σ).2 l = (runSeq p σ').2 l :=
  accesses_runSeq_locality_all.1 p σ σ' F hF hagree

theorem accessesChilds_runChilds_locality {αs : List Type} (cs : Childs ParM αs)
    (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accessesChilds cs σ)) (hagree : ∀ l, l ∉ F → σ l = σ' l) :
    accessesChilds cs σ = accessesChilds cs σ' ∧ (runChilds cs σ).1 = (runChilds cs σ').1 ∧
    ∀ l, l ∉ F → (runChilds cs σ).2 l = (runChilds cs σ').2 l :=
  accesses_runSeq_locality_all.2 cs σ σ' F hF hagree

/-- **Under `Indep`, `accesses`'s asymmetry disappears.** `q`'s footprint and result measured from
`σ₁ := (runSeq p σ).2` — the post-`p` state `accesses` conventionally uses for the right branch —
coincide with those measured from the original `σ`. So an independent `q` really is computed in
isolation, which is Brookes' `σ₁ ∗ σ₂` splitting.

A corollary of `accesses_runSeq_locality` at `F := p`'s writes: `Indep`'s two write-disjointness
clauses are exactly the `FDisjoint` hypothesis there, and `runSeq_frame` is exactly the agreement
hypothesis. -- ref: `docs/access.md` -/
@[simp, grind .]
theorem accesses_runSeq_isolated {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : Indep (accesses p σ) (accesses q (runSeq p σ).2)) :
    accesses q (runSeq p σ).2 = accesses q σ ∧
    (runSeq q (runSeq p σ).2).1 = (runSeq q σ).1 := by
  have hF : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) := ⟨h.2.1, h.1⟩
  have hagree : ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l := runSeq_frame p σ
  obtain ⟨e1, e2, _⟩ := accesses_runSeq_locality q (runSeq p σ).2 σ (accesses p σ).writes hF hagree
  exact ⟨e1, e2⟩

/-! ### Join-point decomposition of `Reaches` at a `par` node

Piece 2 of the proof. Forced by `step`'s own shape: a `.par cs k` config only ever steps to another
`.par` config (some one child moved, via `stepChilds`), to `.wrong` on a race, or — the one case that
leaves `par` form — to `k vs` once *every* child is already `.pure`. -/

/-- **A run out of a `.par` node is always in one of three states**: still a `.par` node with its
children mid-flight, already past the join and inside `k`'s continuation, or crashed to `wrong`.

This pins down *that* a join happens and that nothing else can; which results `vs` and heap `σ''` the
join lands on is `step_combined`'s business, not this lemma's. The N-ary shape costs nothing here:
`stepChilds` returns one entry per child, so "a child moved" is a single case however many there
are. -/
theorem par_dichotomy {β : Type} {αs : List Type} (cs : Childs ParM αs)
    (k : Results αs → ParM β) (σ : State) (C : Conf β)
    (h : Reaches (.run (.par cs k) σ) C) :
    (∃ (cs' : Childs ParM αs) (σ'' : State), C = .run (.par cs' k) σ'') ∨
    (∃ vs σ'', Reaches (.run (.par cs k) σ) (.run (k vs) σ'') ∧
               Reaches (.run (k vs) σ'') C) ∨
    C = .wrong := by
  induction h with
  | refl => left; exact ⟨cs, σ, rfl⟩
  | @tail c c' hc hmem ih =>
      rcases ih with ⟨cs', σ'', heq⟩ | hjoin | hwrong
      · subst heq
        simp only [stepC, step] at hmem
        split at hmem
        · -- a race fired
          simp at hmem
          right; right; exact hmem
        · split at hmem
          · -- every child is `pure`: this step is the join
            rename_i vs _
            simp at hmem
            right; left
            refine ⟨vs, σ'', ?_, ?_⟩
            · exact hc.tail (by simp only [stepC, step]; simp_all)
            · rw [hmem]; exact Reaches.refl
          · -- some one child moved; still a `par` node, unless that child aborted
            simp only [List.mem_map] at hmem
            obtain ⟨r, _, hr⟩ := hmem
            cases r with
            | some x => left; exact ⟨x.1, x.2, hr.symm⟩
            | none => right; right; exact hr.symm
      · rcases hjoin with ⟨vs, σ'', hreach, hrest⟩
        right; left; exact ⟨vs, σ'', hreach, hrest.tail hmem⟩
      · subst hwrong; simp at hmem

/-- A program's *immediate* next labels are already inside its own total footprint, at the same
state — a read label's location among the reads, a write label's among the writes. Purely
structural: no `WellFormed`, no `Reaches`, no independence. -/
theorem nextAccs_subset_accesses_all :
    (∀ {τ : Type} (P : ParM τ), ∀ σ, ∀ lbl ∈ nextAccs P,
        (lbl.isWrite = true → lbl.loc ∈ (accesses P σ).writes) ∧
        (lbl.isWrite = false → lbl.loc ∈ (accesses P σ).reads)) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, ∀ lbl ∈ (nextAccsChilds cs).flatten,
        (lbl.isWrite = true → lbl.loc ∈ (accessesChilds cs σ).writes) ∧
        (lbl.isWrite = false → lbl.loc ∈ (accessesChilds cs σ).reads)) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ; simp
  · intro α l k _ σ; grind [nextAccs, accesses, Footprint.union, Label.isWrite, Label.loc]
  · intro α l v k _ σ; grind [nextAccs, accesses, Footprint.union, Label.isWrite, Label.loc]
  · -- a fork's ready labels are exactly its children's, so the children's bound is the fork's
    intro β αs cs k ih2 _ σ lbl hlbl
    have := ih2 σ lbl (by simpa [nextAccs] using hlbl)
    grind only [accesses, Footprint.union, = List.mem_append]
  · intro σ lbl hlbl; simp [nextAccsChilds] at hlbl
  · -- **the 2-to-N step**: a ready label belongs to the head or to one of the rest; either way it
    -- lands in that side's footprint, and the union keeps it
    intro α αs p ps ihp ihps σ lbl hlbl
    simp only [nextAccsChilds, List.flatten_cons, List.mem_append] at hlbl
    rcases hlbl with hhd | htl
    · have := ihp σ lbl hhd
      grind only [accessesChilds, Footprint.union, = List.mem_append]
    · have := ihps (runSeq p σ).2 lbl htl
      grind only [accessesChilds, Footprint.union, = List.mem_append]

theorem nextAccs_subset_accesses {τ : Type} (P : ParM τ) (σ : State) :
    ∀ lbl ∈ nextAccs P, (lbl.isWrite = true → lbl.loc ∈ (accesses P σ).writes) ∧
                          (lbl.isWrite = false → lbl.loc ∈ (accesses P σ).reads) :=
  nextAccs_subset_accesses_all.1 P σ

theorem nextAccsChilds_subset_accessesChilds {αs : List Type} (cs : Childs ParM αs) (σ : State) :
    ∀ lbl ∈ (nextAccsChilds cs).flatten,
      (lbl.isWrite = true → lbl.loc ∈ (accessesChilds cs σ).writes) ∧
      (lbl.isWrite = false → lbl.loc ∈ (accessesChilds cs σ).reads) :=
  nextAccs_subset_accesses_all.2 cs σ

/-- **Independent footprints cannot race on the first step.** `Indep` on the two total footprints,
both measured at the same state, already rules out `P`'s and `Q`'s immediate next actions
conflicting — bound each head label inside its own footprint with `nextAccs_subset_accesses`, then
read Bernstein's conditions off directly.

Only the first step. Keeping it true at every *later* point of a real interleaving is what
`subset_chain` plus `no_race_contained` supply. -/
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

/-- Drop the left summand of an `Indep` stated against a `Footprint.union`. Used every time a
`read`/`write` node's own label has been consumed and the proof must carry on with independence for
the continuation's footprint alone. -/
theorem Indep.right_union {A B C : Footprint} (h : Indep (Footprint.union A B) C) : Indep B C :=
  ⟨fun l hl hc => h.1 l (List.mem_append_right _ hl) hc,
   fun l hl hc => h.2.1 l (List.mem_append_right _ hl) hc,
   fun l hl hb => h.2.2 l hl (List.mem_append_right _ hb)⟩

/-- Each child's own footprint is unchanged between two states agreeing outside `F`. Induction on the
children list; the step is `accesses_runSeq_locality` for the head, feeding its own agreement
conclusion to the tail. -/
theorem childFootprints_locality {αs : List Type} (cs : Childs ParM αs) :
    ∀ (σ σ' : State) (F : List Loc),
      FDisjoint F (accessesChilds cs σ) → (∀ l ∉ F, σ l = σ' l) →
      childFootprints cs σ = childFootprints cs σ' := by
  induction cs with
  | nil => intro σ σ' F _ _; rfl
  | cons p ps ih =>
      intro σ σ' F hF hagree
      have hFp : FDisjoint F (accesses p σ) := hF.left
      obtain ⟨e1, _, eagree⟩ := accesses_runSeq_locality p σ σ' F hFp hagree
      have hFps : FDisjoint F (accessesChilds ps (runSeq p σ).2) := hF.right
      simp only [childFootprints]
      rw [e1, ih (runSeq p σ).2 (runSeq p σ').2 F hFps eagree]

/-- **Well-formedness is itself local**: it transfers between any two states that agree outside a set
`F` disjoint from `P`'s footprint. The `WellFormed` analogue of `accesses_runSeq_locality`,
state-level only — no `Reaches` involved.

Its job in the `par` case is to bridge `WellFormedChilds cs σ₁` (what `WellFormed (par cs k) σ`
supplies, `σ₁` being the previous child's canonical post-state) and the same at `σ`, which is what a
lemma about a child's *real* execution needs, since that execution starts at `σ`. -/
theorem WellFormed_locality_all :
    (∀ {τ : Type} (P : ParM τ), ∀ (σ σ' : State) (F : List Loc),
        FDisjoint F (accesses P σ) → (∀ l ∉ F, σ l = σ' l) →
        (WellFormed P σ ↔ WellFormed P σ')) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ (σ σ' : State) (F : List Loc),
        FDisjoint F (accessesChilds cs σ) → (∀ l ∉ F, σ l = σ' l) →
        (WellFormedChilds cs σ ↔ WellFormedChilds cs σ')) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ σ' F _ _; simp [WellFormed]
  · intro α l k ih σ σ' F hF hagree
    have hl : l ∉ F := fun hmem => hF.1 l hmem (by simp [accesses, Footprint.union])
    have hv : σ l = σ' l := hagree l hl
    have hFk : FDisjoint F (accesses (k (σ l)) σ) :=
      ⟨fun x hx hmem => hF.1 x hx (by simp [accesses, Footprint.union, hmem]),
       fun x hx hmem => hF.2 x hx (by simp [accesses, Footprint.union, hmem])⟩
    show WellFormed (k (σ l)) σ ↔ WellFormed (k (σ' l)) σ'
    rw [← hv]
    exact ih (σ l) σ σ' F hFk hagree
  · intro α l v k ih σ σ' F hF hagree
    have hFk : FDisjoint F (accesses (k ()) (σ.update l v)) :=
      ⟨fun x hx hmem => hF.1 x hx (by simp [accesses, Footprint.union, hmem]),
       fun x hx hmem => hF.2 x hx (by simp [accesses, Footprint.union, hmem])⟩
    have hagree' : ∀ x ∉ F, (σ.update l v) x = (σ'.update l v) x := by
      intro x hx
      by_cases hxl : x = l
      · subst hxl; simp [State.update]
      · simpa [State.update, hxl] using hagree x hx
    exact ih () (σ.update l v) (σ'.update l v) F hFk hagree'
  · -- a fork: `IndepAll` is stated over `childFootprints`, which locality says is the same from
    -- either state, so only the children and the continuation need transporting
    intro β αs cs k ih2 ihk σ σ' F hF hagree
    have hFcs : FDisjoint F (accessesChilds cs σ) := hF.left
    obtain ⟨eacc, eval, eagree⟩ := accessesChilds_runChilds_locality cs σ σ' F hFcs hagree
    have hFk : FDisjoint F (accesses (k (runChilds cs σ).1) (runChilds cs σ).2) := hF.right
    have hchild := ih2 σ σ' F hFcs hagree
    have hcont := ihk (runChilds cs σ).1 (runChilds cs σ).2 (runChilds cs σ').2 F hFk eagree
    have hfp : childFootprints cs σ = childFootprints cs σ' :=
      childFootprints_locality cs σ σ' F hFcs hagree
    rw [WellFormed, WellFormed, hfp, ← eval]
    exact and_congr Iff.rfl (and_congr hchild hcont)
  · intro σ σ' F _ _; simp [WellFormedChilds]
  · -- **the 2-to-N step**: the head transfers by its own IH, and the tail transfers from the state
    -- the head left, which locality says still agrees outside `F`
    intro α αs p ps ihp ihps σ σ' F hF hagree
    have hFp : FDisjoint F (accesses p σ) := hF.left
    obtain ⟨_, _, eagree⟩ := accesses_runSeq_locality p σ σ' F hFp hagree
    have hFps : FDisjoint F (accessesChilds ps (runSeq p σ).2) := hF.right
    exact and_congr (ihp σ σ' F hFp hagree)
      (ihps (runSeq p σ).2 (runSeq p σ').2 F hFps eagree)

theorem WellFormed_locality {τ : Type} (P : ParM τ) (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accesses P σ)) (hagree : ∀ l ∉ F, σ l = σ' l) :
    WellFormed P σ ↔ WellFormed P σ' :=
  WellFormed_locality_all.1 P σ σ' F hF hagree

theorem WellFormedChilds_locality {αs : List Type} (cs : Childs ParM αs) (σ σ' : State)
    (F : List Loc) (hF : FDisjoint F (accessesChilds cs σ)) (hagree : ∀ l ∉ F, σ l = σ' l) :
    WellFormedChilds cs σ ↔ WellFormedChilds cs σ' :=
  WellFormed_locality_all.2 cs σ σ' F hF hagree

/-! ### Lifting a child's run into the fork

What replaces the old `reaches_par_left`/`reaches_par_right` pair. With N children there is no left
and right, so the two become three: lift a run of the head, lift a run of the tail, and lift any
children-level run into `Reaches` on the fork. Head and tail are exactly the 2-to-N structure. -/

/-- **A run of the head child lifts into the fork**, the other children standing still. -/
theorem reachesChilds_head {α : Type} {αs : List Type} (p : ParM α) (ps : Childs ParM αs)
    (σ : State) (C : Conf α) (h : Reaches (.run p σ) C) :
    (∃ p' σ', C = .run p' σ' ∧ ReachesChilds (.cons p ps) σ (.cons p' ps) σ') ∨ C = .wrong := by
  induction h with
  | refl => left; exact ⟨p, σ, rfl, ReachesChilds.refl⟩
  | @tail c c' hc hmem ih =>
      rcases ih with ⟨p'', σ'', heq, hlift⟩ | hwrong
      · subst heq
        cases c' with
        | wrong => right; rfl
        | run p₃ σ₃ =>
            left
            refine ⟨p₃, σ₃, rfl, hlift.tail ?_⟩
            simp only [stepChilds, List.mem_append, List.mem_map]
            exact Or.inl ⟨.run p₃ σ₃, hmem, rfl⟩
      · subst hwrong; simp at hmem

/-- **A run of the tail lifts into the fork**, the head standing still. The other half of the
2-to-N step. -/
theorem reachesChilds_tail {α : Type} {αs : List Type} (p : ParM α) {ps ps' : Childs ParM αs}
    {σ σ' : State} (h : ReachesChilds ps σ ps' σ') :
    ReachesChilds (.cons p ps) σ (.cons p ps') σ' := by
  induction h with
  | refl => exact ReachesChilds.refl
  | @tail a' σa' a'' σa'' _ hmem ih =>
      refine ih.tail ?_
      simp only [stepChilds, List.mem_append, List.mem_map]
      exact Or.inr ⟨some (a'', σa''), hmem, rfl⟩

/-- **Any children-level run lifts to a run of the fork**, provided no intermediate configuration
races. `stepChilds_eq_nil_of_allPure` is what rules out the fork joining instead of stepping: if a
child could move, not every child was `pure`. -/
theorem reaches_par_of_reachesChilds {β : Type} {αs : List Type}
    (k : Results αs → ParM β) {cs cs' : Childs ParM αs} {σ σ' : State}
    (h : ReachesChilds cs σ cs' σ')
    (hnr : ∀ cs'' σ'', ReachesChilds cs σ cs'' σ'' → racingAll (nextAccsChilds cs'') = false) :
    Reaches (.run (.par cs k) σ) (.run (.par cs' k) σ') := by
  induction h with
  | refl => exact Reaches.refl
  | @tail a' σa' a'' σa'' hreach hmem ih =>
      refine ih.tail ?_
      have hnr' : racingAll (nextAccsChilds a') = false := hnr a' σa' hreach
      have hnotpure : (allPure a').isSome = false := by
        cases hp : allPure a' with
        | none => rfl
        | some vs =>
            exfalso
            rw [stepChilds_eq_nil_of_allPure a' σa' (by rw [hp]; rfl)] at hmem
            simp at hmem
      simp only [stepC, step, hnr', Bool.false_eq_true, if_false]
      cases hp : allPure a' with
      | some vs => rw [hp] at hnotpure; simp at hnotpure
      | none =>
          simp only [List.mem_map]
          exact ⟨some (a'', σa''), hmem, rfl⟩

/-! ### Operational locality and the single-step canonical invariant

Piece 3, and where exactly `WellFormed` earns its place. `step`'s racing check is re-evaluated fresh
at every single step, not once at the top, so a real step that *doesn't* crash is automatically
non-racing at that instant, at any nesting depth, independence or not. Independence is needed for one
narrower thing: when the *right* branch of a `.par` moves before the left finishes, its real starting
state is the raw joint state, not the left-first reference point `σ₁` the whole theorem is stated
against, and only `Indep` makes replaying that step against `σ₁` give the same outcome.
`step_combined` is the single-step form of exactly that. One step at a time is enough; it needs no
containment statement about arbitrary reachable depths. -- ref: `docs/decomposition.md` -/

/-- Bernstein against a union on the right splits into the two halves. -/
theorem Indep.union_right {A B C : Footprint} (hb : Indep A B) (hc : Indep A C) :
    Indep A (Footprint.union B C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hb.1 l hl h
    · exact hc.1 l hl h
  · intro l hl hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hb.2.1 l hl h
    · exact hc.2.1 l hl h
  · intro l hl hmem
    rcases List.mem_append.mp hl with h | h
    · exact hb.2.2 l h hmem
    · exact hc.2.2 l h hmem

/-- Independence against *every child separately* gives independence against the children as a block.
Induction on the children list — this is what turns the flat `IndepAll` obligation into the single
`Indep` the two-branch arguments need. -/
theorem indep_accessesChilds {αs : List Type} (cs : Childs ParM αs) :
    ∀ (f : Footprint) (σ : State), (∀ g ∈ childFootprints cs σ, Indep f g) →
      Indep f (accessesChilds cs σ) := by
  induction cs with
  | nil => intro f σ _; exact ⟨by simp [Footprint.empty], by simp [Footprint.empty],
      by simp [Footprint.empty]⟩
  | cons p ps ih =>
      intro f σ h
      refine Indep.union_right (h _ (by simp [childFootprints])) ?_
      exact ih f (runSeq p σ).2 (fun g hg => h g (by simp [childFootprints]; exact Or.inr hg))

/-- **Under independence from the head, the children-block's footprint is the same measured from the
head's post-state or from `σ`.** The N-ary form of `accesses_runSeq_isolated`. -/
theorem accessesChilds_isolated {α : Type} {αs : List Type} (p : ParM α) (ps : Childs ParM αs)
    (σ : State) (h : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2)) :
    accessesChilds ps (runSeq p σ).2 = accessesChilds ps σ ∧
    (runChilds ps (runSeq p σ).2).1 = (runChilds ps σ).1 := by
  have hF : FDisjoint (accesses p σ).writes (accessesChilds ps (runSeq p σ).2) := ⟨h.2.1, h.1⟩
  obtain ⟨e1, e2, _⟩ := accessesChilds_runChilds_locality ps (runSeq p σ).2 σ
    (accesses p σ).writes hF (fun l hl => runSeq_frame p σ l hl)
  exact ⟨e1, e2⟩

/-- **A real step replays unchanged against an agreeing state.** If `σ` and `σ'` agree outside a set
`F` that `P`'s footprint avoids, then whatever step `P` takes from `σ` it can also take from `σ'`,
reaching the *same* program and states that still agree outside `F`. Operational analogue of
`accesses_runSeq_locality`. -/
theorem step_locality_all :
    (∀ {τ : Type} (P : ParM τ), ∀ (σ σ' : State) (F : List Loc),
        WellFormed P σ → FDisjoint F (accesses P σ) → (∀ l ∉ F, σ l = σ' l) →
        ∀ (P3 : ParM τ) (σ3 : State), Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
        ∃ σ3', Conf.run P3 σ3' ∈ stepC (Conf.run P σ') ∧ (∀ l ∉ F, σ3 l = σ3' l)) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ (σ σ' : State) (F : List Loc),
        WellFormedChilds cs σ → IndepAll (childFootprints cs σ) →
        FDisjoint F (accessesChilds cs σ) → (∀ l ∉ F, σ l = σ' l) →
        ∀ (cs3 : Childs ParM αs) (σ3 : State), some (cs3, σ3) ∈ stepChilds cs σ →
        ∃ σ3', some (cs3, σ3') ∈ stepChilds cs σ' ∧ (∀ l ∉ F, σ3 l = σ3' l)) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ σ' F _ _ _ P3 σ3 hstep; simp [stepC, step] at hstep
  · intro α l k ih σ σ' F hwf hF hagree P3 σ3 hstep
    have hl : l ∉ F := fun hmem => hF.1 l hmem (by simp [accesses, Footprint.union])
    have hv : σ l = σ' l := hagree l hl
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨hP3, hσ3⟩ := hstep
    refine ⟨σ', ?_, ?_⟩
    · simp only [stepC, step, List.mem_singleton, Conf.run.injEq]
      exact ⟨by rw [← hv, hP3], trivial⟩
    · intro x hx; rw [hσ3]; exact hagree x hx
  · intro α l v k ih σ σ' F hwf hF hagree P3 σ3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨hP3, hσ3⟩ := hstep
    refine ⟨σ'.update l v, ?_, ?_⟩
    · simp only [stepC, step, hP3, List.mem_singleton]
    · intro x hx
      rw [hσ3]
      by_cases hxl : x = l
      · subst hxl; simp [State.update]
      · simpa [State.update, hxl] using hagree x hx
  · -- a fork: a race cannot produce a `.run`, a join replays verbatim, and a child's move is the
    -- children-level statement
    intro β αs cs k ih2 ihk σ σ' F hwf hF hagree P3 σ3 hstep
    simp only [stepC, step] at hstep
    split at hstep
    · simp at hstep
    · rename_i hnr
      split at hstep
      · -- the join: same results, same heap, so it replays at σ' untouched
        rename_i vs _
        simp only [List.mem_singleton, Conf.run.injEq] at hstep
        obtain ⟨hP3, hσ3⟩ := hstep
        refine ⟨σ', ?_, ?_⟩
        · simp only [stepC, step, hnr, Bool.false_eq_true, if_false]
          simp_all
        · intro x hx; rw [hσ3]; exact hagree x hx
      · -- some child moved
        simp only [List.mem_map] at hstep
        obtain ⟨r, hr, heq⟩ := hstep
        cases r with
        | none => simp at heq
        | some x =>
            simp only [Conf.run.injEq] at heq
            obtain ⟨hP3, hσ3⟩ := heq
            obtain ⟨σ3', hstep', hag'⟩ :=
              ih2 σ σ' F hwf.2.1 hwf.1 hF.left hagree x.1 x.2 hr
            refine ⟨σ3', ?_, ?_⟩
            · simp only [stepC, step, hnr, Bool.false_eq_true, if_false]
              rename_i hnp
              simp only [hnp, List.mem_map]
              exact ⟨some (x.1, σ3'), hstep', by rw [← hP3]⟩
            · intro y hy; rw [← hσ3]; exact hag' y hy
  · intro σ σ' F _ _ _ _ cs3 σ3 hstep; simp [stepChilds] at hstep
  · -- **the 2-to-N step**: the head moved (its own IH) or the tail moved (the tail's IH, after
    -- isolation moves the tail's footprint from the head's post-state back to `σ`)
    intro α αs p ps ihp ihps σ σ' F hwf hind hF hagree cs3 σ3 hstep
    simp only [stepChilds, List.mem_append, List.mem_map] at hstep
    rcases hstep with ⟨c, hc, heq⟩ | ⟨r, hr, heq⟩
    · cases c with
      | wrong => simp at heq
      | run p3 σ3x =>
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨hcs3, hσ3⟩ := heq
          obtain ⟨σ3', hstep', hag'⟩ :=
            ihp σ σ' F hwf.1 hF.left hagree p3 σ3x hc
          refine ⟨σ3', ?_, ?_⟩
          · simp only [stepChilds, List.mem_append, List.mem_map]
            exact Or.inl ⟨.run p3 σ3', hstep', by rw [← hcs3]⟩
          · intro y hy; rw [← hσ3]; exact hag' y hy
    · cases r with
      | none => simp at heq
      | some y =>
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨hcs3, hσ3⟩ := heq
          -- the tail's own independence, and its footprint moved back to `σ`
          have hindtail : IndepAll (childFootprints ps (runSeq p σ).2) := hind.2
          have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
            indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
          obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
          have hFtail : FDisjoint F (accessesChilds ps σ) := eacc ▸ hF.right
          have hwftail : WellFormedChilds ps σ :=
            (WellFormedChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes
              ⟨hheadtail.2.1, hheadtail.1⟩ (fun l hl => runSeq_frame p σ l hl)).mp hwf.2
          have hindtail0 : IndepAll (childFootprints ps σ) := by
            rw [← childFootprints_locality ps (runSeq p σ).2 σ (accesses p σ).writes
              ⟨hheadtail.2.1, hheadtail.1⟩ (fun l hl => runSeq_frame p σ l hl)]
            exact hindtail
          obtain ⟨σ3', hstep', hag'⟩ :=
            ihps σ σ' F hwftail hindtail0 hFtail hagree y.1 y.2 hr
          refine ⟨σ3', ?_, ?_⟩
          · simp only [stepChilds, List.mem_append, List.mem_map]
            exact Or.inr ⟨some (y.1, σ3'), hstep', by rw [← hcs3]; rfl⟩
          · intro z hz; rw [← hσ3]; exact hag' z hz

theorem step_locality {τ : Type} (P : ParM τ) (σ σ' : State) (F : List Loc)
    (hwf : WellFormed P σ)
    (hF : FDisjoint F (accesses P σ)) (hagree : ∀ l ∉ F, σ l = σ' l)
    (P3 : ParM τ) (σ3 : State) (hstep : Conf.run P3 σ3 ∈ stepC (Conf.run P σ)) :
    ∃ σ3', Conf.run P3 σ3' ∈ stepC (Conf.run P σ') ∧ (∀ l ∉ F, σ3 l = σ3' l) :=
  step_locality_all.1 P σ σ' F hwf hF hagree P3 σ3 hstep

theorem stepChilds_locality {αs : List Type} (cs : Childs ParM αs) (σ σ' : State) (F : List Loc)
    (hwf : WellFormedChilds cs σ) (hind : IndepAll (childFootprints cs σ))
    (hF : FDisjoint F (accessesChilds cs σ)) (hagree : ∀ l ∉ F, σ l = σ' l)
    (cs3 : Childs ParM αs) (σ3 : State) (hstep : some (cs3, σ3) ∈ stepChilds cs σ) :
    ∃ σ3', some (cs3, σ3') ∈ stepChilds cs σ' ∧ (∀ l ∉ F, σ3 l = σ3' l) :=
  step_locality_all.2 cs σ σ' F hwf hind hF hagree cs3 σ3 hstep


/-- A real step changes nothing outside `P`'s write-footprint — the single-step analogue of
`runSeq_frame`. -/
theorem step_frame_all :
    (∀ {τ : Type} (P : ParM τ), ∀ (σ σ3 : State), WellFormed P σ → ∀ (P3 : ParM τ),
        Conf.run P3 σ3 ∈ stepC (Conf.run P σ) → ∀ l ∉ (accesses P σ).writes, σ l = σ3 l) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ (σ σ3 : State), WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) →
        ∀ (cs3 : Childs ParM αs), some (cs3, σ3) ∈ stepChilds cs σ →
        ∀ l ∉ (accessesChilds cs σ).writes, σ l = σ3 l) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ σ3 _ P3 hstep; simp [stepC, step] at hstep
  · intro α l k ih σ σ3 hwf P3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    intro l' _; rw [hstep.2]
  · intro α l v k ih σ σ3 hwf P3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    intro l' hl'
    have hl : l ∈ (accesses (ParM.write l v k) σ).writes := by simp [accesses, Footprint.union]
    have hne : l' ≠ l := fun h => hl' (h ▸ hl)
    rw [hstep.2, State.update_other σ v hne]
  · intro β αs cs k ih2 ihk σ σ3 hwf P3 hstep
    simp only [stepC, step] at hstep
    split at hstep
    · simp at hstep
    · split at hstep
      · simp only [List.mem_singleton, Conf.run.injEq] at hstep
        intro l _; rw [hstep.2]
      · simp only [List.mem_map] at hstep
        obtain ⟨r, hr, heq⟩ := hstep
        cases r with
        | none => simp at heq
        | some x =>
            simp only [Conf.run.injEq] at heq
            intro l hl
            rw [← heq.2]
            refine ih2 σ x.2 hwf.2.1 hwf.1 x.1 hr l ?_
            intro hmem
            exact hl (by simp [accesses, Footprint.union, hmem])
  · intro σ σ3 _ _ cs3 hstep; simp [stepChilds] at hstep
  · -- **the 2-to-N step**: the head's move is bounded by its own writes; the tail runs from `σ` in
    -- reality, so isolation moves its obligation from the staggered state back to `σ`
    intro α αs p ps ihp ihps σ σ3 hwf hind cs3 hstep
    simp only [stepChilds, List.mem_append, List.mem_map] at hstep
    rcases hstep with ⟨c, hc, heq⟩ | ⟨r, hr, heq⟩
    · cases c with
      | wrong => simp at heq
      | run p3 σ3x =>
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          intro l hl
          rw [← heq.2]
          refine ihp σ σ3x hwf.1 p3 hc l ?_
          intro hmem
          exact hl (by simp [accessesChilds, Footprint.union, hmem])
    · cases r with
      | none => simp at heq
      | some y =>
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at heq
          intro l hl
          rw [← heq.2]
          have hltail : l ∉ (accessesChilds ps (runSeq p σ).2).writes := by
            intro hmem
            exact hl (by simp [accessesChilds, Footprint.union, hmem])
          have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
            indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
          have hFw : FDisjoint (accesses p σ).writes (accessesChilds ps (runSeq p σ).2) :=
            ⟨hheadtail.2.1, hheadtail.1⟩
          have hfrm := fun l hl => runSeq_frame p σ l hl
          obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
          have hwftail : WellFormedChilds ps σ :=
            (WellFormedChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm).mp hwf.2
          have hindtail0 : IndepAll (childFootprints ps σ) := by
            rw [← childFootprints_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm]
            exact hind.2
          exact ihps σ y.2 hwftail hindtail0 y.1 hr l (eacc ▸ hltail)

/-- A real step changes nothing outside `P`'s write-footprint — the single-step analogue of
`runSeq_frame`. -/
theorem step_frame {τ : Type} (P : ParM τ) (σ σ3 : State) (hwf : WellFormed P σ) (P3 : ParM τ)
    (hstep : Conf.run P3 σ3 ∈ stepC (Conf.run P σ)) :
    ∀ l ∉ (accesses P σ).writes, σ l = σ3 l :=
  step_frame_all.1 P σ σ3 hwf P3 hstep

theorem stepChilds_frame {αs : List Type} (cs : Childs ParM αs) (σ σ3 : State)
    (hwf : WellFormedChilds cs σ) (hind : IndepAll (childFootprints cs σ))
    (cs3 : Childs ParM αs) (hstep : some (cs3, σ3) ∈ stepChilds cs σ) :
    ∀ l ∉ (accessesChilds cs σ).writes, σ l = σ3 l :=
  step_frame_all.2 cs σ σ3 hwf hind cs3 hstep


/-- A finished fork's children have already produced exactly their results, leaving the heap alone. -/
theorem runChilds_of_allPure {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State) (vs : Results αs),
      allPure cs = some vs → runChilds cs σ = (vs, σ) := by
  intro cs
  induction cs with
  | nil => intro σ vs h; grind [allPure, runChilds]
  | cons p ps ih =>
      intro σ vs h
      match p with
      | .pure a =>
          simp only [allPure] at h
          cases hc : allPure ps with
          | none => rw [hc] at h; exact absurd h (by simp [Option.map])
          | some ws =>
              rw [hc] at h
              have hvs : vs = (a, ws) := by
                simp only [Option.map] at h
                exact (Option.some.inj h).symm
              rw [hvs]
              simp only [runChilds, runSeq, ih σ ws hc]

/-- …and therefore touch nothing. -/
theorem accessesChilds_of_allPure {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State), (allPure cs).isSome = true →
      accessesChilds cs σ = Footprint.empty := by
  intro cs
  induction cs with
  | nil => intro σ _; rfl
  | cons p ps ih =>
      intro σ h
      match p with
      | .pure a =>
          have hps : (allPure ps).isSome = true := by
            revert h; simp only [allPure]; cases allPure ps <;> simp [Option.map]
          simp only [accessesChilds, accesses, runSeq, ih σ hps, Footprint.union, Footprint.empty,
            List.nil_append]

/-- **The single-step canonical invariant.** Under `WellFormed`, one real step never changes the
canonical outcome `runSeq` computes, and never lets a location outside the original footprint leak
into `accesses` — whichever `.par` branch moved, however deeply it is itself `.par`-structured.

The two conjuncts are one statement rather than two lemmas because the hard case needs both at once:
the branch moving *second*, replayed against its reference state via `step_locality`, agrees with that
replay only outside some set, and pinning the replayed state down *exactly* takes the footprint
conjunct of this very conclusion, one level down through `ihq`. Splitting them would require each half
before the other.

Chaining this along a whole `Reaches` derivation additionally needs `WellFormed` back at every
intermediate step — that is `WellFormed_preserved`. -/
theorem step_combined_all :
    (∀ {τ : Type} (P : ParM τ), ∀ σ, WellFormed P σ → ∀ P3 σ3,
        Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
        runSeq P3 σ3 = runSeq P σ ∧
        (∀ F, FDisjoint F (accesses P σ) → FDisjoint F (accesses P3 σ3))) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) → ∀ cs3 σ3,
        some (cs3, σ3) ∈ stepChilds cs σ →
        runChilds cs3 σ3 = runChilds cs σ ∧
        (∀ F, FDisjoint F (accessesChilds cs σ) → FDisjoint F (accessesChilds cs3 σ3))) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _ P3 σ3 hstep; simp [stepC, step] at hstep
  · intro α l k _ σ _ P3 σ3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨rfl, fun F hF => hF.right⟩
  · intro α l v k _ σ _ P3 σ3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨rfl, fun F hF => hF.right⟩
  · -- a fork: a race gives no `.run`; a join has already produced the children's results; a child's
    -- move is the children-level statement, lifted through `runSeq`'s `par` case
    intro β αs cs k ih2 ihk σ hwf P3 σ3 hstep
    simp only [stepC, step] at hstep
    split at hstep
    · simp at hstep
    · split at hstep
      · -- the join
        rename_i vs heqp
        simp only [List.mem_singleton, Conf.run.injEq] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        have hrc : runChilds cs σ3 = (vs, σ3) := runChilds_of_allPure cs σ3 vs heqp
        have hemp : accessesChilds cs σ3 = Footprint.empty :=
          accessesChilds_of_allPure cs σ3 (by rw [heqp]; rfl)
        refine ⟨?_, ?_⟩
        · show runSeq (k vs) σ3 = runSeq (k (runChilds cs σ3).1) (runChilds cs σ3).2
          rw [hrc]
        · intro F hF
          have := hF.right
          rw [hrc] at this
          exact this
      · -- some child moved
        simp only [List.mem_map] at hstep
        obtain ⟨r, hr, heq⟩ := hstep
        cases r with
        | none => simp at heq
        | some x =>
            simp only [Conf.run.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            obtain ⟨heqR, hFsub⟩ := ih2 σ hwf.2.1 hwf.1 x.1 x.2 hr
            refine ⟨?_, ?_⟩
            · show runSeq (k (runChilds x.1 x.2).1) (runChilds x.1 x.2).2 =
                   runSeq (k (runChilds cs σ).1) (runChilds cs σ).2
              rw [heqR]
            · intro F hF
              refine FDisjoint.union_of ?_ ?_
              · exact hFsub F hF.left
              · have := hF.right
                rw [← heqR] at this
                exact this
  · intro σ _ _ cs3 σ3 hstep; simp [stepChilds] at hstep
  · -- **the 2-to-N step.** Head moved: its own IH transports `runSeq`, and the tail follows because
    -- it is replayed from the head's (unchanged) post-state. Tail moved: this is the hard case the
    -- docstring describes — the tail really runs from `σ` while its footprint is recorded at the
    -- head's post-state, so `stepChilds_locality` replays its step there and the footprint conjunct
    -- of this very conclusion, one level down, pins the replayed heap down exactly.
    intro α αs p ps ihp ihps σ hwf hind cs3 σ3 hstep
    simp only [stepChilds, List.mem_append, List.mem_map] at hstep
    rcases hstep with ⟨c, hc, heq⟩ | ⟨r, hr, heq⟩
    · cases c with
      | wrong => simp at heq
      | run p3 σ3x =>
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨heqR, hFsub⟩ := ihp σ hwf.1 p3 σ3x hc
          refine ⟨?_, ?_⟩
          · simp only [runChilds, heqR]
          · intro F hF
            refine FDisjoint.union_of (hFsub F hF.left) ?_
            have := hF.right
            rw [← heqR] at this
            exact this
    · cases r with
      | none => simp at heq
      | some y =>
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          -- move the tail's data from the head's post-state back to `σ`, where it really runs
          have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
            indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
          have hFw : FDisjoint (accesses p σ).writes (accessesChilds ps (runSeq p σ).2) :=
            ⟨hheadtail.2.1, hheadtail.1⟩
          have hfrm := fun l hl => runSeq_frame p σ l hl
          obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
          have hwftail0 : WellFormedChilds ps σ :=
            (WellFormedChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm).mp hwf.2
          have hindtail0 : IndepAll (childFootprints ps σ) := by
            rw [← childFootprints_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm]
            exact hind.2
          have hindep0 : Indep (accesses p σ) (accessesChilds ps σ) := eacc ▸ hheadtail
          -- the head's run is unaffected by the tail's step
          have hFp_t : FDisjoint (accessesChilds ps σ).writes (accesses p σ) :=
            ⟨(Indep.symm hindep0).2.1, (Indep.symm hindep0).1⟩
          have hagree_pt : ∀ l ∉ (accessesChilds ps σ).writes, σ l = y.2 l :=
            stepChilds_frame ps σ y.2 hwftail0 hindtail0 y.1 hr
          obtain ⟨heqAccP, heqA, agree1⟩ :=
            accesses_runSeq_locality p σ y.2 (accessesChilds ps σ).writes hFp_t hagree_pt
          -- replay the tail's step from the head's post-state, where it is measured
          have hFt_p : FDisjoint (accesses p σ).writes (accessesChilds ps σ) :=
            ⟨hindep0.2.1, hindep0.1⟩
          have hagree_σσ1 : ∀ l ∉ (accesses p σ).writes, σ l = (runSeq p σ).2 l :=
            fun l hl => (runSeq_frame p σ l hl).symm
          obtain ⟨σ3x', hstep1, hagree2⟩ :=
            stepChilds_locality ps σ (runSeq p σ).2 (accesses p σ).writes hwftail0 hindtail0
              hFt_p hagree_σσ1 y.1 y.2 hr
          obtain ⟨EQ_shifted, FSUB_shifted⟩ := ihps (runSeq p σ).2 hwf.2 hind.2 y.1 σ3x' hstep1
          -- pin the replayed heap down exactly, using the footprint conjunct one level down
          have heq_full : σ3x' = (runSeq p y.2).2 := by
            funext l
            by_cases hl : l ∈ (accesses p σ).writes
            · have h1 : σ3x' l = (runSeq p σ).2 l :=
                (stepChilds_frame ps (runSeq p σ).2 σ3x' hwf.2 hind.2 y.1 hstep1 l
                  (fun hmem => hFw.2 l hl hmem)).symm
              have h2 : (runSeq p y.2).2 l = (runSeq p σ).2 l := by
                have hl' : l ∉ (accessesChilds ps σ).writes := fun hmem => hFp_t.2 l hmem hl
                exact (agree1 l hl').symm
              rw [h1, h2]
            · have h1 : σ3x' l = y.2 l := (hagree2 l hl).symm
              have h2 : (runSeq p y.2).2 l = y.2 l := by
                refine runSeq_frame p y.2 l ?_
                rw [← heqAccP]; exact hl
              rw [h1, h2]
          refine ⟨?_, ?_⟩
          · simp only [runChilds]
            rw [← heqA, ← heq_full, EQ_shifted]
          · intro F hF
            refine FDisjoint.union_of ?_ ?_
            · rw [← heqAccP]; exact hF.left
            · rw [← heq_full]
              have hFt : FDisjoint F (accessesChilds ps (runSeq p σ).2) := hF.right
              exact FSUB_shifted F hFt

theorem step_combined {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
      runSeq P3 σ3 = runSeq P σ ∧
      (∀ F, FDisjoint F (accesses P σ) → FDisjoint F (accesses P3 σ3)) :=
  step_combined_all.1 P

theorem stepChilds_combined {αs : List Type} (cs : Childs ParM αs) :
    ∀ σ, WellFormedChilds cs σ → IndepAll (childFootprints cs σ) → ∀ cs3 σ3,
      some (cs3, σ3) ∈ stepChilds cs σ →
      runChilds cs3 σ3 = runChilds cs σ ∧
      (∀ F, FDisjoint F (accessesChilds cs σ) → FDisjoint F (accessesChilds cs3 σ3)) :=
  step_combined_all.2 cs


/-! ### Preservation and chaining

Piece 4. `step_combined` gives the invariant for *one* step; using it again on the *next* step needs
`WellFormed` re-established at that point, which needs `Indep`'s three Bernstein conditions
individually — `step_combined`'s own containment conjunct bundles reads and writes together via
one `FDisjoint`, which isn't fine-grained enough to reconstruct them. `step_subset_rw` is the
finer version (same proof shape as `step_combined`'s footprint half, `.reads`/`.writes` tracked as
separate `List.Subset` facts), and `WellFormed_preserved` is what actually chains: it doesn't
re-derive containment for a compound moved branch from scratch — `ihp`/`ihq` (the *same*
`WellFormed_preserved`, structurally smaller) already give `WellFormed` for that branch directly,
so the only new content per step is checking `Indep` monotonically shrinks via `step_subset_rw`. -/

/-- Appending respects containment on both sides — what lifts component subset facts through
`Footprint.union`. -/
theorem append_mono {a a' b b' : List Loc} (ha : a ⊆ a') (hb : b ⊆ b') : a ++ b ⊆ a' ++ b' := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · exact List.mem_append.mpr (Or.inl (ha h))
  · exact List.mem_append.mpr (Or.inr (hb h))

/-- `step_combined`'s containment conjunct at finer grain: a step shrinks the reads and the writes
of `accesses` *separately*, as two `⊆` facts. That separation is what reconstructing `Indep`'s three
Bernstein conditions after a step requires, and what the single bundled `FDisjoint` cannot give. -/
theorem step_subset_rw_all :
    (∀ {τ : Type} (P : ParM τ), ∀ σ, WellFormed P σ → ∀ P3 σ3,
        Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
        runSeq P3 σ3 = runSeq P σ ∧
        (accesses P3 σ3).reads ⊆ (accesses P σ).reads ∧
        (accesses P3 σ3).writes ⊆ (accesses P σ).writes) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) → ∀ cs3 σ3,
        some (cs3, σ3) ∈ stepChilds cs σ →
        runChilds cs3 σ3 = runChilds cs σ ∧
        (accessesChilds cs3 σ3).reads ⊆ (accessesChilds cs σ).reads ∧
        (accessesChilds cs3 σ3).writes ⊆ (accessesChilds cs σ).writes) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _ P3 σ3 hstep; simp [stepC, step] at hstep
  · intro α l k _ σ _ P3 σ3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    refine ⟨rfl, ?_, ?_⟩ <;> simp [accesses, Footprint.union] <;>
      intro x hx <;> simp [hx]
  · intro α l v k _ σ _ P3 σ3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    refine ⟨rfl, ?_, ?_⟩ <;> simp [accesses, Footprint.union] <;>
      intro x hx <;> simp [hx]
  · intro β αs cs k ih2 ihk σ hwf P3 σ3 hstep
    simp only [stepC, step] at hstep
    split at hstep
    · simp at hstep
    · split at hstep
      · rename_i vs heqp
        simp only [List.mem_singleton, Conf.run.injEq] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        have hrc : runChilds cs σ3 = (vs, σ3) := runChilds_of_allPure cs σ3 vs heqp
        have hemp : accessesChilds cs σ3 = Footprint.empty :=
          accessesChilds_of_allPure cs σ3 (by rw [heqp]; rfl)
        refine ⟨by simp only [runSeq, hrc], ?_, ?_⟩
        · simp [accesses, hrc, hemp, Footprint.union, Footprint.empty]
        · simp [accesses, hrc, hemp, Footprint.union, Footprint.empty]
      · simp only [List.mem_map] at hstep
        obtain ⟨r, hr, heq⟩ := hstep
        cases r with
        | none => simp at heq
        | some x =>
            simp only [Conf.run.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            obtain ⟨heqR, hR, hW⟩ := ih2 σ hwf.2.1 hwf.1 x.1 x.2 hr
            refine ⟨by simp only [runSeq, heqR], ?_, ?_⟩
            · simp only [accesses, Footprint.union, heqR]
              exact append_mono hR (fun _ h => h)
            · simp only [accesses, Footprint.union, heqR]
              exact append_mono hW (fun _ h => h)
  · intro σ _ _ cs3 σ3 hstep; simp [stepChilds] at hstep
  · -- **the 2-to-N step**, same chain as `step_combined`'s: head's own IH, or the tail replayed at
    -- the head's post-state with its heap pinned down exactly
    intro α αs p ps ihp ihps σ hwf hind cs3 σ3 hstep
    simp only [stepChilds, List.mem_append, List.mem_map] at hstep
    rcases hstep with ⟨c, hc, heq⟩ | ⟨r, hr, heq⟩
    · cases c with
      | wrong => simp at heq
      | run p3 σ3x =>
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨heqR, hR, hW⟩ := ihp σ hwf.1 p3 σ3x hc
          refine ⟨by simp only [runChilds, heqR], ?_, ?_⟩
          · simp only [accessesChilds, Footprint.union, heqR]
            exact append_mono hR (fun _ h => h)
          · simp only [accessesChilds, Footprint.union, heqR]
            exact append_mono hW (fun _ h => h)
    · cases r with
      | none => simp at heq
      | some y =>
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
            indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
          have hFw : FDisjoint (accesses p σ).writes (accessesChilds ps (runSeq p σ).2) :=
            ⟨hheadtail.2.1, hheadtail.1⟩
          have hfrm := fun l hl => runSeq_frame p σ l hl
          obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
          have hwftail0 : WellFormedChilds ps σ :=
            (WellFormedChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm).mp hwf.2
          have hindtail0 : IndepAll (childFootprints ps σ) := by
            rw [← childFootprints_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm]
            exact hind.2
          have hindep0 : Indep (accesses p σ) (accessesChilds ps σ) := eacc ▸ hheadtail
          have hFp_t : FDisjoint (accessesChilds ps σ).writes (accesses p σ) :=
            ⟨(Indep.symm hindep0).2.1, (Indep.symm hindep0).1⟩
          have hagree_pt : ∀ l ∉ (accessesChilds ps σ).writes, σ l = y.2 l :=
            stepChilds_frame ps σ y.2 hwftail0 hindtail0 y.1 hr
          obtain ⟨heqAccP, heqA, agree1⟩ :=
            accesses_runSeq_locality p σ y.2 (accessesChilds ps σ).writes hFp_t hagree_pt
          have hFt_p : FDisjoint (accesses p σ).writes (accessesChilds ps σ) :=
            ⟨hindep0.2.1, hindep0.1⟩
          have hagree_σσ1 : ∀ l ∉ (accesses p σ).writes, σ l = (runSeq p σ).2 l :=
            fun l hl => (runSeq_frame p σ l hl).symm
          obtain ⟨σ3x', hstep1, hagree2⟩ :=
            stepChilds_locality ps σ (runSeq p σ).2 (accesses p σ).writes hwftail0 hindtail0
              hFt_p hagree_σσ1 y.1 y.2 hr
          obtain ⟨EQ_shifted, hR, hW⟩ := ihps (runSeq p σ).2 hwf.2 hind.2 y.1 σ3x' hstep1
          have heq_full : σ3x' = (runSeq p y.2).2 := by
            funext l
            by_cases hl : l ∈ (accesses p σ).writes
            · have h1 : σ3x' l = (runSeq p σ).2 l :=
                (stepChilds_frame ps (runSeq p σ).2 σ3x' hwf.2 hind.2 y.1 hstep1 l
                  (fun hmem => hFw.2 l hl hmem)).symm
              have h2 : (runSeq p y.2).2 l = (runSeq p σ).2 l := by
                have hl' : l ∉ (accessesChilds ps σ).writes := fun hmem => hFp_t.2 l hmem hl
                exact (agree1 l hl').symm
              rw [h1, h2]
            · have h1 : σ3x' l = y.2 l := (hagree2 l hl).symm
              have h2 : (runSeq p y.2).2 l = y.2 l := by
                refine runSeq_frame p y.2 l ?_
                rw [← heqAccP]; exact hl
              rw [h1, h2]
          refine ⟨?_, ?_, ?_⟩
          · simp only [runChilds]
            rw [← heqA, ← heq_full, EQ_shifted]
          · simp only [accessesChilds, Footprint.union]
            rw [← heqAccP, ← heq_full]
            exact append_mono (fun _ h => h) hR
          · simp only [accessesChilds, Footprint.union]
            rw [← heqAccP, ← heq_full]
            exact append_mono (fun _ h => h) hW

theorem step_subset_rw {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
      runSeq P3 σ3 = runSeq P σ ∧
      (accesses P3 σ3).reads ⊆ (accesses P σ).reads ∧
      (accesses P3 σ3).writes ⊆ (accesses P σ).writes :=
  step_subset_rw_all.1 P

theorem stepChilds_subset_rw {αs : List Type} (cs : Childs ParM αs) :
    ∀ σ, WellFormedChilds cs σ → IndepAll (childFootprints cs σ) → ∀ cs3 σ3,
      some (cs3, σ3) ∈ stepChilds cs σ →
      runChilds cs3 σ3 = runChilds cs σ ∧
      (accessesChilds cs3 σ3).reads ⊆ (accessesChilds cs σ).reads ∧
      (accessesChilds cs3 σ3).writes ⊆ (accessesChilds cs σ).writes :=
  step_subset_rw_all.2 cs


/-- Shrinking the left side preserves disjointness — how `step_subset_rw`'s containment facts turn
back into `Indep` for a branch that has moved. -/
theorem Disjoint.mono_left {a a' b : List Loc} (hsub : a ⊆ a')
    (h : Disjoint a' b) : Disjoint a b :=
  fun l hl hb => h l (hsub hl) hb

/-- Shrinking the right side preserves disjointness. -/
theorem Disjoint.mono_right {a b b' : List Loc} (hsub : b ⊆ b')
    (h : Disjoint a b') : Disjoint a b :=
  fun l ha hl => h l ha (hsub hl)

/-- Shrinking the left-hand footprint preserves Bernstein independence. -/
theorem Indep.mono_left {f f' b : Footprint} (hr : f.reads ⊆ f'.reads) (hw : f.writes ⊆ f'.writes)
    (h : Indep f' b) : Indep f b :=
  ⟨Disjoint.mono_left hw h.1, Disjoint.mono_left hw h.2.1, Disjoint.mono_right hr h.2.2⟩

/-- Shrinking the right-hand footprint preserves Bernstein independence. -/
theorem Indep.mono_right {f b b' : Footprint} (h : Indep f b')
    (hr : b.reads ⊆ b'.reads) (hw : b.writes ⊆ b'.writes) : Indep f b :=
  ⟨Disjoint.mono_right hw h.1, Disjoint.mono_right hr h.2.1, Disjoint.mono_left hw h.2.2⟩

/-- Each child's own footprint sits inside the children-block's. Induction on the list. -/
theorem childFootprint_subset {αs : List Type} (cs : Childs ParM αs) :
    ∀ (σ : State) (g : Footprint), g ∈ childFootprints cs σ →
      g.reads ⊆ (accessesChilds cs σ).reads ∧ g.writes ⊆ (accessesChilds cs σ).writes := by
  induction cs with
  | nil => intro σ g hg; simp [childFootprints] at hg
  | cons p ps ih =>
      intro σ g hg
      simp only [childFootprints, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨fun x hx => List.mem_append.mpr (Or.inl hx),
               fun x hx => List.mem_append.mpr (Or.inl hx)⟩
      · obtain ⟨hr, hw⟩ := ih (runSeq p σ).2 g hg
        exact ⟨fun x hx => List.mem_append.mpr (Or.inr (hr hx)),
               fun x hx => List.mem_append.mpr (Or.inr (hw hx))⟩

/-- **Subject reduction**: a well-formed program is still well-formed after one real step, whichever
branch moved and however deep its own structure. This is what lets `step_combined` be invoked again at
the next step, and so lets the canonical-value invariant survive an entire `Reaches` derivation rather
than a single step. -/
theorem WellFormed_preserved_all :
    (∀ {τ : Type} (P : ParM τ), ∀ σ, WellFormed P σ → ∀ P3 σ3,
        Conf.run P3 σ3 ∈ stepC (Conf.run P σ) → WellFormed P3 σ3) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) → ∀ cs3 σ3, some (cs3, σ3) ∈ stepChilds cs σ →
        WellFormedChilds cs3 σ3 ∧ IndepAll (childFootprints cs3 σ3)) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _ P3 σ3 hstep; simp [stepC, step] at hstep
  · intro α l k ih σ hwf P3 σ3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact hwf
  · intro α l v k ih σ hwf P3 σ3 hstep
    simp only [stepC, step, List.mem_singleton, Conf.run.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact hwf
  · intro β αs cs k ih2 ihk σ hwf P3 σ3 hstep
    simp only [stepC, step] at hstep
    split at hstep
    · simp at hstep
    · split at hstep
      · -- the join: the continuation's own obligation, already in `hwf`
        rename_i vs heqp
        simp only [List.mem_singleton, Conf.run.injEq] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        have hrc : runChilds cs σ3 = (vs, σ3) := runChilds_of_allPure cs σ3 vs heqp
        have := hwf.2.2
        rw [hrc] at this
        exact this
      · -- a child moved: `ih2` gives both halves back, and the continuation is unmoved because
        -- `stepChilds_combined` says the children's canonical outcome is unchanged
        simp only [List.mem_map] at hstep
        obtain ⟨r, hr, heq⟩ := hstep
        cases r with
        | none => simp at heq
        | some x =>
            simp only [Conf.run.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            obtain ⟨hwf3, hind3⟩ := ih2 σ hwf.2.1 hwf.1 x.1 x.2 hr
            obtain ⟨heqR, _⟩ := stepChilds_combined cs σ hwf.2.1 hwf.1 x.1 x.2 hr
            refine ⟨hind3, hwf3, ?_⟩
            rw [heqR]
            exact hwf.2.2
  · intro σ _ _ cs3 σ3 hstep; simp [stepChilds] at hstep
  · -- **the 2-to-N step**: head moved — its own IH plus `step_subset_rw` to shrink the head's
    -- footprint inside the independence facts. Tail moved — the same replay-and-pin chain, with the
    -- head's well-formedness transported to the heap the tail's step produced.
    intro α αs p ps ihp ihps σ hwf hind cs3 σ3 hstep
    simp only [stepChilds, List.mem_append, List.mem_map] at hstep
    rcases hstep with ⟨c, hc, heq⟩ | ⟨r, hr, heq⟩
    · cases c with
      | wrong => simp at heq
      | run p3 σ3x =>
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hwfp3 := ihp σ hwf.1 p3 σ3x hc
          obtain ⟨heqR, hsubR, hsubW⟩ := step_subset_rw p σ hwf.1 p3 σ3x hc
          refine ⟨⟨hwfp3, by rw [heqR]; exact hwf.2⟩, ?_⟩
          refine ⟨?_, by rw [heqR]; exact hind.2⟩
          intro g hg
          rw [heqR] at hg
          exact Indep.mono_left hsubR hsubW (hind.1 g hg)
    · cases r with
      | none => simp at heq
      | some y =>
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
            indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
          have hFw : FDisjoint (accesses p σ).writes (accessesChilds ps (runSeq p σ).2) :=
            ⟨hheadtail.2.1, hheadtail.1⟩
          have hfrm := fun l hl => runSeq_frame p σ l hl
          obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
          have hwftail0 : WellFormedChilds ps σ :=
            (WellFormedChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm).mp hwf.2
          have hindtail0 : IndepAll (childFootprints ps σ) := by
            rw [← childFootprints_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm]
            exact hind.2
          have hindep0 : Indep (accesses p σ) (accessesChilds ps σ) := eacc ▸ hheadtail
          have hFp_t : FDisjoint (accessesChilds ps σ).writes (accesses p σ) :=
            ⟨(Indep.symm hindep0).2.1, (Indep.symm hindep0).1⟩
          have hagree_pt : ∀ l ∉ (accessesChilds ps σ).writes, σ l = y.2 l :=
            stepChilds_frame ps σ y.2 hwftail0 hindtail0 y.1 hr
          obtain ⟨heqAccP, heqA, agree1⟩ :=
            accesses_runSeq_locality p σ y.2 (accessesChilds ps σ).writes hFp_t hagree_pt
          have hwfpy : WellFormed p y.2 :=
            (WellFormed_locality p σ y.2 (accessesChilds ps σ).writes hFp_t hagree_pt).mp hwf.1
          have hFt_p : FDisjoint (accesses p σ).writes (accessesChilds ps σ) :=
            ⟨hindep0.2.1, hindep0.1⟩
          have hagree_σσ1 : ∀ l ∉ (accesses p σ).writes, σ l = (runSeq p σ).2 l :=
            fun l hl => (runSeq_frame p σ l hl).symm
          obtain ⟨σ3x', hstep1, hagree2⟩ :=
            stepChilds_locality ps σ (runSeq p σ).2 (accesses p σ).writes hwftail0 hindtail0
              hFt_p hagree_σσ1 y.1 y.2 hr
          obtain ⟨hwftail3, hindtail3⟩ := ihps (runSeq p σ).2 hwf.2 hind.2 y.1 σ3x' hstep1
          obtain ⟨_, hsubR, hsubW⟩ := stepChilds_subset_rw ps (runSeq p σ).2 hwf.2 hind.2
            y.1 σ3x' hstep1
          have heq_full : σ3x' = (runSeq p y.2).2 := by
            funext l
            by_cases hl : l ∈ (accesses p σ).writes
            · have h1 : σ3x' l = (runSeq p σ).2 l :=
                (stepChilds_frame ps (runSeq p σ).2 σ3x' hwf.2 hind.2 y.1 hstep1 l
                  (fun hmem => hFw.2 l hl hmem)).symm
              have h2 : (runSeq p y.2).2 l = (runSeq p σ).2 l := by
                have hl' : l ∉ (accessesChilds ps σ).writes := fun hmem => hFp_t.2 l hmem hl
                exact (agree1 l hl').symm
              rw [h1, h2]
            · have h1 : σ3x' l = y.2 l := (hagree2 l hl).symm
              have h2 : (runSeq p y.2).2 l = y.2 l := by
                refine runSeq_frame p y.2 l ?_
                rw [← heqAccP]; exact hl
              rw [h1, h2]
          refine ⟨⟨hwfpy, by rw [← heq_full]; exact hwftail3⟩, ?_, ?_⟩
          · -- head-vs-tail independence survives: the tail's footprints only shrank
            intro g hg
            rw [← heq_full] at hg
            obtain ⟨hgr, hgw⟩ := childFootprint_subset y.1 σ3x' g hg
            rw [← heqAccP]
            exact Indep.mono_right
              (Indep.mono_right hheadtail hsubR hsubW) hgr hgw
          · rw [← heq_full]; exact hindtail3

theorem WellFormed_preserved {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) → WellFormed P3 σ3 :=
  WellFormed_preserved_all.1 P

theorem WellFormedChilds_preserved {αs : List Type} (cs : Childs ParM αs) :
    ∀ σ, WellFormedChilds cs σ → IndepAll (childFootprints cs σ) → ∀ cs3 σ3,
      some (cs3, σ3) ∈ stepChilds cs σ →
      WellFormedChilds cs3 σ3 ∧ IndepAll (childFootprints cs3 σ3) :=
  WellFormed_preserved_all.2 cs


/-- **Every configuration a real execution reaches is still well-formed and still computes the same
canonical outcome.** `step_combined` and `WellFormed_preserved` iterated along a whole `Reaches`
chain — the uniqueness direction of `wellFormed_canonical`, before specializing the endpoint to
`.pure`. -/
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

/-- **A real execution never escapes the footprint it started with**, however many steps in: reads
stay inside the original reads, writes inside the original writes. `step_subset_rw` iterated along a
chain. -/
theorem subset_chain {τ : Type} (P : ParM τ) (σ : State) (hwf : WellFormed P σ)
    (C : Conf τ) (h : Reaches (.run P σ) C) :
    ∀ P' σ', C = .run P' σ' →
      (accesses P' σ').reads ⊆ (accesses P σ).reads ∧
      (accesses P' σ').writes ⊆ (accesses P σ).writes := by
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

/-- Two label sets cannot race once each is bounded inside its own side of an `Indep` pair.
`no_race_of_indep` with the containment facts taken as hypotheses rather than derived at a fixed
state — the form needed when labels are bounded by an *original* footprint several steps back. -/
theorem no_race_contained (labP labQ : List Label) (fP fQ : Footprint)
    (hindep : Indep fP fQ)
    (hP : ∀ lbl ∈ labP, (lbl.isWrite = true → lbl.loc ∈ fP.writes) ∧
      (lbl.isWrite = false → lbl.loc ∈ fP.reads))
    (hQ : ∀ lbl ∈ labQ, (lbl.isWrite = true → lbl.loc ∈ fQ.writes) ∧
      (lbl.isWrite = false → lbl.loc ∈ fQ.reads)) :
    ¬ racing labP labQ = true := by
  grind only [= Indep.eq_1, = racing.eq_1, = Disjoint.eq_1, = List.any_eq, = Label.conflicts.eq_1]

/-! ### The canonical-outcome theorem -/

/-- A label set that cannot race the whole block cannot race any one member of it. -/
theorem racing_of_mem_flatten {a : List Label} {l : List (List Label)}
    (h : racing a l.flatten = false) : ∀ b ∈ l, racing a b = false := by
  intro b hb
  cases hr : racing a b with
  | false => rfl
  | true =>
      exfalso
      have hfl : racing a l.flatten = true := by
        simp only [racing, List.any_eq_true] at hr ⊢
        obtain ⟨x, hx, y, hy, hconf⟩ := hr
        exact ⟨x, hx, y, List.mem_flatten.mpr ⟨b, hb, hy⟩, hconf⟩
      rw [hfl] at h
      exact Bool.noConfusion h

/-- **Pairwise-independent children never race.** Induction on the children list: the head cannot
race the rest (their footprints are Bernstein-independent, and ready labels sit inside footprints),
and the rest cannot race each other by the IH. -/
theorem racingAll_of_indepAll {αs : List Type} (cs : Childs ParM αs) :
    ∀ (σ : State), IndepAll (childFootprints cs σ) → racingAll (nextAccsChilds cs) = false := by
  induction cs with
  | nil => intro σ _; rfl
  | cons p ps ih =>
      intro σ hind
      have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
        indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
      have hflat : racing (nextAccs p) (nextAccsChilds ps).flatten = false := by
        cases hc : racing (nextAccs p) (nextAccsChilds ps).flatten with
        | false => rfl
        | true =>
            exact absurd hc (no_race_contained (nextAccs p) (nextAccsChilds ps).flatten
              (accesses p σ) (accessesChilds ps (runSeq p σ).2) hheadtail
              (nextAccs_subset_accesses p σ)
              (nextAccsChilds_subset_accessesChilds ps (runSeq p σ).2))
      have hmem := racing_of_mem_flatten hflat
      have hany : (nextAccsChilds ps).any (fun other => racing (nextAccs p) other) = false := by
        cases hA : (nextAccsChilds ps).any (fun other => racing (nextAccs p) other) with
        | false => rfl
        | true =>
            exfalso
            simp only [List.any_eq_true] at hA
            obtain ⟨b, hb, hr⟩ := hA
            rw [hmem b hb] at hr
            exact Bool.noConfusion hr
      simp only [nextAccsChilds, racingAll, hany, ih (runSeq p σ).2 hind.2, Bool.or_false]

/-- Well-formedness and pairwise independence survive a whole children-level run. -/
theorem reachesChilds_preserves {αs : List Type} {cs cs'' : Childs ParM αs} {σ σ'' : State}
    (h : ReachesChilds cs σ cs'' σ'')
    (hwf : WellFormedChilds cs σ) (hind : IndepAll (childFootprints cs σ)) :
    WellFormedChilds cs'' σ'' ∧ IndepAll (childFootprints cs'' σ'') := by
  induction h with
  | refl => exact ⟨hwf, hind⟩
  | @tail a' σa' a'' σa'' _ hmem ih =>
      obtain ⟨hwf', hind'⟩ := ih
      exact WellFormedChilds_preserved a' σa' hwf' hind' a'' σa'' hmem

theorem allPure_pureChilds : ∀ (αs : List Type) (vs : Results αs),
    allPure (pureChilds αs vs) = some vs := by
  intro αs
  induction αs with
  | nil => intro vs; rfl
  | cons α as ih => intro vs; simp only [pureChilds, allPure, ih vs.2]; rfl

/-- **A well-formed program has exactly one outcome, and it is the canonical one.** Whatever the
schedule, the only `(result, final-state)` pair the real nondeterministic `step`/`Reaches` relation
can reach from `p` and `σ` is `runSeq p σ` — and that pair is always reachable. Both directions, as an
`↔`.

This is Brookes' Parallel Decomposition Lemma for this operational semantics, and the whole content of
the project: `par_seq_eq` and `parAll_par_seq_eq` are this theorem applied to both sides of an
equivalence plus a definitional bridge. `pure`/`read`/`write` are immediate; the `par` case is the
proof, assembled from `runSeq_invariant_chain` (→) and the explicitly constructed "run `p` fully, then
`q`, then step into `k`" schedule (←).

`WellFormed` cannot be weakened to top-level `Indep`: independence has to hold at every nested `par`
node, since a program can race with *itself* inside one branch while the two branches' total
footprints stay disjoint.

The second component is the children-level witness the `par` case needs: every child can be run to
completion, left to right — the N-ary form of "run `p` fully, then `q`". Its `cons` case is the
2-to-N step, and it is mutual with the theorem itself, because running a child to completion *is*
this theorem one level down. -- ref: Brookes CONCUR'04 §5–7; `docs/decomposition.md` -/
theorem wellFormed_canonical_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ r σ', WellFormed p σ →
        (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ)) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) →
        ReachesChilds cs σ (pureChilds αs (runChilds cs σ).1) (runChilds cs σ).2) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ r σ' _
    constructor
    · intro h
      have h2 := Reaches.terminal (c := Conf.run (ParM.pure a) σ) rfl h
      simp_all
    · grind [Reaches]
  · intro α l k ih σ r σ' hwf
    have hstep : stepC (Conf.run (ParM.read l k) σ) = [Conf.run (k (σ l)) σ] := rfl
    constructor
    · grind [Reaches.single_step]
    · intro h
      refine Reaches.trans ?_ ((ih (σ l) σ r σ' hwf).mpr h)
      exact Reaches.tail Reaches.refl (by rw [hstep]; exact List.mem_singleton_self _)
  · intro α l v k ih σ r σ' hwf
    have hstep : stepC (Conf.run (ParM.write l v k) σ) = [Conf.run (k ()) (σ.update l v)] := rfl
    constructor
    · grind [Reaches.single_step]
    · intro h
      refine Reaches.trans ?_ ((ih () (σ.update l v) r σ' hwf).mpr h)
      exact Reaches.tail Reaches.refl (by rw [hstep]; exact List.mem_singleton_self _)
  · -- the fork
    intro β αs cs k ih2 ihk σ r σ' hwf
    obtain ⟨hind, hwfcs, hwfk⟩ := hwf
    constructor
    · -- uniqueness: the invariant chain, specialized to a `.pure` endpoint
      intro h
      obtain ⟨_, heqR⟩ := runSeq_invariant_chain (.par cs k) σ ⟨hind, hwfcs, hwfk⟩
        (.run (ParM.pure r) σ') h (ParM.pure r) σ' rfl
      have hru : runSeq (ParM.pure r) σ' = (r, σ') := rfl
      rw [← hru]
      exact heqR
    · -- reachability: run every child to completion, then join, then continue
      intro heq
      have hRc : ReachesChilds cs σ (pureChilds αs (runChilds cs σ).1) (runChilds cs σ).2 :=
        ih2 σ hwfcs hind
      -- no intermediate configuration races: footprints only shrink along the run
      have hnr : ∀ cs'' σ'', ReachesChilds cs σ cs'' σ'' →
          racingAll (nextAccsChilds cs'') = false := by
        intro cs'' σ'' hR
        exact racingAll_of_indepAll cs'' σ'' (reachesChilds_preserves hR hwfcs hind).2
      have hRpar : Reaches (.run (.par cs k) σ)
          (.run (.par (pureChilds αs (runChilds cs σ).1) k) (runChilds cs σ).2) :=
        reaches_par_of_reachesChilds k hRc hnr
      have hjoin : Conf.run (k (runChilds cs σ).1) (runChilds cs σ).2 ∈
          stepC (Conf.run (.par (pureChilds αs (runChilds cs σ).1) k) (runChilds cs σ).2) := by
        have hap : allPure (pureChilds αs (runChilds cs σ).1) = some (runChilds cs σ).1 :=
          allPure_pureChilds αs (runChilds cs σ).1
        have hnr0 : racingAll (nextAccsChilds (pureChilds αs (runChilds cs σ).1)) = false :=
          hnr _ _ hRc
        simp only [stepC, step, hnr0, Bool.false_eq_true, if_false, hap]
        simp
      refine Reaches.trans (hRpar.tail hjoin) ((ihk (runChilds cs σ).1 (runChilds cs σ).2 r σ'
        hwfk).mpr ?_)
      exact heq
  · intro σ _ _; exact ReachesChilds.refl
  · -- **the 2-to-N step**: run the head to completion (this theorem, one level down), lift it with
    -- the tail standing still, then run the tail from the heap the head left
    intro α αs p ps ihp ihps σ hwf hind
    have hRp : Reaches (.run p σ) (.run (ParM.pure (runSeq p σ).1) (runSeq p σ).2) :=
      (ihp σ (runSeq p σ).1 (runSeq p σ).2 hwf.1).mpr rfl
    rcases reachesChilds_head p ps σ _ hRp with ⟨p', σ'', heq1, hR1⟩ | hcontra
    case inr => simp at hcontra
    simp only [Conf.run.injEq] at heq1
    obtain ⟨rfl, rfl⟩ := heq1
    have hRtail : ReachesChilds ps (runSeq p σ).2
        (pureChilds αs (runChilds ps (runSeq p σ).2).1) (runChilds ps (runSeq p σ).2).2 :=
      ihps (runSeq p σ).2 hwf.2 hind.2
    refine hR1.trans (reachesChilds_tail _ hRtail)

theorem wellFormed_canonical {τ : Type} (p : ParM τ) :
    ∀ σ r σ', WellFormed p σ → (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ) :=
  wellFormed_canonical_all.1 p

theorem reachesChilds_canonical {αs : List Type} (cs : Childs ParM αs) :
    ∀ σ, WellFormedChilds cs σ → IndepAll (childFootprints cs σ) →
      ReachesChilds cs σ (pureChilds αs (runChilds cs σ).1) (runChilds cs σ).2 :=
  wellFormed_canonical_all.2 cs


end Paralever
