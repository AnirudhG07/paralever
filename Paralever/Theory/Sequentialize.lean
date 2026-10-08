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

/-- The sequential fold agrees with the children-block run: same results in order, same final heap.
Induction on the list — the bridge between `seqAll`'s nested `bind`s and `parAll`'s single node. -/
theorem runSeq_seqAll {τ : Type} (ps : List (ParM τ)) (σ : State) :
    runSeq (ParM.seqAll ps) σ =
      (ParM.resultsToList ps (runChilds (ParM.childsOf ps) σ).1,
       (runChilds (ParM.childsOf ps) σ).2) := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih =>
      show runSeq (ParM.bind (ParM.seqPair p (ParM.seqAll ps)) _) σ = _
      rw [runSeq_bind]
      simp only [ParM.seqPair, runSeq_bind, ih]
      rfl

/-- The two sides of the N-ary equivalence have the same canonical run — the definitional bridge for
`parAll_par_seq_eq`. No `Indep` needed. -/
theorem runSeq_parAll_eq_seqAll {τ : Type} (ps : List (ParM τ)) (σ : State) :
    runSeq (ParM.parAll ps) σ = runSeq (ParM.seqAll ps) σ := by
  rw [runSeq_seqAll]
  rfl

/-- Every child of a `parAll` being well-formed is exactly the sequential fold being well-formed.
Induction on the list: `WellFormed_bind` peels one `seqPair`, and `WellFormedChilds` peels one
`cons`, in step. -/
theorem wellFormed_seqAll_of_childs {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormedChilds (ParM.childsOf ps) σ) : WellFormed (ParM.seqAll ps) σ := by
  induction ps generalizing σ with
  | nil => trivial
  | cons p ps ih =>
      show WellFormed (ParM.bind (ParM.seqPair p (ParM.seqAll ps)) _) σ
      rw [WellFormed_bind]
      refine ⟨?_, trivial⟩
      show WellFormed (ParM.bind p (fun a => ParM.bind (ParM.seqAll ps) _)) σ
      rw [WellFormed_bind]
      refine ⟨h.1, ?_⟩
      rw [WellFormed_bind]
      exact ⟨ih (runSeq p σ).2 h.2, trivial⟩

/-- Well-formedness transfers from `parAll` to `seqAll` — the N-ary `wellFormed_of_seqPair`. -/
theorem wellFormed_of_seqAll {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) : WellFormed (ParM.seqAll ps) σ :=
  wellFormed_seqAll_of_childs ps σ h.2.1

/-- A `parPair`'s footprint in binary form: the left branch, then the right measured from the heap the
left one left. What the two-branch examples expect. -/
@[grind .]
theorem accesses_parPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    accesses (ParM.parPair p q) σ
      = Footprint.union (accesses p σ) (accesses q (runSeq p σ).2) := by
  simp [ParM.parPair, accesses, accessesChilds, Footprint.union, Footprint.empty]

/-- A `parPair`'s canonical run in binary form. -/
@[grind .]
theorem runSeq_parPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    runSeq (ParM.parPair p q) σ
      = (((runSeq p σ).1, (runSeq q (runSeq p σ).2).1), (runSeq q (runSeq p σ).2).2) := rfl

/-- An empty `parAll` touches nothing. -/
@[simp, grind .]
theorem accesses_parAll_nil {τ : Type} (σ : State) :
    accesses (ParM.parAll ([] : List (ParM τ))) σ = Footprint.empty := rfl

/-- A `parAll`'s footprint peels one element at a time — the shape every indexed-loop validator
expects, recovered from the single-node definition. -/
@[simp, grind .]
theorem accesses_parAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State) :
    accesses (ParM.parAll (p :: ps)) σ
      = Footprint.union (accesses p σ) (accesses (ParM.parAll ps) (runSeq p σ).2) := by
  simp only [ParM.parAll, ParM.childsOf, accesses, accessesChilds, Footprint.union,
    Footprint.empty, List.append_nil, List.append_assoc]

/-- `WellFormed (parAll (p :: ps)) σ` from the three facts about the head and tail that need proving.
`apply` this to peel one element off a `parAll` well-formedness goal; the tail's independence and
well-formedness are checked at `(runSeq p σ).2`, the state after the head's canonical run. -/
@[simp, grind .]
theorem WellFormed_parAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (h1 : WellFormed p σ)
    (h2 : Indep (accesses p σ) (accesses (ParM.parAll ps) (runSeq p σ).2))
    (h3 : WellFormed (ParM.parAll ps) (runSeq p σ).2) :
    WellFormed (ParM.parAll (p :: ps)) σ := by
  -- `accesses (parAll ps) σ₁` is the children block united with a `pure` continuation, so `h2` is
  -- independence against the block; `childFootprint_subset` turns that into the member-wise form
  have hblock : Indep (accesses p σ) (accessesChilds (ParM.childsOf ps) (runSeq p σ).2) := by
    refine Indep.mono_right h2 ?_ ?_ <;>
      intro x hx <;> exact List.mem_append.mpr (Or.inl hx)
  refine ⟨⟨?_, ?_⟩, ⟨h1, h3.2.1⟩, trivial⟩
  · intro g hg
    obtain ⟨hgr, hgw⟩ := childFootprint_subset (ParM.childsOf ps) (runSeq p σ).2 g hg
    exact Indep.mono_right hblock hgr hgw
  · exact h3.1

/-- An empty `parAll` is well-formed — the base case, nothing to check. -/
@[simp, grind .]
theorem WellFormed_parAll_nil {τ : Type} (σ : State) :
    WellFormed (ParM.parAll ([] : List (ParM τ))) σ := ⟨trivial, trivial, trivial⟩

/-- **The metatheorem for a list of branches**: running `ps` all in parallel reaches exactly the
outcomes running them one after another does, under every schedule, given well-formedness. Now a
genuine N-ary statement about one `par` node, not a corollary of nesting. This is what
`#parallel_for` and every chunked example ultimately appeals to. -/
@[simp, grind .]
theorem parAll_par_seq_eq {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) : ParSeqEq (ParM.parAll ps) (ParM.seqAll ps) σ := by
  intro r σ'
  rw [wellFormed_canonical _ σ r σ' h,
      wellFormed_canonical _ σ r σ' (wellFormed_of_seqAll ps σ h),
      runSeq_parAll_eq_seqAll]


/-! ### Substituting an equivalent program inside a larger one -/

/-- `parPair` and `seqPair` have the same canonical run. The content of `par_seq_eq`
is that the *operational* relation also collapses onto it. -/
theorem runSeq_parPair_eq_seqPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    runSeq (ParM.parPair p q) σ = runSeq (ParM.seqPair p q) σ :=
  runSeq_par_eq_seq p q σ

/-- Equal canonical runs plus well-formedness on both sides is equivalence. The converse
direction of `wellFormed_canonical`, packaged for reuse. -/
theorem parSeqEq_of_runSeq_eq {α : Type} (p q : ParM α) (σ : State)
    (hp : WellFormed p σ) (hq : WellFormed q σ) (h : runSeq p σ = runSeq q σ) :
    ParSeqEq p q σ := by
  intro r σ'
  rw [wellFormed_canonical p σ r σ' hp, wellFormed_canonical q σ r σ' hq, h]

/-- Well-formedness transfers across a substitution with the same canonical run. -/
theorem wellFormed_bind_congr {α β : Type} (p q : ParM α) (f : α → ParM β) (σ : State)
    (hq : WellFormed q σ) (h : runSeq p σ = runSeq q σ)
    (hpf : WellFormed (ParM.bind p f) σ) : WellFormed (ParM.bind q f) σ := by
  rw [WellFormed_bind] at hpf ⊢
  exact ⟨hq, h ▸ hpf.2⟩

/-- **Congruence in the head.** Replacing `p` by an equivalent `q` leaves the rest of the
program's outcomes unchanged. -/
theorem parSeqEq_bind_congr {α β : Type} (p q : ParM α) (f : α → ParM β) (σ : State)
    (hq : WellFormed q σ) (h : runSeq p σ = runSeq q σ)
    (hpf : WellFormed (ParM.bind p f) σ) :
    ParSeqEq (ParM.bind p f) (ParM.bind q f) σ := by
  refine parSeqEq_of_runSeq_eq _ _ σ hpf (wellFormed_bind_congr p q f σ hq h hpf) ?_
  rw [runSeq_bind, runSeq_bind, h]

/-- **Congruence in the continuation.** If the two continuations agree canonically at the
state the prefix reaches, the whole programs are equivalent. -/
theorem parSeqEq_bind_cont {α β : Type} (c : ParM α) (f g : α → ParM β) (σ : State)
    (hcf : WellFormed (ParM.bind c f) σ) (hcg : WellFormed (ParM.bind c g) σ)
    (h : runSeq (f (runSeq c σ).1) (runSeq c σ).2
       = runSeq (g (runSeq c σ).1) (runSeq c σ).2) :
    ParSeqEq (ParM.bind c f) (ParM.bind c g) σ := by
  refine parSeqEq_of_runSeq_eq _ _ σ hcf hcg ?_
  rw [runSeq_bind, runSeq_bind, h]

/-! ### The region theorem

`prefix ; (p ∥ q) ; suffix` versus `prefix ; (p ; q) ; suffix`. -/

/-- **Parallelizing one region of a larger sequential program.** Run sequentially up to the
region, replace the region by its parallel version, continue sequentially after the join: the
whole program's outcomes are unchanged. Only the region needs an independence obligation. -/
theorem par_seq_eq_region {α β γ δ : Type}
    (pre : ParM α) (p : ParM β) (q : ParM γ) (post : β × γ → ParM δ) (σ : State)
    (hpar : WellFormed (ParM.bind pre (fun _ => ParM.bind (ParM.parPair p q) post)) σ) :
    ParSeqEq (ParM.bind pre (fun _ => ParM.bind (ParM.parPair p q) post))
             (ParM.bind pre (fun _ => ParM.bind (ParM.seqPair p q) post)) σ := by
  have hpre : WellFormed pre σ := ((WellFormed_bind pre _ σ).mp hpar).1
  have hreg : WellFormed (ParM.bind (ParM.parPair p q) post) (runSeq pre σ).2 :=
    ((WellFormed_bind pre _ σ).mp hpar).2
  have hwfpair : WellFormed (ParM.parPair p q) (runSeq pre σ).2 :=
    ((WellFormed_bind (ParM.parPair p q) post (runSeq pre σ).2).mp hreg).1
  have hseq : WellFormed (ParM.bind (ParM.seqPair p q) post) (runSeq pre σ).2 :=
    wellFormed_bind_congr (ParM.parPair p q) (ParM.seqPair p q) post (runSeq pre σ).2
      (wellFormed_of_seqPair p q (runSeq pre σ).2 hwfpair)
      (runSeq_parPair_eq_seqPair p q (runSeq pre σ).2) hreg
  refine parSeqEq_bind_cont pre _ _ σ hpar ?_ ?_
  · rw [WellFormed_bind]; exact ⟨hpre, hseq⟩
  · rw [runSeq_bind, runSeq_bind, runSeq_parPair_eq_seqPair]

/-! ### Link ② compositionally: `Computes`

`pure_eq_seq` is proved once per piece. This says those proofs *compose*: a bind chain of pieces
computes the composition of their pure functions, and a parallel region computes the same pure
function its sequential counterpart does. So the pure side is assembled the same way the program is,
and the parallel substitution of `par_seq_eq_region` is invisible to it. -/

/-- `p` computes the pure result `val` and the pure state transformer `F`. -/
def Computes {α : Type} (p : ParM α) (val : State → α) (F : State → State) : Prop :=
  ∀ σ, runSeq p σ = (val σ, F σ)

/-- Sequential composition composes the pure functions. The continuation's pure data may depend on
the value the prefix produced, which is why `val`/`F` are indexed by it. -/
theorem Computes.bind {α β : Type} {p : ParM α} {va : State → α} {F : State → State}
    {k : α → ParM β} {vb : α → State → β} {G : α → State → State}
    (hp : Computes p va F) (hk : ∀ a, Computes (k a) (vb a) (G a)) :
    Computes (ParM.bind p k) (fun σ => vb (va σ) (F σ)) (fun σ => G (va σ) (F σ)) := by
  intro σ
  rw [runSeq_bind, hp σ, hk (va σ) (F σ)]

/-- A sequential pair computes `G ∘ F`, pairing the two results. -/
theorem Computes.seqPair {α β : Type} {p : ParM α} {q : ParM β}
    {va : State → α} {vb : State → β} {F G : State → State}
    (hp : Computes p va F) (hq : Computes q vb G) :
    Computes (ParM.seqPair p q) (fun σ => (va σ, vb (F σ))) (fun σ => G (F σ)) := by
  intro σ
  show runSeq (ParM.bind p (fun a => ParM.bind q (fun b => ParM.pure (a, b)))) σ = _
  rw [runSeq_bind, hp σ, runSeq_bind, hq (F σ)]
  rfl

/-- **The parallel pair computes exactly the same pure function.** No independence hypothesis is
needed, because this is a statement about the canonical run; `par_seq_eq` is what upgrades it to all
schedules. -/
theorem Computes.parPair {α β : Type} {p : ParM α} {q : ParM β}
    {va : State → α} {vb : State → β} {F G : State → State}
    (hp : Computes p va F) (hq : Computes q vb G) :
    Computes (ParM.parPair p q) (fun σ => (va σ, vb (F σ))) (fun σ => G (F σ)) := by
  intro σ
  rw [runSeq_parPair_eq_seqPair]
  exact Computes.seqPair hp hq σ

/-- A `Computes` fact is exactly a `pure_eq_seq` statement about the final heap. -/
theorem Computes.state {α : Type} {p : ParM α} {val F} (h : Computes p val F) (σ : State) :
    (runSeq p σ).2 = F σ := by rw [h σ]

/-- **Two programs computing the same pure function are equivalent**, given well-formedness. This is
how a composed `Computes` proof discharges `seq = par` for a whole program with regions in it. -/
theorem parSeqEq_of_computes {α : Type} {p q : ParM α} {val F} (σ : State)
    (hp : Computes p val F) (hq : Computes q val F)
    (hwfp : WellFormed p σ) (hwfq : WellFormed q σ) : ParSeqEq p q σ :=
  parSeqEq_of_runSeq_eq p q σ hwfp hwfq (by rw [hp σ, hq σ])

end Paralever
