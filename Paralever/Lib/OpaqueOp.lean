import Paralever.Lib.Notation

/-! # Opaque operations — declared footprint, derived not assumed

For parallelism whose bodies are too complex (or too external) to induct over: model only the
interface, `reads R / writes W / net effect f`. The footprint is then a *theorem*
(`opaqueOp_accesses`), not an annotation, because `f` is an ordinary pure function and pure
functions have no footprint.

Rationale: `docs/opaque-ops.md`. -/

namespace Paralever

-- ref: docs/opaque-ops.md; DPJ OOPSLA'09 §2-3 (region declarations, effect over-approximation)

/-! ### Building blocks -/

/-- Read every location in order, collecting the values. -/
def readAll : List Loc → ParM (List Val)
  | []      => .pure []
  | l :: ls => .read l (fun v => ParM.bind (readAll ls) (fun vs => .pure (v :: vs)))

/-- Write each `(location, value)` pair in order. -/
def writeAll : List (Loc × Val) → ParM Unit
  | []           => .pure ()
  | (l, v) :: ps => .write l v (fun _ => writeAll ps)

/-- An operation over a *declared* footprint: reads exactly `R`, writes within `W`, with net effect
given by the pure function `f`. `f` is never inspected — it may be arbitrarily complex. -/
def opaqueOp (R W : List Loc) (f : List Val → List Val) : ParM Unit :=
  ParM.bind (readAll R) (fun vs => writeAll (W.zip (f vs)))

/-! ### Footprints of the building blocks — state-independent, hence usable at any `σ` -/

@[simp, grind .]
theorem readAll_accesses (R : List Loc) (σ : State) :
    accesses (readAll R) σ = ⟨R, []⟩ := by
  induction R generalizing σ with
  | nil => rfl
  | cons l ls ih =>
      simp only [readAll, accesses, accesses_bind, Footprint.union]
      rw [ih]; simp [accesses, Footprint.empty]

@[simp, grind .]
theorem writeAll_accesses (ps : List (Loc × Val)) (σ : State) :
    accesses (writeAll ps) σ = ⟨[], ps.map Prod.fst⟩ := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨l, v⟩ := p
      simp only [writeAll, accesses, Footprint.union]
      rw [ih]; simp

@[simp, grind .]
theorem readAll_wellformed (R : List Loc) (σ : State) : WellFormed (readAll R) σ := by
  induction R generalizing σ with
  | nil => trivial
  | cons l ls ih =>
      simp only [readAll, WellFormed]
      rw [WellFormed_bind]; exact ⟨ih σ, trivial⟩

@[simp, grind .]
theorem writeAll_wellformed (ps : List (Loc × Val)) (σ : State) :
    WellFormed (writeAll ps) σ := by
  induction ps generalizing σ with
  | nil => trivial
  | cons p ps ih => obtain ⟨l, v⟩ := p; simp only [writeAll, WellFormed]; exact ih _

/-- `zip` can only shorten, so the locations actually written are a sub-list of `W`. This is why
`opaqueOp`'s writes are `⊆ W` rather than `= W` — the sound direction, see `docs/opaque-ops.md`. -/
@[grind .]
theorem zip_fst_subset (W : List Loc) (vals : List Val) :
    ∀ l ∈ (W.zip vals).map Prod.fst, l ∈ W := by
  induction W generalizing vals with
  | nil => simp
  | cons w ws ih =>
      cases vals with
      | nil => simp
      | cons v vs =>
          intro l hl
          simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hl
          rcases hl with h | h
          · exact h ▸ List.mem_cons_self
          · exact List.mem_cons_of_mem w (ih vs l h)

/-! ### The declared footprint is the real one -/

@[simp, grind .]
theorem opaqueOp_wellformed (R W : List Loc) (f : List Val → List Val) (σ : State) :
    WellFormed (opaqueOp R W f) σ := by
  simp only [opaqueOp]
  rw [WellFormed_bind]
  exact ⟨readAll_wellformed R σ, writeAll_wellformed _ _⟩

/-- Reads are exactly `R`; writes lie within `W`. Proved, not assumed — this is the whole point
of the construction. -/
@[grind .]
theorem opaqueOp_accesses (R W : List Loc) (f : List Val → List Val) (σ : State) :
    (accesses (opaqueOp R W f) σ).reads = R ∧
    ∀ l ∈ (accesses (opaqueOp R W f) σ).writes, l ∈ W := by
  simp only [opaqueOp, accesses_bind, Footprint.union]
  rw [readAll_accesses, writeAll_accesses]
  refine ⟨by simp, ?_⟩
  intro l hl
  simp only [List.nil_append] at hl
  exact zip_fst_subset W _ l hl

@[grind .]
theorem opaqueOp_reads (R W : List Loc) (f : List Val → List Val) (σ : State) :
    (accesses (opaqueOp R W f) σ).reads = R := (opaqueOp_accesses R W f σ).1

@[grind .]
theorem opaqueOp_writes_subset (R W : List Loc) (f : List Val → List Val) (σ : State) :
    ∀ l ∈ (accesses (opaqueOp R W f) σ).writes, l ∈ W := (opaqueOp_accesses R W f σ).2

/-! ### Independence from the declared footprints alone

Stated at two *separate* states: `opaqueOp`'s footprint does not depend on `σ`, so the caller never
has to reconcile "measured from `σ`" with "measured from `(runSeq p σ).2`". -/

/-- Bernstein independence between two opaque ops, decided entirely by their declared `R`/`W` —
`f` and `g` are never mentioned. -/
@[grind .]
theorem opaqueOp_indep (R₁ W₁ R₂ W₂ : List Loc) (f g : List Val → List Val) (σ₁ σ₂ : State)
    (hww : Disjoint W₁ W₂) (hwr : Disjoint W₁ R₂) (hrw : Disjoint W₂ R₁) :
    Indep (accesses (opaqueOp R₁ W₁ f) σ₁) (accesses (opaqueOp R₂ W₂ g) σ₂) := by
  obtain ⟨hr1, hw1⟩ := opaqueOp_accesses R₁ W₁ f σ₁
  obtain ⟨hr2, hw2⟩ := opaqueOp_accesses R₂ W₂ g σ₂
  refine ⟨?_, ?_, ?_⟩
  · intro l h1 h2; exact hww l (hw1 l h1) (hw2 l h2)
  · intro l h1 h2; rw [hr2] at h2; exact hwr l (hw1 l h1) h2
  · intro l h1 h2; rw [hr1] at h2; exact hrw l (hw2 l h1) h2

/-! ### User-facing: the smart constructor and the one-shot theorem -/

/-- Build `Independent` from declared footprints alone. The bodies `f`, `g` are universally
quantified — the theorem holds for every pair of pure functions. -/
@[grind .]
theorem Independent.of_declared_footprint (R₁ W₁ R₂ W₂ : List Loc)
    (f g : List Val → List Val) (σ : State)
    (hww : Disjoint W₁ W₂) (hwr : Disjoint W₁ R₂) (hrw : Disjoint W₂ R₁) :
    Independent (opaqueOp R₁ W₁ f) (opaqueOp R₂ W₂ g) σ :=
  ⟨opaqueOp_wellformed R₁ W₁ f σ, opaqueOp_wellformed R₂ W₂ g _,
   opaqueOp_indep R₁ W₁ R₂ W₂ f g σ _ hww hwr hrw⟩

/-- **The payoff**: two arbitrarily complex computations on declared non-conflicting footprints run
in parallel exactly as they do in sequence. Three `Disjoint` facts on the declared location lists
and nothing else. -/
@[grind .]
theorem opaqueOp_par_seq_eq (R₁ W₁ R₂ W₂ : List Loc) (f g : List Val → List Val) (σ : State)
    (hww : Disjoint W₁ W₂) (hwr : Disjoint W₁ R₂) (hrw : Disjoint W₂ R₁) :
    ParM.parPair (opaqueOp R₁ W₁ f) (opaqueOp R₂ W₂ g)
      ∥≡ ParM.seqPair (opaqueOp R₁ W₁ f) (opaqueOp R₂ W₂ g) from σ :=
  (Independent.of_declared_footprint R₁ W₁ R₂ W₂ f g σ hww hwr hrw).par_seq_eq

end Paralever
