import Paralever.Core.Semantics

/-! # Footprints and independence

`accesses` is a reference interpreter (canonical left-to-right unfolding), not the operational
semantics — it exists to state `Indep` against. Rationale: `docs/access.md`.
-/

namespace Paralever

/-- The set of locations a computation reads and the set it writes.

Lists rather than finite sets: every use is a membership or a disjointness check, so duplicates are
harmless, and concrete footprints stay `decide`-able. -/
structure Footprint where
  reads  : List Loc
  writes : List Loc
  deriving Repr

namespace Footprint

/-- Touches nothing. The footprint of `pure`. -/
def empty : Footprint := ⟨[], []⟩

/-- Everything either side touches. Reads and writes are combined componentwise. -/
@[simp, grind .]
def union (a b : Footprint) : Footprint := ⟨a.reads ++ b.reads, a.writes ++ b.writes⟩

/-- `∪` notation for `Footprint.union`. -/
instance : Union Footprint := ⟨union⟩

/-- `union` is associative, so a footprint fold needs no bracketing convention. -/
theorem union_assoc (a b c : Footprint) :
    Footprint.union (Footprint.union a b) c = Footprint.union a (Footprint.union b c) := by
  simp [Footprint.union, List.append_assoc]

/-- `empty` is a left unit. -/
theorem empty_union (f : Footprint) : Footprint.union Footprint.empty f = f := by
  simp [Footprint.union, Footprint.empty]

end Footprint

/-- No location lies in both lists. -/
@[simp, grind .]
def Disjoint (a b : List Loc) : Prop := ∀ l, l ∈ a → l ∈ b → False

/-- Decidable `Disjoint`. `Disjoint` is a `∀` with no `Decidable` instance, so concrete checks go
through this and `disjointB_iff`. -/
@[simp, grind .]
def disjointB (a b : List Loc) : Bool := a.all (fun l => !b.contains l)

/-- `disjointB` decides `Disjoint`. -/
theorem disjointB_iff (a b : List Loc) : disjointB a b = true ↔ Disjoint a b := by
  unfold disjointB Disjoint
  simp only [List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]

/-- **Bernstein's conditions**: two computations may run concurrently when neither writes what the
other touches. Three clauses, not four — there is deliberately no `Disjoint f₁.reads f₂.reads`,
because concurrent *reads* of the same cell are harmless. That omission is load-bearing: matrix
multiply writes disjoint output cells but reads overlapping rows and columns, so the stronger
`∗`-style disjointness would reject it. -- ref: Bernstein 1966; `docs/access.md` -/
@[simp, grind .]
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads

/-- Decidable `Indep` — the whole Bernstein check as one `Bool`, so a concrete obligation is
`(indepB_iff _ _).mp (by decide)`. -/
@[simp, grind .]
def indepB (f₁ f₂ : Footprint) : Bool :=
  disjointB f₁.writes f₂.writes && disjointB f₁.writes f₂.reads && disjointB f₂.writes f₁.reads

/-- `indepB` decides `Indep`. -/
theorem indepB_iff (f₁ f₂ : Footprint) : indepB f₁ f₂ = true ↔ Indep f₁ f₂ := by
  grind only [indepB, Indep, disjointB, Disjoint, = List.all_eq, = List.contains_eq_mem]

/-- **Bernstein from subsets.** The general move whenever writes are present: confine each side's
whole footprint to a set, show the two sets are disjoint. -/
theorem indep_of_footprint_subset {f g : Footprint} {A B : List Loc}
    (hfr : f.reads ⊆ A) (hfw : f.writes ⊆ A) (hgr : g.reads ⊆ B) (hgw : g.writes ⊆ B)
    (hAB : Disjoint A B) : Indep f g :=
  ⟨fun l h1 h2 => hAB l (hfw h1) (hgw h2),
   fun l h1 h2 => hAB l (hfw h1) (hgr h2),
   fun l h1 h2 => hAB l (hfr h2) (hgw h1)⟩

/-- **Componentwise containment.** `f` touches no more than `g` does, read-for-read and
write-for-write. This is what a *syntactic* footprint gives when the address is not known until the
run: not the exact set, but a bound. -/
def Footprint.Sub (f g : Footprint) : Prop := f.reads ⊆ g.reads ∧ f.writes ⊆ g.writes

namespace Footprint.Sub

theorem rfl' (f : Footprint) : f.Sub f := ⟨fun _ h => h, fun _ h => h⟩

theorem of_eq {f g : Footprint} (h : f = g) : f.Sub g := h ▸ rfl' f

theorem trans {f g h : Footprint} (hfg : f.Sub g) (hgh : g.Sub h) : f.Sub h :=
  ⟨fun _ m => hgh.1 (hfg.1 m), fun _ m => hgh.2 (hfg.2 m)⟩

/-- Either half of a union is bounded by it — the bound for a branch taken at run time. -/
theorem left (a b : Footprint) : a.Sub (Footprint.union a b) :=
  ⟨fun _ m => List.mem_append.mpr (Or.inl m), fun _ m => List.mem_append.mpr (Or.inl m)⟩

theorem right (a b : Footprint) : b.Sub (Footprint.union a b) :=
  ⟨fun _ m => List.mem_append.mpr (Or.inr m), fun _ m => List.mem_append.mpr (Or.inr m)⟩

/-- Bounds compose over `union`, which is what lets the bound be read off the syntax by a fold. -/
theorem union {a a' b b' : Footprint} (ha : a.Sub a') (hb : b.Sub b') :
    (Footprint.union a b).Sub (Footprint.union a' b') := by
  constructor
  · intro l m
    simp only [Footprint.union, List.mem_append] at m ⊢
    exact m.elim (fun h => Or.inl (ha.1 h)) (fun h => Or.inr (hb.1 h))
  · intro l m
    simp only [Footprint.union, List.mem_append] at m ⊢
    exact m.elim (fun h => Or.inl (ha.2 h)) (fun h => Or.inr (hb.2 h))
end Footprint.Sub

/-- Independence is preserved by shrinking either side — so checking Bernstein on *bounds* implies
it for the actual footprints. Load-bearing for data-dependent addressing: `Indep` has no `R∩R`
clause, so widening a read set can never manufacture a conflict that was not there. -/
theorem Indep.of_sub {f g f' g' : Footprint} (hf : f'.Sub f) (hg : g'.Sub g) (h : Indep f g) :
    Indep f' g' :=
  ⟨fun l h1 h2 => h.1 l (hf.2 h1) (hg.2 h2),
   fun l h1 h2 => h.2.1 l (hf.2 h1) (hg.1 h2),
   fun l h1 h2 => h.2.2 l (hg.2 h1) (hf.1 h2)⟩

/-- Nothing conflicts with a computation that touches nothing. -/
theorem Indep.empty_right (f : Footprint) : Indep f Footprint.empty :=
  ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
   fun _ h _ => (List.not_mem_nil h).elim⟩

/-- Independence does not depend on which branch you call left. -/
theorem Indep.symm {f₁ f₂ : Footprint} (h : Indep f₁ f₂) : Indep f₂ f₁ :=
  ⟨fun l hb ha => h.1 l ha hb, h.2.2, h.2.1⟩

/-! ### Reference execution and `accesses`

Both definitions below are total structural recursions: `ParM` has no `iter`, so every value is a
finite tree, and each case recurses into `p`, `q`, or a continuation applied to a value already in
hand — the same pattern `ParM.bind` uses. -/

mutual

/-- Run `p` from `σ` under the canonical left-to-right schedule, returning its result and the final
heap. This is the *reference* execution: `accesses` and `WellFormed` are stated against it, and
`wellFormed_canonical` proves every real interleaving of a well-formed program agrees with it. -/
@[simp, grind .]
def runSeq {τ : Type} : ParM τ → State → τ × State
  | .pure a,      σ => (a, σ)
  | .read l k,    σ => runSeq (k (σ l)) σ
  | .write l v k, σ => runSeq (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      runSeq (k r.1) r.2

/-- The children, left to right, threading the heap. The reference order a fork is measured against. -/
@[simp, grind .]
def runChilds {αs : List Type} : Childs ParM αs → State → Results αs × State
  | .nil,       σ => ((), σ)
  | .cons p ps, σ =>
      let r := runSeq p σ
      let r' := runChilds ps r.2
      ((r.1, r'.1), r'.2)

end

mutual

/-- Every location `p` reads or writes along the canonical run from `σ`.

A fold over the same tree `runSeq` walks, which is why it must carry a state: continuations are
functions, so you cannot see what comes after a `read` without supplying the value it returns. Each
child is measured from the heap the one before it left; `accesses_runSeq_isolated` shows that
staggering vanishes under independence. -/
@[simp, grind .]
def accesses {τ : Type} : ParM τ → State → Footprint
  | .pure _,      _ => .empty
  | .read l k,    σ => Footprint.union ⟨[l], []⟩ (accesses (k (σ l)) σ)
  | .write l v k, σ => Footprint.union ⟨[], [l]⟩ (accesses (k ()) (σ.update l v))
  | .par cs k,    σ =>
      let r := runChilds cs σ
      Footprint.union (accessesChilds cs σ) (accesses (k r.1) r.2)

/-- The children's combined footprint, each measured from the heap the one before it left. -/
@[simp, grind .]
def accessesChilds {αs : List Type} : Childs ParM αs → State → Footprint
  | .nil,       _ => .empty
  | .cons p ps, σ => Footprint.union (accesses p σ) (accessesChilds ps (runSeq p σ).2)

end

/-- Each child's footprint **on its own**, measured from the heap the one before it left. What the
all-pairs independence check ranges over. -/
@[simp, grind .]
def childFootprints {αs : List Type} : Childs ParM αs → State → List Footprint
  | .nil,       _ => []
  | .cons p ps, σ => accesses p σ :: childFootprints ps (runSeq p σ).2

/-! ### `WellFormed`

The real per-program obligation: Bernstein at *every* `par` node, each against the heap that node
sees along the canonical run. The outermost check alone is unsound — `docs/decomposition.md` has the
counterexample. -/
/-- **Bernstein between every pair of children.** The N-ary independence obligation, stated flatly
rather than spread over nesting levels. -/
@[simp, grind .]
def IndepAll : List Footprint → Prop
  | []      => True
  | f :: fs => (∀ g ∈ fs, Indep f g) ∧ IndepAll fs

/-- Decidable `IndepAll`. -/
@[simp, grind .]
def indepAllB : List Footprint → Bool
  | []      => true
  | f :: fs => fs.all (fun g => indepB f g) && indepAllB fs

theorem indepAllB_iff (fs : List Footprint) : indepAllB fs = true ↔ IndepAll fs := by
  induction fs with
  | nil => simp [indepAllB, IndepAll]
  | cons f fs ih =>
      simp only [indepAllB, IndepAll, Bool.and_eq_true, List.all_eq_true, ih, indepB_iff]

mutual

/-- Bernstein independence checked at *every* `par` node, each against the heap that node sees along
the canonical run. The outermost check alone would be unsound — `docs/decomposition.md` has the
counterexample. -/
@[simp, grind .]
def WellFormed {τ : Type} : ParM τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormed (k (σ l)) σ
  | .write l v k, σ => WellFormed (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      IndepAll (childFootprints cs σ) ∧ WellFormedChilds cs σ ∧ WellFormed (k r.1) r.2

/-- Every child is itself well-formed, from the heap the one before it left. -/
@[simp, grind .]
def WellFormedChilds {αs : List Type} : Childs ParM αs → State → Prop
  | .nil,       _ => True
  | .cons p ps, σ => WellFormed p σ ∧ WellFormedChilds ps (runSeq p σ).2

end

/-- Build `WellFormed (parPair p q) σ` from the three facts that actually need proving. The goal is
a conjunction whose last component is trivial for `parPair`'s `pure` continuation; this hides that
bookkeeping. -/
theorem WellFormed_par_intro {α β : Type} {p : ParM α} {q : ParM β} {σ : State}
    (hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2))
    (hp : WellFormed p σ) (hq : WellFormed q (runSeq p σ).2) :
    WellFormed (ParM.parPair p q) σ := by
  refine ⟨?_, ⟨hp, hq, trivial⟩, trivial⟩
  show IndepAll [accesses p σ, accesses q (runSeq p σ).2]
  refine ⟨?_, ?_, trivial⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    exact hg ▸ hindep
  · intro g hg
    simp at hg

end Paralever
