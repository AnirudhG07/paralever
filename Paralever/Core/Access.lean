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

/-- Independence does not depend on which branch you call left. -/
theorem Indep.symm {f₁ f₂ : Footprint} (h : Indep f₁ f₂) : Indep f₂ f₁ :=
  ⟨fun l hb ha => h.1 l ha hb, h.2.2, h.2.1⟩

/-! ### Reference execution and `accesses`

Both definitions below are total structural recursions: `ParM` has no `iter`, so every value is a
finite tree, and each case recurses into `p`, `q`, or a continuation applied to a value already in
hand — the same pattern `ParM.bind` uses. -/

/-- Run `p` from `σ` under the canonical left-to-right schedule, returning its result and the final
heap. This is the *reference* execution: `accesses` and `WellFormed` are stated against it, and
`wellFormed_canonical` proves every real interleaving of a well-formed program agrees with it.

Written with an explicit `{τ}` rather than reusing `α`/`β`/`γ` so that the three recursive calls in
the `par` case — left branch, right branch, continuation, each at a different type — are
unambiguous. -/
@[simp, grind .]
def runSeq {τ : Type} : ParM τ → State → τ × State
  | .pure a,      σ => (a, σ)
  | .read l k,    σ => runSeq (k (σ l)) σ
  | .write l v k, σ => runSeq (k ()) (σ.update l v)
  | .par p q k,   σ =>
      let (a, σ₁) := runSeq p σ
      let (b, σ₂) := runSeq q σ₁
      runSeq (k (a, b)) σ₂

/-- Every location `p` reads or writes along the canonical run from `σ`.

A fold over the same tree `runSeq` walks, which is why it must carry a state: continuations are
functions, so you cannot see what comes after a `read` without supplying the value it returns. Note
the asymmetry in the `par` case: `q`'s branch is measured from `σ₁`, the heap after `p`, not from
`σ`. `accesses_runSeq_isolated` shows that asymmetry vanishes under `Indep`; `docs/access.md` says
why it is there at all. -/
@[simp, grind .]
def accesses {τ : Type} : ParM τ → State → Footprint
  | .pure _,      _ => .empty
  | .read l k,    σ => Footprint.union ⟨[l], []⟩ (accesses (k (σ l)) σ)
  | .write l v k, σ => Footprint.union ⟨[], [l]⟩ (accesses (k ()) (σ.update l v))
  | .par p q k,   σ =>
      let (a, σ₁) := runSeq p σ
      let (b, σ₂) := runSeq q σ₁
      Footprint.union (accesses p σ) (Footprint.union (accesses q σ₁) (accesses (k (a, b)) σ₂))

/-! ### `WellFormed`

The real per-program obligation. Top-level `Indep` between `p` and `q` says nothing about `par`
nodes nested *inside* `p` or `q` — `docs/decomposition.md` has the counterexample showing the
outermost check alone is unsound. `WellFormed` therefore checks Bernstein independence at *every*
`par` node in the tree, each against the heap that node sees along the canonical run. Same recursion
shape as `accesses`. -/
@[simp, grind .]
def WellFormed {τ : Type} : ParM τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormed (k (σ l)) σ
  | .write l v k, σ => WellFormed (k ()) (σ.update l v)
  | .par p q k,   σ =>
      let (a, σ₁) := runSeq p σ
      let (b, σ₂) := runSeq q σ₁
      Indep (accesses p σ) (accesses q σ₁) ∧ WellFormed p σ ∧ WellFormed q σ₁ ∧
      WellFormed (k (a, b)) σ₂

/-- Build `WellFormed (parPair p q) σ` from the three facts that actually need proving. The goal is
a four-way conjunction whose last component is trivial for `parPair`'s `pure` continuation; this
hides that bookkeeping. -/
theorem WellFormed_par_intro {α β : Type} {p : ParM α} {q : ParM β} {σ : State}
    (hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2))
    (hp : WellFormed p σ) (hq : WellFormed q (runSeq p σ).2) :
    WellFormed (ParM.parPair p q) σ :=
  ⟨hindep, hp, hq, trivial⟩

end Paralever
