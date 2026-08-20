import Paralever.Core.Semantics

/-! # Footprints and independence

`accesses` is a reference interpreter (canonical left-to-right unfolding), not the operational
semantics — it exists to state `Indep` against. Rationale: `docs/access.md`.
-/

namespace Paralever

structure Footprint where
  reads  : List Loc
  writes : List Loc
  deriving Repr

namespace Footprint

def empty : Footprint := ⟨[], []⟩

@[simp, grind .]
def union (a b : Footprint) : Footprint := ⟨a.reads ++ b.reads, a.writes ++ b.writes⟩

instance : Union Footprint := ⟨union⟩

theorem union_assoc (a b c : Footprint) :
    Footprint.union (Footprint.union a b) c = Footprint.union a (Footprint.union b c) := by
  simp [Footprint.union, List.append_assoc]

theorem empty_union (f : Footprint) : Footprint.union Footprint.empty f = f := by
  simp [Footprint.union, Footprint.empty]

end Footprint

@[simp, grind .]
def Disjoint (a b : List Loc) : Prop := ∀ l, l ∈ a → l ∈ b → False

@[simp, grind .]
def disjointB (a b : List Loc) : Bool := a.all (fun l => !b.contains l)

theorem disjointB_iff (a b : List Loc) : disjointB a b = true ↔ Disjoint a b := by
  unfold disjointB Disjoint
  simp only [List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]

/-- Bernstein's conditions. Deliberately no `Disjoint f₁.reads f₂.reads` — shared reads are fine. -/
@[simp, grind .]
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads

@[simp, grind .]
def indepB (f₁ f₂ : Footprint) : Bool :=
  disjointB f₁.writes f₂.writes && disjointB f₁.writes f₂.reads && disjointB f₂.writes f₁.reads

theorem indepB_iff (f₁ f₂ : Footprint) : indepB f₁ f₂ = true ↔ Indep f₁ f₂ := by
  grind only [indepB, Indep, disjointB, Disjoint, = List.all_eq, = List.contains_eq_mem]

theorem Indep.symm {f₁ f₂ : Footprint} (h : Indep f₁ f₂) : Indep f₂ f₁ :=
  ⟨fun l hb ha => h.1 l ha hb, h.2.2, h.2.1⟩

/-! ### Reference execution and `accesses`

Total structural recursion: `ParM` has no `iter`, so every value is a finite tree, and each case
recurses into `p`, `q`, or a continuation applied to a value already in hand — the same pattern
`ParM.bind` uses. -/

/-- Canonical left-to-right sequential run: the reference execution `accesses` measures against.

Written with explicit `{τ}` (rather than reusing `α`/`β`/`γ`) so the recursive calls at the `par`
case — each instantiated at a *different* type (the left branch's, the right branch's, the
continuation's) — are unambiguous. -/
@[simp, grind .]
def runSeq {τ : Type} : ParM τ → State → τ × State
  | .pure a,      σ => (a, σ)
  | .read l k,    σ => runSeq (k (σ l)) σ
  | .write l v k, σ => runSeq (k ()) (σ.update l v)
  | .par p q k,   σ =>
      let (a, σ₁) := runSeq p σ
      let (b, σ₂) := runSeq q σ₁
      runSeq (k (a, b)) σ₂

/-- What `p` touches, referenced against the canonical sequential run. See `docs/access.md` for
why `q`'s branch is measured from `σ₁` rather than `σ`, and why that asymmetry vanishes under
`Indep`. -/
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
nodes nested *inside* `p` or `q` — see `docs/decomposition.md` for the counterexample. `WellFormed`
checks Bernstein independence at every `par` node in the tree, against the state that node sees
along the canonical run. Same recursion shape as `accesses`. -/
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

/-- `WellFormed (parPair p q) σ` is a 4-way nested conjunction with a trivial last conjunct —
`apply WellFormed_par_intro` turns it into exactly the two things worth proving: independence,
and each side's own well-formedness. -/
theorem WellFormed_par_intro {α β : Type} {p : ParM α} {q : ParM β} {σ : State}
    (hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2))
    (hp : WellFormed p σ) (hq : WellFormed q (runSeq p σ).2) :
    WellFormed (ParM.parPair p q) σ :=
  ⟨hindep, hp, hq, trivial⟩

end Paralever
