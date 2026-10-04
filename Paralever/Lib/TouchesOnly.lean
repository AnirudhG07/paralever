import Paralever.Pragma.ArrRef

/-! # Location predicates for range-based independence

Generic `InRange lo hi` and `TouchesOnly lo hi N` (data + scratch channel) — location predicates
that compose with `FootprintWithin`/`indep_of_footprint_within` to discharge Bernstein obligations
via `omega`. Extracted from `Examples/MergeSort.lean` where `TouchesOnly` was defined locally.

Rationale: `docs/theory.md` §9 — footprints confined to predicates. -/

namespace Paralever

-- ref: DPJ §4.2 — region-based disjointness for array parallelism

/-- Location `l` is in the half-open range `[lo, hi)`. -/
@[simp, grind .]
def InRange (lo hi : Nat) (l : Loc) : Prop := lo ≤ l ∧ l < hi

@[simp, grind .]
theorem InRange.disjoint {lo₁ hi₁ lo₂ hi₂ : Nat}
    (h : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁) {l : Loc}
    (h1 : InRange lo₁ hi₁ l) (h2 : InRange lo₂ hi₂ l) : False := by
  grind

@[simp, grind .]
theorem InRange.mono {lo lo' hi hi' : Nat} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    {l : Loc} (h : InRange lo hi l) : InRange lo' hi' l := by
  grind

theorem InRange.subset {lo lo' hi hi' : Nat} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    ∀ l, InRange lo hi l → InRange lo' hi' l := fun _ h => h.mono hlo hhi

/-- `ArrRef.InRange` is `InRange base (base + len)`. -/
@[simp, grind .]
theorem ArrRef.inRange_eq (a : ArrRef) :
    a.InRange = Paralever.InRange a.base (a.base + a.len) := by
  ext l; simp [ArrRef.InRange, Paralever.InRange]

/-- Location `l` is in the data range `[lo, hi)` or the scratch range `[N+lo, N+hi)`.
The standard pattern for divide-and-conquer with an auxiliary buffer (mergesort). -/
@[simp, grind .]
def TouchesOnly (lo hi N : Nat) (l : Loc) : Prop :=
  InRange lo hi l ∨ InRange (N + lo) (N + hi) l

@[simp, grind .]
theorem TouchesOnly.mono {lo hi lo' hi' N : Nat} (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
    {l : Loc} (h : TouchesOnly lo hi N l) : TouchesOnly lo' hi' N l := by
  grind

@[simp, grind .]
theorem TouchesOnly.disjoint {lo mid hi N : Nat} (hhN : hi ≤ N)
    {l : Loc} (h1 : TouchesOnly lo mid N l) (h2 : TouchesOnly mid hi N l) : False := by
  grind

/-- Two `InRange` predicates with non-overlapping ranges ⇒ `Indep`. -/
@[simp, grind .]
theorem indep_of_inRange {lo₁ hi₁ lo₂ hi₂ : Nat}
    {f g : Footprint}
    (hf : FootprintWithin f (Paralever.InRange lo₁ hi₁))
    (hg : FootprintWithin g (Paralever.InRange lo₂ hi₂))
    (hdisj : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁) :
    Indep f g :=
  indep_of_footprint_within hf hg (fun _ h1 h2 => InRange.disjoint hdisj h1 h2)

end Paralever
