import Paralever.Lib.ArrRef

/-! # Location predicates for range-based independence

Generic `InRange lo hi` and `TouchesOnly lo hi N` (data + scratch channel) — location predicates
that compose with `FootprintWithin`/`indep_of_footprint_within` to discharge Bernstein obligations
via `omega`. Extracted from `Examples/Programs/MergeSort.lean` where `TouchesOnly` was defined locally.

Rationale: `docs/theory.md` §9 — footprints confined to predicates. -/

namespace Paralever

-- ref: DPJ §4.2 — region-based disjointness for array parallelism

/-- The locations of the half-open range `[lo, hi)`, as a predicate on `Loc` rather than a list, so it
plugs straight into `FootprintWithin` and composes under `omega`. -/
@[simp, grind .]
def InRange (lo hi : Nat) (l : Loc) : Prop := lo ≤ l ∧ l < hi

/-- Non-overlapping ranges share no location. The premise is the arithmetic side condition an example
discharges by `omega`; everything else about independence is downstream of it. -/
@[simp, grind .]
theorem InRange.disjoint {lo₁ hi₁ lo₂ hi₂ : Nat}
    (h : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁) {l : Loc}
    (h1 : InRange lo₁ hi₁ l) (h2 : InRange lo₂ hi₂ l) : False := by
  grind

/-- A location in `[lo, hi)` is in any wider range — how a recursive call's bound is weakened to its
parent's. -/
@[simp, grind .]
theorem InRange.mono {lo lo' hi hi' : Nat} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    {l : Loc} (h : InRange lo hi l) : InRange lo' hi' l := by
  grind

/-- `InRange.mono` as a pointwise implication, which is the form `ReadsWithin.mono` and friends
expect. -/
theorem InRange.subset {lo lo' hi hi' : Nat} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    ∀ l, InRange lo hi l → InRange lo' hi' l := fun _ h => h.mono hlo hhi

/-- An `ArrRef`'s own location predicate is the generic one on its endpoints, so `ArrRef`-shaped and
range-shaped bounds are interchangeable. -/
@[simp, grind .]
theorem ArrRef.inRange_eq (a : ArrRef) :
    a.InRange = Paralever.InRange a.base (a.base + a.len) := by
  ext l; simp [ArrRef.InRange, Paralever.InRange]

/-- The locations of the data range `[lo, hi)` together with its mirror image in the scratch buffer,
`[N+lo, N+hi)`. A divide-and-conquer function with an auxiliary buffer of the same size `N` touches
exactly this pair of ranges, and the index `i` and its scratch cell `N+i` stay in lockstep — which is
what makes the halves of a recursive split disjoint on both channels at once. -/
@[simp, grind .]
def TouchesOnly (lo hi N : Nat) (l : Loc) : Prop :=
  InRange lo hi l ∨ InRange (N + lo) (N + hi) l

/-- Widening the data range widens both channels, since the scratch range is its translate. -/
@[simp, grind .]
theorem TouchesOnly.mono {lo hi lo' hi' N : Nat} (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
    {l : Loc} (h : TouchesOnly lo hi N l) : TouchesOnly lo' hi' N l := by
  grind

/-- **Adjacent halves of a split touch no common location**, scratch channels included. `hi ≤ N` is
what keeps the data and scratch ranges from colliding, and without it a sufficiently high index would
land inside the buffer. This single lemma is the independence argument for recursive mergesort — see
`Examples/Programs/MergeSort.lean`. -/
@[simp, grind .]
theorem TouchesOnly.disjoint {lo mid hi N : Nat} (hhN : hi ≤ N)
    {l : Loc} (h1 : TouchesOnly lo mid N l) (h2 : TouchesOnly mid hi N l) : False := by
  grind

/-- Two footprints confined to non-overlapping ranges are Bernstein-independent — the common case
packaged so an example supplies two confinement proofs and one `omega`. -/
@[simp, grind .]
theorem indep_of_inRange {lo₁ hi₁ lo₂ hi₂ : Nat}
    {f g : Footprint}
    (hf : FootprintWithin f (Paralever.InRange lo₁ hi₁))
    (hg : FootprintWithin g (Paralever.InRange lo₂ hi₂))
    (hdisj : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁) :
    Indep f g :=
  indep_of_footprint_within hf hg (fun _ h1 h2 => InRange.disjoint hdisj h1 h2)

end Paralever
