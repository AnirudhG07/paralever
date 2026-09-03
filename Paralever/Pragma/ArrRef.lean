import Paralever.Theory.Intervals

/-! # `ArrRef` — array-shaped locations, instead of bare `Loc`

`ParM`'s only primitives are `.read`/`.write` at a raw `Loc := Nat`. Every example so far computes
addresses by hand (`i*n+k`) and re-derives its own footprint-bound induction. `ArrRef` is the
missing layer between "bare heap address" and "your actual array": once locations are always
`a.loc i` for a named `a : ArrRef`, two facts become *generic*, proved once here instead of
per-example:

1. `ArrM.get`/`ArrM.set`'s footprint is always exactly `{a.loc i}`, confined to `a.InRange`
   (`ArrM.get_footprintWithin`/`.set_footprintWithin`) — feeds straight into
   `Theory/Intervals.lean`'s `FootprintWithin` combinators.
2. Two `ArrRef`s (or two slices of the same one — `MergeSort.lean`'s data/scratch channels, or its
   own `[lo,mid)`/`[mid,hi)` split) with non-overlapping `[base,base+len)` ranges are automatically
   independent, no matter what indices inside each are actually touched
   (`ArrRef.disjoint_of_range`) — one `omega` call on the two pairs of constants, not a bespoke
   induction re-deriving the same fact every time.

Composing `ArrM.get`/`.set` into a larger program (loops, recursion) still needs its own structural
induction to bound *that* program's footprint — `ArrRef` doesn't eliminate that, only the address
arithmetic and the disjointness step at the end of it. -/

namespace Paralever
open Paralever

/-- A named, bounds-checked view into the heap: `base` locations `[base, base+len)`. -/
structure ArrRef where
  base : Loc
  len  : Nat

/-- The `Loc` of index `i` in `a` — the one piece of address arithmetic every example otherwise
does by hand. -/
def ArrRef.loc (a : ArrRef) (i : Nat) : Loc := a.base + i

/-- `l` is one of `a`'s locations — a location predicate, so it plugs directly into
`FootprintWithin`/`ReadsWithin`/`WritesWithin`. -/
def ArrRef.InRange (a : ArrRef) (l : Loc) : Prop := a.base ≤ l ∧ l < a.base + a.len

theorem ArrRef.loc_mem (a : ArrRef) {i : Nat} (hi : i < a.len) : a.InRange (a.loc i) := by
  unfold ArrRef.loc ArrRef.InRange; grind

/-- A contiguous sub-range `[lo,hi)` of `a`, as its own `ArrRef` — e.g. `MergeSort.lean`'s left/
right halves of one backing array. -/
def ArrRef.slice (a : ArrRef) (lo hi : Nat) : ArrRef := ⟨a.base + lo, hi - lo⟩

theorem ArrRef.slice_inRange {a : ArrRef} {lo hi : Nat} (hle : hi ≤ a.len) {l : Loc}
    (h : (a.slice lo hi).InRange l) : a.InRange l := by
  unfold ArrRef.slice ArrRef.InRange at *
  grind

/-- Two `ArrRef`s (or two slices of one) whose ranges don't overlap never share a location — the
one fact `indep_of_footprint_within`/`indep_of_read_write_confined` need, reduced to `omega` on
the four constants `a.base`, `a.len`, `b.base`, `b.len` instead of a bespoke argument about
whatever indices happen to be touched inside each. -/
theorem ArrRef.disjoint_of_range {a b : ArrRef}
    (h : a.base + a.len ≤ b.base ∨ b.base + b.len ≤ a.base) :
    ∀ l, a.InRange l → b.InRange l → False := by
  unfold ArrRef.InRange at *; grind

namespace ArrM

/-- Read index `i` of `a`. -/
def get (a : ArrRef) (i : Nat) : ParM Val := .read (a.loc i) .pure

/-- Write `v` to index `i` of `a`. -/
def set (a : ArrRef) (i : Nat) (v : Val) : ParM Unit := .write (a.loc i) v .pure

theorem get_accesses (a : ArrRef) (i : Nat) (σ : State) :
    accesses (get a i) σ = ⟨[a.loc i], []⟩ := rfl

theorem set_accesses (a : ArrRef) (i : Nat) (v : Val) (σ : State) :
    accesses (set a i v) σ = ⟨[], [a.loc i]⟩ := rfl

theorem get_wellformed (a : ArrRef) (i : Nat) (σ : State) : WellFormed (get a i) σ := trivial

theorem set_wellformed (a : ArrRef) (i : Nat) (v : Val) (σ : State) :
    WellFormed (set a i v) σ := trivial

/-- `get`'s footprint is confined to `a.InRange`, given `i` is in bounds. -/
theorem get_footprintWithin (a : ArrRef) {i : Nat} (hi : i < a.len) (σ : State) :
    FootprintWithin (accesses (get a i) σ) a.InRange := by
  rw [get_accesses]; exact FootprintWithin.read _ _ (a.loc_mem hi)

/-- `set`'s footprint is confined to `a.InRange`, given `i` is in bounds. -/
theorem set_footprintWithin (a : ArrRef) {i : Nat} (hi : i < a.len) (v : Val) (σ : State) :
    FootprintWithin (accesses (set a i v) σ) a.InRange := by
  rw [set_accesses]; exact FootprintWithin.write _ _ (a.loc_mem hi)

end ArrM
end Paralever
