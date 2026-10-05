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

/-- A named view into the heap covering the `len` consecutive locations `[base, base+len)`. Not a
container: it holds no elements, only the address range, and the values live in the `State` as
always. -/
structure ArrRef where
  base : Loc
  len  : Nat

/-- The `Loc` of index `i` in `a` — the one piece of address arithmetic every example otherwise
does by hand. -/
def ArrRef.loc (a : ArrRef) (i : Nat) : Loc := a.base + i

/-- `l` lies in `a`'s range. A `Loc → Prop`, so it is exactly the shape
`FootprintWithin`/`ReadsWithin`/`WritesWithin` take — this is what makes `ArrRef` plug into
`Theory/Intervals.lean` with no glue. -/
def ArrRef.InRange (a : ArrRef) (l : Loc) : Prop := a.base ≤ l ∧ l < a.base + a.len

/-- An in-bounds index addresses a location in range. -/
@[simp, grind .]
theorem ArrRef.loc_mem (a : ArrRef) {i : Nat} (hi : i < a.len) : a.InRange (a.loc i) := by
  unfold ArrRef.loc ArrRef.InRange; grind

/-- The sub-range `[lo, hi)` of `a` as an `ArrRef` in its own right, so two halves of one backing
array (`MergeSort.lean`'s `[lo,mid)`/`[mid,hi)`) are two `ArrRef`s and `disjoint_of_range` applies to
them unchanged. -/
def ArrRef.slice (a : ArrRef) (lo hi : Nat) : ArrRef := ⟨a.base + lo, hi - lo⟩

/-- A slice's locations are the parent's — `FootprintWithin.mono`'s hypothesis for lifting a bound on
a slice to a bound on the whole array. -/
@[simp, grind .]
theorem ArrRef.slice_inRange {a : ArrRef} {lo hi : Nat} (hle : hi ≤ a.len) {l : Loc}
    (h : (a.slice lo hi).InRange l) : a.InRange l := by
  unfold ArrRef.slice ArrRef.InRange at *
  grind

/-- **Non-overlapping ranges share no location.** `a` entirely before `b` or `b` entirely before `a`
is all it takes, and that is one `omega` on the four constants `a.base`, `a.len`, `b.base`, `b.len` —
no reasoning about which indices are actually touched inside either.

This is the disjointness hypothesis `indep_of_footprint_within`/`indep_of_read_write_confined` want,
so it is the last step of almost every array example's independence proof. -/
@[simp, grind .]
theorem ArrRef.disjoint_of_range {a b : ArrRef}
    (h : a.base + a.len ≤ b.base ∨ b.base + b.len ≤ a.base) :
    ∀ l, a.InRange l → b.InRange l → False := by
  unfold ArrRef.InRange at *; grind

namespace ArrM

/-- Read index `i` of `a`, returning its value. No bounds check: an out-of-range `i` addresses
`a.base + i` like any other location, and it is the confinement lemmas below that require `i < a.len`.
-/
def get (a : ArrRef) (i : Nat) : ParM Val := .read (a.loc i) .pure

/-- Write `v` to index `i` of `a`. -/
def set (a : ArrRef) (i : Nat) (v : Val) : ParM Unit := .write (a.loc i) v .pure

/-- A `get` reads exactly one location and writes none. -/
@[simp, grind .]
theorem get_accesses (a : ArrRef) (i : Nat) (σ : State) :
    accesses (get a i) σ = ⟨[a.loc i], []⟩ := rfl

/-- A `set` writes exactly one location and reads none. -/
@[simp, grind .]
theorem set_accesses (a : ArrRef) (i : Nat) (v : Val) (σ : State) :
    accesses (set a i v) σ = ⟨[], [a.loc i]⟩ := rfl

/-- A `get` has no `par` node, so it is well-formed. -/
@[simp, grind .]
theorem get_wellformed (a : ArrRef) (i : Nat) (σ : State) : WellFormed (get a i) σ := trivial

/-- A `set` has no `par` node, so it is well-formed. -/
@[simp, grind .]
theorem set_wellformed (a : ArrRef) (i : Nat) (v : Val) (σ : State) :
    WellFormed (set a i v) σ := trivial

/-- An in-bounds `get` stays inside `a`'s range. The leaf case of every footprint-confinement
induction over a program built from `ArrM`. -/
@[simp, grind .]
theorem get_footprintWithin (a : ArrRef) {i : Nat} (hi : i < a.len) (σ : State) :
    FootprintWithin (accesses (get a i) σ) a.InRange := by
  rw [get_accesses]; exact FootprintWithin.read _ _ (a.loc_mem hi)

/-- An in-bounds `set` stays inside `a`'s range. -/
@[simp, grind .]
theorem set_footprintWithin (a : ArrRef) {i : Nat} (hi : i < a.len) (v : Val) (σ : State) :
    FootprintWithin (accesses (set a i v) σ) a.InRange := by
  rw [set_accesses]; exact FootprintWithin.write _ _ (a.loc_mem hi)

end ArrM

/-! ### Binary array independence — the "two programs on disjoint arrays" one-shot -/

-- ref: Apt & Olderog §3.2 — parallel composition rule for disjoint variables

/-- **Two programs confined to disjoint arrays are parallel-sequential equivalent.** The caller
supplies each side's well-formedness, each side's confinement to one `ArrRef`, and range
disjointness — that last one `omega`. No `Indep` to assemble by hand.

Requires reads *and* writes inside the respective arrays, so it rejects shared reads;
`par_seq_eq_of_disjoint_writes` is the Bernstein-strength version. -/
@[simp, grind .]
theorem par_seq_eq_of_disjoint_arrefs {α β : Type} (a b : ArrRef) (p : ParM α) (q : ParM β) (σ : State)
    (hp_wf : WellFormed p σ) (hq_wf : WellFormed q (runSeq p σ).2)
    (hp : FootprintWithin (accesses p σ) a.InRange)
    (hq : FootprintWithin (accesses q (runSeq p σ).2) b.InRange)
    (hdisj : a.base + a.len ≤ b.base ∨ b.base + b.len ≤ a.base) :
    ParSeqEq (ParM.parPair p q) (ParM.seqPair p q) σ :=
  par_seq_eq p q σ (WellFormed_par_intro
    (indep_of_footprint_within hp hq (ArrRef.disjoint_of_range hdisj)) hp_wf hq_wf)

/-- **Shared reads allowed**: the two sides may read anywhere, as long as their *writes* live in
disjoint arrays and neither writes what the other reads. Bernstein in `ArrRef` form — the cross
read/write conditions (`hp_wr`, `hq_wr`) stay explicit because reads are unconfined here, so only
write/write reduces to a range comparison. -/
@[simp, grind .]
theorem par_seq_eq_of_disjoint_writes {α β : Type} (wa wb : ArrRef) (p : ParM α) (q : ParM β) (σ : State)
    (hp_wf : WellFormed p σ) (hq_wf : WellFormed q (runSeq p σ).2)
    (hp_w : WritesWithin (accesses p σ) wa.InRange)
    (hq_w : WritesWithin (accesses q (runSeq p σ).2) wb.InRange)
    (hp_wr : Disjoint (accesses p σ).writes (accesses q (runSeq p σ).2).reads)
    (hq_wr : Disjoint (accesses q (runSeq p σ).2).writes (accesses p σ).reads)
    (hdisj : wa.base + wa.len ≤ wb.base ∨ wb.base + wb.len ≤ wa.base) :
    ParSeqEq (ParM.parPair p q) (ParM.seqPair p q) σ :=
  par_seq_eq p q σ (WellFormed_par_intro
    ⟨fun l h1 h2 => ArrRef.disjoint_of_range hdisj l (hp_w l h1) (hq_w l h2), hp_wr, hq_wr⟩
    hp_wf hq_wf)

end Paralever
