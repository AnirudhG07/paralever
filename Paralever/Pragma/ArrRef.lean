import Paralever.Theory.Intervals

/-! # `ArrRef` — array-shaped locations, instead of bare `Loc`

The layer between a raw `Loc` and your actual array. Two facts become generic, proved once here:
`ArrM.get`/`.set`'s footprint is exactly `{a.loc i}` confined to `a.InRange`, and two non-overlapping
`ArrRef`s are independent whatever indices they touch (`disjoint_of_range`) — one `omega` on four
constants instead of a bespoke induction.

Composing them into loops or recursion still needs that program's own footprint bound; `ArrRef` only
removes the address arithmetic and the final disjointness step. -/

namespace Paralever
open Paralever

/-- The `len` consecutive locations `[base, base+len)`. Not a container: values live in the
`State`. -/
structure ArrRef where
  base : Loc
  len  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The `Loc` of index `i` in `a`. -/
def ArrRef.loc (a : ArrRef) (i : Nat) : Loc := a.base + i

/-- `l` lies in `a`'s range. A `Loc → Prop`, the shape `FootprintWithin` takes. -/
def ArrRef.InRange (a : ArrRef) (l : Loc) : Prop := a.base ≤ l ∧ l < a.base + a.len

/-- An in-bounds index addresses a location in range. -/
@[simp, grind .]
theorem ArrRef.loc_mem (a : ArrRef) {i : Nat} (hi : i < a.len) : a.InRange (a.loc i) := by
  unfold ArrRef.loc ArrRef.InRange; grind

/-- Every cell of `a` — the bound a data-dependent index gets, since which cell is unknown
statically. -- ref: `docs/block-ir.md` -/
def ArrRef.cells (a : ArrRef) : List Loc :=
  (List.range (max a.len 1)).map (fun i => a.base + i)

/-- **Confined to its array by construction**: the index wraps, so `addr_mem_cells` needs no
hypothesis — unlike a raw `store l` (`Examples/Pointers.lean`). -/
def ArrRef.addr (a : ArrRef) (i : Int) : Loc := a.base + i.toNat % max a.len 1

/-- `addr` lands in `cells`, for every index. -/
theorem ArrRef.addr_mem_cells (a : ArrRef) (i : Int) : a.addr i ∈ a.cells := by
  unfold ArrRef.addr ArrRef.cells
  exact List.mem_map.mpr ⟨i.toNat % max a.len 1,
    List.mem_range.mpr (Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))),
    rfl⟩

/-- …and inside the range when the array is non-empty. -/
theorem ArrRef.addr_inRange (a : ArrRef) (h : 0 < a.len) (i : Int) : a.InRange (a.addr i) := by
  unfold ArrRef.addr ArrRef.InRange
  have : max a.len 1 = a.len := Nat.max_eq_left h
  rw [this]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mod_lt _ h) a.base⟩

/-- The sub-range `[lo, hi)` as an `ArrRef`, so two halves of one array are two `ArrRef`s. -/
def ArrRef.slice (a : ArrRef) (lo hi : Nat) : ArrRef := ⟨a.base + lo, hi - lo⟩

/-- A slice's locations are the parent's — `FootprintWithin.mono`'s hypothesis for lifting a bound on
a slice to a bound on the whole array. -/
@[simp, grind .]
theorem ArrRef.slice_inRange {a : ArrRef} {lo hi : Nat} (hle : hi ≤ a.len) {l : Loc}
    (h : (a.slice lo hi).InRange l) : a.InRange l := by
  unfold ArrRef.slice ArrRef.InRange at *
  grind

/-- **Non-overlapping ranges share no location** — one `omega` on four constants, with no
reasoning about which indices are touched. The last step of almost every array proof. -/
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
