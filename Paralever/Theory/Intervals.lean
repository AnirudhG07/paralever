import Paralever.Theory.Sequentialize

/-! # Footprints confined to a location predicate — "different memory ⇒ independent," mechanized

The recurring shape across every array-style example (chunked reduce, mergesort, anything whose
Bernstein obligation is arithmetic rather than data-dependent): once each side's footprint is known
to lie in a set of locations, and the two sets never overlap, `Indep` and the frame property both
follow with no further case analysis. This file makes that step generic and reusable — an example
only ever has to supply (a) a footprint-confinement proof for its own functions (by structural/fuel
induction, using `.read`/`.write`/`.pure` here as building blocks) and (b) an `omega` call showing
two location predicates are disjoint. Everything downstream of that is this file, not per-example
bookkeeping.

`P : Loc → Prop` rather than a `List Loc` subset or a `(lo, hi)` pair: pointwise predicates compose
under `∧`/`∨`/`omega` directly, and cover both a single contiguous range and a union of ranges
(e.g. mergesort's data-plus-scratch channels) with the same vocabulary.
-/

namespace Paralever

/-- `f`'s reads and writes both satisfy `P`. The one fact every footprint-confinement proof below
produces, and the one fact `indep_of_footprint_within`/`frame_of_footprint` consume. -/
def FootprintWithin (f : Footprint) (P : Loc → Prop) : Prop :=
  (∀ l ∈ f.reads, P l) ∧ (∀ l ∈ f.writes, P l)

namespace FootprintWithin

theorem reads {f : Footprint} {P : Loc → Prop} (h : FootprintWithin f P) :
    ∀ l ∈ f.reads, P l := h.1

theorem writes {f : Footprint} {P : Loc → Prop} (h : FootprintWithin f P) :
    ∀ l ∈ f.writes, P l := h.2

theorem empty (P : Loc → Prop) : FootprintWithin Footprint.empty P :=
  ⟨by simp [Footprint.empty], by simp [Footprint.empty]⟩

/-- The combinator every `.read`/`.write` step's continuation needs: "this step's own access
satisfies `P`" plus "the rest of the computation satisfies `P`" gives "the whole thing satisfies
`P`" — exactly `Footprint.union`'s shape, so this is what turns a structural induction over `accesses`
into one line per case instead of a hand-threaded state argument. -/
@[simp, grind .]
theorem union {a b : Footprint} {P : Loc → Prop}
    (ha : FootprintWithin a P) (hb : FootprintWithin b P) : FootprintWithin (Footprint.union a b) P :=
  ⟨fun l hl => (List.mem_append.mp hl).elim (ha.reads l) (hb.reads l),
   fun l hl => (List.mem_append.mp hl).elim (ha.writes l) (hb.writes l)⟩

theorem mono {f : Footprint} {P Q : Loc → Prop} (h : ∀ l, P l → Q l) (hf : FootprintWithin f P) :
    FootprintWithin f Q :=
  ⟨fun l hl => h l (hf.reads l hl), fun l hl => h l (hf.writes l hl)⟩

@[simp, grind .]
theorem read (l : Loc) (P : Loc → Prop) (hl : P l) : FootprintWithin ⟨[l], []⟩ P :=
  ⟨fun l' hl' => by simp only [List.mem_singleton] at hl'; exact hl' ▸ hl, by simp⟩

@[simp, grind .]
theorem write (l : Loc) (P : Loc → Prop) (hl : P l) : FootprintWithin ⟨[], [l]⟩ P :=
  ⟨by simp, fun l' hl' => by simp only [List.mem_singleton] at hl'; exact hl' ▸ hl⟩

end FootprintWithin

/-- `f`'s writes alone satisfy `P` — all `frame_of_footprint` ever needs, and often true (e.g.
`mergeStep`: writes confined to a scratch range) when the *reads* aren't confined to the same
predicate at all (there: the data range), so `FootprintWithin` would be too strong to ask for. -/
def WritesWithin (f : Footprint) (P : Loc → Prop) : Prop := ∀ l ∈ f.writes, P l

namespace WritesWithin

theorem empty (P : Loc → Prop) : WritesWithin Footprint.empty P := by simp [Footprint.empty, WritesWithin]

@[simp, grind .]
theorem union {a b : Footprint} {P : Loc → Prop}
    (ha : WritesWithin a P) (hb : WritesWithin b P) : WritesWithin (Footprint.union a b) P :=
  fun l hl => (List.mem_append.mp hl).elim (ha l) (hb l)

theorem mono {f : Footprint} {P Q : Loc → Prop} (h : ∀ l, P l → Q l) (hf : WritesWithin f P) :
    WritesWithin f Q := fun l hl => h l (hf l hl)

@[simp, grind .]
theorem read (l : Loc) (P : Loc → Prop) : WritesWithin (⟨[l], []⟩ : Footprint) P := by simp [WritesWithin]

@[simp, grind .]
theorem write (l : Loc) (P : Loc → Prop) (hl : P l) : WritesWithin (⟨[], [l]⟩ : Footprint) P := by
  intro l' hl'; simp only [List.mem_singleton] at hl'; exact hl' ▸ hl

theorem of_footprintWithin {f : Footprint} {P : Loc → Prop} (h : FootprintWithin f P) :
    WritesWithin f P := h.writes

end WritesWithin

/-- **The independence step, done once.** Two footprints confined to predicates that are never
simultaneously true of the same location are Bernstein-independent — no shared-write, write/read,
read/write cross terms to check by hand; `hdisj` (usually one `omega` call on interval bounds) is
the entire obligation. This is "touch different memory ⇒ done," made literal. -/
@[simp, grind .]
theorem indep_of_footprint_within {f g : Footprint} {Pf Pg : Loc → Prop}
    (hf : FootprintWithin f Pf) (hg : FootprintWithin g Pg)
    (hdisj : ∀ l, Pf l → Pg l → False) : Indep f g :=
  ⟨fun l hlf hlg => hdisj l (hf.writes l hlf) (hg.writes l hlg),
   fun l hlf hlg => hdisj l (hf.writes l hlf) (hg.reads l hlg),
   fun l hlf hlg => hdisj l (hf.reads l hlg) (hg.writes l hlf)⟩

/-- **The frame step, done once.** A location outside `c`'s confinement predicate is untouched by
`c`'s run — direct corollary of `runSeq_frame`, so no example ever re-derives frame by induction on
`runSeq`/`State.update` again; it only has to supply the confinement bound. -/
@[simp, grind .]
theorem frame_of_footprint {τ : Type} (c : ParM τ) (σ : State) (P : Loc → Prop)
    (hb : WritesWithin (accesses c σ) P) (l : Loc) (hl : ¬ P l) :
    (runSeq c σ).2 l = σ l :=
  runSeq_frame c σ l (fun hmem => hl (hb l hmem))

end Paralever
