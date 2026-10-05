import Paralever.Theory.Sequentialize

/-! # Footprints confined to a location predicate — "different memory ⇒ independent," mechanized

The recurring shape across every array-style example (chunked reduce, mergesort, anything whose
Bernstein obligation is arithmetic rather than data-dependent): once each side's footprint is known
to lie in a set of locations, and the relevant sets never overlap, `Indep` and the frame property
both follow with no further case analysis. This file makes that step generic and reusable — an
example only ever has to supply (a) a footprint-confinement proof for its own functions (by
structural/fuel induction, using `.read`/`.write`/`.pure` here as building blocks) and (b) an
`omega` call showing two location predicates are disjoint. Everything downstream of that is this
file, not per-example bookkeeping.

**One base combinator.** `ReadsWithin`, `WritesWithin`, `FootprintWithin` are all "every location in
this list satisfies `P`" for a specific projection of a `Footprint` — so they share one proof of
`empty`/`union`/`mono`/`singleton` (`Within`, private to this file) rather than three copies of the
same induction. `FootprintWithin f P` is literally `ReadsWithin f P ∧ WritesWithin f P` with the
*same* `P` on both sides — strictly stronger than Bernstein needs (it forbids shared reads), so
`Indep` itself is proved from `ReadsWithin`/`WritesWithin` with *independent* predicates per side
(`indep_of_read_write_confined`), and the same-`P` lemma (`indep_of_footprint_within`, the common
case when an example's reads and writes happen to share one region) is a corollary of that, not a
separate proof.

`P : Loc → Prop` rather than a `List Loc` subset or a `(lo, hi)` pair: pointwise predicates compose
under `∧`/`∨`/`omega` directly, and cover both a single contiguous range and a union of ranges
(e.g. mergesort's data-plus-scratch channels) with the same vocabulary.
-/

namespace Paralever

/-- Every location in `L` satisfies `P` — the one shape `Reads`/`Writes`/`FootprintWithin` all
reduce to. Not exported; downstream code only ever sees it through those three names. -/
private def Within (L : List Loc) (P : Loc → Prop) : Prop := ∀ l ∈ L, P l

namespace Within

/-- The empty list is within every predicate. -/
theorem empty (P : Loc → Prop) : Within [] P := by simp [Within]

/-- Two lists within `P` concatenate to a list within `P`. -/
theorem union {a b : List Loc} {P : Loc → Prop} (ha : Within a P) (hb : Within b P) :
    Within (a ++ b) P := fun l hl => (List.mem_append.mp hl).elim (ha l) (hb l)

/-- Weakening: a bound by `P` is also a bound by anything `P` implies. -/
theorem mono {L : List Loc} {P Q : Loc → Prop} (h : ∀ l, P l → Q l) (hL : Within L P) :
    Within L Q := fun l hl => h l (hL l hl)

/-- A one-element list is within `P` exactly when its element satisfies `P`. -/
theorem singleton {l : Loc} {P : Loc → Prop} (hl : P l) : Within [l] P := by
  intro l' hl'; simp only [List.mem_singleton] at hl'; exact hl' ▸ hl

end Within

/-- `f`'s reads all satisfy `P`. -/
def ReadsWithin (f : Footprint) (P : Loc → Prop) : Prop := Within f.reads P

/-- `f`'s writes all satisfy `P` — all `frame_of_footprint` ever needs, and often true (e.g.
`mergeStep`: writes confined to a scratch range) when the *reads* aren't confined to the same
predicate at all (there: the data range). -/
def WritesWithin (f : Footprint) (P : Loc → Prop) : Prop := Within f.writes P

/-- `f`'s reads *and* writes both satisfy the same `P`. The common case (one region covers
everything a function touches) — `indep_of_footprint_within` below is for exactly this case;
`indep_of_read_write_confined` is the one to reach for when reads and writes need different
regions (shared reads, e.g. matmul). -/
def FootprintWithin (f : Footprint) (P : Loc → Prop) : Prop := ReadsWithin f P ∧ WritesWithin f P

/-! ### The combinator algebra

One member per shape a footprint can be built out of, for each of the three predicates. A
confinement proof for a real program is assembled from these: `empty` at a `pure` leaf, `read`/
`write` at a primitive node, `union` wherever `accesses` combines two footprints, `mono` to relax
the predicate, and `apply` to turn the finished bound back into a membership fact about one
location. `Footprint.empty` and `Footprint.union` are the only shapes `accesses` produces, so the
list is complete. -/

namespace ReadsWithin

/-- Use the bound: every location `f` reads satisfies `P`. -/
theorem apply {f : Footprint} {P : Loc → Prop} (h : ReadsWithin f P) : ∀ l ∈ f.reads, P l := h

/-- Reading nothing is within every predicate. -/
theorem empty (P : Loc → Prop) : ReadsWithin Footprint.empty P := Within.empty P
/-- Bounding each side's reads bounds the union's. -/
theorem union {a b : Footprint} {P : Loc → Prop} (ha : ReadsWithin a P) (hb : ReadsWithin b P) :
    ReadsWithin (Footprint.union a b) P := Within.union ha hb
/-- Weaken the predicate: a read bound by `P` is bound by anything `P` implies. -/
theorem mono {f : Footprint} {P Q : Loc → Prop} (h : ∀ l, P l → Q l) (hf : ReadsWithin f P) :
    ReadsWithin f Q := Within.mono h hf
/-- A lone read of `l` is confined to `P` as soon as `l` itself satisfies `P`. -/
theorem read (l : Loc) (P : Loc → Prop) (hl : P l) : ReadsWithin (⟨[l], []⟩ : Footprint) P :=
  Within.singleton hl
/-- A lone write reads nothing, so every `P` confines its reads — no hypothesis on `l`. -/
theorem write (l : Loc) (P : Loc → Prop) : ReadsWithin (⟨[], [l]⟩ : Footprint) P := Within.empty P

end ReadsWithin

namespace WritesWithin

/-- Use the bound: every location `f` writes satisfies `P`. This is the form
`indep_of_read_write_confined` and `frame_of_footprint` consume. -/
@[grind .]
theorem apply {f : Footprint} {P : Loc → Prop} (h : WritesWithin f P) : ∀ l ∈ f.writes, P l := h

/-- Writing nothing is within every predicate. -/
theorem empty (P : Loc → Prop) : WritesWithin Footprint.empty P := Within.empty P
/-- Bounding each side's writes bounds the union's. -/
theorem union {a b : Footprint} {P : Loc → Prop} (ha : WritesWithin a P) (hb : WritesWithin b P) :
    WritesWithin (Footprint.union a b) P := Within.union ha hb
/-- Weaken the predicate: a write bound by `P` is bound by anything `P` implies. -/
theorem mono {f : Footprint} {P Q : Loc → Prop} (h : ∀ l, P l → Q l) (hf : WritesWithin f P) :
    WritesWithin f Q := Within.mono h hf
/-- A lone read writes nothing, so every `P` confines its writes — no hypothesis on `l`. -/
theorem read (l : Loc) (P : Loc → Prop) : WritesWithin (⟨[l], []⟩ : Footprint) P := Within.empty P
/-- A lone write to `l` is confined to `P` as soon as `l` itself satisfies `P`. -/
theorem write (l : Loc) (P : Loc → Prop) (hl : P l) : WritesWithin (⟨[], [l]⟩ : Footprint) P :=
  Within.singleton hl

end WritesWithin

namespace FootprintWithin

/-- Project out the reads half. -/
theorem reads {f : Footprint} {P : Loc → Prop} (h : FootprintWithin f P) : ReadsWithin f P := h.1
/-- Project out the writes half — what `frame_of_footprint` needs. -/
theorem writes {f : Footprint} {P : Loc → Prop} (h : FootprintWithin f P) : WritesWithin f P := h.2

/-- Touching nothing is within every predicate — the `pure` leaf of a confinement proof. -/
theorem empty (P : Loc → Prop) : FootprintWithin Footprint.empty P :=
  ⟨ReadsWithin.empty P, WritesWithin.empty P⟩
/-- Bounding each side bounds the union — the step for every `accesses` case that combines
footprints, including `par`. -/
theorem union {a b : Footprint} {P : Loc → Prop} (ha : FootprintWithin a P) (hb : FootprintWithin b P) :
    FootprintWithin (Footprint.union a b) P :=
  ⟨ReadsWithin.union ha.reads hb.reads, WritesWithin.union ha.writes hb.writes⟩
/-- Weaken the predicate — how a bound on one array's range becomes a bound on a larger region
(e.g. a slice's bound lifted to the whole backing array). -/
theorem mono {f : Footprint} {P Q : Loc → Prop} (h : ∀ l, P l → Q l) (hf : FootprintWithin f P) :
    FootprintWithin f Q := ⟨ReadsWithin.mono h hf.reads, WritesWithin.mono h hf.writes⟩
/-- A lone read of `l` touches only `l`, so `P l` confines it. -/
theorem read (l : Loc) (P : Loc → Prop) (hl : P l) : FootprintWithin ⟨[l], []⟩ P :=
  ⟨ReadsWithin.read l P hl, WritesWithin.read l P⟩
/-- A lone write to `l` touches only `l`, so `P l` confines it. -/
theorem write (l : Loc) (P : Loc → Prop) (hl : P l) : FootprintWithin ⟨[], [l]⟩ P :=
  ⟨ReadsWithin.write l P, WritesWithin.write l P hl⟩

end FootprintWithin

/-- **Bernstein from four confinement predicates** — one region per side per access kind. Only the
write/write (`hww`) and the two write/read (`hwr`, `hrw`) cross terms have to be disjoint;
`Pfr`/`Pgr`, the two read regions, never do. That omission is what lets this handle shared-read
loops like matmul (disjoint output cells, overlapping input rows and columns) — with separate
`Pfr`/`Pfw` per side there is simply nothing to prove about overlapping reads.
-- ref: Bernstein 1966; `docs/access.md` -/
theorem indep_of_read_write_confined {f g : Footprint} {Pfr Pfw Pgr Pgw : Loc → Prop}
    (hfr : ReadsWithin f Pfr) (hfw : WritesWithin f Pfw)
    (hgr : ReadsWithin g Pgr) (hgw : WritesWithin g Pgw)
    (hww : ∀ l, Pfw l → Pgw l → False)
    (hwr : ∀ l, Pfw l → Pgr l → False)
    (hrw : ∀ l, Pgw l → Pfr l → False) : Indep f g :=
  ⟨fun l hlf hlg => hww l (hfw.apply l hlf) (hgw.apply l hlg),
   fun l hlf hlg => hwr l (hfw.apply l hlf) (hgr.apply l hlg),
   fun l hlf hlg => hrw l (hgw.apply l hlf) (hfr.apply l hlg)⟩

/-- **The independence step, done once**, for the common case where one region covers everything a
function touches (reads and writes alike) — no shared reads to worry about, so the one disjointness
fact `hdisj` between `Pf`/`Pg` covers all three of `Indep`'s conditions. A corollary of
`indep_of_read_write_confined` at `Pfr = Pfw = Pf`, `Pgr = Pgw = Pg`, not a separate proof. -/
theorem indep_of_footprint_within {f g : Footprint} {Pf Pg : Loc → Prop}
    (hf : FootprintWithin f Pf) (hg : FootprintWithin g Pg)
    (hdisj : ∀ l, Pf l → Pg l → False) : Indep f g :=
  indep_of_read_write_confined hf.reads hf.writes hg.reads hg.writes hdisj hdisj
    (fun l hgl hfl => hdisj l hfl hgl)

/-- **The frame step, done once.** A location outside `c`'s confinement predicate is untouched by
`c`'s run — direct corollary of `runSeq_frame`, so no example ever re-derives frame by induction on
`runSeq`/`State.update` again; it only has to supply the confinement bound. -/
theorem frame_of_footprint {τ : Type} (c : ParM τ) (σ : State) (P : Loc → Prop)
    (hb : WritesWithin (accesses c σ) P) (l : Loc) (hl : ¬ P l) :
    (runSeq c σ).2 l = σ l :=
  runSeq_frame c σ l (fun hmem => hl (hb.apply l hmem))

end Paralever
