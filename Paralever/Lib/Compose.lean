import Paralever.Theory.Intervals

/-! # Footprint composition through `bind` — one-step lemmas

Every program built from `ParM.bind` requires the same `rw [accesses_bind]; apply .union` dance
to compose its footprint bound from its parts. These lemmas do that once, so the user writes
`footprintWithin_bind hp hf` instead of the two-line expansion.

Rationale: `docs/access.md`. -/

namespace Paralever

/-- Everything `p >>= f` touches lies in `P` when everything `p` touches does and everything the
continuation touches does. The continuation is measured from `(runSeq p σ).2`, the heap `p` leaves
behind, so a bound on a composed program follows one `bind` at a time instead of by one induction
over the whole tree. -/
@[simp, grind .]
theorem footprintWithin_bind {α β : Type} (p : ParM α) (f : α → ParM β)
    (σ : State) (P : Loc → Prop)
    (hp : FootprintWithin (accesses p σ) P)
    (hf : FootprintWithin (accesses (f (runSeq p σ).1) (runSeq p σ).2) P) :
    FootprintWithin (accesses (ParM.bind p f) σ) P := by
  rw [accesses_bind]; exact FootprintWithin.union hp hf

/-- The reads-only version of `footprintWithin_bind`, for when reads and writes need different
predicates (shared reads). -/
@[simp, grind .]
theorem readsWithin_bind {α β : Type} (p : ParM α) (f : α → ParM β)
    (σ : State) (P : Loc → Prop)
    (hp : ReadsWithin (accesses p σ) P)
    (hf : ReadsWithin (accesses (f (runSeq p σ).1) (runSeq p σ).2) P) :
    ReadsWithin (accesses (ParM.bind p f) σ) P := by
  rw [accesses_bind]; exact ReadsWithin.union hp hf

/-- The writes-only version of `footprintWithin_bind`, for the frame side of an obligation. -/
@[simp, grind .]
theorem writesWithin_bind {α β : Type} (p : ParM α) (f : α → ParM β)
    (σ : State) (P : Loc → Prop)
    (hp : WritesWithin (accesses p σ) P)
    (hf : WritesWithin (accesses (f (runSeq p σ).1) (runSeq p σ).2) P) :
    WritesWithin (accesses (ParM.bind p f) σ) P := by
  rw [accesses_bind]; exact WritesWithin.union hp hf

/-- A composition of read-only programs is read-only: empty writes on both sides compose. -/
@[simp, grind .]
theorem no_writes_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State)
    (hp : (accesses p σ).writes = [])
    (hf : (accesses (f (runSeq p σ).1) (runSeq p σ).2).writes = []) :
    (accesses (ParM.bind p f) σ).writes = [] := by
  rw [accesses_bind]; simp [Footprint.union, hp, hf]

/-- Two read-only footprints are Bernstein-independent. All three clauses quantify over a write, so
they hold vacuously — this is why shared reads never need an argument. -/
@[simp, grind .]
theorem indep_of_no_writes (f g : Footprint) (hf : f.writes = []) (hg : g.writes = []) :
    Indep f g := by
  simp [Indep, Disjoint, hf, hg]

end Paralever
