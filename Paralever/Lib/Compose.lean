import Paralever.Theory.Intervals

/-! # Footprint composition through `bind` — one-step lemmas

Every program built from `ParM.bind` requires the same `rw [accesses_bind]; apply .union` dance
to compose its footprint bound from its parts. These lemmas do that once, so the user writes
`footprintWithin_bind hp hf` instead of the two-line expansion.

Rationale: `docs/access.md`. -/

namespace Paralever

@[simp, grind .]
theorem footprintWithin_bind {α β : Type} (p : ParM α) (f : α → ParM β)
    (σ : State) (P : Loc → Prop)
    (hp : FootprintWithin (accesses p σ) P)
    (hf : FootprintWithin (accesses (f (runSeq p σ).1) (runSeq p σ).2) P) :
    FootprintWithin (accesses (ParM.bind p f) σ) P := by
  rw [accesses_bind]; exact FootprintWithin.union hp hf

@[simp, grind .]
theorem readsWithin_bind {α β : Type} (p : ParM α) (f : α → ParM β)
    (σ : State) (P : Loc → Prop)
    (hp : ReadsWithin (accesses p σ) P)
    (hf : ReadsWithin (accesses (f (runSeq p σ).1) (runSeq p σ).2) P) :
    ReadsWithin (accesses (ParM.bind p f) σ) P := by
  rw [accesses_bind]; exact ReadsWithin.union hp hf

@[simp, grind .]
theorem writesWithin_bind {α β : Type} (p : ParM α) (f : α → ParM β)
    (σ : State) (P : Loc → Prop)
    (hp : WritesWithin (accesses p σ) P)
    (hf : WritesWithin (accesses (f (runSeq p σ).1) (runSeq p σ).2) P) :
    WritesWithin (accesses (ParM.bind p f) σ) P := by
  rw [accesses_bind]; exact WritesWithin.union hp hf

/-- Read-only programs: if both `p` and `f _` have empty writes, so does the composition. -/
@[simp, grind .]
theorem no_writes_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State)
    (hp : (accesses p σ).writes = [])
    (hf : (accesses (f (runSeq p σ).1) (runSeq p σ).2).writes = []) :
    (accesses (ParM.bind p f) σ).writes = [] := by
  rw [accesses_bind]; simp [Footprint.union, hp, hf]

/-- Bernstein independence is trivially satisfied when both sides have no writes. Generalized
from `Examples/SumArray.lean`'s local `indep_of_no_writes`. -/
@[simp, grind .]
theorem indep_of_no_writes (f g : Footprint) (hf : f.writes = []) (hg : g.writes = []) :
    Indep f g := by
  simp [Indep, Disjoint, hf, hg]

end Paralever
