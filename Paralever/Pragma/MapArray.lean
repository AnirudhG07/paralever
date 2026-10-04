import Paralever.Pragma.ParallelFor
import Paralever.Pragma.ArrRef

/-! # `mapArray` — elementwise array map, one proof for all pure functions

"Read `src[i]`, apply `f`, write `dst[i]`, for all `i` in parallel" is the most common pattern
(DoubleInto). `mapArray_par_seq_eq` discharges the entire independence proof given only
`src.len = dst.len` and disjointness of `src`/`dst` ranges. Internally uses
`parAll_par_seq_eq_of_indexed_rw` with separate read/write predicates.

Rationale: `docs/theory.md` §9. -/

namespace Paralever
open Paralever

-- ref: PolCert §4 — elementwise map as the simplest pragmatic pattern

/-- One iteration: read `src[i]`, apply `f`, write `dst[i]`. -/
@[simp, grind .]
def mapArrayStep (src dst : ArrRef) (f : Val → Val) (i : Nat) : ParM Unit :=
  ParM.bind (ArrM.get src i) (fun v => ArrM.set dst i (f v))

@[simp, grind .]
def mapArrayPar (src dst : ArrRef) (f : Val → Val) : ParM (List Unit) :=
  ParM.parAll ((List.range src.len).map (mapArrayStep src dst f))

@[simp, grind .]
def mapArraySeq (src dst : ArrRef) (f : Val → Val) : ParM (List Unit) :=
  ParM.seqAll ((List.range src.len).map (mapArrayStep src dst f))

/-! ### Per-step lemmas -/

@[simp, grind .]
theorem mapArrayStep_accesses (src dst : ArrRef) (f : Val → Val) (i : Nat) (σ : State) :
    accesses (mapArrayStep src dst f i) σ = ⟨[src.loc i], [dst.loc i]⟩ := by
  simp [mapArrayStep, ArrM.get, ArrM.set, ArrRef.loc, accesses, ParM.bind,
        Footprint.union, Footprint.empty]

@[simp, grind .]
theorem mapArrayStep_wellformed (src dst : ArrRef) (f : Val → Val) (i : Nat) (σ : State) :
    WellFormed (mapArrayStep src dst f i) σ := by
  simp [mapArrayStep, ArrM.get, ArrM.set, WellFormed, ParM.bind]

@[simp, grind .]
theorem mapArrayStep_readsWithin (src dst : ArrRef) (f : Val → Val) {i : Nat}
    (hi : i < src.len) (σ : State) :
    ReadsWithin (accesses (mapArrayStep src dst f i) σ) src.InRange := by
  rw [mapArrayStep_accesses]; exact Within.singleton (src.loc_mem hi)

@[simp, grind .]
theorem mapArrayStep_writesWithin (src dst : ArrRef) (f : Val → Val) {i : Nat}
    (_hi : i < dst.len) (σ : State) :
    WritesWithin (accesses (mapArrayStep src dst f i) σ) (fun l => l = dst.loc i) := by
  rw [mapArrayStep_accesses]; exact Within.singleton rfl

/-! ### The headline theorem -/

@[simp, grind .]
theorem mapArray_par_seq_eq (src dst : ArrRef) (f : Val → Val)
    (hlen : src.len = dst.len)
    (hdisj : src.base + src.len ≤ dst.base ∨ dst.base + dst.len ≤ src.base) (σ : State) :
    ParSeqEq (mapArrayPar src dst f) (mapArraySeq src dst f) σ := by
  unfold mapArrayPar mapArraySeq
  apply Pragma.ParallelFor.parAll_par_seq_eq_of_indexed_rw
    (List.range src.len) (mapArrayStep src dst f)
    (fun _ => src.InRange) (fun i l => l = dst.loc i)
    List.nodup_range
  · intro i hi σ'; exact mapArrayStep_wellformed src dst f i σ'
  · intro i hi σ'; exact mapArrayStep_readsWithin src dst f (List.mem_range.mp hi) σ'
  · intro i hi σ'; exact mapArrayStep_writesWithin src dst f
      (hlen ▸ List.mem_range.mp hi) σ'
  · intro i j _ _ hij l hli hlj; grind [ArrRef.loc]
  · intro i j hi _ _ l hli hlj; grind [ArrRef.loc, ArrRef.InRange]

end Paralever
