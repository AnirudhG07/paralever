import Paralever.Pragma.ParallelFor
import Paralever.Pragma.ArrRef
import Paralever.Lib.Notation
import Paralever.Lib.Cost

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
  doₚ
    let v ← ArrM.get src i
    ArrM.set dst i (f v)

/-- All `src.len` iterations in parallel. -/
@[simp, grind .]
def mapArrayPar (src dst : ArrRef) (f : Val → Val) : ParM (List Unit) :=
  ParM.parAll ((List.range src.len).map (mapArrayStep src dst f))

/-- The same iterations one after another, ascending — the sequential program every theorem below
compares against. -/
@[simp, grind .]
def mapArraySeq (src dst : ArrRef) (f : Val → Val) : ParM (List Unit) :=
  ParM.seqAll ((List.range src.len).map (mapArrayStep src dst f))

/-! ### Per-step lemmas

What `mapArray_par_seq_eq` has to supply to `parAll_par_seq_eq_of_indexed_rw`, one per hypothesis
it takes. All four are about a single iteration; the loop itself is the validator's business. -/

/-- Iteration `i` reads `src[i]` and writes `dst[i]`, nothing else. -/
@[simp, grind .]
theorem mapArrayStep_accesses (src dst : ArrRef) (f : Val → Val) (i : Nat) (σ : State) :
    accesses (mapArrayStep src dst f i) σ = ⟨[src.loc i], [dst.loc i]⟩ := by
  simp [mapArrayStep, ArrM.get, ArrM.set, ArrRef.loc, accesses, ParM.bind,
        Footprint.union, Footprint.empty]

/-- An iteration contains no `par` node, so it is well-formed at every state. -/
@[simp, grind .]
theorem mapArrayStep_wellformed (src dst : ArrRef) (f : Val → Val) (i : Nat) (σ : State) :
    WellFormed (mapArrayStep src dst f i) σ := by
  simp [mapArrayStep, ArrM.get, ArrM.set, WellFormed, ParM.bind]

/-- An iteration's reads stay inside `src` — the whole array, not one cell, which is all the
read side ever needs since read/read is not a conflict. -/
@[simp, grind .]
theorem mapArrayStep_readsWithin (src dst : ArrRef) (f : Val → Val) {i : Nat}
    (hi : i < src.len) (σ : State) :
    ReadsWithin (accesses (mapArrayStep src dst f i) σ) src.InRange := by
  rw [mapArrayStep_accesses]; exact Within.singleton (src.loc_mem hi)

/-- An iteration's writes land on the single cell `dst.loc i`. Confined per-index, not to all of
`dst`: distinct iterations must have *disjoint* write predicates, which `dst.InRange` would not give.
-/
@[simp, grind .]
theorem mapArrayStep_writesWithin (src dst : ArrRef) (f : Val → Val) {i : Nat}
    (_hi : i < dst.len) (σ : State) :
    WritesWithin (accesses (mapArrayStep src dst f i) σ) (fun l => l = dst.loc i) := by
  rw [mapArrayStep_accesses]; exact Within.singleton rfl

/-! ### The headline theorem -/

/-- **An elementwise map parallelizes, on two hypotheses**: `src` and `dst` have the same length, and
their ranges do not overlap. Both are `omega`-level facts about four constants; no induction over the
loop, no per-index reasoning, whatever `f` is.

`hdisj` rules out `src = dst`. That is stronger than Bernstein strictly needs here — it is forced by
bounding each iteration's reads by all of `src` rather than by cell `i`, which is what keeps the
obligation down to two range comparisons. An in-place map would need the tighter per-index read bound
instead. -/
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

/-! ### Pure state updates — the `foldl` a sequential single-cell loop computes

Generic in the address functions `rd`/`wr`, so they say nothing about `ArrRef`; `mapArraySeq_spec`
instantiates them at `src.loc`/`dst.loc`. -/

/-- A fold of single-cell updates leaves every cell it never writes alone — the frame property for the
pure side. -/
theorem foldl_update_frame (wr : Nat → Loc) (g : Nat → State → Val) :
    ∀ (idxs : List Nat) (σ : State) (l : Loc), (∀ j ∈ idxs, wr j ≠ l) →
      (idxs.foldl (fun s k => s.update (wr k) (g k s)) σ) l = σ l := by
  intro idxs
  induction idxs with
  | nil => intro σ l _; rfl
  | cons k ks ih =>
      intro σ l h
      rw [List.foldl_cons, ih _ l (fun j hj => h j (List.mem_cons_of_mem k hj)),
        State.update_other σ _ (Ne.symm (h k List.mem_cons_self))]

/-- **Pointwise reading of the fold**: cell `wr i` ends up holding `f i` of the *initial* value at
`rd i`. The two hypotheses are what make that true — distinct indices write distinct cells, and no
write lands on a cell any iteration reads — so no later iteration can disturb iteration `i`'s result
or its input. -/
theorem foldl_update_spec (rd wr : Nat → Loc) (f : Nat → Val → Val) :
    ∀ (idxs : List Nat), idxs.Nodup →
      (∀ j ∈ idxs, ∀ k ∈ idxs, j ≠ k → wr j ≠ wr k) →
      (∀ j ∈ idxs, ∀ k ∈ idxs, wr j ≠ rd k) →
      ∀ (σ : State) (i : Nat), i ∈ idxs →
        (idxs.foldl (fun s k => s.update (wr k) (f k (s (rd k)))) σ) (wr i) = f i (σ (rd i)) := by
  intro idxs
  induction idxs with
  | nil => intro _ _ _ σ i hi; simp at hi
  | cons k ks ih =>
      intro hnd hwinj hrw σ i hi
      have hknot : k ∉ ks := (List.nodup_cons.mp hnd).1
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [foldl_update_frame wr (fun j s => f j (s (rd j))) ks _ (wr i)
          (fun j hj => hwinj j (List.mem_cons_of_mem i hj) i List.mem_cons_self
            (fun he => hknot (he ▸ hj))), State.update_same]
      · rw [ih (List.nodup_cons.mp hnd).2
          (fun j hj k' hk' => hwinj j (List.mem_cons_of_mem k hj) k'
            (List.mem_cons_of_mem k hk'))
          (fun j hj k' hk' => hrw j (List.mem_cons_of_mem k hj) k'
            (List.mem_cons_of_mem k hk')) _ i hi,
          State.update_other σ _ (fun he =>
            hrw k List.mem_cons_self i (List.mem_cons_of_mem k hi) he.symm)]

/-! ### Link 2: `mapArraySeq` computes a pure state transformer -/

/-- The pure counterpart of `mapArraySeq`: a `State → State` fold over the index range, no monad
anywhere. -/
def mapArrayPure (src dst : ArrRef) (f : Val → Val) (σ : State) : State :=
  (List.range src.len).foldl (fun s i => s.update (dst.loc i) (f (s (src.loc i)))) σ

/-- **The sequential program's final heap *is* `mapArrayPure`'s.** No hypothesis at all — this is a
fact about the two definitions, and it is what lets the spec below be read off a fold instead of a
`ParM` tree. -/
theorem mapArraySeq_eq_pure (src dst : ArrRef) (f : Val → Val) (σ : State) :
    (runSeq (mapArraySeq src dst f) σ).2 = mapArrayPure src dst f σ := by
  show (runSeq (ParM.seqAll ((List.range src.len).map (mapArrayStep src dst f))) σ).2 = _
  unfold mapArrayPure
  generalize List.range src.len = idxs
  induction idxs generalizing σ with
  | nil => rfl
  | cons i is ih =>
      show (runSeq (ParM.seqAll ((i :: is).map (mapArrayStep src dst f))) σ).2 = _
      simp only [List.map_cons, ParM.seqAll, ParM.seqPair, runSeq, runSeq_bind, ParM.bind,
        mapArrayStep, ArrM.get, ArrM.set, List.foldl_cons]
      exact ih (σ.update (dst.loc i) (f (σ (src.loc i))))

/-- **The elementwise spec**: `dst[i]` ends up holding `f` of the initial `src[i]`. Stated about
`mapArraySeq`; `mapArray_par_seq_eq` carries it over to the parallel version, which is the division of
labour the whole project is built on — correctness proved once, sequentially. Same two hypotheses. -/
theorem mapArraySeq_spec (src dst : ArrRef) (f : Val → Val) (hlen : src.len = dst.len)
    (hdisj : src.base + src.len ≤ dst.base ∨ dst.base + dst.len ≤ src.base)
    (σ : State) (i : Nat) (hi : i < src.len) :
    (runSeq (mapArraySeq src dst f) σ).2 (dst.loc i) = f (σ (src.loc i)) := by
  rw [mapArraySeq_eq_pure]
  refine foldl_update_spec src.loc dst.loc (fun _ v => f v) (List.range src.len)
    List.nodup_range ?_ ?_ σ i (List.mem_range.mpr hi)
  · intro j _ k _ hjk; grind [ArrRef.loc]
  · intro j hj k hk
    have hj' : j < src.len := List.mem_range.mp hj
    have hk' : k < src.len := List.mem_range.mp hk
    grind [ArrRef.loc]


/-- `WellFormed` for an arbitrary nodup list of in-bounds indices, not just `List.range src.len` —
the generality `mapArray_time_lt` needs, since it has to talk about the loop's *tail*. -/
theorem mapArray_wellformed_idxs (src dst : ArrRef) (f : Val → Val) (hlen : src.len = dst.len)
    (hdisj : src.base + src.len ≤ dst.base ∨ dst.base + dst.len ≤ src.base)
    (idxs : List Nat) (hnd : idxs.Nodup) (hb : ∀ i ∈ idxs, i < src.len) (σ : State) :
    WellFormed (ParM.parAll (idxs.map (mapArrayStep src dst f))) σ :=
  (Pragma.ParallelFor.parAll_wellformed_of_indexed_rw idxs (mapArrayStep src dst f)
    (fun _ => src.InRange) (fun i l => l = dst.loc i) hnd
    (fun i _ σ' => mapArrayStep_wellformed src dst f i σ')
    (fun i hi σ' => mapArrayStep_readsWithin src dst f (hb i hi) σ')
    (fun i hi σ' => mapArrayStep_writesWithin src dst f (hlen ▸ hb i hi) σ')
    (by intro i j _ _ hij l hli hlj; grind [ArrRef.loc])
    (by intro i j hi _ _ l hli hlj; grind [ArrRef.loc, ArrRef.InRange]) σ).1

/-- The whole parallel map is well-formed, from the same two range hypotheses. This is the
`WellFormed` obligation `parAll_par_seq_eq` takes, exposed on its own for callers that need it
separately from `ParSeqEq` (the cost laws do). -/
theorem mapArray_wellformed (src dst : ArrRef) (f : Val → Val) (hlen : src.len = dst.len)
    (hdisj : src.base + src.len ≤ dst.base ∨ dst.base + dst.len ≤ src.base) (σ : State) :
    WellFormed (mapArrayPar src dst f) σ :=
  mapArray_wellformed_idxs src dst f hlen hdisj (List.range src.len) List.nodup_range
    (fun _ hi => List.mem_range.mp hi) σ

/-- One iteration costs two parallel rounds: the read must finish before the write starts.
-- ref: `docs/cost.md` -/
theorem mapArrayStep_time (src dst : ArrRef) (f : Val → Val) (i : Nat) (σ : State) :
    time (mapArrayStep src dst f i) σ = 2 := rfl

/-- An iteration takes at least one round — the non-degeneracy side condition `mapArray_time_lt`
needs, since a zero-cost branch could not shorten anything. -/
theorem mapArrayStep_time_pos (src dst : ArrRef) (f : Val → Val) (i : Nat) (σ : State) :
    0 < time (mapArrayStep src dst f i) σ := by rw [mapArrayStep_time]; omega

/-- **The parallel map is strictly faster**, in parallel rounds, as soon as there are two elements to
map. The companion to `mapArray_par_seq_eq`: same output, fewer rounds, and `time` is counted from a
round-by-round relation rather than stipulated at the `par` node. -- ref: `docs/cost.md` -/
theorem mapArray_time_lt (src dst : ArrRef) (f : Val → Val) (hlen : src.len = dst.len)
    (hdisj : src.base + src.len ≤ dst.base ∨ dst.base + dst.len ≤ src.base)
    (h2 : 2 ≤ src.len) (σ : State) :
    time (mapArrayPar src dst f) σ < time (mapArraySeq src dst f) σ := by
  obtain ⟨m, hm⟩ : ∃ m, src.len = m + 2 := ⟨src.len - 2, by omega⟩
  have hR : List.range src.len = 0 :: List.range' 1 (m + 1) := by
    rw [hm, List.range_eq_range', List.range'_succ]
  have hT : List.range' 1 (m + 1) = 1 :: List.range' 2 m := by rw [List.range'_succ]
  have hndT : (List.range' 1 (m + 1)).Nodup := List.nodup_range' 1
  have hbT : ∀ i ∈ List.range' 1 (m + 1), i < src.len := by
    intro i hi; rw [List.mem_range'_1] at hi; omega
  show time (ParM.parAll ((List.range src.len).map (mapArrayStep src dst f))) σ
      < time (ParM.seqAll ((List.range src.len).map (mapArrayStep src dst f))) σ
  rw [hR, List.map_cons]
  refine time_parAll_lt_seqAll _ _ σ ?_ (mapArrayStep_time_pos src dst f 0 σ) ?_
  · rw [← List.map_cons, ← hR]; exact mapArray_wellformed src dst f hlen hdisj σ
  · have hwfT := mapArray_wellformed_idxs src dst f hlen hdisj _ hndT hbT σ
    rw [hT, List.map_cons] at hwfT ⊢
    exact time_parAll_pos _ _ σ hwfT (mapArrayStep_time_pos src dst f 1 σ)

end Paralever
