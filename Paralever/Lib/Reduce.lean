import Paralever.Lib.Loop
import Paralever.Lib.Notation
import Paralever.Lib.Cost

/-! # Reductions — `Σ`-shaped loops with a pure accumulator

`N` independent reductions in parallel: each folds over `[0,m)` reading index-determined locations,
accumulating in a **pure value** (not a heap cell), then writes one output. Because the accumulator
is pure, a whole reduction's write set is a single location — so independence is two arithmetic
facts: `dst` injective, and `dst` outside the read region.

Does for `Σ` what `Kernels/MapArray.lean` does for elementwise map.

Rationale: `docs/reductions.md`. -/

namespace Paralever
open Paralever.Loop

-- ref: docs/reductions.md; Blom et al. STTT'21 §3 (iteration contracts encoding data dependences)

/-! ### The fold -/

/-- Run `body k`, `body (k+1)`, … for `fuel` steps, threading the accumulator through as an ordinary
Lean value. The accumulator is never a heap cell, which is why the inner loop of a reduction
contributes reads only. -/
def reduceFold {α : Type} (body : Nat → α → ParM α) : Nat → Nat → α → ParM α
  | 0,        _, acc => .pure acc
  | fuel + 1, k, acc => doₚ
      let acc' ← body k acc
      reduceFold body fuel (k + 1) acc'

/-- One whole reduction: fold `body` over `[0,m)` from `init`, then store the result at `dst` through
`toVal`. That store is the program's only write. -/
def reduceInto {α : Type} (body : Nat → α → ParM α) (m : Nat) (init : α)
    (toVal : α → Val) (dst : Loc) : ParM Unit :=
  doₚ
    let s ← reduceFold body m 0 init
    .write dst (toVal s) .pure

/-! ### Fold lemmas — the fuel induction, written once

Hypotheses are `∀ σ'` because a reduction body's footprint depends on indices, not on state;
see `docs/reductions.md`. -/

/-- A fold of well-formed bodies is well-formed: the fold itself introduces no `par` node. -/
@[grind .]
theorem reduceFold_wellformed {α : Type} (body : Nat → α → ParM α)
    (hwf : ∀ k acc σ', WellFormed (body k acc) σ') :
    ∀ (fuel k : Nat) (acc : α) (σ : State), WellFormed (reduceFold body fuel k acc) σ := by
  intro fuel
  induction fuel with
  | zero => intro k acc σ; trivial
  | succ fuel ih =>
      intro k acc σ
      simp only [reduceFold]
      rw [WellFormed_bind]
      exact ⟨hwf k acc σ, ih (k + 1) _ _⟩

/-- If no step writes, the whole fold writes nothing — however much fuel it is given. -/
@[grind .]
theorem reduceFold_no_writes {α : Type} (body : Nat → α → ParM α)
    (hnw : ∀ k acc σ', (accesses (body k acc) σ').writes = []) :
    ∀ (fuel k : Nat) (acc : α) (σ : State), (accesses (reduceFold body fuel k acc) σ).writes = [] := by
  intro fuel
  induction fuel with
  | zero => intro k acc σ; rfl
  | succ fuel ih =>
      intro k acc σ
      simp only [reduceFold, accesses_bind, Footprint.union]
      simp [hnw k acc σ, ih (k + 1)]

/-- A fold whose every step reads within `P` reads within `P`. This is the fuel induction each
reduction example used to write for itself.

`hr` is required only at in-range indices (`k < m`), since `k + fuel ≤ m` is all the fold ever
supplies and a body's address arithmetic is typically in range only there. -/
@[grind .]
theorem reduceFold_readsWithin {α : Type} (body : Nat → α → ParM α) (P : Loc → Prop) (m : Nat)
    (hr : ∀ k, k < m → ∀ (acc : α) (σ' : State), ReadsWithin (accesses (body k acc) σ') P) :
    ∀ (fuel k : Nat), k + fuel ≤ m → ∀ (acc : α) (σ : State),
      ReadsWithin (accesses (reduceFold body fuel k acc) σ) P := by
  intro fuel
  induction fuel with
  | zero => intro k _ acc σ; exact ReadsWithin.empty _
  | succ fuel ih =>
      intro k hk acc σ
      simp only [reduceFold, accesses_bind]
      exact ReadsWithin.union (hr k (by omega) acc σ) (ih (k + 1) (by omega) _ _)

/-! ### One reduction's footprint: reads in `P`, writes exactly `{dst}` -/

/-- One reduction is well-formed as soon as its body is. -/
@[grind .]
theorem reduceInto_wellformed {α : Type} (body : Nat → α → ParM α) (m : Nat) (init : α)
    (toVal : α → Val) (dst : Loc)
    (hwf : ∀ k acc σ', WellFormed (body k acc) σ') (σ : State) :
    WellFormed (reduceInto body m init toVal dst) σ := by
  simp only [reduceInto]
  rw [WellFormed_bind]
  exact ⟨reduceFold_wellformed body hwf m 0 init σ, trivial⟩

/-- One reduction's reads stay inside `P`: the closing write adds a write, never a read. -/
@[grind .]
theorem reduceInto_readsWithin {α : Type} (body : Nat → α → ParM α) (m : Nat) (init : α)
    (toVal : α → Val) (dst : Loc) (P : Loc → Prop)
    (hr : ∀ k, k < m → ∀ (acc : α) (σ' : State), ReadsWithin (accesses (body k acc) σ') P)
    (σ : State) :
    ReadsWithin (accesses (reduceInto body m init toVal dst) σ) P := by
  simp only [reduceInto, accesses_bind]
  refine ReadsWithin.union (reduceFold_readsWithin body P m hr m 0 (by omega) init σ) ?_
  simp only [accesses]
  exact ReadsWithin.union (ReadsWithin.write _ _) (ReadsWithin.empty _)

/-- **The whole reduction writes one location, `dst`.** The payoff of keeping the accumulator pure,
and the reason `Indep` — which only ever checks writes — is cheap for reductions. -/
@[grind .]
theorem reduceInto_writesWithin {α : Type} (body : Nat → α → ParM α) (m : Nat) (init : α)
    (toVal : α → Val) (dst : Loc)
    (hnw : ∀ k acc σ', (accesses (body k acc) σ').writes = []) (σ : State) :
    WritesWithin (accesses (reduceInto body m init toVal dst) σ) (fun l => l = dst) := by
  simp only [reduceInto, accesses_bind]
  intro l hl
  simp only [Footprint.union, List.mem_append] at hl
  rcases hl with h | h
  · rw [reduceFold_no_writes body hnw m 0 init σ] at h; simp at h
  · simp only [accesses, Footprint.union, Footprint.empty] at h; simp at h; exact h

/-! ### The headline theorem -/

/-- `N` reductions run in parallel: iteration `p` folds `body p` over `[0,m)` and writes `dst p`. -/
def reduceArrayPar {α : Type} (N m : Nat) (body : Nat → Nat → α → ParM α) (init : α)
    (toVal : α → Val) (dst : Nat → Loc) : ParM (List Unit) :=
  ParM.parAll ((List.range N).map (fun p => reduceInto (body p) m init toVal (dst p)))

/-- Sequential counterpart of `reduceArrayPar`: the same `N` reductions, run one after another. -/
def reduceArraySeq {α : Type} (N m : Nat) (body : Nat → Nat → α → ParM α) (init : α)
    (toVal : α → Val) (dst : Nat → Loc) : ParM (List Unit) :=
  ParM.seqAll ((List.range N).map (fun p => reduceInto (body p) m init toVal (dst p)))

/-- **`N` independent reductions in parallel reach exactly the sequential outcomes.**

Reads are confined to one shared predicate `P` — deliberately the *same* for every iteration, so
reductions may overlap their reads arbitrarily (matmul's row sharing). The only checks are the two
arithmetic facts `hdstinj` (distinct outputs) and `hdstout` (outputs outside the read region). -/
theorem reduceArray_par_seq_eq {α : Type} (N m : Nat) (body : Nat → Nat → α → ParM α) (init : α)
    (toVal : α → Val) (dst : Nat → Loc) (P : Loc → Prop)
    (hwf : ∀ p k acc σ', WellFormed (body p k acc) σ')
    (hreads : ∀ p, p < N → ∀ k, k < m → ∀ (acc : α) (σ' : State),
      ReadsWithin (accesses (body p k acc) σ') P)
    (hnowrite : ∀ p k acc σ', (accesses (body p k acc) σ').writes = [])
    (hdstinj : ∀ p q, p < N → q < N → p ≠ q → dst p ≠ dst q)
    (hdstout : ∀ p, p < N → ¬ P (dst p)) (σ : State) :
    reduceArrayPar N m body init toVal dst ∥≡ reduceArraySeq N m body init toVal dst from σ := by
  unfold reduceArrayPar reduceArraySeq
  apply parAll_par_seq_eq_of_indexed_rw (List.range N)
    (fun p => reduceInto (body p) m init toVal (dst p))
    (fun _ => P) (fun p l => l = dst p) List.nodup_range
  · intro p _ σ'; exact reduceInto_wellformed (body p) m init toVal (dst p) (hwf p) σ'
  · intro p hp σ'
    exact reduceInto_readsWithin (body p) m init toVal (dst p) P
      (hreads p (List.mem_range.mp hp)) σ'
  · intro p _ σ'; exact reduceInto_writesWithin (body p) m init toVal (dst p) (hnowrite p) σ'
  · intro p q hp hq hpq l hlp hlq
    exact hdstinj p q (List.mem_range.mp hp) (List.mem_range.mp hq) hpq (hlp ▸ hlq)
  · intro p q hp _ _ l hlp hlq
    exact hdstout p (List.mem_range.mp hp) (hlp ▸ hlq)

/-! ### Cost of a reduction -/

/-- A reduction always ends by writing its output, so it always costs at least one round. -/
theorem reduceInto_time_pos {α : Type} (body : Nat → α → ParM α) (m : Nat) (init : α)
    (toVal : α → Val) (dst : Loc) (hwf : ∀ k acc σ', WellFormed (body k acc) σ') (σ : State) :
    0 < time (reduceInto body m init toVal dst) σ := by
  have hb : reduceInto body m init toVal dst =
      ParM.bind (reduceFold body m 0 init) (fun s => ParM.write dst (toVal s) ParM.pure) := rfl
  rw [hb, time_bind_add _ _ σ (hb ▸ reduceInto_wellformed body m init toVal dst hwf σ)]
  have : time (ParM.write dst (toVal (runSeq (reduceFold body m 0 init) σ).1) ParM.pure)
      (runSeq (reduceFold body m 0 init) σ).2 = 1 := rfl
  omega

/-- `WellFormed` for the reductions indexed by an arbitrary duplicate-free `idxs ⊆ [0,N)`, not just
`List.range N`. Needed by `reduceArray_time_lt`, which peels indices off the front and must still
know the remaining tail is well-formed. -/
theorem reduceArray_wellformed_idxs {α : Type} (N m : Nat) (body : Nat → Nat → α → ParM α)
    (init : α) (toVal : α → Val) (dst : Nat → Loc) (P : Loc → Prop)
    (hwf : ∀ p k acc σ', WellFormed (body p k acc) σ')
    (hreads : ∀ p, p < N → ∀ k, k < m → ∀ (acc : α) (σ' : State),
      ReadsWithin (accesses (body p k acc) σ') P)
    (hnowrite : ∀ p k acc σ', (accesses (body p k acc) σ').writes = [])
    (hdstinj : ∀ p q, p < N → q < N → p ≠ q → dst p ≠ dst q)
    (hdstout : ∀ p, p < N → ¬ P (dst p))
    (idxs : List Nat) (hnd : idxs.Nodup) (hb : ∀ p ∈ idxs, p < N) (σ : State) :
    WellFormed (ParM.parAll (idxs.map
      (fun p => reduceInto (body p) m init toVal (dst p)))) σ :=
  (parAll_wellformed_of_indexed_rw idxs (fun p => reduceInto (body p) m init toVal (dst p))
    (fun _ => P) (fun p l => l = dst p) hnd
    (fun p _ σ' => reduceInto_wellformed (body p) m init toVal (dst p) (hwf p) σ')
    (fun p hp σ' => reduceInto_readsWithin (body p) m init toVal (dst p) P
      (hreads p (hb p hp)) σ')
    (fun p _ σ' => reduceInto_writesWithin (body p) m init toVal (dst p) (hnowrite p) σ')
    (fun p q hp hq hpq _ hlp hlq => hdstinj p q (hb p hp) (hb q hq) hpq (hlp ▸ hlq))
    (fun p _ hp _ _ _ hlp hPl => hdstout p (hb p hp) (hlp ▸ hPl)) σ).1

/-- **`time par < time seq`** for `N ≥ 2` independent reductions. Same hypotheses as
`reduceArray_par_seq_eq`, plus `2 ≤ N`. -/
theorem reduceArray_time_lt {α : Type} (N m : Nat) (body : Nat → Nat → α → ParM α) (init : α)
    (toVal : α → Val) (dst : Nat → Loc) (P : Loc → Prop)
    (hwf : ∀ p k acc σ', WellFormed (body p k acc) σ')
    (hreads : ∀ p, p < N → ∀ k, k < m → ∀ (acc : α) (σ' : State),
      ReadsWithin (accesses (body p k acc) σ') P)
    (hnowrite : ∀ p k acc σ', (accesses (body p k acc) σ').writes = [])
    (hdstinj : ∀ p q, p < N → q < N → p ≠ q → dst p ≠ dst q)
    (hdstout : ∀ p, p < N → ¬ P (dst p)) (h2 : 2 ≤ N) (σ : State) :
    time (reduceArrayPar N m body init toVal dst) σ
      < time (reduceArraySeq N m body init toVal dst) σ := by
  obtain ⟨M, hM⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hR : List.range N = 0 :: List.range' 1 (M + 1) := by
    rw [hM, List.range_eq_range', List.range'_succ]
  have hT : List.range' 1 (M + 1) = 1 :: List.range' 2 M := by rw [List.range'_succ]
  have hndT : (List.range' 1 (M + 1)).Nodup := List.nodup_range' 1
  have hbT : ∀ p ∈ List.range' 1 (M + 1), p < N := by
    intro p hp; rw [List.mem_range'_1] at hp; omega
  have wf := reduceArray_wellformed_idxs N m body init toVal dst P hwf hreads hnowrite
    hdstinj hdstout
  have hwfFull := wf (List.range N) List.nodup_range (fun _ hp => List.mem_range.mp hp) σ
  have hwfT := wf _ hndT hbT σ
  rw [hR, List.map_cons] at hwfFull
  rw [hT, List.map_cons] at hwfT
  have hpos : 0 < time (ParM.parAll ((List.range' 1 (M + 1)).map
      (fun p => reduceInto (body p) m init toVal (dst p)))) σ := by
    rw [hT, List.map_cons]
    exact time_parAll_pos _ _ σ hwfT
      (reduceInto_time_pos (body 1) m init toVal (dst 1) (hwf 1) σ)
  show time (ParM.parAll ((List.range N).map _)) σ < time (ParM.seqAll ((List.range N).map _)) σ
  rw [hR, List.map_cons]
  exact time_parAll_lt_seqAll _ _ σ hwfFull
    (reduceInto_time_pos (body 0) m init toVal (dst 0) (hwf 0) σ) hpos

end Paralever
