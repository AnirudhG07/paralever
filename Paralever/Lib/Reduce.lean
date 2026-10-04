import Paralever.Pragma.ParallelFor
import Paralever.Lib.Notation

/-! # Reductions — `Σ`-shaped loops with a pure accumulator

`N` independent reductions in parallel: each folds over `[0,m)` reading index-determined locations,
accumulating in a **pure value** (not a heap cell), then writes one output. Because the accumulator
is pure, a whole reduction's write set is a single location — so independence is two arithmetic
facts: `dst` injective, and `dst` outside the read region.

Does for `Σ` what `Pragma/MapArray.lean` does for elementwise map.

Rationale: `docs/reductions.md`. -/

namespace Paralever
open Paralever.Pragma.ParallelFor

-- ref: docs/reductions.md; Blom et al. STTT'21 §3 (iteration contracts encoding data dependences)

/-! ### The fold -/

/-- Fold `body` over `fuel` steps starting at index `k`, threading a pure accumulator. -/
def reduceFold {α : Type} (body : Nat → α → ParM α) : Nat → Nat → α → ParM α
  | 0,        _, acc => .pure acc
  | fuel + 1, k, acc => ParM.bind (body k acc) (reduceFold body fuel (k + 1))

/-- One reduction: fold, then write the result to `dst`. The only write in the whole thing. -/
def reduceInto {α : Type} (body : Nat → α → ParM α) (m : Nat) (init : α)
    (toVal : α → Val) (dst : Loc) : ParM Unit :=
  ParM.bind (reduceFold body m 0 init) (fun s => .write dst (toVal s) .pure)

/-! ### Fold lemmas — the fuel induction, written once

Hypotheses are `∀ σ'` because a reduction body's footprint depends on indices, not on state;
see `docs/reductions.md`. -/

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

/-- The read bound is stated for in-range indices only (`k < m`), because that is all the fold ever
supplies — a body's address arithmetic is typically only in range for `k < m`. -/
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

@[grind .]
theorem reduceInto_wellformed {α : Type} (body : Nat → α → ParM α) (m : Nat) (init : α)
    (toVal : α → Val) (dst : Loc)
    (hwf : ∀ k acc σ', WellFormed (body k acc) σ') (σ : State) :
    WellFormed (reduceInto body m init toVal dst) σ := by
  simp only [reduceInto]
  rw [WellFormed_bind]
  exact ⟨reduceFold_wellformed body hwf m 0 init σ, trivial⟩

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

/-- The payoff of a pure accumulator: the whole reduction writes **one** location. -/
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

def reduceArrayPar {α : Type} (N m : Nat) (body : Nat → Nat → α → ParM α) (init : α)
    (toVal : α → Val) (dst : Nat → Loc) : ParM (List Unit) :=
  ParM.parAll ((List.range N).map (fun p => reduceInto (body p) m init toVal (dst p)))

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

end Paralever
