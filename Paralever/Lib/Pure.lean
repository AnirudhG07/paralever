import Paralever.Lib.Reduce
import Paralever.Lib.OpaqueOp   -- for `readAll` and its footprint/runSeq lemmas

/-! # The pure ↔ `ParM` bridge

A user's algorithm is naturally a **pure** function of the heap: "look at these locations, fold them
together." `ParM` is needed only to make the *memory accesses visible as data* so `accesses` can see
them. This file provides the mechanical conversion in both directions and — the part that matters —
proves the conversion faithful:

    (runSeq (reduceFold (readsCombine locs f) m 0 init) σ).1 = foldPure σ locs f m 0 init

so the `ParM` program provably computes the pure specification. Generalizes
`Examples/SumArray.lean`'s hand-written `sumRange_eq_sumRangePure`.

Rationale: `docs/pure-bridge.md`. -/

namespace Paralever

-- ref: docs/pure-bridge.md; Blom et al. STTT'21 (sequential correctness ⇒ parallelised correctness)

/-! ### The read-and-combine body

One reduction step: read the locations this step needs, fold their values into the accumulator.
`locs k` is a *list*, so a step may read several cells (matmul reads one from `A` and one from `B`). -/

/-- The reduction body "read the cells step `k` needs, fold their values into `acc`". No writes: the
accumulator is returned as a value, not stored.

The split that makes the conversion mechanical — `f` is *what* to combine (pure, arbitrary), `locs`
is *where* to read (the layout, arithmetic only). -/
def readsCombine {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (k : Nat) (acc : α) : ParM α :=
  doₚ
    let vs ← readAll (locs k)
    .pure (f vs acc)

/-- The algorithm itself, with no monad: fold `f` over the values `σ` holds at `locs k`, for `fuel`
steps from index `k`. This is the specification `reduceFold_eq_foldPure` proves the `ParM` program
meets. -/
def foldPure {α : Type} (σ : State) (locs : Nat → List Loc) (f : List Val → α → α) :
    Nat → Nat → α → α
  | 0,        _, acc => acc
  | fuel + 1, k, acc => foldPure σ locs f fuel (k + 1) (f ((locs k).map σ) acc)

/-! ### Footprint of one step — immediate, no `Val` case splits -/

/-- One step reads exactly `locs k` and writes nothing, at every state and every accumulator. -/
@[simp, grind .]
theorem readsCombine_accesses {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (k : Nat) (acc : α) (σ : State) :
    accesses (readsCombine locs f k acc) σ = ⟨locs k, []⟩ := by
  simp only [readsCombine, accesses_bind, readAll_accesses, readAll_runSeq]
  simp [accesses, Footprint.union, Footprint.empty]

/-- A `readsCombine` step is reads and a `pure`, so it is well-formed unconditionally. -/
@[simp, grind .]
theorem readsCombine_wellformed {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (k : Nat) (acc : α) (σ : State) :
    WellFormed (readsCombine locs f k acc) σ := by
  simp only [readsCombine]
  rw [WellFormed_bind]
  exact ⟨readAll_wellformed _ _, trivial⟩

/-- Reads are confined to `P` as soon as every location this step touches satisfies `P`. One
arithmetic fact, no induction, no `Val` analysis. -/
@[grind .]
theorem readsCombine_readsWithin {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (k : Nat) (acc : α) (σ : State) (P : Loc → Prop) (h : ∀ l ∈ locs k, P l) :
    ReadsWithin (accesses (readsCombine locs f k acc) σ) P := by
  rw [readsCombine_accesses]; exact h

/-- **The accumulator is pure, so nothing is written.** -/
@[simp, grind .]
theorem readsCombine_no_writes {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (k : Nat) (acc : α) (σ : State) :
    (accesses (readsCombine locs f k acc) σ).writes = [] := by
  rw [readsCombine_accesses]

/-! ### Faithfulness — the `ParM` program computes the pure specification -/

/-- Reading never changes the state, so a `readsCombine` fold leaves `σ` alone. -/
@[grind .]
theorem reduceFold_readsCombine_state {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (σ : State) :
    ∀ (fuel k : Nat) (acc : α), (runSeq (reduceFold (readsCombine locs f) fuel k acc) σ).2 = σ := by
  intro fuel
  induction fuel with
  | zero => intro k acc; rfl
  | succ fuel ih =>
      intro k acc
      simp only [reduceFold, runSeq_bind, readsCombine, runSeq, readAll_runSeq]
      exact ih (k + 1) _

/-- **The bridge.** The `ParM` fold returns exactly what the pure fold computes. This is what makes
it legitimate to write the algorithm once, purely, and reason about the `ParM` version. -/
theorem reduceFold_eq_foldPure {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (σ : State) :
    ∀ (fuel k : Nat) (acc : α),
      (runSeq (reduceFold (readsCombine locs f) fuel k acc) σ).1 = foldPure σ locs f fuel k acc := by
  intro fuel
  induction fuel with
  | zero => intro k acc; rfl
  | succ fuel ih =>
      intro k acc
      simp only [reduceFold, runSeq_bind, readsCombine, runSeq, readAll_runSeq, foldPure]
      exact ih (k + 1) _

/-! ### The user-facing one-shot

`reduceArray_par_seq_eq` needs five hypotheses; for a `readsCombine` body three of them are
discharged generically above, leaving only arithmetic. -/

/-- `N` pure folds in parallel: iteration `p` folds `f` over the cells `locs p k` and writes
`dst p`. -/
def reduceArrayPureP {α : Type} (N m : Nat) (locs : Nat → Nat → List Loc) (f : List Val → α → α)
    (init : α) (toVal : α → Val) (dst : Nat → Loc) : ParM (List Unit) :=
  reduceArrayPar N m (fun p => readsCombine (locs p) f) init toVal dst

/-- Sequential counterpart of `reduceArrayPureP`. -/
def reduceArrayPureS {α : Type} (N m : Nat) (locs : Nat → Nat → List Loc) (f : List Val → α → α)
    (init : α) (toVal : α → Val) (dst : Nat → Loc) : ParM (List Unit) :=
  reduceArraySeq N m (fun p => readsCombine (locs p) f) init toVal dst

/-- **`N` independent pure folds in parallel.** Three hypotheses, all arithmetic: where the reads
land, that outputs are distinct, and that outputs avoid the read region. No footprint induction and
no `Val` case analysis anywhere at the call site. -/
theorem reduceArrayPure_par_seq_eq {α : Type} (N m : Nat) (locs : Nat → Nat → List Loc)
    (f : List Val → α → α) (init : α) (toVal : α → Val) (dst : Nat → Loc) (P : Loc → Prop)
    (hlocs : ∀ p, p < N → ∀ k, k < m → ∀ l ∈ locs p k, P l)
    (hdstinj : ∀ p q, p < N → q < N → p ≠ q → dst p ≠ dst q)
    (hdstout : ∀ p, p < N → ¬ P (dst p)) (σ : State) :
    reduceArrayPureP N m locs f init toVal dst
      ∥≡ reduceArrayPureS N m locs f init toVal dst from σ := by
  unfold reduceArrayPureP reduceArrayPureS
  exact reduceArray_par_seq_eq N m (fun p => readsCombine (locs p) f) init toVal dst P
    (fun p k acc σ' => readsCombine_wellformed _ f k acc σ')
    (fun p hp k hk acc σ' => readsCombine_readsWithin _ f k acc σ' P (hlocs p hp k hk))
    (fun p k acc σ' => readsCombine_no_writes _ f k acc σ')
    hdstinj hdstout σ

end Paralever
