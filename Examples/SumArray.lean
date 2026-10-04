import Paralever.Theory.Sequentialize

/-! # Example: chunked reduce, uneven pieces included

Sum an array by splitting it into chunks, summing each independently, then combining — the
`parAll`/`seqAll` case (`docs/decomposition.md`'s N-ary generalization).

**Pure first, then `ParM`.** `sumRangePure` is an ordinary recursive `Int`-returning function —
no monad. `sumRange` is its `ParM` *conversion*: same recursive shape, one `σ l` lookup replaced
by one `.read l k` effect per step. `sumRange_eq_sumRangePure` proves the conversion is faithful,
by induction that mirrors the two definitions step for step.

**Chunks can be uneven.** A `ChunkPlan` is a plain `List (List Loc)`, one entry per chunk, each an
independently-sized list of locations — no assumption that `n` divides evenly by the chunk count.
`sumRangePar`/`sumRangeSeq` are named wrappers over `ParM.parAll`/`ParM.seqAll`, so the headline
theorem reads as `ParSeqEq (sumRangePar chunks) (sumRangeSeq chunks) σ` — the two things actually
being equated are named, not buried inside raw combinator applications.

Three further sections, answering "does this scale?" honestly:

- **§1 (n = 8)**: `decide` on concrete footprints works fine.
- **§2 (n = 100)**: `decide` on 25-element chunk footprints **times out** — kernel-level list
  membership checking is not compiled code, and does not scale the way `native_decide` would (we
  don't use `native_decide`; see `CLAUDE.md`). This is a real wall, not a hypothetical one.
- **§3 (arbitrary n, arbitrary chunking)**: the actual fix is not a faster decision procedure —
  it's a **proof**. `wellFormed_sumRangePar` below is proved once, for *any* `ChunkPlan`
  (including uneven ones) and any array, and covers §1 and §2 as special cases with no `decide` at
  all. It works because `sumRange` never writes, so Bernstein's conditions are vacuous regardless
  of how chunk boundaries fall — see `indep_of_no_writes`. A version with writes (e.g. storing
  partial sums into an output array) would not get this for free and would need real
  chunk-disjointness reasoning for arbitrary chunking: an arithmetic disjointness lemma over
  `List.range'`, discharged by `omega`, not `decide` — flagged here as the natural next step should
  a write-based variant of this example be needed.

`wellFormed_sumRangePar`/`sumRange_par_seq_eq` still carry the one open dependency tracked as a
TODO in `Theory/Decomposition.lean` (`wellFormed_canonical`'s `par` case) — see
`docs/decomposition.md`. Everything else in this file is sorry-free.
-/

namespace Paralever.Examples.SumArray

open ParM

/-! ### The pure algorithm, and its conversion into `ParM` -/

/-- Ordinary recursive `Int`-returning function. No monad, no `ParM` — this is the algorithm,
stated as plainly as possible: look up a location's value, add it to the sum of the rest. -/
def sumRangePure (σ : State) : List Loc → Int
  | []      => 0
  | l :: ls =>
      match σ l with
      | .int n => n + sumRangePure σ ls
      | _      => sumRangePure σ ls

/-- The `ParM` **conversion** of `sumRangePure`: same recursion, same shape, one change per
step — a direct `σ l` lookup becomes a `.read l k` effect, threading the rest of the computation
through the continuation `k` instead of a direct recursive call. Written in `ParM` constructors
(not `do`-notation) so the inductive proof below unfolds by `simp`/`rfl` without fighting the
`Monad` instance. -/
def sumRange : List Loc → ParM Int
  | []      => .pure 0
  | l :: ls => .read l (fun v =>
      match v with
      | .int n => ParM.bind (sumRange ls) (fun rest => .pure (n + rest))
      | _      => sumRange ls)

/-- The conversion is faithful: `sumRange`'s `ParM` computation, against any state `σ`, agrees
with `sumRangePure σ` on the same locations. Proved by induction on the location list, mirroring
`sumRangePure`/`sumRange`'s shared recursive shape case for case. -/
theorem sumRange_eq_sumRangePure (locs : List Loc) (σ : State) :
    (runSeq (sumRange locs) σ).1 = sumRangePure σ locs := by
  induction locs generalizing σ with
  | nil => rfl
  | cons l ls ih =>
      simp only [sumRange, sumRangePure, runSeq]
      cases σ l with
      | int n => simp [runSeq_bind, ih]
      | bool b => exact ih σ
      | unit => exact ih σ

/-- An array as a `State`: value at location `l` is `vals[l]` (0 outside range). Scales to any
size with no per-location cases — this is the answer to "do I write out `σ0` by hand for 100
locations": no, you write this once. -/
def arrayState (vals : List Int) : State := fun l => .int (vals.getD l 0)

/-! ### `sumRange` never writes — this is what makes independence free -/

theorem sumRange_no_writes (locs : List Loc) (σ : State) :
    (accesses (sumRange locs) σ).writes = [] := by
  induction locs generalizing σ with
  | nil => rfl
  | cons l ls ih =>
      simp only [sumRange, accesses]
      cases σ l with
      | int n => simp [accesses_bind, Footprint.union, Footprint.empty, ih]
      | bool b => exact ih σ
      | unit => exact ih σ

theorem sumRange_state_eq (locs : List Loc) (σ : State) : (runSeq (sumRange locs) σ).2 = σ := by
  funext l
  by_cases hl : l ∈ (accesses (sumRange locs) σ).writes
  · rw [sumRange_no_writes] at hl; simp at hl
  · exact runSeq_frame (sumRange locs) σ l hl

theorem sumRange_wellformed (locs : List Loc) (σ : State) : WellFormed (sumRange locs) σ := by
  induction locs generalizing σ with
  | nil => trivial
  | cons l ls ih =>
      simp only [sumRange, WellFormed]
      cases σ l with
      | int n => rw [WellFormed_bind]; exact ⟨ih σ, trivial⟩
      | bool b => exact ih σ
      | unit => exact ih σ

/-- Both sides write-free is what actually makes Bernstein vacuous — one side alone is *not*
enough: the third condition (`g`'s writes vs `f`'s reads) needs `g` write-free too. A write-based
variant of this example (e.g. writing partial sums into an output array) would not get this for
free and would need real chunk-disjointness reasoning — see the module docstring. -/
theorem indep_of_no_writes {f g : Footprint} (hf : f.writes = []) (hg : g.writes = []) :
    Indep f g := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl _; rw [hf] at hl; simp at hl
  · intro l hl _; rw [hf] at hl; simp at hl
  · intro l hl _; rw [hg] at hl; simp at hl

/-! ### Chunk plans — uneven splits, named `par`/`seq` versions -/

/-- A parallelization plan: one entry per chunk, each an arbitrary, independently-sized list of
locations. No uniform chunk size is assumed anywhere below — chunks may differ in length, be
non-contiguous, whatever the caller likes. This is genuinely uneven chunking, not a special case
of an even split. -/
abbrev ChunkPlan := List (List Loc)

/-- Sum every chunk in `chunks`, in parallel, and return the list of partial sums. The named
wrapper is the point: the headline theorem reads as `ParSeqEq (sumRangePar chunks)
(sumRangeSeq chunks) σ`, not a bare `parAll (chunks.map sumRange)`. -/
def sumRangePar (chunks : ChunkPlan) : ParM (List Int) := ParM.parAll (chunks.map sumRange)

/-- The sequential counterpart: same chunks, same combine, run one after another. -/
def sumRangeSeq (chunks : ChunkPlan) : ParM (List Int) := ParM.seqAll (chunks.map sumRange)

/-- `Σ∥ f, chunks` / `Σ; f, chunks`: map `f` over every chunk (in parallel / in sequence) and add
the partial results — the first real piece of the `Notation/` layer sketched in `PLAN.md`
(`∥`, `A[i]`, `parallel for`), specialized to "sum." Pure `macro_rules`, so it can never affect
any proof: it expands to exactly `sumRangePar`/`sumRangeSeq` plus one `foldl`, which
`sum_notation_eq` below checks by `rfl`. -/
syntax "Σ∥ " term ", " term : term
macro_rules
  | `(Σ∥ $f, $chunks) =>
      `(ParM.bind (ParM.parAll (List.map $f $chunks)) (fun rs => ParM.pure (List.foldl (· + ·) 0 rs)))

syntax "Σ; " term ", " term : term
macro_rules
  | `(Σ; $f, $chunks) =>
      `(ParM.bind (ParM.seqAll (List.map $f $chunks)) (fun rs => ParM.pure (List.foldl (· + ·) 0 rs)))

example (chunks : ChunkPlan) :
    (Σ∥ sumRange, chunks : ParM Int)
      = ParM.bind (sumRangePar chunks) (fun rs => ParM.pure (rs.foldl (· + ·) 0)) := rfl

example (chunks : ChunkPlan) :
    (Σ; sumRange, chunks : ParM Int)
      = ParM.bind (sumRangeSeq chunks) (fun rs => ParM.pure (rs.foldl (· + ·) 0)) := rfl

theorem sumRangePar_no_writes (chunks : ChunkPlan) (σ : State) :
    (accesses (sumRangePar chunks) σ).writes = [] := by
  induction chunks generalizing σ with
  | nil => rfl
  | cons c cs ih =>
      simp only [sumRangePar] at ih
      simp only [sumRangePar, List.map_cons, ParM.parAll, ParM.parPair, accesses_bind, accesses,
        Footprint.union, Footprint.empty]
      simp [sumRange_no_writes, ih]

/-- **General**, for *any* `ChunkPlan` — including uneven ones — and any array. No `decide`
anywhere, so this scales to arbitrary chunk counts and sizes, not just a concrete instance.
Because `sumRange` never writes, the state literally never changes across chunks
(`sumRange_state_eq`), so the induction needs no bookkeeping about where one chunk ends and the
next begins. -/
theorem wellFormed_sumRangePar (chunks : ChunkPlan) (vals : List Int) :
    WellFormed (sumRangePar chunks) (arrayState vals) := by
  induction chunks with
  | nil => exact WellFormed_parAll_nil _
  | cons c cs ih =>
      simp only [sumRangePar, List.map_cons]
      apply WellFormed_parAll_cons
      · exact sumRange_wellformed _ _
      · exact indep_of_no_writes (sumRange_no_writes _ _) (sumRangePar_no_writes _ _)
      · rw [sumRange_state_eq]; exact ih

/-- The metatheorem, named end to end: summing `chunks` in parallel reaches exactly the outcomes
summing them in sequence does, for any chunk plan and any array. -/
theorem sumRange_par_seq_eq (chunks : ChunkPlan) (vals : List Int) :
    ParSeqEq (sumRangePar chunks) (sumRangeSeq chunks) (arrayState vals) :=
  parAll_par_seq_eq (chunks.map sumRange) (arrayState vals) (wellFormed_sumRangePar chunks vals)

/-! ### §1 — n = 8, even chunks. `decide` works fine at this size. -/

def evenPlan8 : ChunkPlan := [[0, 1], [2, 3], [4, 5], [6, 7]]
def vals8 : List Int := [1, 2, 3, 4, 5, 6, 7, 8]

example : (runSeq (sumRangePar evenPlan8) (arrayState vals8)).1 = [3, 7, 11, 15] := by decide

/-! ### §1b — genuinely uneven chunks: sizes 3, 1, 4 over the same 8-element array. -/

def unevenPlan8 : ChunkPlan := [[0, 1, 2], [3], [4, 5, 6, 7]]

example : (runSeq (sumRangePar unevenPlan8) (arrayState vals8)).1 = [6, 4, 26] := by decide

example : WellFormed (sumRangePar unevenPlan8) (arrayState vals8) :=
  wellFormed_sumRangePar unevenPlan8 vals8

/-! ### §2 — n = 100. `decide` on the `Indep` check between a 25-element chunk and the combined
75-element remainder times out: kernel-reduction list-membership checking is quadratic in list
length and is not compiled code. The fix is not a bigger heartbeat budget — it's
`wellFormed_sumRangePar`, which needs no `decide` at all. -/

def vals100 : List Int := (List.range 100).map (fun i : Nat => (i : Int) + 1)

/-- Even split of 100 into 4 chunks of 25 — built as a `ChunkPlan` literal via `List.range'`,
still just an instance of the general uneven-capable machinery above. -/
def evenPlan100 : ChunkPlan := (List.range 4).map (fun i => List.range' (i * 25) 25)

example : WellFormed (sumRangePar evenPlan100) (arrayState vals100) :=
  wellFormed_sumRangePar evenPlan100 vals100

/-! ### §3 — arbitrary n, arbitrary (including uneven) chunking. Already proved in general above:
`sumRange_par_seq_eq` is the theorem, for any `ChunkPlan` and any array. -/

end Paralever.Examples.SumArray
