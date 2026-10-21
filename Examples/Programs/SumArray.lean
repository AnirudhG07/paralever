import Paralever.Lib.Compose
import Paralever.Lib.Cost
import Paralever.Lib.Notation
import Lang.Core.Imp


namespace Paralever.Examples.SumArray
open ParM

/-- One entry per chunk, each an independently-sized list of locations. -/
abbrev ChunkPlan := List (List Loc)

/-- An array as a `State`: location `l` holds `vals[l]`, and `0` outside the range. -/
def arrayState (vals : List Int) : State := fun l => .int (vals.getD l 0)

/-! ### pure -/

def sumRangePure (σ : State) : List Loc → Int
  | []      => 0
  | l :: ls =>
      match σ l with
      | .int n => n + sumRangePure σ ls
      | _      => sumRangePure σ ls

/-! ### seq

`sumRange` is the per-chunk `ParM` conversion of `sumRangePure`: the same recursion with each `σ l`
lookup replaced by one `.read l k` effect. Written in raw constructors rather than `do`-notation so
the inductions below unfold without fighting the `Monad` instance — see `Lib/Notation.lean`. -/

def sumRange : List Loc → ParM Int
  | []      => .pure 0
  | l :: ls => .read l (fun v =>
      match v with
      | .int n => ParM.bind (sumRange ls) (fun rest => .pure (n + rest))
      | _      => sumRange ls)

def sumRangeSeq (chunks : ChunkPlan) : ParM (List Int) := ParM.seqAll (chunks.map sumRange)

/-! ### par -/

def sumRangePar (chunks : ChunkPlan) : ParM (List Int) := ParM.parAll (chunks.map sumRange)

/-! ### pure = seq -/

theorem sumRange_eq_sumRangePure (locs : List Loc) (σ : State) :
    (runSeq (sumRange locs) σ).1 = sumRangePure σ locs := by
  fun_induction sumRange <;> grind [= sumRange, = sumRangePure]

theorem sumRange_state_eq (locs : List Loc) (σ : State) : (runSeq (sumRange locs) σ).2 = σ := by
  fun_induction sumRange <;> grind

theorem pure_eq_seq (chunks : ChunkPlan) (σ : State) :
    (runSeq (sumRangeSeq chunks) σ).1 = chunks.map (sumRangePure σ) := by
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
      simp only [sumRangeSeq, List.map_cons, ParM.seqAll, ParM.seqPair, runSeq_bind, runSeq,
        sumRange_state_eq, sumRange_eq_sumRangePure]
      simp only [sumRangeSeq] at ih
      rw [ih]

/-! ### seq = par

Independence is free because both sides are write-free: Bernstein's three conditions are vacuous
when `w₁ = w₂ = ∅`. `indep_of_no_writes` (`Lib/Compose.lean`) needs *both* sides write-free. -/

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

theorem sumRange_wellformed (locs : List Loc) (σ : State) : WellFormed (sumRange locs) σ := by
  fun_induction sumRange <;> grind only [= WellFormed.eq_1, = WellFormed.eq_2, WellFormed_bind]

theorem sumRangePar_no_writes (chunks : ChunkPlan) (σ : State) :
    (accesses (sumRangePar chunks) σ).writes = [] := by
  induction chunks generalizing σ with
  | nil => rfl
  | cons c cs ih =>
      simp only [sumRangePar] at ih
      show (accesses (ParM.parAll ((c :: cs).map sumRange)) σ).writes = []
      rw [List.map_cons, accesses_parAll_cons]
      simp [Footprint.union, sumRange_no_writes, ih]

/-- Holds for *any* `ChunkPlan`, including uneven ones, and any state — no `decide`, so it does not
degrade with chunk count or chunk size. `sumRange` never writes, so the state never changes across
chunks (`sumRange_state_eq`) and chunk boundaries never need to be reasoned about. -/
theorem wellFormed_sumRangePar (chunks : ChunkPlan) (σ : State) :
    WellFormed (sumRangePar chunks) σ := by
  induction chunks generalizing σ with
  | nil => exact WellFormed_parAll_nil _
  | cons c cs ih =>
      simp only [sumRangePar, List.map_cons]
      apply WellFormed_parAll_cons
      · exact sumRange_wellformed _ _
      · exact indep_of_no_writes _ _ (sumRange_no_writes _ _) (sumRangePar_no_writes _ _)
      · rw [sumRange_state_eq]; exact ih σ

theorem seq_eq_par (chunks : ChunkPlan) (σ : State) :
    sumRangePar chunks ∥≡ sumRangeSeq chunks from σ :=
  parAll_par_seq_eq (chunks.map sumRange) σ (wellFormed_sumRangePar chunks σ)

/-! ### time par < time seq

`sumRange` is read-only, but a read is still a memory operation, so it still costs rounds: the
cost model counts rounds, not writes. A nonempty chunk begins with a `.read`, which is one round
whatever the state holds — that is `sumRange_time_pos`, and it is what `time_parAll_lt_seqAll`
needs of the head and of the tail. -/

theorem sumRange_time_pos (l : Loc) (ls : List Loc) (σ : State) :
    0 < time (sumRange (l :: ls)) σ :=
  time_pos _ σ rfl

/-- Two or more nonempty chunks: strictly fewer rounds in parallel. -/
theorem time_lt (l₁ : Loc) (ls₁ : List Loc) (l₂ : Loc) (ls₂ : List Loc) (rest : ChunkPlan)
    (σ : State) :
    time (sumRangePar ((l₁ :: ls₁) :: (l₂ :: ls₂) :: rest)) σ
      < time (sumRangeSeq ((l₁ :: ls₁) :: (l₂ :: ls₂) :: rest)) σ := by
  have hwf := wellFormed_sumRangePar ((l₁ :: ls₁) :: (l₂ :: ls₂) :: rest) σ
  have hwf' := wellFormed_sumRangePar ((l₂ :: ls₂) :: rest) σ
  simp only [sumRangePar, sumRangeSeq, List.map_cons] at hwf hwf' ⊢
  exact time_parAll_lt_seqAll _ _ σ hwf (sumRange_time_pos l₁ ls₁ σ)
    (time_parAll_pos _ _ σ hwf' (sumRange_time_pos l₂ ls₂ σ))

/-- Same work either way — only the rounds shrink. -/
theorem work_eq (chunks : ChunkPlan) (σ : State) :
    work (sumRangePar chunks) σ = work (sumRangeSeq chunks) σ :=
  work_parAll_eq_seqAll (chunks.map sumRange) σ

/-! ### Fixtures, shared with `SumArrayTask.lean`, and one concrete check -/

def vals8 : List Int := [1, 2, 3, 4, 5, 6, 7, 8]
def evenPlan8 : ChunkPlan := [[0, 1], [2, 3], [4, 5], [6, 7]]
def unevenPlan8 : ChunkPlan := [[0, 1, 2], [3], [4, 5, 6, 7]]

example : (runSeq (sumRangePar unevenPlan8) (arrayState vals8)).1 = [6, 4, 26] := by decide

/-! ## 4. The same program, written in the surface language

The same program in the DSL, where the obligation is decided rather than proved. One difference is
forced: registers are **thread-private**, so a thread cannot return a value the way
`sumRange : ParM Int` does — it writes its partial sum to a cell of its own, which is why `reduceK`'s
write set is one location per thread. -/

namespace Surface
open Paralever.Lang

/-- Chunk `c` zeroes an accumulator register, adds its `len` cells into it, and stores the partial
sum at `out + c`. Written in the surface syntax; `reduceK` builds the same thing. -/
def sumChunks (nchunks len out : Nat) : ParProg :=
  ParProg.parFor nchunks fun c =>
    ParProg.block
      ([ paralever { %0 := 0 } ]
        ++ (List.range len).map (fun k => paralever {
              %1 := [c * len + k];
              %0 := %0 + %1 })
        ++ [ paralever { [out + c] := %0 } ])

/-! At three chunks of two it is three threads, each reading its own pair and writing its own cell:

```text
parallel {
  thread 0 { t0 := 0; t1 := M[0]; t0 := (t0 + t1); t1 := M[1]; t0 := (t0 + t1); M[100] := t0; }
  thread 1 { t0 := 0; t1 := M[2]; t0 := (t0 + t1); t1 := M[3]; t0 := (t0 + t1); M[101] := t0; }
  thread 2 { t0 := 0; t1 := M[4]; t0 := (t0 + t1); t1 := M[5]; t0 := (t0 + t1); M[102] := t0; }
}
```
-/

-- #eval IO.println (ParProg.renderProg (sumChunks 3 2 100))

/-- The obligation, decided. -/
example : ParProg.wfB (sumChunks 3 2 100) = true := by decide
example : ParProg.wfB (sumChunks 8 4 100) = true := by decide

/-- …and Par = Seq follows with nothing further to supply. -/
theorem par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (sumChunks 3 2 100) ρ)
             (ParProg.execSeq (sumChunks 3 2 100) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- **Par ≤ Seq in rounds**, the cost counterpart, from the same `Bool`. §3's `time_lt` is the
hand-built `ParM` version of this; `ParProg.time_le` proves it once for the whole language. -/
theorem time_le (ρ : Regs) (σ : State) :
    time (ParProg.execPar (sumChunks 3 2 100) ρ) σ
      ≤ time (ParProg.execSeq (sumChunks 3 2 100) ρ) σ :=
  ParProg.time_le (by decide) ρ σ

/-- The two executions agree — proved, not observed — so a benchmark of `runTask` against
`runTaskSeq` measures speed and nothing else. -/
theorem runTask_eq_seq (ρ : Regs) (σ : State) :
    ParProg.runTask (sumChunks 3 2 100) ρ σ = ParProg.runTaskSeq (sumChunks 3 2 100) ρ σ :=
  ParProg.runTask_eq_runTaskSeq (by decide) ρ σ

/-- It runs on real threads — one `Task` per chunk — and `runTask_eq` says the threaded run computes
the sequential answer. On `[1,2,3,4,5,6]` the partial sums are `3, 7, 11`. -/
def σ6 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4 | 4 => .int 5 | 5 => .int 6
  | _ => .int 0

-- #eval ParProg.evalTask (sumChunks 3 2 100) σ6 [100, 101, 102]

theorem runTask_eq_runSeq (ρ : Regs) (σ : State) :
    ParProg.runTask (sumChunks 3 2 100) ρ σ
      = runSeq (ParProg.execPar (sumChunks 3 2 100) ρ) σ :=
  ParProg.runTask_eq (by decide) ρ σ

end Surface

end Paralever.Examples.SumArray
