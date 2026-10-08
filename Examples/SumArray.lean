import Paralever.Lib.Compose
import Paralever.Lib.Cost
import Paralever.Lib.Notation

/-! # Chunked sum of an array, uneven chunks included

The six standard steps: **pure**, **seq**, **par**, then `pure = seq`, `seq = par`,
`time par < time seq`. A `ChunkPlan` is any `List (List Loc)`, so chunks may differ in size and
need not be contiguous; every theorem below holds for an arbitrary plan. Rationale:
`docs/decomposition.md`, `docs/cost.md`. -/

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

end Paralever.Examples.SumArray
