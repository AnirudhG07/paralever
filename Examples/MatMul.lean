import Paralever.Lib.Reduce

/-! # Example: parallel matrix multiply — the demo `PLAN.md` calls "probably the most compelling"

Every cell `C[i,j] = Σ_k A[i,k]*B[k,j]` is computed by its own independent task. **This is the one
example that genuinely cannot be proved independent without Bernstein**: cell `(i,j)` writes only its
own output `C[i,j]`, but reads an entire row of `A` and an entire column of `B` — and different cells'
rows/columns overlap constantly (every cell in row `i` reads the *same* row of `A`). A naive `∗`-style
exclusive-heap-split treatment would reject this outright.

The proof needs none of that overlap reasoning. `Lib/Reduce.lean` discharges the fuel induction
generically; all this file supplies is the layout (`A` at `[0,n²)`, `B` at `[n²,2n²)`, `C` at
`[2n²,3n²)`), a one-step body, and the two arithmetic facts that `C`'s cells are distinct and lie
outside `A`/`B`. Reads are confined to one *shared* predicate, so row/column overlap is never
mentioned — see `docs/reductions.md`. -/

namespace Paralever.Examples.MatMul
open Paralever

/-! ### Layout and the one-step body — the only manual parts

The accumulator is a plain `Int`, never a heap cell. That is what makes the whole inner loop
read-only, hence a cell's write set a single location. -/

/-- One step of `Σ_k A[i,k]*B[k,j]` for cell `p = i*n+j`: read `A[i,k]`, read `B[k,j]`, accumulate. -/
def dotBody (n p k : Nat) (acc : Int) : ParM Int :=
  .read (p / n * n + k) (fun va => .read (n * n + (k * n + p % n)) (fun vb =>
    match va, vb with
    | .int a, .int b => .pure (acc + a * b)
    | _, _ => .pure acc))

/-- `A` and `B` together occupy `[0, 2n²)`; `C` starts at `2n²`. -/
def InputRegion (n : Nat) (l : Loc) : Prop := l < n * n + n * n

def cellLoc (n p : Nat) : Loc := n * n + n * n + p

def matmulPar (n : Nat) : ParM (List Unit) :=
  reduceArrayPar (n * n) n (dotBody n) 0 Val.int (cellLoc n)

def matmulSeq (n : Nat) : ParM (List Unit) :=
  reduceArraySeq (n * n) n (dotBody n) 0 Val.int (cellLoc n)

/-! ### The three facts about `dotBody`, each one line -/

theorem dotBody_wellformed (n p k : Nat) (acc : Int) (σ : State) :
    WellFormed (dotBody n p k acc) σ := by
  simp only [dotBody, WellFormed]
  cases σ (p / n * n + k) <;> cases σ (n * n + (k * n + p % n)) <;> trivial

/-- Both reads land below `2n²` — `A`'s row and `B`'s column, bounded *loosely*, since Bernstein
never needs to know which row or column, only that it is on the input side. -/
theorem dotBody_readsWithin (n p k : Nat) (hp : p < n * n) (hk : k < n) (acc : Int) (σ : State) :
    ReadsWithin (accesses (dotBody n p k acc) σ) (InputRegion n) := by
  have hn : 0 < n := by rcases Nat.eq_zero_or_pos n with h | h; · subst h; simp at hp
                        · exact h
  have hA : p / n * n + k < n * n + n * n := by
    have h1 : p / n < n := Nat.div_lt_of_lt_mul (by omega)
    have h2 : p / n * n + k < (p / n + 1) * n := by rw [Nat.succ_mul]; omega
    have h3 : (p / n + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
    omega
  have hB : n * n + (k * n + p % n) < n * n + n * n := by
    have h1 : p % n < n := Nat.mod_lt p hn
    have h2 : k * n + p % n < (k + 1) * n := by rw [Nat.succ_mul]; omega
    have h3 : (k + 1) * n ≤ n * n := Nat.mul_le_mul_right n hk
    omega
  simp only [dotBody, accesses]
  refine ReadsWithin.union (ReadsWithin.read _ _ hA) ?_
  refine ReadsWithin.union (ReadsWithin.read _ _ hB) ?_
  cases σ (p / n * n + k) <;> cases σ (n * n + (k * n + p % n)) <;>
    simp only [accesses] <;> exact ReadsWithin.empty _

/-- `dotBody` never writes — the accumulator is a pure `Int`. -/
theorem dotBody_no_writes (n p k : Nat) (acc : Int) (σ : State) :
    (accesses (dotBody n p k acc) σ).writes = [] := by
  simp only [dotBody, accesses]
  cases σ (p / n * n + k) <;> cases σ (n * n + (k * n + p % n)) <;>
    simp [Footprint.union, Footprint.empty]

/-! ### The payoff — five hypotheses, four of them one line -/

/-- **The payoff, for any `n`**: every cell of `C = A*B` computed in parallel reaches exactly the
outcomes computing them one at a time does — despite every cell in a row sharing reads with every
other cell in that row. -/
theorem matmulPar_par_seq_eq (n : Nat) (σ : State) : matmulPar n ∥≡ matmulSeq n from σ := by
  unfold matmulPar matmulSeq
  apply reduceArray_par_seq_eq (n * n) n (dotBody n) 0 Val.int (cellLoc n) (InputRegion n)
  · intro p k acc σ'; exact dotBody_wellformed n p k acc σ'
  · intro p hp k hk acc σ'; exact dotBody_readsWithin n p k hp hk acc σ'
  · intro p k acc σ'; exact dotBody_no_writes n p k acc σ'
  · intro p q hp hq hpq; grind [cellLoc]
  · intro p hp; grind [cellLoc, InputRegion]

/-! ### Concrete check: `A * I = A`, `n = 2`

`A = [[1,2],[3,4]]` at locations 0-3, `B = I` at locations 4-7, so `C` should equal `A` at 8-11. -/

def σ2 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | 4 => .int 1 | 5 => .int 0 | 6 => .int 0 | 7 => .int 1
  | _ => .int 0

example : (runSeq (matmulPar 2) σ2).2 8 = .int 1 := rfl
example : (runSeq (matmulPar 2) σ2).2 9 = .int 2 := rfl
example : (runSeq (matmulPar 2) σ2).2 10 = .int 3 := rfl
example : (runSeq (matmulPar 2) σ2).2 11 = .int 4 := rfl

end Paralever.Examples.MatMul
