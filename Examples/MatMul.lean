import Paralever.Pragma.ParallelFor
import Paralever.Lib.Notation

/-! # Example: parallel matrix multiply — the demo `PLAN.md` calls "probably the most compelling"

Every cell `C[i,j] = Σ_k A[i,k]*B[k,j]` is computed by its own independent task, `#parallel_for`
over the flattened `n*n` cell index. **This is the one example that genuinely cannot be proved
independent without Bernstein**: cell `(i,j)` writes only its own output `C[i,j]`, but reads an
entire row of `A` and an entire column of `B` — and different cells' rows/columns overlap constantly
(every cell in row `i` reads the *same* row of `A`). A naive `∗`-style exclusive-heap-split
treatment would reject this outright.

The proof needs none of that overlap reasoning, though — `Pragma/ParallelFor.lean`'s
`parAll_wellformed_of_indexed_rw` only ever checks a cell's *writes* against every other cell's
reads/writes, never read-against-read, so the whole independence argument reduces to: `A`/`B` occupy
`[0, 2n²)`, `C` occupies `[2n², 3n²)`, and `i*n+j` is injective — two `grind` calls, no row/column
bookkeeping at all (`matmul_ww`, `matmul_wr`).

Layout: `A` at `[0,n²)`, `B` at `[n²,2n²)`, `C` at `[2n²,3n²)`. `dotStep` is the per-cell inner
product, fuel-bounded over `k` the same way `MergeSort.lean`'s loops are. -/

namespace Paralever.Examples.MatMul
open Paralever ParM Paralever.Pragma.ParallelFor

/-! ### The per-cell computation -/

/-- Accumulate `Σ A[i,k]*B[k,j]` for `k` in `[k, k+fuel)`. -/
def dotStep (n i j : Nat) : Nat → Nat → Int → ParM Int
  | 0, _, acc => .pure acc
  | fuel + 1, k, acc =>
      .read (i * n + k) (fun va => .read (n * n + (k * n + j)) (fun vb =>
        match va, vb with
        | .int a, .int b => dotStep n i j fuel (k + 1) (acc + a * b)
        | _, _ => .pure acc))

theorem dotStep_wellformed (n i j : Nat) :
    ∀ (fuel k : Nat) (acc : Int) (σ : State), WellFormed (dotStep n i j fuel k acc) σ := by
  intro fuel
  induction fuel with
  | zero => intro k acc σ; trivial
  | succ fuel ih =>
      intro k acc σ
      have heq : dotStep n i j (fuel + 1) k acc
          = .read (i * n + k) (fun va => .read (n * n + (k * n + j)) (fun vb =>
              match va, vb with
              | .int a, .int b => dotStep n i j fuel (k + 1) (acc + a * b)
              | _, _ => .pure acc)) := rfl
      rw [heq]
      grind [WellFormed]

/-- `dotStep`'s reads stay inside `[0, 2n²)` — `A`'s row `i` and `B`'s column `j`, but bounded
*loosely* (not tracked precisely) since Bernstein never needs to know exactly which row/column,
only that it's on the input side, not the output side. -/
theorem dotStep_readswithin (n i j : Nat) (hi : i < n) (hj : j < n) :
    ∀ (fuel k : Nat), k + fuel ≤ n → ∀ (acc : Int) (σ : State),
      ReadsWithin (accesses (dotStep n i j fuel k acc) σ) (fun l => l < n * n + n * n) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k _ acc σ
      have heq : dotStep n i j 0 k acc = .pure acc := rfl
      rw [heq]; simp only [accesses]; exact ReadsWithin.empty _
  | succ fuel ih =>
      intro k hk acc σ
      have hkn : k < n := by omega
      have heq : dotStep n i j (fuel + 1) k acc
          = .read (i * n + k) (fun va => .read (n * n + (k * n + j)) (fun vb =>
              match va, vb with
              | .int a, .int b => dotStep n i j fuel (k + 1) (acc + a * b)
              | _, _ => .pure acc)) := rfl
      rw [heq]
      simp only [accesses]
      have hbound1 : i * n + k < n * n + n * n := by
        have h1 : i * n + k < (i + 1) * n := by rw [Nat.succ_mul]; omega
        have h2 : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n hi
        omega
      have hbound2 : n * n + (k * n + j) < n * n + n * n := by
        have h1 : k * n + j < (k + 1) * n := by rw [Nat.succ_mul]; omega
        have h2 : (k + 1) * n ≤ n * n := Nat.mul_le_mul_right n hkn
        omega
      have hb1 : ReadsWithin (Footprint.mk [i * n + k] []) (fun l => l < n * n + n * n) :=
        ReadsWithin.read (i * n + k) _ hbound1
      have hb2 : ReadsWithin (Footprint.mk [n * n + (k * n + j)] []) (fun l => l < n * n + n * n) :=
        ReadsWithin.read (n * n + (k * n + j)) _ hbound2
      apply ReadsWithin.union hb1
      apply ReadsWithin.union hb2
      cases σ (i * n + k) with
      | int a =>
          cases σ (n * n + (k * n + j)) with
          | int b => exact ih (k + 1) (by omega) (acc + a * b) σ
          | bool b => simp only [accesses]; exact ReadsWithin.empty _
          | unit => simp only [accesses]; exact ReadsWithin.empty _
      | bool b => simp only [accesses]; exact ReadsWithin.empty _
      | unit => simp only [accesses]; exact ReadsWithin.empty _

/-- `dotStep` never writes — it only accumulates into a local `Int`, so its writes-within any
predicate at all is vacuously true. -/
theorem dotStep_writeswithin (n i j : Nat) (P : Loc → Prop) :
    ∀ (fuel k : Nat) (acc : Int) (σ : State),
      WritesWithin (accesses (dotStep n i j fuel k acc) σ) P := by
  intro fuel
  induction fuel with
  | zero => intro k acc σ; simp only [dotStep, accesses]; exact WritesWithin.empty _
  | succ fuel ih =>
      intro k acc σ
      have heq : dotStep n i j (fuel + 1) k acc
          = .read (i * n + k) (fun va => .read (n * n + (k * n + j)) (fun vb =>
              match va, vb with
              | .int a, .int b => dotStep n i j fuel (k + 1) (acc + a * b)
              | _, _ => .pure acc)) := rfl
      rw [heq]
      simp only [accesses]
      apply WritesWithin.union
      · exact WritesWithin.read _ _
      apply WritesWithin.union
      · exact WritesWithin.read _ _
      cases σ (i * n + k) with
      | int a =>
          cases σ (n * n + (k * n + j)) with
          | int b => exact ih (k + 1) (acc + a * b) σ
          | bool b => simp only [accesses]; exact WritesWithin.empty _
          | unit => simp only [accesses]; exact WritesWithin.empty _
      | bool b => simp only [accesses]; exact WritesWithin.empty _
      | unit => simp only [accesses]; exact WritesWithin.empty _

/-- Cell `p` (flattened `i*n+j`) of `C`: compute the dot product of `A`'s row `p/n` and `B`'s
column `p%n`, write it to `C[p]`. -/
def cellCompute (n p : Nat) : ParM Unit :=
  ParM.bind (dotStep n (p / n) (p % n) n 0 0) (fun s => .write (n * n + n * n + p) (.int s) .pure)

def matmulPar (n : Nat) : ParM (List Unit) := #parallel_for (n * n), (cellCompute n)
def matmulSeq (n : Nat) : ParM (List Unit) := ParM.seqAll ((List.range (n * n)).map (cellCompute n))

theorem cellCompute_wellformed (n p : Nat) (σ : State) : WellFormed (cellCompute n p) σ := by
  simp only [cellCompute, WellFormed_bind]
  exact ⟨dotStep_wellformed n (p / n) (p % n) n 0 0 σ, trivial⟩

theorem div_lt (n p : Nat) (hp : p < n * n) : p / n < n := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0; simp at hp
    · exact hn0
  exact Nat.div_lt_of_lt_mul (by omega)

theorem mod_lt (n p : Nat) (hp : p < n * n) : p % n < n := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0; simp at hp
    · exact hn0
  exact Nat.mod_lt p hn0

theorem cellCompute_readswithin (n p : Nat) (hp : p < n * n) (σ : State) :
    ReadsWithin (accesses (cellCompute n p) σ) (fun l => l < n * n + n * n) := by
  simp only [cellCompute, accesses_bind]
  apply ReadsWithin.union (dotStep_readswithin n (p / n) (p % n) (div_lt n p hp) (mod_lt n p hp)
    n 0 (by omega) 0 σ)
  simp only [accesses]
  exact ReadsWithin.write _ _

theorem cellCompute_writeswithin (n p : Nat) (σ : State) :
    WritesWithin (accesses (cellCompute n p) σ) (fun l => l = n * n + n * n + p) := by
  simp only [cellCompute, accesses_bind]
  apply WritesWithin.union
  · exact dotStep_writeswithin n (p / n) (p % n) _ n 0 0 σ
  simp only [accesses]
  exact WritesWithin.write _ _ rfl

/-! ### The independence check — two `grind` calls, no row/column reasoning -/

/-- Two distinct output cells never collide — `p ≠ q` forces `n*n+n*n+p ≠ n*n+n*n+q`. -/
theorem matmul_ww (n p q : Nat) (hpq : p ≠ q) :
    ∀ l, l = n * n + n * n + p → l = n * n + n * n + q → False := by
  grind

/-- An output cell's location is always `≥ n*n+n*n`; every input location is always `< n*n+n*n` —
`A`/`B` and `C` simply never overlap, regardless of which specific row/column is involved. -/
theorem matmul_wr (n p : Nat) : ∀ l, l = n * n + n * n + p → l < n * n + n * n → False := by
  grind

/-- **The payoff, for any `n`**: computing every cell of `C = A*B` in parallel reaches exactly the
outcomes computing them one at a time does — despite every cell in a row sharing reads with every
other cell in that row (and likewise for columns). -/
theorem matmulPar_par_seq_eq (n : Nat) (σ : State) : matmulPar n ∥≡ matmulSeq n from σ :=
  parAll_par_seq_eq_of_indexed_rw (List.range (n * n)) (cellCompute n)
    (fun _ l => l < n * n + n * n) (fun p l => l = n * n + n * n + p)
    List.nodup_range
    (fun p _ => cellCompute_wellformed n p)
    (fun p hp => cellCompute_readswithin n p (List.mem_range.mp hp))
    (fun p _ => cellCompute_writeswithin n p)
    (fun p q _ _ hpq => matmul_ww n p q hpq)
    (fun p _ _ _ _ => matmul_wr n p) σ

/-! ### Concrete check: `A * I = A`, `n = 2` -/

/-- `A = [[1,2],[3,4]]` at locations 0-3, `B = I` (identity) at locations 4-7 — so `C` should equal
`A`, at locations 8-11. -/
def σ2 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | 4 => .int 1 | 5 => .int 0 | 6 => .int 0 | 7 => .int 1
  | _ => .int 0

example : (runSeq (matmulPar 2) σ2).2 8 = .int 1 := rfl
example : (runSeq (matmulPar 2) σ2).2 9 = .int 2 := rfl
example : (runSeq (matmulPar 2) σ2).2 10 = .int 3 := rfl
example : (runSeq (matmulPar 2) σ2).2 11 = .int 4 := rfl

end Paralever.Examples.MatMul
