import Paralever.Lib.Pure

/-! # `C[i,j] := Σ_k A[i,k]*B[k,j]`, one task per cell

Cell `(i,j)` writes only `C[i,j]` but reads a whole row of `A` and a whole column of `B`, so
different cells' read sets overlap heavily — this is the example that needs Bernstein rather than
`∗`-disjointness. Rationale: `docs/reductions.md`, `docs/pure-bridge.md`, `docs/cost.md`. -/

namespace Paralever.Examples.MatMul
open Paralever

/-! ### Layout: `A` at `[0,n²)`, `B` at `[n²,2n²)`, `C` at `[2n²,3n²)` -/

/-- Cell `p = i*n+j`, step `k`: read `A[i,k]` and `B[k,j]`. -/
def dotLocs (n : Nat) (p k : Nat) : List Loc := [p / n * n + k, n * n + (k * n + p % n)]

def cellLoc (n p : Nat) : Loc := n * n + n * n + p

/-- The read region: `A` and `B` together. Deliberately loose — Bernstein needs only that a read is
on the input side, never which row or column. -/
def InputRegion (n : Nat) (l : Loc) : Prop := l < n * n + n * n

private theorem hlocs (n : Nat) :
    ∀ p, p < n * n → ∀ k, k < n → ∀ l ∈ dotLocs n p k, InputRegion n l := by
  intro p hp k hk l hl
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hp
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
  simp only [dotLocs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h
  · exact h ▸ hA
  · exact h ▸ hB

private theorem hdstinj (n : Nat) :
    ∀ p q, p < n * n → q < n * n → p ≠ q → cellLoc n p ≠ cellLoc n q := by
  intro p q hp hq hpq; grind [cellLoc]

private theorem hdstout (n : Nat) : ∀ p, p < n * n → ¬ InputRegion n (cellLoc n p) := by
  intro p hp; grind [cellLoc, InputRegion]

/-! ### pure -/

/-- Multiply the two values a step reads into the accumulator. The accumulator is a plain `Int`,
never a heap cell — that is what makes a cell's write set the single location `C[i,j]`. -/
def dotCombine : List Val → Int → Int
  | [.int a, .int b], acc => acc + a * b
  | _,                acc => acc

/-- `C[p]` as a function of the heap. -/
def matmulPure (n : Nat) (σ : State) (p : Nat) : Int := foldPure σ (dotLocs n p) dotCombine n 0 0

/-! ### seq -/

def matmulSeq (n : Nat) : ParM (List Unit) :=
  reduceArrayPureS (n * n) n (dotLocs n) dotCombine 0 Val.int (cellLoc n)

/-! ### par -/

def matmulPar (n : Nat) : ParM (List Unit) :=
  reduceArrayPureP (n * n) n (dotLocs n) dotCombine 0 Val.int (cellLoc n)

/-! ### pure = seq

`reduceFold (readsCombine ...) n 0 0` is the inner loop `matmulSeq` runs for cell `p`. -/

theorem pure_eq_seq (n p : Nat) (σ : State) :
    (runSeq (reduceFold (readsCombine (dotLocs n p) dotCombine) n 0 (0 : Int)) σ).1
      = matmulPure n σ p :=
  reduceFold_eq_foldPure (dotLocs n p) dotCombine σ n 0 0

/-! ### seq = par -/

theorem seq_eq_par (n : Nat) (σ : State) : matmulPar n ∥≡ matmulSeq n from σ :=
  reduceArrayPure_par_seq_eq (n * n) n (dotLocs n) dotCombine 0 Val.int (cellLoc n) (InputRegion n)
    (hlocs n) (hdstinj n) (hdstout n) σ

/-! ### time par < time seq -/

theorem time_lt (n : Nat) (h2 : 2 ≤ n) (σ : State) :
    time (matmulPar n) σ < time (matmulSeq n) σ := by
  unfold matmulPar matmulSeq reduceArrayPureP reduceArrayPureS
  exact reduceArray_time_lt (n * n) n (fun p => readsCombine (dotLocs n p) dotCombine) 0 Val.int
    (cellLoc n) (InputRegion n)
    (fun p k acc σ' => readsCombine_wellformed _ _ k acc σ')
    (fun p hp k hk acc σ' =>
      readsCombine_readsWithin _ _ k acc σ' (InputRegion n) (hlocs n p hp k hk))
    (fun p k acc σ' => readsCombine_no_writes _ _ k acc σ')
    (hdstinj n) (hdstout n)
    (Nat.le_trans h2 (Nat.le_mul_of_pos_left n (by omega))) σ

/-! ### Concrete check: `A * I = A` for `n = 2`

`A = [[1,2],[3,4]]` at 0-3, `B = I` at 4-7, so `C` at 8-11 should equal `A`. -/

def σ2 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | 4 => .int 1 | 5 => .int 0 | 6 => .int 0 | 7 => .int 1
  | _ => .int 0

example : (runSeq (matmulPar 2) σ2).2 8 = .int 1 := rfl
example : (runSeq (matmulPar 2) σ2).2 9 = .int 2 := rfl
example : (runSeq (matmulPar 2) σ2).2 10 = .int 3 := rfl
example : (runSeq (matmulPar 2) σ2).2 11 = .int 4 := rfl

end Paralever.Examples.MatMul
