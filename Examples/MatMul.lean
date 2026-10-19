import Paralever.Lib.Pure
import Paralever.Kernels.Grid
import Paralever.Lang.Imp

/-! # `C[i,j] := Σ_k A[i,k]*B[k,j]`, two ways of keying the tasks

Cell `(i,j)` writes only `C[i,j]` but reads a whole row of `A` and a whole column of `B`, so
different cells' read sets overlap heavily — this is the example that needs Bernstein rather than
`∗`-disjointness, and it is the same under either keying below.

What differs is *what identifies a task*:

* **§1, linear.** Tasks are numbered `p < n²`, which is how `Lib/Reduce.lean`'s `Nat`-indexed
  validator wants them. Every read address then has to be written in terms of `p / n` and `p % n`,
  and the read-region obligation needs bounds on those quotients before it can even be stated.
* **§2, by coordinate.** Tasks are keyed by `(i,j)` directly (`Kernels/Grid.lean`), so no address
  mentions `/` or `%` and the obligations are stated in the indices the programmer already has.
* **§4, written down.** The same program in the surface language of `Lang/Imp.lean`. Because a
  `ParProg` carries its own footprint, the obligation is not proved at all — it is `decide`d.

§3 proves the first two layouts are the same one. Both are kept because the comparison is the point:
the second is shorter, but it only became available once the loop validator was generalised from
`List Nat` keys to keys of any type.

Rationale: `docs/reductions.md`, `docs/pure-bridge.md`, `docs/cost.md`. -/

namespace Paralever.Examples.MatMul
open Paralever

/-! ## Shared: layout, combining function, read region

`A` occupies `[0,n²)`, `B` occupies `[n²,2n²)` and `C` occupies `[2n²,3n²)`. -/

/-- Multiply the two values a step reads into the accumulator. The accumulator is a plain `Int`,
never a heap cell — that is what makes a cell's write set the single location `C[i,j]`. -/
def dotCombine : List Val → Int → Int
  | [.int a, .int b], acc => acc + a * b
  | _,                acc => acc

/-- The read region: `A` and `B` together. Deliberately loose — Bernstein needs only that a read is
on the input side, never which row or column. The *same* region for every task, which is what
permits the overlap. -/
def InputRegion (n : Nat) (l : Loc) : Prop := l < n * n + n * n

/-- `A = [[1,2],[3,4]]` at 0–3, `B = I` at 4–7, so `C` at 8–11 should equal `A`. -/
def σ2 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | 4 => .int 1 | 5 => .int 0 | 6 => .int 0 | 7 => .int 1
  | _ => .int 0

/-! ## 1. One task per linear index `p`

The original formulation. `p` ranges over `[0, n²)`, and the row and column it stands for are
recovered arithmetically. -/

/-- Cell `p = i*n+j`, step `k`: read `A[i,k]` and `B[k,j]`. -/
def dotLocs (n : Nat) (p k : Nat) : List Loc := [p / n * n + k, n * n + (k * n + p % n)]

def cellLoc (n p : Nat) : Loc := n * n + n * n + p

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

/-! ### pure, seq, par -/

/-- `C[p]` as a function of the heap. -/
def matmulPure (n : Nat) (σ : State) (p : Nat) : Int := foldPure σ (dotLocs n p) dotCombine n 0 0

def matmulSeq (n : Nat) : ParM (List Unit) :=
  reduceArrayPureS (n * n) n (dotLocs n) dotCombine 0 Val.int (cellLoc n)

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

example : (runSeq (matmulPar 2) σ2).2 8 = .int 1 := rfl
example : (runSeq (matmulPar 2) σ2).2 9 = .int 2 := rfl
example : (runSeq (matmulPar 2) σ2).2 10 = .int 3 := rfl
example : (runSeq (matmulPar 2) σ2).2 11 = .int 4 := rfl

/-! ## 2. One task per coordinate `(i,j)`

The same program against `Kernels/Grid.lean`. The task key is the coordinate, so `gridIdx` supplies
distinctness and no address is ever divided. -/

namespace Grid

def aLoc (n i k : Nat) : Loc := lin n i k
def bLoc (n k j : Nat) : Loc := n * n + lin n k j
def cLoc (n i j : Nat) : Loc := n * n + n * n + lin n i j

/-- Step `k` of cell `(i,j)`: one entry of `A`, one of `B`. Compare `MatMul.dotLocs` above. -/
def dotLocs (n i j k : Nat) : List Loc := [aLoc n i k, bLoc n k j]

def matmulPar (n : Nat) : ParM (List Unit) :=
  gridReducePar n n n (dotLocs n) dotCombine 0 Val.int (cLoc n)

def matmulSeq (n : Nat) : ParM (List Unit) :=
  gridReduceSeq n n n (dotLocs n) dotCombine 0 Val.int (cLoc n)

/-! ### The three obligations

Each follows from `lin_lt` or `lin_ne_of_ne`; none mentions `/` or `%`. Compare the three private
lemmas in §1, which have to bound `p / n` and `p % n` first. -/

theorem hlocs (n : Nat) : ∀ i j, i < n → j < n → ∀ k, k < n → ∀ l ∈ dotLocs n i j k,
    InputRegion n l := by
  intro i j hi hj k hk l hl
  simp only [dotLocs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · show lin n i k < n * n + n * n
    exact Nat.lt_of_lt_of_le (lin_lt hi hk) (Nat.le_add_right _ _)
  · show n * n + lin n k j < n * n + n * n
    exact Nat.add_lt_add_left (lin_lt hk hj) (n * n)

theorem hinj (n : Nat) : ∀ i j i' j', i < n → j < n → i' < n → j' < n →
    (i ≠ i' ∨ j ≠ j') → cLoc n i j ≠ cLoc n i' j' := by
  intro i j i' j' _ hj _ hj' hne
  simp only [cLoc]
  exact lin_ne_of_ne hj hj' hne

theorem hout (n : Nat) : ∀ i j, i < n → j < n → ¬ InputRegion n (cLoc n i j) := by
  intro i j _ _
  show ¬ (n * n + n * n + lin n i j < n * n + n * n)
  exact Nat.not_lt.mpr (Nat.le_add_right _ _)

/-! ### seq = par -/

theorem seq_eq_par (n : Nat) (σ : State) : matmulPar n ∥≡ matmulSeq n from σ :=
  gridReduce_par_seq_eq n n n (dotLocs n) dotCombine 0 Val.int (cLoc n) (InputRegion n)
    (hlocs n) (hinj n) (hout n) σ

example : (runSeq (matmulPar 2) σ2).2 8 = .int 1 := rfl
example : (runSeq (matmulPar 2) σ2).2 9 = .int 2 := rfl
example : (runSeq (matmulPar 2) σ2).2 10 = .int 3 := rfl
example : (runSeq (matmulPar 2) σ2).2 11 = .int 4 := rfl

end Grid

/-! ## 4. The same program, written in the surface language

Matrix multiply is where a first-order program pays most: §1's obligations are entirely about
bounding `p / n` and `p % n`, and here there is nothing to bound — `gridIdx` and `List.range` unroll
when the term elaborates, so every address is a literal by the time the thread exists. -/

namespace Surface
open Paralever.Lang

/-- One thread per output cell: zero the accumulator, fold `A[i,k] * B[k,j]` over `k`, store. The
accumulator is a **register**, so the thread's whole write set is the single cell `C[i,j]` — which
is what lets different cells read overlapping rows and columns. -/
def matmul (n : Nat) : ParProg :=
  ParProg.parEach (gridIdx n n) fun ij =>
    ParProg.block
      ([ paralever { %2 := 0 } ]
        ++ (List.range n).map (fun k => paralever {
              %0 := [ij.1 * n + k];
              %1 := [n * n + (k * n + ij.2)];
              %2 := R 2 + R 0 * R 1 })
        ++ [ paralever { [n * n + n * n + (ij.1 * n + ij.2)] := R 2 } ])

/-! At `n = 2` it renders as four threads, and the shared reads are visible: threads 0 and 1 both
read `M[0]` and `M[1]` — row 0 of `A` — while writing `M[8]` and `M[9]`.

```text
parallel {
  thread 0 { t2 := 0; t0 := M[0]; t1 := M[4]; t2 := (t2 + (t0 * t1));
                      t0 := M[1]; t1 := M[6]; t2 := (t2 + (t0 * t1)); M[8] := t2; }
  thread 1 { t2 := 0; t0 := M[0]; t1 := M[5]; t2 := (t2 + (t0 * t1));
                      t0 := M[1]; t1 := M[7]; t2 := (t2 + (t0 * t1)); M[9] := t2; }
  …
}
```
-/

-- #eval IO.println (ParProg.renderProg (matmul 2))

/-! ### The obligation

This is the whole proof. Compare §1's `hlocs`, `hdstinj` and `hdstout`, and §2's `lin_lt` and
`lin_ne_of_ne`. -/

example : ParProg.wfB (matmul 2) = true := by decide
example : ParProg.wfB (matmul 3) = true := by decide

/-- …and the equivalence follows with nothing further to supply. -/
theorem par_seq_eq_2 (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (matmul 2) ρ) (ParProg.execSeq (matmul 2) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- It computes the same thing: `A · I = A` on the fixture of §1. -/
def ρ0 : Regs := fun _ => 0

example : (runSeq (ParProg.execPar (matmul 2) ρ0) σ2).2 8  = .int 1 := rfl
example : (runSeq (ParProg.execPar (matmul 2) ρ0) σ2).2 9  = .int 2 := rfl
example : (runSeq (ParProg.execPar (matmul 2) ρ0) σ2).2 10 = .int 3 := rfl
example : (runSeq (ParProg.execPar (matmul 2) ρ0) σ2).2 11 = .int 4 := rfl

/-! ### …and it runs

`#eval` runs this matmul on real `Task`s, one per output cell, and `runTask_eq` says the spawned run
computes the canonical sequential answer — so the same `decide` certifies both.
-- ref: `Lang/Exec.lean` § Running it on real threads

With `A = [[1,2],[3,4]]` and `B = [[5,6],[7,8]]`, `#eval` gives `[19, 22, 43, 50]`: -/

def σ2' : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | 4 => .int 5 | 5 => .int 6 | 6 => .int 7 | 7 => .int 8
  | _ => .int 0

-- #eval ParProg.evalTask (matmul 2) σ2' [8, 9, 10, 11]

/-- The threaded run agrees with the reference run, by theorem rather than by observation. -/
theorem runTask_eq_runSeq (ρ : Regs) (σ : State) :
    ParProg.runTask (matmul 2) ρ σ = runSeq (ParProg.execPar (matmul 2) ρ) σ :=
  ParProg.runTask_eq (by decide) ρ σ

/-- **Par ≤ Seq in rounds.** §1's `time_lt` is the hand-built version; this is the same statement
for the language, from the same `decide`. -/
theorem time_le_2 (ρ : Regs) (σ : State) :
    time (ParProg.execPar (matmul 2) ρ) σ ≤ time (ParProg.execSeq (matmul 2) ρ) σ :=
  ParProg.time_le (by decide) ρ σ

/-- Threaded and single-threaded executions agree, so `runTask` vs `runTaskSeq` is a fair benchmark:
both go through `execTask`, and only one of them spawns. -/
theorem runTask_eq_seq (ρ : Regs) (σ : State) :
    ParProg.runTask (matmul 2) ρ σ = ParProg.runTaskSeq (matmul 2) ρ σ :=
  ParProg.runTask_eq_runTaskSeq (by decide) ρ σ

/-! ### What it costs, and where it stops

`decide` reduces concrete lists in the kernel, so it scales with the program's size rather than
with the difficulty of the argument. Measured, for `wfB (matmul n) = true`:

| `n` | threads | `by decide` |
|---|---|---|
| 2 | 4   | < 1 s |
| 4 | 16  | 0.8 s |
| 6 | 36  | 2.0 s |
| 8 | 64  | 6.6 s |
| 10 | 100 | 19 s |

`decide` needs a *concrete* `n`. At symbolic `n` the obligation is a lemma again — `wfB_parFor`
plus §2's `lin_ne_of_ne` — which is what §4 pays. -/

end Surface


/-! ## 4. The surface kernel at every size

§2 has matmul at every `n` at the `ParM` layer; this is the same reach in the DSL, which is the
layer `wfB` and `decide` work at. Bases are parameters, not expressions in `n` — how a `Layout`
hands them over, and what keeps the arithmetic linear.

**Access pattern, not arithmetic.** `gridK`'s `reduceBody` loads one cell per step, so `step` never
sees two operands to multiply; §2's `gridReducePar` takes a *list* per step and does the real dot
product. Closing that gap in the DSL is the next kernel to add. -/

namespace SurfaceSymbolic
open Paralever.Lang Paralever.Lang.ParProg

/-- Three `n×n` blocks at bases `a`, `b`, `c`; cell `(i,j)` folds row `i` of `a` then column `j`
of `b` into `c[i,j]`. -/
def mmGrid (n : Nat) (a b c : Loc) : ParProg :=
  gridK n n (2 * n)
    (fun i j k => if k < n then a + lin n i k else b + lin n (k - n) j)
    (fun x y => x + y)
    (fun i j => c + lin n i j)

/-- **The obligation at every `n`**, from two range inequalities. -/
theorem mmGrid_wf (n : Nat) (a b c : Loc)
    (hab : a + n * n ≤ b) (hbc : b + n * n ≤ c) : wfB (mmGrid n a b c) = true := by
  refine wfB_gridK n n (2 * n) _ _ _ ?_ ?_
  · intro i j i' j' _ hj _ hj' hne
    exact lin_ne_of_ne hj hj' hne
  · intro i j i' j' hi hj hi' hj' k hk
    have h1 : lin n i j < n * n := lin_lt hi hj
    split
    · rename_i hkn
      have h2 : lin n i' k < n * n := lin_lt hi' hkn
      grind
    · rename_i hkn
      have h2 : lin n (k - n) j' < n * n := lin_lt (by omega) hj'
      grind

theorem mmGrid_par_seq_eq (n : Nat) (a b c : Loc)
    (hab : a + n * n ≤ b) (hbc : b + n * n ≤ c) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (mmGrid n a b c) ρ) (execSeq (mmGrid n a b c) ρ) σ :=
  ParProg.par_seq_eq (mmGrid_wf n a b c hab hbc) ρ σ

/-- The cost separation comes from the same `Bool`, also at every size. -/
theorem mmGrid_time_le (n : Nat) (a b c : Loc)
    (hab : a + n * n ≤ b) (hbc : b + n * n ≤ c) (ρ : Regs) (σ : State) :
    time (execPar (mmGrid n a b c) ρ) σ ≤ time (execSeq (mmGrid n a b c) ρ) σ :=
  ParProg.time_le (mmGrid_wf n a b c hab hbc) ρ σ

/-- The symbolic and `decide` routes agree at a size where both are available. -/
example : wfB (mmGrid 3 0 9 18) = true := mmGrid_wf 3 0 9 18 (by decide) (by decide)
example : wfB (mmGrid 3 0 9 18) = true := by decide

end SurfaceSymbolic


/-! ## 3. The two keyings describe the same layout

Not needed by either proof — stated so that "the same program, keyed differently" is a checked
claim rather than a comment. `lin_div`/`lin_mod` (`Kernels/Grid.lean`) are the un-linearising
direction of the layout. -/

theorem cellLoc_eq (n i j : Nat) : cellLoc n (lin n i j) = Grid.cLoc n i j := rfl

theorem dotLocs_eq (n i j : Nat) (hn : 0 < n) (hj : j < n) (k : Nat) :
    dotLocs n (lin n i j) k = Grid.dotLocs n i j k := by
  simp only [dotLocs, Grid.dotLocs, Grid.aLoc, Grid.bLoc]
  rw [lin_div hn hj, lin_mod hj]
  simp [lin]

end Paralever.Examples.MatMul
