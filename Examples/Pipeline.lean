import Paralever.Kernels.Assign
import Paralever.Lib.Cost
import Paralever.Lib.Notation
import Paralever.Lib.Render

/-! # An everyday program: sequential code with two parallel loops in it

Most real code is neither wholly sequential nor wholly parallel. It is a run of ordinary statements,
then a loop that happens to be independent, then more ordinary statements that need what the loop
produced, then another such loop. This file is exactly that, over an array `A` of length `n`:

```text
  phase 1   total    A[0] … A[n-1]  ──►  S          sequential  (one accumulator)
  LOOP 1    scale    A[i], S        ──►  B[i]       PARALLEL    (n tasks)
  phase 2   pick     B[0]           ──►  T          sequential  (needs loop 1)
  LOOP 2    offset   B[i], T        ──►  C[i]       PARALLEL    (n tasks)
  phase 3   stamp    C[0]           ──►  done       sequential  (needs loop 2)
```

Every arrow between phases is a genuine read-after-write dependence, and §5 proves all four of them
by evaluation: the development *refuses* to overlap any adjacent pair. The two loops are the
opposite case — task `i` reads its own cell **and a scalar every other task also reads**, and writes
only its own output, so the read sets overlap by design. `∗`-disjointness rejects both loops; the
Bernstein criterion accepts them.

The two loops have the same shape, so §2 proves the obligation once, generically, and §3 and §4
instantiate it. §6 sequentialises the two loops one at a time — `par_seq_eq_region_of` for each,
composed with `ParSeqEq.trans` — which is the point of the file: nothing about the sequential phases
is disturbed, and they are not required to be independent of anything. -/

namespace Paralever.Examples.Pipeline
open Paralever

/-! ## Layout

`A` at `[0,n)`, `B` at `[n,2n)`, `C` at `[2n,3n)`, the scalars `S`,`T` and the flag above them.
`abbrev` rather than `def` so address arithmetic stays visible to `grind`. -/

abbrev aBase : Nat := 0
abbrev bBase (n : Nat) : Nat := n
abbrev cBase (n : Nat) : Nat := n + n
abbrev sLoc (n : Nat) : Loc := n + n + n
abbrev tLoc (n : Nat) : Loc := n + n + n + 1
abbrev doneLoc (n : Nat) : Loc := n + n + n + 2

def ival : Val → Int
  | .int k => k
  | _      => 0

/-! ## 1. The loop body, once

Both loops are "read my own cell and one shared scalar, write my own output". Writing it once means
the independence obligation is proved once too (§2). -/

/-- Task `i`: read `src + i` and `sc`, write `dst + i`. -/
def mapStep (src dst : Nat) (sc : Loc) (f : Int → Int → Int) (i : Nat) : ParM Unit :=
  .read (src + i) (fun v => .read sc (fun s => .write (dst + i) (.int (f (ival v) (ival s))) .pure))

@[simp] theorem mapStep_accesses (src dst : Nat) (sc : Loc) (f : Int → Int → Int) (i : Nat)
    (σ : State) : accesses (mapStep src dst sc f i) σ = ⟨[src + i, sc], [dst + i]⟩ := rfl

@[simp] theorem mapStep_wellformed (src dst : Nat) (sc : Loc) (f : Int → Int → Int) (i : Nat)
    (σ : State) : WellFormed (mapStep src dst sc f i) σ := trivial

/-- A whole loop of such tasks. -/
def mapLoopPar (n src dst : Nat) (sc : Loc) (f : Int → Int → Int) : ParM (List Unit) :=
  ParM.parAll ((List.range n).map (mapStep src dst sc f))

def mapLoopSeq (n src dst : Nat) (sc : Loc) (f : Int → Int → Int) : ParM (List Unit) :=
  ParM.seqAll ((List.range n).map (mapStep src dst sc f))

/-! ## 2. The obligation, proved once for every such loop

Two facts, both arithmetic: the output region does not meet the input region, and does not contain
the scalar. Nothing is assumed about the reads overlapping — they always do, on `sc`. -/

theorem mapLoop_wellformed (n src dst : Nat) (sc : Loc) (f : Int → Int → Int)
    (hio : ∀ i j, i < n → j < n → dst + i ≠ src + j)
    (hsc : ∀ i, i < n → dst + i ≠ sc) (σ : State) :
    WellFormed (mapLoopPar n src dst sc f) σ := by
  refine (Pragma.ParallelFor.parAll_wellformed_of_indexed_rw (List.range n)
    (mapStep src dst sc f)
    (fun i l => l = src + i ∨ l = sc) (fun i l => l = dst + i)
    (List.nodup_range) (fun i _ σ' => mapStep_wellformed src dst sc f i σ') ?_ ?_ ?_ ?_ σ).1
  · intro i _ σ' l hl
    rw [mapStep_accesses] at hl
    simpa using hl
  · intro i _ σ' l hl
    rw [mapStep_accesses] at hl
    simpa using hl
  · intro i j hi hj hij l hli hlj
    have h1 : l = dst + i := hli
    have h2 : l = dst + j := hlj
    grind
  · intro i j hi hj _ l hli hlj
    rw [List.mem_range] at hi hj
    have h1 : l = dst + i := hli
    have h2 : l = src + j ∨ l = sc := hlj
    rcases h2 with h | h
    · exact hio i j hi hj (h1 ▸ h)
    · exact hsc i hi (h1 ▸ h)

/-! ## 3. The phases

Three sequential ones and two loops. Nothing here is special-cased: the loops are `mapLoopPar`
at different offsets. -/

/-- Phase 1: sum `A` into `S`, one accumulator, inherently a dependent chain. -/
def totalFold : Nat → Int → ParM Int
  | 0,        acc => .pure acc
  | fuel + 1, acc => .read (aBase + fuel) (fun v => totalFold fuel (acc + ival v))

def total (n : Nat) : ParM Unit :=
  ParM.bind (totalFold n 0) (fun s => .write (sLoc n) (.int s) .pure)

theorem totalFold_wellformed :
    ∀ (fuel : Nat) (acc : Int) (σ : State), WellFormed (totalFold fuel acc) σ := by
  intro fuel
  induction fuel with
  | zero => intro acc σ; trivial
  | succ f ih => intro acc σ; exact ih (acc + ival (σ (aBase + f))) σ

theorem total_wellformed (n : Nat) (σ : State) : WellFormed (total n) σ := by
  simp only [total, WellFormed_bind]
  exact ⟨totalFold_wellformed n 0 σ, trivial⟩

/-- Loop 1: `B[i] := A[i] * S`. -/
def scalePar (n : Nat) : ParM (List Unit) := mapLoopPar n aBase (bBase n) (sLoc n) (· * ·)
def scaleSeq (n : Nat) : ParM (List Unit) := mapLoopSeq n aBase (bBase n) (sLoc n) (· * ·)

/-- Phase 2: `T := B[0] + 1`. Sequential, needs loop 1, feeds loop 2. -/
def pick (n : Nat) : ParM Unit :=
  .read (bBase n + 0) (fun v => .write (tLoc n) (.int (ival v + 1)) .pure)

/-- Loop 2: `C[i] := B[i] + T`. -/
def offsetPar (n : Nat) : ParM (List Unit) := mapLoopPar n (bBase n) (cBase n) (tLoc n) (· + ·)
def offsetSeq (n : Nat) : ParM (List Unit) := mapLoopSeq n (bBase n) (cBase n) (tLoc n) (· + ·)

/-- Phase 3: record that the program ran. -/
def stamp (n : Nat) : ParM Unit :=
  .read (cBase n + 0) (fun v => .write (doneLoc n) (.int (ival v + 1)) .pure)

/-! ## 4. The whole program, in three forms

`wholePar` has both loops parallel, `wholeMid` only the second, `wholeSeq` neither. The middle form
exists because §6 substitutes one region at a time. -/

def body (n : Nat) (L1 L2 : ParM (List Unit)) : ParM Unit :=
  ParM.bind (total n) (fun _ =>
    ParM.bind L1 (fun _ =>
      ParM.bind (pick n) (fun _ =>
        ParM.bind L2 (fun _ => stamp n))))

def wholePar (n : Nat) : ParM Unit := body n (scalePar n) (offsetPar n)
def wholeMid (n : Nat) : ParM Unit := body n (scaleSeq n) (offsetPar n)
def wholeSeq (n : Nat) : ParM Unit := body n (scaleSeq n) (offsetSeq n)

theorem scale_wellformed (n : Nat) (σ : State) : WellFormed (scalePar n) σ :=
  mapLoop_wellformed n aBase (bBase n) (sLoc n) _ (by intro i j hi hj; grind)
    (by intro i hi; grind) σ

theorem offset_wellformed (n : Nat) (σ : State) : WellFormed (offsetPar n) σ :=
  mapLoop_wellformed n (bBase n) (cBase n) (tLoc n) _ (by intro i j hi hj; grind)
    (by intro i hi; grind) σ

/-- The sequential phases carry no obligation of their own — they contain no `par` node — so the
whole program's well-formedness is exactly the two loops'. -/
theorem wholePar_wellformed (n : Nat) (σ : State) : WellFormed (wholePar n) σ := by
  rw [wholePar, body, WellFormed_bind]
  refine ⟨total_wellformed n σ, ?_⟩
  rw [WellFormed_bind]
  refine ⟨scale_wellformed n _, ?_⟩
  rw [WellFormed_bind]
  refine ⟨trivial, ?_⟩
  rw [WellFormed_bind]
  exact ⟨offset_wellformed n _, trivial⟩

/-! ## 5. Every phase boundary is a real dependency

Anti-vacuity for this program. All four adjacent pairs fail Bernstein by evaluation, so none of them
could have been merged or run concurrently; the two loops' tasks pass despite sharing a scalar.
Shown at `n = 4`. -/

example : indepB (accesses (total 4) (fun _ => .int 0))
                 (accesses (mapStep aBase (bBase 4) (sLoc 4) (· * ·) 0) (fun _ => .int 0))
          = false := rfl

example : indepB (accesses (mapStep aBase (bBase 4) (sLoc 4) (· * ·) 0) (fun _ => .int 0))
                 (accesses (pick 4) (fun _ => .int 0)) = false := rfl

example : indepB (accesses (pick 4) (fun _ => .int 0))
                 (accesses (mapStep (bBase 4) (cBase 4) (tLoc 4) (· + ·) 0) (fun _ => .int 0))
          = false := rfl

example : indepB (accesses (mapStep (bBase 4) (cBase 4) (tLoc 4) (· + ·) 0) (fun _ => .int 0))
                 (accesses (stamp 4) (fun _ => .int 0)) = false := rfl

/-- Inside a loop, by contrast, two tasks are independent — though both read the scalar. -/
example : indepB (accesses (mapStep aBase (bBase 4) (sLoc 4) (· * ·) 1) (fun _ => .int 0))
                 (accesses (mapStep aBase (bBase 4) (sLoc 4) (· * ·) 2) (fun _ => .int 0))
          = true := rfl

/-! ## 6. Sequentialising the two loops, one at a time

Each step is `par_seq_eq_region_of` with the surrounding code as `pre` and `post`; the two are
composed with `ParSeqEq.trans`. Re-associating the binds between the steps is sound because the
monad laws hold as equalities of *trees* (`ParM.bind_assoc`). -/

/-- Step 1: replace loop 1, leaving loop 2 parallel. -/
theorem par_eq_mid (n : Nat) (σ : State) : ParSeqEq (wholePar n) (wholeMid n) σ :=
  par_seq_eq_region_of (total n) (scalePar n) (scaleSeq n)
    (fun _ => ParM.bind (pick n) (fun _ => ParM.bind (offsetPar n) (fun _ => stamp n))) σ
    (runSeq_parAll_eq_seqAll _)
    (fun τ h => wellFormed_of_seqAll _ τ h)
    (wholePar_wellformed n σ)

theorem wholeMid_wellformed (n : Nat) (σ : State) : WellFormed (wholeMid n) σ := by
  rw [wholeMid, body, WellFormed_bind]
  refine ⟨total_wellformed n σ, ?_⟩
  rw [WellFormed_bind]
  refine ⟨wellFormed_of_seqAll _ _ (scale_wellformed n _), ?_⟩
  rw [WellFormed_bind]
  refine ⟨trivial, ?_⟩
  rw [WellFormed_bind]
  exact ⟨offset_wellformed n _, trivial⟩

/-- Step 2: replace loop 2. The program is re-associated so that everything before loop 2 — two
sequential phases *and* the now-sequential loop 1 — is the `pre` of the region theorem. -/
theorem mid_eq_seq (n : Nat) (σ : State) : ParSeqEq (wholeMid n) (wholeSeq n) σ := by
  have hre : ∀ L : ParM (List Unit), body n (scaleSeq n) L
      = ParM.bind (ParM.bind (total n) (fun _ => ParM.bind (scaleSeq n) (fun _ => pick n)))
          (fun _ => ParM.bind L (fun _ => stamp n)) := by
    intro L; simp only [body, ParM.bind_assoc]
  rw [wholeMid, wholeSeq, hre, hre]
  refine par_seq_eq_region_of _ (offsetPar n) (offsetSeq n) (fun _ => stamp n) σ
    (runSeq_parAll_eq_seqAll _) (fun τ h => wellFormed_of_seqAll _ τ h) ?_
  rw [← hre, ← wholeMid]
  exact wholeMid_wellformed n σ

/-- **The whole program is unchanged by parallelising both loops.** -/
theorem whole_par_seq_eq (n : Nat) (σ : State) : ParSeqEq (wholePar n) (wholeSeq n) σ :=
  (par_eq_mid n σ).trans (mid_eq_seq n σ)

/-! ## 7. A concrete run: `n = 4`, `A = [1,2,3,4]`

`S = 10`, so `B = [10,20,30,40]`; `T = B[0]+1 = 11`; `C = [21,31,41,51]`; `done = C[0]+1 = 22`. -/

def σ4 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3 | 3 => .int 4
  | _ => .int 0

example : (runSeq (wholePar 4) σ4).2 (sLoc 4)    = .int 10 := rfl
example : (runSeq (wholePar 4) σ4).2 (bBase 4)   = .int 10 := rfl
example : (runSeq (wholePar 4) σ4).2 (tLoc 4)    = .int 11 := rfl
example : (runSeq (wholePar 4) σ4).2 (cBase 4)   = .int 21 := rfl
example : (runSeq (wholePar 4) σ4).2 (cBase 4 + 3) = .int 51 := rfl
example : (runSeq (wholePar 4) σ4).2 (doneLoc 4) = .int 22 := rfl

/-- All three forms agree, independently of the theorem. -/
example : (runSeq (wholePar 4) σ4).2 (doneLoc 4) = (runSeq (wholeSeq 4) σ4).2 (doneLoc 4) := rfl
example : (runSeq (wholeMid 4) σ4).2 (doneLoc 4) = (runSeq (wholeSeq 4) σ4).2 (doneLoc 4) := rfl

/-- …and both loops really do save rounds: eight tasks collapse to two rounds. -/
example : time (wholePar 4) σ4 < time (wholeSeq 4) σ4 := by decide

/-! ## 8. Reading the program back

`codeStr` (`Lib/Render.lean`) prints the tree as imperative code, with each read's observed value as
a trailing comment. Uncomment to print the whole program at `n = 3` (`A = [1,2,3]`, so `S = 6`):

```text
t0 := M[2]                  // reads 3
t1 := M[1]                  // reads 2
t2 := M[0]                  // reads 1
M[9] := 6                            -- phase 1 wrote S
parallel {                           -- LOOP 1
  thread 0 { t3 := M[0]  t4 := M[9]  M[3] := 6  }
  thread 1 { t5 := M[1]  t6 := M[9]  M[4] := 12 }
  thread 2 { t7 := M[2]  t8 := M[9]  M[5] := 18 }
}
t9 := M[3]                  // reads 6
M[10] := 7                           -- phase 2 wrote T
parallel {                           -- LOOP 2
  thread 0 { … M[6] := 13 }
  thread 1 { … M[7] := 19 }
  thread 2 { … M[8] := 25 }
}
t16 := M[6]                 // reads 13
M[11] := 14                          -- phase 3 wrote done
```

Every thread of loop 1 reads `M[9]`, and every thread of loop 2 reads `M[10]` — the shared scalar is
visible in the rendering, which is the clearest way to see why this program needs Bernstein and not
`∗`-disjointness. -/

def σ3 : State
  | 0 => .int 1 | 1 => .int 2 | 2 => .int 3
  | _ => .int 0

-- #eval IO.println (codeStr (wholePar 3) σ3)
-- #eval IO.println (reportStr (wholePar 3) σ3)

end Paralever.Examples.Pipeline
