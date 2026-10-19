import Paralever.Lang.Imp

/-! # A small convolutional net, written in the DSL

Not one `ParM` constructor in the file: the net is assembled from premade kernels, so its
equivalence is a single `decide`.

```text
  x ──conv1dK──► c ──mapK (ReLU)──► r ──denseK──► y
                                                  │
                            target t ──zipK(−)──► e ──outerUpdateK──► W
```

Each layer's obligation was discharged once at every size, and `wfB` on `seq` is definitional, so
the program's is their conjunction. Sections: the net, the equivalence, the cost separation, a
training run. -/

namespace Paralever.Examples.NeuralNet
open Paralever Paralever.Lang

/-! ## Layout

Declared, not addressed: `alloc` assigns the bases, so the disjointness the net depends on holds by
construction. §5 shows what happened when it was maintained by hand. -/

def mem : Layout := Layout.of
  [ buf "x"  [8]    ones         -- input
  , buf "cw" [3]    ones         -- conv weights
  , buf "c"  [6]                 -- conv output      — a shape alone is zeros
  , buf "r"  [6]                 -- relu output
  , buf "w2" [2, 6]              -- dense weights, 2×6
  , buf "b2" [2]                 -- dense bias
  , buf "y"  [2]                 -- prediction
  , buf "t"  [2]    [30, -18]    -- target
  , buf "e"  [2] ]               -- error

example : mem.wfB = true := by decide

abbrev X  : Nat := mem.at "x"
abbrev CW : Nat := mem.at "cw"
abbrev C  : Nat := mem.at "c"
abbrev Rl : Nat := mem.at "r"
abbrev W2 : Nat := mem.at "w2"
abbrev B2 : Nat := mem.at "b2"
abbrev Y  : Nat := mem.at "y"
abbrev T  : Nat := mem.at "t"
abbrev E  : Nat := mem.at "e"

/-! ## 1. The net

`conv1dK` loads its weights from memory, so every thread reads the whole weight array *and* its own
window — two kinds of read sharing at once, and neither costs anything, because `Indep` constrains
writes only. -/

/-- Forward pass: convolution, ReLU, dense layer. -/
def forward : ParProg :=
  ParProg.block
    [ ParProg.conv1dK 6 3 X CW C
    , ParProg.mapK 6 C Rl (fun v => AExp.max v (.lit 0))
    , ParProg.denseK 2 6 W2 Rl B2 Y ]

/-- One SGD step: forward, then the error, then an in-place weight update with learning rate
`1 / lrDen`. The update's thread `(i,j)` reads and writes `W[i,j]` *in place* — admissible only
because each thread owns its own cell. -/
def trainStep (lrDen : Int) : ParProg :=
  ParProg.block
    [ forward
    , ParProg.zipK 2 Y T E (fun y t => y - t)
    , ParProg.outerUpdateK 2 6 W2 E Rl lrDen ]

/-! ## 2. Par = Seq, in one line

The obligation is decidable because every address is a literal by the time the thread exists, so
`footprintOf` is a fold and `wfB` is a `Bool`. -/

example : ParProg.wfB forward = true := by decide
example : ParProg.wfB (trainStep 36) = true := by decide

/-- **The theorem.** Under every schedule, the net with all its layers' threads running at once
reaches exactly the outcomes it reaches run thread-by-thread. -/
theorem forward_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar forward ρ) (ParProg.execSeq forward ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- And for a training step, which also writes back into the weights. -/
theorem trainStep_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (trainStep 36) ρ) (ParProg.execSeq (trainStep 36) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ## 3. Cost: fewer rounds, same work

`work` counts memory operations and `time` counts parallel rounds. Parallelism reorders operations;
it does not remove any — so `work` is identical and only `time` falls. -/

/-- **Par ≤ Seq in rounds**, proved from the same `Bool` as the equivalence. -/
theorem forward_time_le (ρ : Regs) (σ : State) :
    time (ParProg.execPar forward ρ) σ ≤ time (ParProg.execSeq forward ρ) σ :=
  ParProg.time_le (by decide) ρ σ

/-- The initial heap *is* the declaration. -/
def σ0 : State := mem.state

def ρ0 : Regs := fun _ => 0

/-! Evaluating the two measures on the forward pass gives

```text
#eval (work (execPar forward ρ0) σ0,     -- 82   memory operations
       time (execPar forward ρ0) σ0,     -- 23   rounds, parallel
       time (execSeq forward ρ0) σ0)     -- 82   rounds, sequential
```

Identical work, **23 rounds against 82** — a 3.6× reduction in span, with the inequality itself
proved for every heap by `forward_time_le`. -/

-- #eval (work (ParProg.execPar forward ρ0) σ0,
--        time (ParProg.execPar forward ρ0) σ0,
--        time (ParProg.execSeq forward ρ0) σ0)

/-! ## 4. Training

Zero initial weights, targets `(30, -18)`, squared error per epoch under `trainStep 36`:

```text
1224, 576, 144, 36, 36, 36, 36, …          (51 epochs)
```

The plateau is integer-SGD granularity, not a bug: once `|e·x| < 36`, `/ 36` truncates the step to
zero. `AExp` is `Int`-valued by design.

The harness threads a strict `Array` between epochs — a `State` is a *function*, so holding one
across 50 epochs chains closures and each read re-walks them. -/

def toArr (σ : State) : Array Val := Id.run do
  let mut a : Array Val := #[]
  for l in [0:100] do
    a := a.push (σ l)
  return a

def ofArr (a : Array Val) : State := fun l => a.getD l (.int 0)

def ival : Val → Int | .int k => k | _ => 0

/-- The squared error of the net's prediction, from a snapshotted heap. -/
def sqErr (a : Array Val) : Int :=
  let b := toArr ((runSeq (ParProg.execPar forward ρ0) (ofArr a)).2)
  let d0 := ival b[Y]!   - ival b[T]!
  let d1 := ival b[Y+1]! - ival b[T+1]!
  d0 * d0 + d1 * d1

/-- `n` epochs of training, reporting the squared error before each. -/
def epochs (lrDen : Int) : Nat → Array Val → List Int
  | 0,     a => [sqErr a]
  | k + 1, a =>
      sqErr a :: epochs lrDen k (toArr ((runSeq (ParProg.execPar (trainStep lrDen) ρ0) (ofArr a)).2))

-- #eval epochs 36 50 (toArr σ0)

/-! ## 5. The layout is checked, not assumed

Building this file, the benchmark layout put the output region on top of the weight region. The
check caught it: the program is not well-formed, and the parallel and sequential runs genuinely
disagree — exactly what the theorem predicts when its hypothesis fails. -/

set_option maxRecDepth 8000

/-- Weights at `1000..1029` and outputs at `5000..` — disjoint. -/
example : ParProg.wfB (ParProg.conv1dK 8 30 0 1000 5000) = true := by decide

/-- Weights at `48..77` and outputs at `60..67` — overlapping, so threads write cells other threads
read. Rejected, and `par_seq_eq` correctly does not apply. -/
example : ParProg.wfB (ParProg.conv1dK 8 30 0 48 60) = false := by decide

/-- The bug is now unwriteable: a declared layout packs its buffers, so the addresses above had to
be written by hand to produce the overlap at all. -/
example : (Layout.of [buf "w" [30], buf "out" [8]]).disjointB "w" "out" = true := by decide

end Paralever.Examples.NeuralNet
