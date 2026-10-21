import Lang.Core.Imp
import Paralever.AutoPar.Print


namespace Paralever.Examples.Writing
open Paralever Paralever.Lang

/-! ## A program

Two inputs at `M[0]`, `M[1]`; their sum at `M[2]`; then three independent threads reading `M[2]`
and writing cells of their own. The threads share a read — all three consult `M[2]` — which is the
case Bernstein admits and `∗`-disjointness does not. -/

-- ANCHOR: site-writing
def prog : ParProg := paralever {
  %0 := [0];
  %1 := [1];
  [2] := %0 + %1;
  %2 := %0 * %1;
  parallel { %3 := [2]; [3] := %3 * 2 + %2 }
    | { %4 := [2]; [4] := %4 - 1 }
    | { [5] := 7 }
}
-- ANCHOR_END: site-writing

/-! ## What it prints

```text
t0 := M[0]
t1 := M[1]
M[2] := (t0 + t1)
t2 := (t0 * t1)
parallel {
  thread 0 { t3 := M[2]   M[3] := ((t3 * 2) + t2) }
  thread 1 { t4 := M[2]   M[4] := (t4 - 1)        }
  thread 2 {              M[5] := 7               }
}
-- reads  [0, 1, 2, 2]
-- writes [2, 3, 4, 5]
-- independent: true
```
-/

-- #eval IO.println (ParProg.reportProg prog)

/-! ## The obligation, by evaluation

`footprintOf` is a fold over the syntax, so the footprint is `rfl` and the Bernstein check is
`decide`. Nothing here mentions `accesses`, `runSeq` or a heap. -/

-- ANCHOR: site-writing-theorem
example : ParProg.footprintOf prog = ⟨[0, 1, 2, 2], [2, 3, 4, 5]⟩ := rfl

theorem prog_wf : ParProg.wfB prog = true := by decide
-- ANCHOR_END: site-writing-theorem

/-! ## …and the theorem

`execPar` lowers the statement into `ParM`; `par_seq_eq` says that running the `parallel` block
with all three threads at once reaches exactly the outcomes running them in order does, under every
schedule, from every register file and every heap. -/

theorem prog_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar prog ρ) (ParProg.execSeq prog ρ) σ :=
  ParProg.par_seq_eq prog_wf ρ σ

/-- The footprint the lowered program actually has is the one read off the syntax — an *equality*,
because every address here is a literal. A data-dependent `A[e]` gets a bound instead
(`execPar_accesses_sub`), which is all the obligation needs. -/
example (ρ : Regs) (σ : State) : accesses (ParProg.execPar prog ρ) σ = ParProg.footprintOf prog :=
  ParProg.execPar_accesses prog (by decide) ρ σ

/-! ## Anti-vacuity: a program the check rejects

Two threads writing the same cell. `wfB` is `false`, so `par_seq_eq` does not apply — and it
must not, since the two orders disagree. -/

def racy : ParProg := paralever {
  [0] := 1;
  parallel { [1] := 2 } | { [1] := 3 }
}

example : ParProg.wfB racy = false := by decide

/-- Changing only which cells the threads write makes the same program acceptable. -/
def fixed : ParProg := paralever {
  [0] := 1;
  parallel { [1] := 2 } | { [2] := 3 }
}

example : ParProg.wfB fixed = true := by decide

theorem fixed_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar fixed ρ) (ParProg.execSeq fixed ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ## A concrete run

`M[0] = 3`, `M[1] = 4`, so `M[2] = 7`, `t2 = 12`, and the threads write `7*2+12 = 26`, `7-1 = 6`
and `7`. -/

def σ0 : State
  | 0 => .int 3 | 1 => .int 4
  | _ => .int 0

def ρ0 : Regs := fun _ => 0

example : (runSeq (ParProg.execPar prog ρ0) σ0).2 2 = .int 7  := rfl
example : (runSeq (ParProg.execPar prog ρ0) σ0).2 3 = .int 26 := rfl
example : (runSeq (ParProg.execPar prog ρ0) σ0).2 4 = .int 6  := rfl
example : (runSeq (ParProg.execPar prog ρ0) σ0).2 5 = .int 7  := rfl

/-! ## Detecting the parallelism instead of writing it

A `ParProg` carries its own footprint, so "may these two statements run together?" is a `Bool`.
`dependences` reports where the sequential order is forced, and `autoPar` proposes a parallelisation.

Take a chain of four stores and a dependent read: -/

def chain : ParProg := paralever {
  [1] := 10;
  [2] := 20;
  [3] := 30;
  %0 := [1];
  [4] := %0 + 1
}

/-- Two orderings are forced: statement 0 writes `M[1]` which statement 3 reads, and statement 3
sets `t0` which statement 4 reads. The second is a *register* dependence — invisible to a
memory-only analysis, and fatal, because a forked thread would read a stale private copy. -/
example : ParProg.dependences chain = [(0, 3), (3, 4)] := by decide

/-! So the proposal forks the three independent stores and leaves the dependent pair alone:

```text
parallel {
  thread 0 { M[1] := 10 }
  thread 1 { M[2] := 20 }
  thread 2 { M[3] := 30 }
}
t0 := M[1]
M[4] := (t0 + 1)
```
-/

/--
info: parallel {
  thread 0 {
    M[1] := 10;
  }
  thread 1 {
    M[2] := 20;
  }
  thread 2 {
    M[3] := 30;
  }
}
%0 := M[1];
M[4] := (%0 + 1);
-/
#guard_msgs in
#eval IO.println (ParProg.renderProg (ParProg.autoPar chain))

/-- The proposal is re-checked, never believed: `autoPar` is untrusted, `wfB` is the proved check. -/
example : ParProg.wfB (ParProg.autoPar chain) = true := by decide

/-! ### The same chain, through the proved route

`AutoPar.rewrite` schedules the same units and carries `rewrite_sound`, so no per-program check is
needed: the heap it leaves is `chain`'s heap for every register file and every heap, and
`rewrite_parSeqEq` lifts that to every schedule. `report` prints the result in the language it came
from. -- ref: docs/autopar-algorithm.md -/

/-- Four units, two stages, and the plan attains the dependence DAG's bound. -/
example : AutoPar.quality chain = (3, 3, 5) := by decide
example : AutoPar.optimalB chain = true := by decide
example : (AutoPar.planOf chain).length = 2 := by decide

/--
info: paralever {
  parallel { [1] := 10 } | { [2] := 20 } | { [3] := 30 };
  parallel { %0 := [1]; [4] := (%0 + 1) }
}
-- units      4
-- stages     2
-- threads    4
-- depth      3  (sequential 5, lower bound 3)
-- optimal    true
-- committed  true
-/
#guard_msgs in
#eval IO.println (AutoPar.report chain)

/-- The soundness theorem, at this program: no hypothesis to discharge. -/
example (ρ : Regs) (σ : State) :
    (runSeq (ParProg.execPar (AutoPar.rewrite chain) ρ) σ).2
      = (runSeq (ParProg.execSeq chain ρ) σ).2 :=
  AutoPar.rewrite_sound chain ρ σ

/-! ## The kernels, written in the language

`mapK`, `broadcastK`, `reduceK` and `gridK` build the same shapes as `Kernels/`, as `ParProg`s.
Their obligations are `decide` at a concrete size, or `wfB_mapK` at every size. -/

def doubler : ParProg := ParProg.mapK 3 0 10 (fun e => e * 2)

example : ParProg.wfB doubler = true := by decide

/-- …and at every size, given the layout fact that output misses input. -/
example (n : Nat) : ParProg.wfB (ParProg.mapK n 0 (n + 1) (fun e => e * 2)) = true :=
  ParProg.wfB_mapK n 0 (n + 1) _ (by intro i j hi hj; omega)

/-- A reduction per cell: the accumulator is a register, so each thread's write set is one cell. -/
def dots : ParProg :=
  ParProg.reduceK 2 2 (fun p k => p * 2 + k) (fun a b => a + b) (fun p => 100 + p)

example : ParProg.wfB dots = true := by decide

/-! ## Loop-carried dependences

A loop whose next iteration needs the previous one's result is expressible — it is an ordinary `;`
chain, because `seq` *is* sequential composition. What the language will not let you do is claim it
is parallel.

`A[i+1] := A[i] + 1`, the canonical carried RAW: -/

/-- The sequential form: iteration `i` reads `base + i` and writes `base + i + 1`. -/
def incFromPrev (n base : Nat) : ParProg :=
  ParProg.block ((List.range n).map fun i =>
    .seq (.load 0 (base + i)) (.store (base + i + 1) (%0 + 1)))

/-- The analysis finds the carried chain. Two iterations unroll to four statements — load, store,
load, store — and every one of them is pinned: `(0,1)` and `(2,3)` are the register dependences
inside an iteration, `(1,2)` is the carried one through `M[1]`, and `(0,2)`, `(0,3)` follow. -/
example : ParProg.dependences (incFromPrev 2 0) = [(0,1), (0,2), (0,3), (1,2), (2,3)] := by decide

/-- …so `autoPar` leaves the program exactly as it found it: nothing can be forked. -/
example : ParProg.renderProg (ParProg.autoPar (incFromPrev 3 0))
        = ParProg.renderProg (incFromPrev 3 0) := by decide

/-- The proved route agrees, and says so with a certificate: one thread, and the depth it reaches
is the dependence DAG's own lower bound, so there was nothing to find. -/
example : (AutoPar.threads (AutoPar.planOf (incFromPrev 3 0))).length = 1 := by decide
example : AutoPar.optimalB (incFromPrev 3 0) = true := by decide

/-- And asserting the parallel form is **rejected**: the check is `false`, so `par_seq_eq`
does not apply — which is correct, since the two orders genuinely disagree. -/
def incFromPrevPar (n base : Nat) : ParProg :=
  ParProg.parFor n fun i => .seq (.load 0 (base + i)) (.store (base + i + 1) (%0 + 1))

example : ParProg.wfB (incFromPrevPar 3 0) = false := by decide

/-! ### Where the dependence distance matters

`A[i+s] := A[i] + 1` at stride `s`: iteration `i` writes `base + i + s` and iteration `j` reads
`base + j`, so the loop is parallelisable exactly when no iteration's write lands on another's read.
Over three iterations that fails at strides 1 and 2 and holds from stride 3 on — the dependence
distance, decided rather than argued. -/

def strided (n base s : Nat) : ParProg :=
  ParProg.parFor n fun i => .seq (.load 0 (base + i)) (.store (base + i + s) (%0 + 1))

example : ParProg.wfB (strided 3 0 1) = false := by decide
example : ParProg.wfB (strided 3 0 2) = false := by decide
example : ParProg.wfB (strided 3 0 3) = true  := by decide
example : ParProg.wfB (strided 3 0 4) = true  := by decide

/-- At stride 3 the loop really is equivalent to running the iterations in order. -/
theorem strided3_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (strided 3 0 3) ρ) (ParProg.execSeq (strided 3 0 3) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ## A pipeline, assembled from proved pieces

Phases named with `:: "…"` so each can be stated about on its own; the whole chain's obligation is
their conjunction. -- ref: `Lang/Core/Prog.lean` § Composing a pipeline out of proved pieces -/

def pipeline (n : Nat) : ParProg := paralever {
  for i in n { [100 + i] := 0 };
  parfor i in n { %0 := [i]; [100 + i] := %0 * 2 } :: "scale";
  [99] := 1;
  parfor i in n { %0 := [100 + i]; [200 + i] := %0 + 1 } :: "offset"
}

/-! It renders with the phase names in place:

```text
M[100] := 0;
M[101] := 0;
-- scale
parallel {
  thread 0 { t0 := M[0];   M[100] := (t0 * 2); }
  thread 1 { t0 := M[1];   M[101] := (t0 * 2); }
}
M[99] := 1;
-- offset
parallel {
  thread 0 { t0 := M[100]; M[200] := (t0 + 1); }
  thread 1 { t0 := M[101]; M[201] := (t0 + 1); }
}
```
-/

-- #eval IO.println (ParProg.renderProg (pipeline 2))

/-- A named region can be pulled back out and reasoned about alone. -/
example : (ParProg.findLabel "scale" (pipeline 2)).isSome = true := by decide

/-- At a concrete size the whole pipeline's obligation is one `decide`… -/
example : ParProg.wfB (pipeline 3) = true := by decide

/-- …and that is all that stands between the program and Par = Seq. -/
theorem pipeline_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (pipeline 3) ρ) (ParProg.execSeq (pipeline 3) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ### Why no further work is needed

`pipeline_par_seq_eq` takes, per phase, either "no `parallel` block here" or "this kernel is
proved", and gives the whole chain's equivalence. -/

example (s : ParProg) (h : ParProg.hasPar s = false) : ParProg.wfB s = true :=
  ParProg.wfB_of_parFree s h

example (phases : List ParProg) (h : ∀ p ∈ phases, ParProg.wfB p = true) (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (ParProg.block phases) ρ)
             (ParProg.execSeq (ParProg.block phases) ρ) σ :=
  ParProg.pipeline_par_seq_eq phases h ρ σ

/-! ## Misusing a kernel is caught

A kernel is a **builder** — a Lean function returning a `ParProg` — not a certificate. `wfB` is
computed from `footprintOf` of the program actually produced and has no idea it came from a kernel,
so the check sees the instantiation rather than the promise.

`mapK n src dst f` forks `n` threads, thread `i` reading `src + i` and writing `dst + i`: -/

example : ParProg.wfB (ParProg.mapK 3 0 10 (fun e => e * 2)) = true  := by decide
example : ParProg.wfB (ParProg.mapK 3 0 1  (fun e => e * 2)) = false := by decide

/-! The second shifts the output by one, so thread `i` writes the cell thread `i+1` reads — a real
loop-carried dependence — and the check refuses it.

A case worth noticing is in between: `mapK 3 0 0` maps the array **in place**, and that is
`true` — thread `i` reads and writes only cell `i`, so the threads really are independent. The check
is not "do the regions overlap", it is Bernstein on each pair, which is what lets an in-place map
through and stops a shifted one. -/

example : ParProg.wfB (ParProg.mapK 3 0 0 (fun e => e * 2)) = true := by decide

/-! The same holds for the other kernels. Writing into the broadcast input, or giving two reduction
cells the same output, is caught the moment the program is built: -/

example : ParProg.wfB (ParProg.broadcastK 2 [0,1,2] 10 (fun _ => %0)) = true  := by decide
example : ParProg.wfB (ParProg.broadcastK 2 [0,1,2] 1  (fun _ => %0)) = false := by decide

example : ParProg.wfB
    (ParProg.reduceK 3 2 (fun p k => p*2+k) (fun a b => a+b) (fun p => 100 + p)) = true := by decide
example : ParProg.wfB
    (ParProg.reduceK 3 2 (fun p k => p*2+k) (fun a b => a+b) (fun _ => 100)) = false := by decide

example : ParProg.wfB
    (ParProg.gridK 2 2 2 (fun i _ k => i*2+k) (fun a b => a+b) (fun i j => 100 + i*2+j))
      = true := by decide
example : ParProg.wfB
    (ParProg.gridK 2 2 2 (fun i _ k => i*2+k) (fun a b => a+b) (fun i _ => 100 + i))
      = false := by decide

/-! ### The symbolic lemmas are gated the same way

At a symbolic size the obligation is a lemma rather than a `decide`, and the side condition is what
stops a bad instantiation: `wfB_mapK` demands

```text
hout : ∀ i j, i < n → j < n → dst + i ≠ src + j
```

which is simply false when `dst = src + 1`, so the lemma cannot be applied to the shifted map. The
kernel does not hand you its conclusion — it hands you an implication, and you pay for the
antecedent. -/

example (n : Nat) : ParProg.wfB (ParProg.mapK n 0 (n + 1) (fun e => e * 2)) = true :=
  ParProg.wfB_mapK n 0 (n + 1) _ (by intro i j hi hj; omega)

/-! Finally, nothing above is special to kernels. A hand-written `parallel` block is checked by the
same `wfB`, so the guarantee is uniform: what `par_seq_eq` consumes is the check, and the check is
computed from the program. -/

/-! ## Launching threads: a kernel written elsewhere

A kernel is a function of the thread index — an ordinary Lean definition, which may live in any
other file. `launch n kernel` forks `n` threads, thread `t` running `kernel t`. -/

/-- SAXPY: `out[tid] := a * x[tid] + y[tid]`. Written on its own, with no idea where it will run. -/
def saxpy (a : Int) (xs ys out : Nat) (tid : ParProg.Tid) : ParProg := paralever {
  %0 := [xs + tid];
  %1 := [ys + tid];
  [out + tid] := AExp.lit a * %0 + %1
}

/-- Four threads of it, over `x` at `[0,4)`, `y` at `[10,14)`, `out` at `[20,24)`. -/
def saxpy4 : ParProg := ParProg.launch 4 (saxpy 3 0 10 20)

/-! ```text
parallel {
  thread 0 { t0 := M[0]; t1 := M[10]; M[20] := ((3 * t0) + t1); }
  thread 1 { t0 := M[1]; t1 := M[11]; M[21] := ((3 * t0) + t1); }
  thread 2 { t0 := M[2]; t1 := M[12]; M[22] := ((3 * t0) + t1); }
  thread 3 { t0 := M[3]; t1 := M[13]; M[23] := ((3 * t0) + t1); }
}
```
-/

-- #eval IO.println (ParProg.renderProg saxpy4)

example : ParProg.wfB saxpy4 = true := by decide

theorem saxpy4_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar saxpy4 ρ) (ParProg.execSeq saxpy4 ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ### Blocks and threads

`launchGrid blocks threads kernel` gives the body both indices, which is CUDA's `blockIdx` /
`threadIdx` split. The pair is the task's *key*, so the grid is not linearised and no address needs
`/` or `%`; `globalTid` is there for when a kernel does want one flat index. -/

def tagKernel (threads out : Nat) (b t : ParProg.Tid) : ParProg :=
  paralever { [out + ParProg.globalTid threads b t] :=
          AExp.lit (Int.ofNat b) * 10 + AExp.lit (Int.ofNat t) }

example : ParProg.wfB (ParProg.launchGrid 2 3 (tagKernel 3 50)) = true := by decide

/-! Each thread's registers are its own (`Lowering`), so `%0` in one thread is not `%0` in another —
the same discipline CUDA's per-thread registers have, and the reason the obligation is about memory
alone. -/

/-! ## Kernels from machine learning

The shape most ML kernels have — each task reads a window of the input and writes one cell of its
own — is the Bernstein case exactly. Four that recur, each pre-verified in `Lang/Core/Kernels.lean`: -/

/-- Elementwise binary: `out[i] := a[i] + b[i]`. Add, multiply, `max` for a ReLU. -/
example : ParProg.wfB (ParProg.zipK 4 0 10 20 (fun x y => x + y)) = true  := by decide
example : ParProg.wfB (ParProg.zipK 4 0 10 2  (fun x y => x + y)) = false := by decide

/-- At every `n`, given the layout facts. -/
example (n : Nat) : ParProg.wfB (ParProg.zipK n 0 n (2*n) (fun x y => x + y)) = true :=
  ParProg.wfB_zipK n 0 n (2*n) _ (by intro i j hi hj; omega) (by intro i j hi hj; omega)

/-! **1-D convolution** is the showcase. Thread `i` and thread `i+1` read windows overlapping in
`w-1` cells, so the read sets share nearly everything while the writes stay disjoint — the case
`∗`-disjointness rejects outright. It is visible in the rendering:

```text
thread 0 { t2 := 0; t0 := M[0]; t2 := (t2 + (1 * t0));
                    t0 := M[1]; t2 := (t2 + (2 * t0));
                    t0 := M[2]; t2 := (t2 + (3 * t0)); M[100] := t2; }
thread 1 { t2 := 0; t0 := M[1]; …   t0 := M[2]; …   t0 := M[3]; …   M[101] := t2; }
```
-/

example : ParProg.wfB (ParProg.stencilK 4 3 0 100 (fun _ => AExp.lit 1)) = true  := by decide
example : ParProg.wfB (ParProg.stencilK 4 3 0 2   (fun _ => AExp.lit 1)) = false := by decide

/-- **Transpose** — reads and writes both permute, so a region-based check would reject it and the
per-pair one does not. -/
example : ParProg.wfB (ParProg.transposeK 2 3 0 100) = true  := by decide
example : ParProg.wfB (ParProg.transposeK 2 3 0 3)   = false := by decide

/-- **Bias add** — every row reads the same bias vector: broadcast along one axis. -/
example : ParProg.wfB (ParProg.biasAddK 2 3 0 50 100) = true  := by decide
example : ParProg.wfB (ParProg.biasAddK 2 3 0 50 51)  = false := by decide

/-! ## Named registers

`%n` and `%name` are the same syntax on either side of a `:=`. A name is any identifier of type
`Reg`, so one `abbrev` buys it; nothing in the semantics knows the difference, which is why the two
spellings below are the *same term*. -- ref: `Lang/Core/Notation.lean` -/

abbrev acc : Reg := 0
abbrev tmp : Reg := 1

def named : ParProg := paralever {
  %acc := [0];
  %tmp := [1];
  [2] := %acc * %acc + %tmp
}

def numbered : ParProg := paralever {
  %0 := [0];
  %1 := [1];
  [2] := %0 * %0 + %1
}

example : named = numbered := rfl

/-- info: Paralever.Val.int 11 -/
#guard_msgs in
#eval (runSeq (ParProg.execPar named (fun _ => 0))
        (fun l => if l = 0 then Val.int 3 else Val.int 2)).2 2

end Paralever.Examples.Writing
