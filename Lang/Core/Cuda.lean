import Lang.Core.Kernels

/-! # Launching threads, CUDA-style

A thread is distinguished only by its index, so a kernel is a *function of the index* — an ordinary
Lean definition that may live in any file. This is the vocabulary for that: `launch`, `launchGrid`
with CUDA's `blockIdx`/`threadIdx` split, and `globalTid`. -/

namespace Paralever.Lang
open Paralever

namespace ParProg

/-! ### Launching threads, CUDA-style

A kernel is a function of the thread index, which is what `parFor` already takes; these give it the
vocabulary:

```lean
def addOne (tid : Tid) : ParProg := paralever {
  %0 := [tid];
  [100 + tid] := %0 + 1
}

def prog : ParProg := launch 8 addOne                -- <<<8>>> threads
```

Each thread gets its own register file (`Lowering`), so `%0` in one thread is not `%0` in another —
the reason the independence obligation is about memory alone. -/

/-- A thread index. -/
abbrev Tid := Nat

/-- **Launch `n` threads.** Thread `t` runs `kernel t`; all of them fork at one `parallel` node, and
`execTask` spawns a `Task` for each. -/
def launch (n : Nat) (kernel : Tid → ParProg) : ParProg := parFor n kernel

/-- **Launch a grid of blocks × threads.** `kernel b t` is the body for thread `t` of block `b`,
which is CUDA's `blockIdx` / `threadIdx` split. The two indices are the task's *key*, so nothing is
linearised and no address needs `/` or `%`. -/
def launchGrid (blocks threads : Nat) (kernel : Nat → Tid → ParProg) : ParProg :=
  parEach (gridIdx blocks threads) (fun bt => kernel bt.1 bt.2)

/-- The flat index of thread `t` in block `b`, for addressing a single array from a grid launch. -/
abbrev globalTid (threads b t : Nat) : Nat := b * threads + t
/-- Launching is `parFor`, so its obligation is `wfB_parFor`'s: the bodies pairwise independent. -/
@[simp] theorem wfB_launch (n : Nat) (kernel : Tid → ParProg)
    (hbody : ∀ t, t < n → wfB (kernel t) = true)
    (hdisj : ∀ t u, t < n → u < n → t ≠ u →
      indepB (footprintOf (kernel t)) (footprintOf (kernel u)) = true) :
    wfB (launch n kernel) = true := wfB_parFor n kernel hbody hdisj

end ParProg

end Paralever.Lang
