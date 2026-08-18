import Paralever.Core.Semantics

/-! # Executable sanity checks for the semantics

Guards against the two ways this project can go wrong: a race check too weak (theorem false) or
too strong (theorem vacuous). Rationale: `docs/semantics.md`.

Proved by `decide`/`rfl` only — never `native_decide`, which would add `Lean.ofReduceBool` to the
axiom set.
-/

namespace Paralever.Test

open Paralever ParM

def σ0 : State := fun _ => Val.int 0

def isWrong {α : Type} : Conf α → Bool
  | .wrong => true
  | _      => false

/-! ### Race detection -/

example : racing (nextAccs (wr 7 (.int 1))) (nextAccs (wr 7 (.int 2))) = true := rfl
example : racing (nextAccs (wr 0 (.int 1))) (nextAccs (wr 1 (.int 2))) = false := rfl
example : racing (nextAccs (rd 7)) (nextAccs (wr 7 (.int 1))) = true := rfl

/-- Shared reads must not race. Bernstein rather than `∗`; matmul depends on it. -/
example : racing (nextAccs (rd 7)) (nextAccs (rd 7)) = false := rfl

/-! ### Stepping -/

/-- Anti-vacuity witness: conflicting writes abort, so `Safe` genuinely excludes something. -/
example : (step (parPair (wr 7 (.int 1)) (wr 7 (.int 2))) σ0).map isWrong = [true] := rfl

/-- Disjoint writes interleave two ways, neither aborting. -/
example : (step (parPair (wr 0 (.int 1)) (wr 1 (.int 2))) σ0).map isWrong = [false, false] := rfl

/-- The sequential counterpart is deterministic. -/
example : (step (seqPair (wr 0 (.int 1)) (wr 1 (.int 2))) σ0).length = 1 := rfl

end Paralever.Test
