import Paralever.Core.Access

/-! # Executable sanity checks for `accesses` / `Indep`

The one property that must hold: shared reads are independent, same-location writes are not.
Bernstein, not `∗`. Rationale: `docs/access.md`. `decide` only — see `Test/Sanity.lean`. -/

namespace Paralever.Test

open Paralever ParM

def σ0 : State := fun _ => Val.int 0

example : indepB (accesses (wr 0 (.int 1)) σ0) (accesses (wr 1 (.int 2)) σ0) = true := by decide

example : indepB (accesses (wr 7 (.int 1)) σ0) (accesses (wr 7 (.int 2)) σ0) = false := by decide

/-- Shared reads are independent — this is what distinguishes Bernstein from `∗`-disjointness
and is what makes matmul provable. -/
example : indepB (accesses (rd 7) σ0) (accesses (rd 7) σ0) = true := by decide

example : indepB (accesses (rd 7) σ0) (accesses (wr 7 (.int 1)) σ0) = false := by decide

end Paralever.Test
