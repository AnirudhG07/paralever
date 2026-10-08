
import Paralever.Core.ParM
import Paralever.Core.Semantics
import Paralever.Core.Access
import Paralever.Theory.Decomposition
import Paralever.Theory.WellFormedCanonical
import Paralever.Theory.Sequentialize
import Paralever.Theory.Intervals
import Paralever.Pragma.ParallelFor
import Paralever.Pragma.ArrRef
import Paralever.Pragma.ParMap
import Paralever.Compile.TaskFacts
import Paralever.Compile.Exec
import Paralever.Search.RaceSearch
import Paralever.Logic.BIInstance
import Paralever.Logic.Rules
import Paralever.Lib.Compose
import Paralever.Lib.TypedRead
import Paralever.Lib.TouchesOnly
import Paralever.Pragma.MapArray
import Paralever.Lib.FootprintSimp
import Paralever.Lib.Notation
import Paralever.Lib.OpaqueOp
import Paralever.Lib.Reduce
import Paralever.Lib.Pure
import Paralever.Lib.Render
import Paralever.Lib.Cost
import Paralever.Lib.Block

/-! # Paralever — parallel programs equal their sequential counterparts

Prove one metatheorem — independent branches ⇒ `par p q` behaves exactly like `seqPair p q` under
*every* schedule — and each program then reduces to discharging an independence obligation.

Where things live:

| directory | contents |
|---|---|
| `Core/` | `ParM` (programs as data), the small-step semantics, footprints and `Indep` |
| `Theory/` | `par_seq_eq` and its machinery (`wellFormed_canonical`, footprint intervals) |
| `Lib/` | the proof-burden layer: typed access, block IR, reductions, the pure bridge, cost |
| `Pragma/` | user-facing loop forms — `#parallel_for`, `mapArray`, `parMap`, `ArrRef` |
| `Logic/` | Tier-2 Hoare triples and the iris-lean BI instance |
| `Compile/` | `execTask`, which runs a program on real threads, and the `Task` facts it rests on |
| `Search/` | counterexample search: race-site scan, schedules, `follow_sound` |

Design rationale lives in `docs/`, one file per topic; the plan is `PLAN.md` and the reading list is
`papers.md`. Start at `docs/program-model.md`.
-/

-- Examples/ and Test/ are separate lean_lib entries (see lakefile.toml), not part of the
-- Paralever library umbrella. Build them with `lake build Examples` / `lake build Test`.
