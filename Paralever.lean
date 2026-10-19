
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
import Paralever.Search.Explain
import Paralever.Search.ExplainHtml
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
import Paralever.Kernels.Assign
import Paralever.Kernels.Grid
import Paralever.Lang.Core
import Paralever.Lang.Layout
import Paralever.Lang.Kernels
import Paralever.Lang.Cuda
import Paralever.Lang.Cost
import Paralever.Lang.Exec
import Paralever.Lang.Analysis
import Paralever.Lang.AutoParSound
import Paralever.Lang.Notation
import Paralever.AutoPar.Chain
import Paralever.AutoPar.Plan
import Paralever.AutoPar.Dag
import Paralever.AutoPar.Sound
import Paralever.AutoPar.Rewrite

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
| `Kernels/` | one-line data-parallel shapes — `parEach`, `broadcastPar`, `gridReducePar` |
| `Lang/` | a first-order imperative language with `parallel` blocks, lowered into `ParM`; `Core` + `Kernels` + `Cuda` + `Cost` + `Exec` + `Analysis` + `Notation` |
| `Logic/` | Tier-2 Hoare triples and the iris-lean BI instance |
| `Compile/` | `execTask`, which runs a program on real threads, and the `Task` facts it rests on |
| `Search/` | counterexample search: race-site scan, schedules, `follow_sound`, `Explain` (the interleaving printed) and `ExplainHtml` (the same, as an infoview widget) |

Design rationale lives in `docs/`, one file per topic; the plan is `PLAN.md` and the reading list is
`papers.md`. Start at `docs/program-model.md`.
-/

-- Examples/ and Test/ are separate lean_lib entries (see lakefile.toml), not part of the
-- Paralever library umbrella. Build them with `lake build Examples` / `lake build Test`.
