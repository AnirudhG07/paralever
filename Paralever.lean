
import Paralever.Core.ParM
import Paralever.Core.Semantics
import Paralever.Core.Access
import Paralever.Theory.Decomposition
import Paralever.Theory.WellFormedCanonical
import Paralever.Theory.Sequentialize
import Paralever.Theory.Intervals
import Paralever.Theory.Box
import Paralever.Theory.Nest
import Paralever.Compile.TaskFacts
import Paralever.Compile.Exec
import Paralever.Search.RaceSearch
import Paralever.Search.Explain
import Paralever.Search.ExplainHtml
import Paralever.Tactic
import Paralever.Logic.Rules
import Paralever.Lib.ArrRef
import Paralever.Lib.Compose
import Paralever.Lib.TypedRead
import Paralever.Lib.TouchesOnly
import Paralever.Lib.Loop
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
import Paralever.Kernels.MapArray
import Paralever.Kernels.ParMap
import Lang.Core.Prog
import Lang.Core.Layout
import Lang.Core.Kernels
import Lang.Core.Cuda
import Lang.Core.Cost
import Lang.Core.Exec
import Lang.Core.Analysis
import Lang.Core.AutoParSound
import Lang.Core.Notation
import Paralever.AutoPar.Chain
import Paralever.AutoPar.Plan
import Paralever.AutoPar.Dag
import Paralever.AutoPar.Sound
import Paralever.AutoPar.Print

/-! # Paralever — parallel programs equal their sequential counterparts

Prove one metatheorem — independent branches ⇒ `par p q` behaves exactly like `seqPair p q` under
*every* schedule — and each program then reduces to discharging an independence obligation.

Where things live:

| directory | contents |
|---|---|
| `Core/` | `ParM` (programs as data), the small-step semantics, footprints and `Indep` |
| `Theory/` | `par_seq_eq` and its machinery (`wellFormed_canonical`, footprint intervals) |
| `Lib/` | the proof-burden layer: `ArrRef`, the `#parallel_for` loop validator, typed access, block IR, reductions, the pure bridge, cost |
| `Kernels/` | named parallel shapes with one-shot theorems — `parEach`, `broadcastPar`, `gridReducePar`, `mapArray`, `parMap` |
| `Lang/` | a first-order imperative language with `parallel` blocks, lowered into `ParM`; `Core` + `Kernels` + `Cuda` + `Cost` + `Exec` + `Analysis` + `Notation` |
| `Logic/` | Tier-2 Hoare triples, over `Core/Access.lean`'s own footprints |
| `Compile/` | `execTask`, which runs a program on real threads, and the `Task` facts it rests on |
| `Search/` | counterexample search: race-site scan, schedules, `follow_sound`, `Explain` (the interleaving printed) and `ExplainHtml` (the same, as an infoview widget) |

Design rationale lives in `docs/`, one file per topic; the plan is `PLAN.md` and the reading list is
`papers.md`. Start at `docs/program-model.md`.
-/

-- Examples/ and Test/ are separate lean_lib entries (see lakefile.toml), not part of the
-- Paralever library umbrella. Build them with `lake build Examples` / `lake build Test`.
