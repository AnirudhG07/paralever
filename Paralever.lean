-- This module serves as the root of the `Paralever` library.
-- Import modules here that should be built as part of the library.
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

-- Examples/ and Test/ are separate lean_lib entries (see lakefile.toml), not part of the
-- Paralever library umbrella. Build them with `lake build Examples` / `lake build Test`.
