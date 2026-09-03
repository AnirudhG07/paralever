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
import Paralever.Examples.SumArray
import Paralever.Examples.SumArrayTask
import Paralever.Examples.Sort
import Paralever.Examples.SortTask
import Paralever.Examples.SharedReads
import Paralever.Examples.DoubleInto
import Paralever.Examples.MatMul
import Paralever.Examples.MatMulTask
import Paralever.Examples.MergeSort
import Paralever.Examples.ParMapDemo

-- `Test/*.lean` are standalone sanity checks, built directly by the library glob (this file's
-- role is the public-facing umbrella); not imported here since `Sanity.lean` and
-- `AccessSanity.lean` each define their own `σ0` under `namespace Paralever.Test`, which collide
-- if both land in one file's environment.
