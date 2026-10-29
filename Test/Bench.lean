import Bench.Report
import Bench.Scale

/-! # The harness's own gates

The harness measures; these gate the measuring. Everything here is pure — a corpus *run* is the
executable's job, deliberately, because `lake build` must not time anything (`docs/bench.md`). So
what is gated is the scoring arithmetic, the soundness rule, and the manifest's labels.

The scoring code is the same code `MLIR/Corpus.lean` calls for its seven pilots, so a change that
broke one of these would also move that module's pinned `(3, 0, 0, 4)`.

Rationale: `docs/bench.md`. -/

namespace Paralever.Test.Bench
open Paralever.Bench

/-! ## The matrix counts what it says it counts -/

private def synth (racy : Bool) (nm : String) : Entry Unit := entry nm () racy

private def four : List (Entry Unit) :=
  [synth true "a", synth true "b", synth false "c", synth false "d"]

-- a perfect check
#guard (confusionOf four (fun e => some e.racy)).tuple == (2, 0, 0, 2)
-- a check that calls everything racy: every race caught, nothing proved
#guard (confusionOf four (fun _ => some true)).tuple == (2, 2, 0, 0)
-- a check that calls everything race-free: the false-negative column, which must never be non-zero
#guard (confusionOf four (fun _ => some false)).tuple == (0, 0, 2, 2)
-- no answer is counted apart, not folded into an error column
#guard confusionOf four (fun _ => none) == { skipped := 4 }
#guard (confusionOf four (fun _ => none)).scored == 0

/-! ### The two columns a refuse-everything tool cannot game

`sensitivity` and `specificity` are reported separately because the reachable DataRaceBench subset
is skewed 47 racy to 29 race-free: one combined accuracy figure would reward refusing everything.
-/

#guard (confusionOf four (fun _ => some true)).sensitivity == (2, 2)    -- looks perfect …
#guard (confusionOf four (fun _ => some true)).specificity == (0, 2)    -- … and is not

/-! ## The precision gap

Refused for every heap, accepted at this one. An empty gap is the position seven pilots are in. -/

#guard gapOf four (fun _ => some true) (fun _ => some false) == ["a", "b", "c", "d"]
#guard gapOf four (fun _ => some true) (fun _ => some true) == []
#guard gapOf four (fun _ => some false) (fun _ => some false) == []

/-! ## The soundness rule

A false refusal is imprecision and reportable; a false acceptance is a soundness bug and stops the
build. Only the second may fail. -/

#guard soundnessHolds [.proved, .soundRefusal, .inconclusive 11]
#guard soundnessHolds [.falseRefusal .computedAddress, .falseRefusal .branch, .overCeiling]
#guard !soundnessHolds [.proved, .falseAcceptance]
#guard !soundnessHolds [.falseAcceptance]

/-! ## The denominator

An entry the model does not describe is reported with its count, never booked as a false positive.
-- ref: `docs/mlir.md` § the DataRaceBench methodology -/

private def mixed : List (Entry Unit) :=
  [ synth true "racy"
  , { name := "locked", item := (), racy := false, reach := .unmodelled "omp_set_lock" }
  , { name := "huge",   item := (), racy := false, reach := .overCeiling } ]

#guard (reachable mixed).length == 1
#guard (outsideDenominator mixed).map Prod.fst == ["locked", "huge"]
#guard (confusionReachable mixed (fun e => some e.racy)).tuple == (1, 0, 0, 0)
-- and scoring the whole thing instead would have claimed three answers
#guard (confusionOf mixed (fun e => some e.racy)).tuple == (1, 0, 0, 2)

/-! ## Two labels, because the two matrices ask different questions

`Entry.racyHere` defaults to `racy`, so an entry that is racy at every heap states one label. -/

#guard (synth true "x").racyAtDeclared == true
#guard (synth false "y").racyAtDeclared == false
#guard ({ name := "s", item := (), racy := true, racyHere := some false } :
          Entry Unit).racyAtDeclared == false
#guard heapSensitive four == []

/-! ## The manifest

### The `.prl` half

Nineteen `.prl` entries, every one justified, and three of them heap-sensitive — which is what makes
this corpus able to exhibit a gap at all. The measured verdicts are in `docs/bench.md`. -/

#guard Manifest.prlCorpus.length == 19
#guard Manifest.prlCorpus.all (fun e => e.why != "")
#guard Manifest.prlCorpus.all (fun e => e.item.endsWith ".prl")
#guard Manifest.prlCorpus.all (fun e => e.reach == .reachable)

-- three entries are racy at some heap; exactly one is racy at the heap its file declares
#guard (Manifest.prlCorpus.filter (fun e => e.racy)).map Entry.name
        == ["race", "scatter", "stripe"]
#guard (Manifest.prlCorpus.filter (fun e => e.racyAtDeclared)).map Entry.name == ["race"]

-- `scatter` and `stripe` are the heap-sensitive pair: racy somewhere, race-free here. `branch`
-- carries the *same* label both ways and is simply refused, so it is not heap-sensitive -- it is
-- the inconclusive cell, which is a different finding and counted separately.
#guard Manifest.gapCapable == ["scatter", "stripe"]
#guard (Manifest.prlCorpus.filter (fun e => e.name == "branch")).map
          (fun e => (e.racy, e.racyHere)) == [(false, some false)]

/-! ### The MLIR half

Nine pilots, the same nine files `MLIR/Corpus.lean` gates, and the label is the one the filename
carries — DataRaceBench's convention, so the two modules cannot disagree about what a pilot is.
Four are racy, and none is heap-sensitive, which is why the gap is empty on the pilots alone. -/

#guard Manifest.mlirCorpus.length == 9
#guard Manifest.mlirCorpus.all (fun e => e.why != "")
#guard Manifest.mlirCorpus.all (fun e => e.item.endsWith ".mlir")
#guard Manifest.mlirCorpus.all (fun e => e.racy == e.name.endsWith "-yes")
#guard (Manifest.mlirCorpus.filter (fun e => e.racy)).length == 4
#guard heapSensitive Manifest.mlirCorpus == []

-- the two corpora together, and the gap comes entirely from the `.prl` half
#guard Manifest.corpus.length == 28
#guard Manifest.gapCapable == ["scatter", "stripe"]
#guard (Manifest.corpus.filter (fun e => e.racy)).length == 7

/-! ## The cost curve's shapes

Both ceilings, and the two forms of one shape. The point count is the number the curve is read
against, so it is gated rather than trusted: `elemwise` is `n²` and `gemm` is `n³`. -/

#guard Scale.Shape.elemwise.points 20 == 400
#guard Scale.Shape.gemm.points 10 == 1000
#guard ({} : Scale.Limits).ms == 8000
#guard ({} : Scale.Limits).points == 65536

-- the rolled source is the same handful of lines at every size; the unrolled one grows with the
-- iteration space, which is the cost the curve measures
#guard ((Scale.Shape.elemwise.rolledSrc 8).splitOn "\n").length
        == ((Scale.Shape.elemwise.rolledSrc 800).splitOn "\n").length
#guard (Scale.Shape.elemwise.unrolledSrc 4).length > (Scale.Shape.elemwise.rolledSrc 4).length
#guard (Scale.Shape.elemwise.unrolledSrc 8).length > (Scale.Shape.elemwise.unrolledSrc 4).length

-- one `parallel` arm per thread: n - 1 separators for n threads
#guard ((Scale.Shape.elemwise.unrolledSrc 5).splitOn "} | {").length == 5
#guard ((Scale.Shape.gemm.unrolledSrc 3).splitOn "} | {").length == 3

-- and both forms compile, agree on the thread count, and are accepted
private def bothOf (sh : Scale.Shape) (n : Nat) : Option (Bool × Bool × Nat × Nat) :=
  match Lang.ofString (sh.rolledSrc n), Lang.ofString (sh.unrolledSrc n) with
  | .ok a, .ok b =>
      some (Lang.ParProg.wfB a.prog, Lang.ParProg.wfB b.prog
           , Lang.ParProg.threadCount a.prog, Lang.ParProg.threadCount b.prog)
  | _, _ => none

#guard bothOf .elemwise 20 == some (true, true, 20, 20)
#guard bothOf .gemm 12 == some (true, true, 12, 12)

/-! ## Timing arithmetic

The median, not the mean, and the spread beside it so a noisy measurement is visible. -/

#guard medianOf [5] == 5
#guard medianOf [1, 100, 2] == 2                      -- the mean would say 34
#guard medianOf [] == 0
#guard (samplesOf [3, 1, 2]).median == 2
#guard (samplesOf [3, 1, 2]).min == 1
#guard (samplesOf [3, 1, 2]).max == 3
#guard (samplesOf [3, 1, 2]).runs == 3

/-! ## Fanning out preserves order

A report must not depend on which core finished first, so `stripe` partitions and `mapParallel`
sorts back. The partition is gated here; that the sort restores order is gated by the executable
producing identical CSV at `--jobs 1` and `--jobs 8`. -/

#guard stripe 3 [0, 1, 2, 3, 4, 5, 6] == [[0, 3, 6], [1, 4], [2, 5]]
#guard (stripe 4 (List.range 10)).flatten.length == 10
#guard ((stripe 4 (List.range 10)).flatten.mergeSort (· ≤ ·)) == List.range 10
#guard stripe 1 [0, 1, 2] == [[0, 1, 2]]
-- a degenerate request still partitions, rather than dropping the work
#guard stripe 0 [0, 1, 2] == [[0, 1, 2]]

end Paralever.Test.Bench
