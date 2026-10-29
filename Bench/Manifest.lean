import Bench.Verdict

/-! # The corpus, as data

Every entry carries a declared label and the reason for it. A label without a justification is an
assertion, and a corpus of assertions cannot be audited — so the `why` field is not decoration.

Two labels per entry, because the two matrices ask different questions (`Bench/Verdict.lean`
explains why on `Entry.racyHere`). The `.prl` entries below are the project's own examples, relabelled
*semantically*: `Test/Lang.lean`'s corpus records what `wfB` does, which is the answer, not the
question. Scoring a check against its own output measures nothing.

Rationale: `docs/bench.md`. -/

namespace Paralever.Bench.Manifest
open Paralever.Bench

/-- A `.prl` entry: the path, the two labels, and the justification. -/
private def prl (name : String) (racy : Bool) (why : String)
    (racyHere : Option Bool := none) : Entry String :=
  { name := name, item := "Examples/Language/" ++ name ++ ".prl"
  , racy := racy, racyHere := racyHere, why := why }

/-- **The project's own `.prl` examples, labelled by what the program does** rather than by what the
check says about it. Measured verdicts are in `docs/bench.md`; the labels here are prior to them. -/
def prlCorpus : List (Entry String) :=
  [ prl "sum"      false "chunked reduce: each thread writes its own partial"
  , prl "matmul"   false "disjoint output cells, overlapping input rows and columns"
  , prl "stencil"  false "writes B, reads A — different buffers"
  , prl "pipeline" false "stages separated by barriers"
  , prl "control"  false "a branch whose arms touch disjoint cells"
  , prl "chain"    false "straight-line: no fork at all"
  , prl "arena"    false "placed buffers whose live ranges are disjoint"
  , prl "phases"   false "a barrier between the phases"
  , prl "funcs"    false "a def written out at each call site, hygienically"
  , prl "sortnet"  false "comparator phases, disjoint within a phase"
  , prl "equiv"    false "two sorts compared; the left side has no fork"
  , prl "twofold"  false "two parallel reductions, disjoint partials"
  , prl "strength" false "two programs agreeing in memory and in registers"
  , prl "tally"    false "race-free; the two sides disagree on %cnt, which is a claim failure"
    -- the first entry carried **rolled**: 144 points as one `ParProg.loop`, so what the check
    -- decides is three subscript maps rather than an iteration space
  , prl "rolled"   false "a rolled 12 x 12 nest: thread i owns the twelve consecutive cells \
C[i, 0..12), so the write is injective across threads although it mentions the sequential level"
    -- the genuinely racy one
  , prl "race"     true  "two threads write one cell at every heap"
    -- heap-sensitive: racy somewhere, race-free at the heap the file declares
  , prl "scatter"  true  "A[B[i]]: two threads collide exactly when two entries of B agree, which \
the declared heap does not" (racyHere := some false)
  , prl "stripe"   true  "a computed address whose Int.toNat clamp folds two indices onto one cell \
at some heap, but not at the declared one" (racyHere := some false)
    -- believed race-free, and wfB cannot see it: the open case
  , prl "branch"   false "mirror-image arms, so only one of the conflicting writes ever runs. \
Race-free by inspection; wfB refuses because it unions both arms, and the bounded probe finds no \
counterexample — this is the inconclusive cell, not a proof" (racyHere := some false) ]

/-- An MLIR entry. The label is the one the **filename** carries, which is DataRaceBench's
convention and already what `MLIR/Corpus.lean` scores against: `-yes` expects a race, `-no` expects
none. -- ref: `docs/mlir.md` § The corpus -/
private def mlir (name : String) (why : String) : Entry String :=
  { name := name, item := "Examples/Mlir/" ++ name ++ ".mlir"
  , racy := name.endsWith "-yes", why := why }

/-- **The MLIR pilots**, the same nine files `MLIR/Corpus.lean` gates. They are scored here through
the same front end the command line uses — `Tool.loadAny` reads the file — so the harness measures
the path a user takes rather than an `include_str` of it. -/
def mlirCorpus : List (Entry String) :=
  [ mlir "doall-no"           "C[i] := A[i] + B[i]: eight threads write disjoint cells"
  , mlir "antidep-yes"        "A[i] := A[i+1]: a thread reads the cell its neighbour writes"
  , mlir "reduction-yes"      "every thread accumulates into S[0] — the missing reduction clause"
  , mlir "reduction-split-no" "the same reduction done right: one partial per thread"
  , mlir "stencil-f64-no"     "a floating-point sliding window: reads overlap, writes do not"
  , mlir "nested-2d-no"       "a two-dimensional index space over disjoint output cells"
  , mlir "indirect-yes"       "A[B[i]]: a computed address, and genuinely racy here"
  , mlir "pretty-doall-no"    "doall-no in MLIR custom form, read by MLIR/Pretty.lean"
  , mlir "pretty-reduce-yes"  "reduction-yes in custom form" ]

/-- **Both front ends, one run.** The two corpora are scored together because the matrix is about
the checks, not about which reader produced the program — and a row's `front` column says which
did. -/
def corpus : List (Entry String) := prlCorpus ++ mlirCorpus

/-- Entries whose two labels differ, so the corpus can exhibit the gap at all. A corpus where this
is empty cannot measure precision — which is the position the nine MLIR pilots are in. -/
def gapCapable : List String := heapSensitive corpus

end Paralever.Bench.Manifest
