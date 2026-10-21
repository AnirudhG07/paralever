import MLIR.Eval
import MLIR.Load

/-! # The labelled corpus, as build gates

Seven hand-written benchmarks, each covering a pattern DataRaceBench covers, with the label in the
filename exactly as DataRaceBench carries it: `-yes` means a race is expected and `-no` means none
is. Hand-written on purpose — it decouples this step from a Polygeist build, so the reader, the
lowering and the reference interpreter can be gated before any external toolchain exists.
-- ref: `docs/mlir.md` § The corpus

Everything below is a `#guard`, so a regression fails the build rather than a report. The five
numbers the plan asks a corpus report for are `summary`:

1. **expressiveness** — `unsupportedOps` must be empty for every entry;
2. **verdict accuracy** — the confusion matrix against the labels, with zero false negatives
   expected by `raceSites_nil_iff` rather than hoped for;
3. **the precision gap** — entries `wfB` rejects and `wellFormedB` accepts, which is what an
   over-approximated footprint costs;
4. **differential execution** — the `ParProg` run against the ℚ reference run, cell for cell;
5. **the round trip** — `render ∘ parse` idempotent, so a reader bug cannot hide behind a lowering
   that happens to work. -/

namespace Paralever.MLIR.Corpus
open Paralever Paralever.MLIR

/-- One benchmark: a name, its source, and the label its filename carries. -/
structure Entry where
  name : String
  src  : String
  /-- `true` when the filename ends `-yes`, i.e. a race is expected. -/
  racy : Bool

/-- The pilots, in the order the report lists them. Each covers a distinct pattern: a `doall`, an
antidependence, a missing reduction clause, the same reduction done right, a floating-point
sliding window, a two-dimensional index space, and an indirect access. -/
def corpus : List Entry :=
  [ ⟨"doall-no",            include_str "../Examples/Mlir/doall-no.mlir",            false⟩
  , ⟨"antidep-yes",         include_str "../Examples/Mlir/antidep-yes.mlir",         true⟩
  , ⟨"reduction-yes",       include_str "../Examples/Mlir/reduction-yes.mlir",       true⟩
  , ⟨"reduction-split-no",  include_str "../Examples/Mlir/reduction-split-no.mlir",  false⟩
  , ⟨"stencil-f64-no",      include_str "../Examples/Mlir/stencil-f64-no.mlir",      false⟩
  , ⟨"nested-2d-no",        include_str "../Examples/Mlir/nested-2d-no.mlir",        false⟩
  , ⟨"indirect-yes",        include_str "../Examples/Mlir/indirect-yes.mlir",        true⟩ ]

/-- Parsed and lowered, keeping the ops so the reference interpreter can be run on them. -/
def lowered (e : Entry) : Option (List Op × Lowered) :=
  match parse e.src with
  | .error _ => none
  | .ok ops  =>
      match lower ops with
      | .error _ => none
      | .ok r    => some (ops, r)

def byName (nm : String) : Option (List Op × Lowered) :=
  (corpus.find? (fun e => e.name == nm)).bind lowered

/-! ## 5. The round trip -/

#guard corpus.all (fun e => roundTrips e.src)

/-! ## 1. Expressiveness

Every op in every pilot has a lowering rule. When a benchmark is added that does not, this gate is
what turns "it did not work" into a named op to implement. -/

/-- Op names the lowering has no rule for, per entry. -/
def missing (e : Entry) : List String :=
  match parse e.src with
  | .error _ => ["<parse failed>"]
  | .ok ops  => unsupportedOps ops

#guard corpus.all (fun e => (missing e).isEmpty)
#guard corpus.all (fun e => (lowered e).isSome)

/-! ## 2. Verdict accuracy

`wellFormedB` is the exact per-heap check, and `raceSites_nil_iff` makes it complete for the
obligation — so a false negative here is a bug in `raceSites`, not a tuning matter. -/

/-- The tool's answer: is this program racy? -/
def detected (e : Entry) : Option Bool := (lowered e).map (fun p => !p.2.verdictExact)

/-- `(true positives, false positives, false negatives, true negatives)`. -/
def confusion : Nat × Nat × Nat × Nat :=
  corpus.foldl
    (fun (c : Nat × Nat × Nat × Nat) e =>
      let (tp, fp, fn, tn) := c
      match detected e with
      | some true  => if e.racy then (tp + 1, fp, fn, tn) else (tp, fp + 1, fn, tn)
      | some false => if e.racy then (tp, fp, fn + 1, tn) else (tp, fp, fn, tn + 1)
      | none       => c)
    (0, 0, 0, 0)

#guard confusion == (3, 0, 0, 4)
#guard corpus.all (fun e => detected e == some e.racy)

/-! ## 3. The precision gap

`wfB` compares syntactic footprints over every heap; `wellFormedB` measures them along the
canonical run at one heap. An entry the first rejects and the second accepts is the price of an
over-approximation, and `indirect-yes` is the shape that normally pays it — here it does not,
because the program is genuinely racy. -/

/-- Entries rejected syntactically but accepted exactly. -/
def gap : List String :=
  (corpus.filter (fun e =>
    match lowered e with
    | some (_, r) => !r.verdict && r.verdictExact
    | none        => false)).map Entry.name

#guard gap == []

/-- Entries whose footprint is a bound rather than the exact set. -/
def approximated : List String :=
  (corpus.filter (fun e =>
    match lowered e with
    | some (_, r) => !r.footprintIsExact
    | none        => false)).map Entry.name

#guard approximated == ["indirect-yes"]

/-! ## 4. Differential execution

The `ParProg` run against the ℚ reference run, cell for cell. It is a test of the lowering only on
a **race-free** program with integral values: a racy program has no determinate answer, so a
disagreement there is a second witness of the race rather than a fault — and a float program
disagrees by the `Int` truncation `Lowered.notes` already named. -/

/-- Entries on which the two runs must agree: race-free, and values exact in `Int`. -/
def determinate (e : Entry) : Bool :=
  match lowered e with
  | some (_, r) => r.verdictExact && r.exactValues
  | none        => false

#guard corpus.all (fun e =>
  if determinate e then
    match lowered e with
    | some (ops, r) => r.agrees ops == some true
    | none          => false
  else true)

/-! ### The values themselves

Pinned so a change of meaning fails the build, not just a change of verdict. -/

/-- A named buffer after the `ParProg` run. -/
def progOf (nm buf : String) : Option (List Scalar) := (byName nm).map (fun p => p.2.progCells buf)

/-- A named buffer after the ℚ reference run. -/
def refOf (nm buf : String) : Option (List Scalar) :=
  (byName nm).bind (fun p => (p.2.refCells p.1 buf).toOption)

-- `doall`: elementwise sum, both ways.
#guard progOf "doall-no" "C" == some [.int 11, .int 22, .int 33, .int 44,
                                      .int 55, .int 66, .int 77, .int 88]
#guard refOf  "doall-no" "C" == progOf "doall-no" "C"

-- `nested-2d`: a 3×4 index space, row-major through the buffer's own strides.
#guard progOf "nested-2d-no" "C" == some [.int 2, .int 4, .int 6, .int 8, .int 10, .int 12,
                                          .int 14, .int 16, .int 18, .int 20, .int 22, .int 24]

-- the reduction done right: disjoint partials, then a sequential fold.
#guard progOf "reduction-split-no" "part" == some [.int 3, .int 7, .int 11, .int 15]
#guard progOf "reduction-split-no" "sum"  == some [.int 36]
#guard refOf  "reduction-split-no" "sum"  == some [.int 36]

/-! **The race, as a value.** The reference run takes the canonical schedule and reaches 36; the
threaded run reaches something else. That is the anti-vacuity obligation discharged through MLIR:
the program the verdict rejects really does depend on its schedule.
-- ref: `CLAUDE.md` § Anti-vacuity discipline -/

#guard refOf "reduction-yes" "sum" == some [.int 36]
#guard refOf "reduction-yes" "sum" != progOf "reduction-yes" "sum"

/-! **ℚ is exact where `Int` is not.** `0.5·1 + 0.25·2 + 0.25·3 = 7/4`, which the reference run
computes and the `Int` lowering truncates to `0` — and the verdict is `true` either way, because a
footprint does not depend on a value. -/

#guard refOf "stencil-f64-no" "B" == some [.rat (7/4), .rat (11/4), .rat (15/4),
                                           .rat (19/4), .rat (23/4), .rat (27/4),
                                           .rat 0, .rat 0]
#guard (byName "stencil-f64-no").map (fun p => p.2.verdictExact) == some true
#guard (byName "stencil-f64-no").map (fun p => p.2.exactValues)  == some false

/-! ## The report -/

/-- One line per benchmark: label, verdict, footprint, values, and whether the runs agree. -/
def row (e : Entry) : String :=
  match lowered e with
  | none          => e.name ++ "  <failed>"
  | some (ops, r) =>
      e.name
        ++ "  label=" ++ (if e.racy then "racy    " else "race-free")
        ++ "  wfB=" ++ toString r.verdict
        ++ "  exact=" ++ toString r.verdictExact
        ++ "  sites=" ++ toString r.sites.length
        ++ "  fp=" ++ (if r.footprintIsExact then "exact" else "bound")
        ++ "  values=" ++ (if r.exactValues then "Int" else "ℚ only")
        ++ "  agrees=" ++ toString (r.agrees ops)

/-! ## 6. The equivalence, once per race-free pilot

A `#guard` on `verdict` says the obligation was discharged; these say what discharging it buys.
`mlir_prog` quotes the lowered program, so `decide` sees a `ParProg` literal and `par_seq_eq`
applies to it with nothing further to supply. -/

def doall : Lang.ParProg           := mlir_prog "../Examples/Mlir/doall-no.mlir"
def reductionSplit : Lang.ParProg  := mlir_prog "../Examples/Mlir/reduction-split-no.mlir"
def stencil : Lang.ParProg         := mlir_prog "../Examples/Mlir/stencil-f64-no.mlir"
def nested2d : Lang.ParProg        := mlir_prog "../Examples/Mlir/nested-2d-no.mlir"

theorem doall_ok (ρ : Regs) (σ : State) :
    ParSeqEq (Lang.ParProg.execPar doall ρ) (Lang.ParProg.execSeq doall ρ) σ :=
  Lang.ParProg.par_seq_eq (by decide) ρ σ

theorem reductionSplit_ok (ρ : Regs) (σ : State) :
    ParSeqEq (Lang.ParProg.execPar reductionSplit ρ) (Lang.ParProg.execSeq reductionSplit ρ) σ :=
  Lang.ParProg.par_seq_eq (by decide) ρ σ

/-- The `f64` window. Values are approximated in `Int` (`exactValues = false`); the verdict and
therefore this theorem are unaffected, because no footprint inspects a `Val`. -/
theorem stencil_ok (ρ : Regs) (σ : State) :
    ParSeqEq (Lang.ParProg.execPar stencil ρ) (Lang.ParProg.execSeq stencil ρ) σ :=
  Lang.ParProg.par_seq_eq (by decide) ρ σ

theorem nested2d_ok (ρ : Regs) (σ : State) :
    ParSeqEq (Lang.ParProg.execPar nested2d ρ) (Lang.ParProg.execSeq nested2d ρ) σ :=
  Lang.ParProg.par_seq_eq (by decide) ρ σ

-- The three racy pilots have no such theorem: `wfB` refuses each of them, which is the `tp = 3`
-- of the confusion count above.
#guard ["antidep-yes", "reduction-yes", "indirect-yes"].all
  (fun nm => (byName nm).all (fun p => !p.2.verdict))

/-- The five numbers, plus a row per benchmark. -/
def summary : String :=
  let (tp, fp, fn, tn) := confusion
  "expressible    " ++ toString (corpus.filter (fun e => (lowered e).isSome)).length
    ++ "/" ++ toString corpus.length
    ++ "\nunsupported    " ++ toString (corpus.flatMap missing).eraseDups
    ++ "\nconfusion      tp=" ++ toString tp ++ " fp=" ++ toString fp
                     ++ " fn=" ++ toString fn ++ " tn=" ++ toString tn
    ++ "\nprecision gap  " ++ toString gap
    ++ "\nover-approx    " ++ toString approximated
    ++ "\nround trip     " ++ toString (corpus.all (fun e => roundTrips e.src))
    ++ "\n\n" ++ "\n".intercalate (corpus.map row)

end Paralever.MLIR.Corpus
