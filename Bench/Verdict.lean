/-! # The scoring, once, for every corpus

A labelled corpus and a check that answers over it produce a confusion matrix. `MLIR/Corpus.lean`
computed one for its seven pilots; this module is that computation generalised over the corpus and
over the check, so the pilots and every suite added later are scored by the *same* code and cannot
disagree. That module's pinned values are unchanged by the move, which is the test that generalising
changed no meaning.

Imports nothing. The `MLIR` and `Lang` libs call into this one, so it must not call back — and a
scoring rule with no dependencies is also a scoring rule that can be read on its own.

Rationale: `docs/bench.md`. -/

namespace Paralever.Bench

/-! ## A corpus is labelled data

Without a declared label there is no matrix, only a list of outputs. -/

/-- Why a kernel is in the corpus at all, and whether a verdict on it is even meaningful.
`unreachable` is not a failure: it is a program the model does not describe, and
`docs/bench.md` keeps it out of the denominator with its count reported. -/
inductive Reach where
  /-- Both front ends can read it and every construct is modelled. -/
  | reachable : Reach
  /-- A construct with no counterpart in `ParM` — a lock, an atomic, a task. -/
  | unmodelled : String → Reach
  /-- Readable in principle, but past the unrolling or `decide` ceiling. -/
  | overCeiling : Reach
  deriving Repr, Inhabited, DecidableEq

/-- One corpus entry: a name, the thing itself, the declared label, and why it is reachable. -/
structure Entry (α : Type) where
  name  : String
  item  : α
  /-- `true` when a race is expected **at some heap** — the general question `wfB` answers. The
  `-yes`/`-no` filename convention DataRaceBench uses, and `MLIR/Corpus.lean:6` already follows,
  states this one. -/
  racy  : Bool
  /-- `true` when a race is expected **at the heap the file declares** — the question the exact
  check answers. `none` means "the same as `racy`", which is the common case.

  The two differ, and a single label cannot serve both matrices. `Examples/Language/scatter.prl`
  writes `A[B[i]]`: at the declared heap the indices are distinct and nothing collides, so it is
  race-free *here*; at a heap where two entries of `B` agree, two threads write one cell, so it is
  racy *somewhere*. `wfB`'s refusal is therefore sound for the general question and not a false
  refusal, and booking it as one would be a measurement error. -- ref: `docs/bench.md` -/
  racyHere : Option Bool := none
  reach : Reach := .reachable
  /-- Why the label is what it is. A label without a justification is an assertion. -/
  why   : String := ""

/-- A reachable entry with no recorded justification -- the common case, and the shape the MLIR
pilots were written in before the structure was shared. An anonymous constructor would have to
supply `reach` and `why` even though both default. -/
def entry {α : Type} (name : String) (item : α) (racy : Bool) : Entry α :=
  { name := name, item := item, racy := racy }

/-- The label for the per-heap question: the declared one, or the general one when the two agree. -/
def Entry.racyAtDeclared {α : Type} (e : Entry α) : Bool := e.racyHere.getD e.racy

/-- Entries whose two labels differ — the programs for which "racy" is not a property of the
program alone. Reported, because a corpus where this list is empty cannot exhibit the gap. -/
def heapSensitive {α : Type} (corpus : List (Entry α)) : List String :=
  (corpus.filter (fun e => e.racyHere.isSome && e.racyHere != some e.racy)).map Entry.name

/-! ## The matrix -/

/-- The four counts, named rather than positional — a bare `(3, 0, 0, 4)` cannot say which is
which. -/
structure Matrix where
  /-- labelled racy, reported racy -/
  tp : Nat := 0
  /-- labelled race-free, reported racy -/
  fp : Nat := 0
  /-- labelled racy, reported race-free. A soundness bug, not a tuning matter. -/
  fn : Nat := 0
  /-- labelled race-free, reported race-free -/
  tn : Nat := 0
  /-- no answer: the check did not apply, or the entry is not reachable -/
  skipped : Nat := 0
  deriving Repr, Inhabited, DecidableEq, BEq

namespace Matrix

/-- The positional form `MLIR/Corpus.lean` pins, so its existing `#guard` keeps its shape. -/
def tuple (m : Matrix) : Nat × Nat × Nat × Nat := (m.tp, m.fp, m.fn, m.tn)

def scored (m : Matrix) : Nat := m.tp + m.fp + m.fn + m.tn

/-- Of the entries labelled racy, the fraction caught. Reported separately from `specificity`
because the reachable DataRaceBench subset is label-skewed 47 to 29: a tool that refused every
program would score 62 % overall and 100 % here, and 0 % on the other column. -/
def sensitivity (m : Matrix) : Nat × Nat := (m.tp, m.tp + m.fn)

/-- Of the entries labelled race-free, the fraction proved. The column refusing everything cannot
game. -/
def specificity (m : Matrix) : Nat × Nat := (m.tn, m.tn + m.fp)

def add (a b : Matrix) : Matrix :=
  ⟨a.tp + b.tp, a.fp + b.fp, a.fn + b.fn, a.tn + b.tn, a.skipped + b.skipped⟩

/-- One line, in the order `MLIR/Corpus.lean`'s report prints it. -/
def line (m : Matrix) : String :=
  "tp=" ++ toString m.tp ++ " fp=" ++ toString m.fp
    ++ " fn=" ++ toString m.fn ++ " tn=" ++ toString m.tn
    ++ (if m.skipped == 0 then "" else " skipped=" ++ toString m.skipped)

end Matrix

/-- **The matrix, for any corpus and any check.** `detected e = some true` means the check reported
a race. `none` means it had no answer, which is counted apart rather than folded into either error
column — a tool that cannot read a file has not misclassified it. -/
def confusionOf {α : Type} (corpus : List (Entry α)) (detected : Entry α → Option Bool) : Matrix :=
  corpus.foldl
    (fun m e =>
      match detected e with
      | some true  => if e.racy then { m with tp := m.tp + 1 } else { m with fp := m.fp + 1 }
      | some false => if e.racy then { m with fn := m.fn + 1 } else { m with tn := m.tn + 1 }
      | none       => { m with skipped := m.skipped + 1 })
    {}

/-- The reachable entries — the denominator `docs/bench.md` insists on. -/
def reachable {α : Type} (corpus : List (Entry α)) : List (Entry α) :=
  corpus.filter (fun e => e.reach == .reachable)

/-- Everything else, with its reason, to be reported beside the matrix and never inside it. -/
def outsideDenominator {α : Type} (corpus : List (Entry α)) : List (String × Reach) :=
  (corpus.filter (fun e => e.reach != .reachable)).map (fun e => (e.name, e.reach))

/-- The matrix over the reachable entries only. -/
def confusionReachable {α : Type} (corpus : List (Entry α))
    (detected : Entry α → Option Bool) : Matrix :=
  confusionOf (reachable corpus) detected

/-! ## The precision gap

Every entry is scored twice: once by the check that answers for *every* heap, and once by the check
that answers for the heap the file declares. The gap between them is what an over-approximated
footprint costs, and it is the quantity both the nest certificate and the SMT route exist to shrink.
`MLIR/Corpus.lean` scored only the second, which is why its gap is empty. -/

/-- Entries the general check refuses and the exact check accepts. -/
def gapOf {α : Type} (corpus : List (Entry α))
    (general exact : Entry α → Option Bool) : List String :=
  (corpus.filter (fun e => general e == some true && exact e == some false)).map Entry.name

/-- Both matrices and the gap between them — the three numbers a precision claim needs. -/
structure TwoMatrices where
  /-- scored against the every-heap check -/
  anyHeap  : Matrix
  /-- scored against the this-heap check -/
  thisHeap : Matrix
  /-- refused generally, accepted exactly -/
  gap      : List String
  deriving Repr, Inhabited

def twoMatrices {α : Type} (corpus : List (Entry α))
    (general exact : Entry α → Option Bool) : TwoMatrices :=
  ⟨confusionOf corpus general, confusionOf corpus exact, gapOf corpus general exact⟩

/-! ## Why a refusal happened

A count of false refusals is not actionable; an attribution is. There are exactly three widening
clauses in the footprint and they reduce to two causes, so this list is determined by the
implementation rather than guessed — `Lang/Core/Prog.lean:191`, and `ParProg.widenedBy` returns
exactly those two strings. -/

/-- Why a race-free program was refused. -/
inductive Cause where
  /-- A computed address: every cell of the buffer. `Examples/Language/scatter.prl`'s shape. -/
  | computedAddress : Cause
  /-- A branch: both arms, although one runs. `Examples/Language/branch.prl`'s shape. -/
  | branch : Cause
  /-- Not a refusal to fix. -/
  | genuinelyRacy : Cause
  /-- Past the unrolling or `decide` ceiling — what `docs/loops.md` targets. -/
  | ceiling : Cause
  /-- The front end could not read it, or the construct is out of scope. -/
  | unreachable : String → Cause
  deriving Repr, Inhabited, DecidableEq

def Cause.word : Cause → String
  | .computedAddress => "computed address"
  | .branch          => "branch"
  | .genuinelyRacy   => "genuinely racy"
  | .ceiling         => "over the ceiling"
  | .unreachable s   => "unreachable: " ++ s

/-- The one outcome a corpus run reports per entry. `falseAcceptance` is the only cell that fails a
build: a false refusal is imprecision to report, a false acceptance is a soundness bug. -/
inductive Cell where
  | proved : Cell
  | soundRefusal : Cell
  | falseRefusal : Cause → Cell
  | falseAcceptance : Cell
  | inconclusive : Nat → Cell
  | overCeiling : Cell
  | unreachable : String → Cell
  deriving Repr, Inhabited

def Cell.word : Cell → String
  | .proved            => "proved"
  | .soundRefusal      => "sound refusal"
  | .falseRefusal c    => "FALSE REFUSAL (" ++ c.word ++ ")"
  | .falseAcceptance   => "FALSE ACCEPTANCE"
  | .inconclusive n    => "inconclusive (" ++ toString n ++ " heaps probed)"
  | .overCeiling       => "over the ceiling"
  | .unreachable s     => "unreachable: " ++ s

/-- **The gate.** A non-zero false-acceptance count means the hypothesis check accepted a program
labelled racy, so the build stops rather than printing a table. -/
def soundnessHolds (cells : List Cell) : Bool :=
  cells.all (fun c => match c with | .falseAcceptance => false | _ => true)

end Paralever.Bench
