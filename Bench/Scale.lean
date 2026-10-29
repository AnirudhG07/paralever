import Bench.Run
import Tool.Proof

/-! # The cost curve: the same program rolled and unrolled

The one measurement the corpus cannot make. Every `.prl` and `.mlir` entry is small, so each row
reports 0 ms and the matrices say nothing about *cost* — but the claim rolling makes is entirely
about cost, and a claim about cost needs a curve rather than one point.

So this module generates one program per size, compiles it **twice** — once with `rollLimit := 0`
so every nest is carried rolled, once with `rollLimit := neverRoll` so every nest is written out —
and times the same two stages on each: reading plus lowering, then the two-part verdict. The two
compilations differ in representation only; `Test/Roll.lean` gates that they decide the same thing.

Two honesty conditions, the same two `Bench/Time.lean` states, plus one more:

* **the unrolled side has a ceiling.** Past `ceilingMs` it is not measured, and the row says
  `over the ceiling` rather than carrying a number from a run that was abandoned. This is the
  `Reach.overCeiling` cell of the taxonomy, measured rather than asserted.
* **the two sides are the same program.** The generator produces one text; `rollLimit` is the only
  difference between the two compilations of it.

Rationale: `docs/bench.md` § Verification cost. -/

namespace Paralever.Bench.Scale
open Paralever Paralever.Lang Paralever.Bench

/-- **Where a curve stops.** Both ceilings are needed and neither replaces the other: `ms` can only
be tested once a row has returned, so it bounds how many rows are attempted rather than how long one
takes, and an unrolled 10⁹-point program does not return at all. `points` is therefore a ceiling on
what the unrolled side is allowed to *start*.

Both are reported with the table and both are settable, because a ceiling is a property of the
machine the run happened on and not of the method. -/
structure Limits where
  ms     : Ms  := 8000
  /-- the unrolled side is not started above this many points -/
  points : Nat := 65536
  deriving Repr, Inhabited

/-! ## The shapes

**Each shape is written two ways, as source.** The rolled text is a `for`/`parfor` nest; the
unrolled text is the same iteration space written out, one `parallel` arm per thread and one
statement per point, which is what a user without rolling would have had to write and what
`Examples/Scale/matmul12.prl` is. Two texts rather than one compiled twice, because the generated
proof module re-reads the *file* while it elaborates — a knob inside the compiler would be invisible
to `prl_file`, and the two rows would then both measure the rolled route.
-- ref: `docs/cli.md`, `docs/scale.md`

Two, both perfectly nested, because a perfect nest is what `affine.for` produces and what the
certificate reads. The second is gemm's forked level: the write mentions a *sequential* level, which
is the shape the scaled `innerSpan` clause exists for. -- ref: `docs/loops.md` § d -/

inductive Shape where
  /-- `C[i,j] := A[i,j] + B[i,j]` — two levels, `n²` points, `n` threads. -/
  | elemwise : Shape
  /-- gemm's index space — three levels, `n³` points, `n` threads, forked at `d = 1`. -/
  | gemm     : Shape
  deriving Repr, DecidableEq, Inhabited

def Shape.name : Shape → String
  | .elemwise => "elemwise"
  | .gemm     => "gemm"

/-- The points the nest covers: what the unrolled route pays per level of the tree. -/
def Shape.points (s : Shape) (n : Nat) : Nat :=
  match s with
  | .elemwise => n * n
  | .gemm     => n * n * n

private def lines (ls : List String) : String := "\n".intercalate ls

private def decls (n : Nat) : List String :=
  let N := toString n
  [ "buf A[" ++ N ++ ", " ++ N ++ "] = 3"
  , "buf B[" ++ N ++ ", " ++ N ++ "] = 4"
  , "buf C[" ++ N ++ ", " ++ N ++ "]" ]

/-- The nest, rolled: the shape as four or six lines whatever `n` is. -/
def Shape.rolledSrc (s : Shape) (n : Nat) : String :=
  let N := toString n
  lines (decls n ++
    match s with
    | .elemwise =>
        [ "parfor i in " ++ N ++ " {"
        , "  for j in " ++ N ++ " {"
        , "    %a := A[i, j]"
        , "    %b := B[i, j]"
        , "    C[i, j] := %a + %b"
        , "  }"
        , "}" ]
    | .gemm =>
        [ "parfor i in " ++ N ++ " {"
        , "  for j in " ++ N ++ " {"
        , "    for k in " ++ N ++ " {"
        , "      %a := A[i, k]"
        , "      %b := B[k, j]"
        , "      C[i, j] := %a"
        , "    }"
        , "  }"
        , "}" ])

/-- One thread of the unrolled form: its own two registers, reused down the sequential levels, so
the register table stays `2n` entries rather than one per point. -/
private def threadBody (s : Shape) (n i : Nat) : List String :=
  let a := "%a" ++ toString i
  let b := "%b" ++ toString i
  let c (x y : Nat) : String := "[" ++ toString x ++ ", " ++ toString y ++ "]"
  match s with
  | .elemwise =>
      (List.range n).flatMap (fun j =>
        [ "  " ++ a ++ " := A" ++ c i j
        , "  " ++ b ++ " := B" ++ c i j
        , "  C" ++ c i j ++ " := " ++ a ++ " + " ++ b ])
  | .gemm =>
      (List.range n).flatMap (fun j =>
        (List.range n).flatMap (fun k =>
          [ "  " ++ a ++ " := A" ++ c i k
          , "  " ++ b ++ " := B" ++ c k j
          , "  C" ++ c i j ++ " := " ++ a ]))

/-- **The same iteration space written out**: one `parallel` arm per thread, one statement per
point. This is the text, and the cost, that rolling removes. -/
def Shape.unrolledSrc (s : Shape) (n : Nat) : String :=
  let arms := (List.range n).map (fun i => lines (threadBody s n i))
  lines (decls n ++ ["parallel {"] )
    ++ "\n" ++ String.intercalate "\n} | {\n" arms ++ "\n}"

def Shape.src (s : Shape) (n : Nat) (rolled : Bool) : String :=
  if rolled then s.rolledSrc n else s.unrolledSrc n

/-! ## One point on the curve -/

structure ScaleRow where
  shape   : String
  n       : Nat
  points  : Nat
  /-- which form the source was written in -/
  asked   : Bool
  /-- which form the program is actually in, read off the compiled tree. Below `Roll.maxUnroll` a
  rolled *source* still lowers unrolled, which is the threshold doing its job and not an anomaly. -/
  carried : Bool := asked
  /-- `false` when the row was not measured because the previous size passed `ceilingMs` -/
  taken   : Bool
  threads : Nat
  /-- `true` when the nest really is one `ParProg.loop` (rolled) or really is a `.par` list
  (unrolled). Measured, not assumed, so a silent fallback cannot be reported as a rolled run. -/
  asAsked : Bool
  /-- `wfB` accepted: the general verdict, which is what `par_seq_eq` needs -/
  proved  : Bool
  readMs  : Ms
  checkMs : Ms
  /-- writing the Lean module `paralever prove` writes. `none` when the stage was not asked for. -/
  proveMs : Option Ms := none
  /-- **elaborating that module** — `wfB` decided by the kernel rather than by compiled code, which
  is the cost a `par_seq_eq` actually has and the one `docs/mlir.md` measured at 19 s for a hundred
  unrolled threads. `none` when not asked for, `some 0` is a real 0. -/
  elabMs  : Option Ms := none
  /-- whether that module typechecked -/
  elabOK  : Bool := true
  deriving Repr, Inhabited

/-- Whether the top-level program carries a rolled nest. `ParProg.block [s] = s`, so a file holding
one nest *is* the nest. -/
partial def isRolled : ParProg → Bool
  | .loop _    => true
  | .label _ s => isRolled s
  | .seq a b   => isRolled a || isRolled b
  | _          => false

/-! ## The proof stage

The three stages above run as compiled code, where `wfB` is a machine-word loop. A `par_seq_eq`
does not: `by decide` is evaluated by the *kernel*, and `Examples/Programs/MatMul.lean` measured
that at 19 s for a hundred unrolled threads. So a cost curve that stopped at the verdict would
measure the cheap half. This stage writes the module `paralever prove` writes — through
`Tool.proofFile`, the same function the command uses, not a copy of it — and then elaborates it
with `lake env lean`, which is the only external process the harness starts and is the toolchain
the repository already requires.

`docs/bench.md` § Verification cost. -/

/-- Write and elaborate the module for one compiled program. The returned pair is
`(writing it, elaborating it)`; `elabOK` false means `lean` rejected it, which is a finding and not
a measurement error. -/
def proveStage (dir : System.FilePath) (stem : String) (srcPath : System.FilePath)
    (c : Compiled) : IO (Ms × Ms × Bool) := do
  let subj : Tool.Subject :=
    { kind := .prl, path := srcPath.toString, name := stem ++ ".prl"
    , stem := Tool.identOf (stem ++ ".prl"), prog := c }
  let out := dir / (Tool.upperOf (Tool.identOf (stem ++ ".prl")) ++ ".lean")
  let (txt, writeMs) ← timed (do
    let t := Tool.proofFile subj
    IO.FS.writeFile out t
    pure t)
  let _ := txt.length
  let (res, elabMs) ← timed (IO.Process.output
    { cmd := "lake", args := #["env", "lean", out.toString] })
  pure (writeMs, elabMs, res.exitCode == 0)

/-- One compilation, timed. `roll` picks which of the two representations is built, and `proveIn`
asks for the proof stage as well — in that directory, because it writes two files per row. -/
def measure (s : Shape) (n : Nat) (roll : Bool) (proveIn : Option System.FilePath := none) :
    IO ScaleRow := do
  let src := s.src n roll
  let (c?, readMs) ← timed (pure (Lang.ofString src))
  match c? with
  | .error d =>
      -- a shape that does not compile is a bug in the generator, so it is reported in the row
      -- rather than thrown away
      pure { shape := s.name ++ "!" ++ d.msg, n := n, points := s.points n
           , asked := roll, taken := true, threads := 0, asAsked := false, proved := false
           , readMs := readMs, checkMs := 0 }
  | .ok c => do
      let (_, _, checkMs) ← timedForced (fun _ => reprStr (Lang.verdictParts c))
      let stem := s.name ++ toString n ++ (if roll then "r" else "u")
      let proof ← match proveIn with
        | none     => pure none
        | some dir => do
            -- the generated module re-reads the source while it elaborates, so the `.prl` has to
            -- exist beside it -- ref: `docs/cli.md`
            let srcPath := dir / (stem ++ ".prl")
            IO.FS.writeFile srcPath src
            let (w, e, ok) ← proveStage dir stem (System.mkFilePath [".", stem ++ ".prl"]) c
            pure (some (w, e, ok))
      let carried := isRolled c.prog
      pure { shape := s.name, n := n, points := s.points n, asked := roll, carried := carried
           , taken := true
           , threads := ParProg.threadCount c.prog
             -- a rolled source under the threshold lowers unrolled, which is the threshold working
           , asAsked := carried == roll || (roll && s.points n ≤ Roll.maxUnroll)
           , proved := ParProg.wfB c.prog
           , readMs := readMs, checkMs := checkMs
           , proveMs := proof.map (fun p => p.1)
           , elabMs  := proof.map (fun p => p.2.1)
           , elabOK  := (proof.map (fun p => p.2.2)).getD true }

/-- A row that was not measured, because the size below it already passed the ceiling. -/
def skipped (s : Shape) (n : Nat) (roll : Bool) : ScaleRow :=
  { shape := s.name, n := n, points := s.points n, asked := roll, taken := false
  , threads := 0, asAsked := false, proved := false, readMs := 0, checkMs := 0 }

/-- **One curve: one shape, one representation, increasing size.** A size is attempted only while
two ceilings hold: the unrolled side never *starts* a program over `maxUnrolledPoints`, and neither
side starts a size after one whose total passed `ceilingMs`. Both are needed, because a time ceiling
can only be tested once a row has finished — it bounds how many rows are attempted, not how long one
takes, and an unrolled 10⁹-point program does not return. Every size above a ceiling is reported as
skipped rather than left out.

Each row is emitted as it lands, so a run still going is still readable. -/
def curve (lim : Limits) (s : Shape) (roll : Bool) (sizes : List Nat)
    (emit : ScaleRow → IO Unit) (proveIn : Option System.FilePath := none) :
    IO (List ScaleRow) := do
  let mut out : List ScaleRow := []
  let mut stop := false
  for n in sizes do
    if stop || (!roll && lim.points < s.points n) then do
      let r := skipped s n roll
      out := out ++ [r]
      emit r
    else do
      let r ← measure s n roll proveIn
      out := out ++ [r]
      emit r
      if lim.ms ≤ r.readMs + r.checkMs + (r.elabMs.getD 0) then stop := true
  pure out

/-! ## The sizes

Chosen so the unrolled side crosses its ceiling inside the table rather than outside it: `elemwise`
at `n = 40` is 1600 points and `gemm` at `n = 12` is 1728, and both are tractable; the sizes above
them are where the two routes separate. The rolled side runs every size, including `n = 1000`,
whose `10⁹` points no unrolled representation can hold. -/

def elemSizes : List Nat := [8, 12, 20, 32, 40, 64, 100, 200, 1000]
def gemmSizes : List Nat := [4, 8, 10, 12, 16, 24, 50, 100, 1000]

/-- Every curve, each row handed to `emit` as it is measured. -/
def run (lim : Limits) (emit : ScaleRow → IO Unit) (proveIn : Option System.FilePath := none) :
    IO (List ScaleRow) := do
  let a ← curve lim .elemwise true  elemSizes emit proveIn
  let b ← curve lim .elemwise false elemSizes emit proveIn
  let c ← curve lim .gemm     true  gemmSizes emit proveIn
  let d ← curve lim .gemm     false gemmSizes emit proveIn
  pure (a ++ b ++ c ++ d)

/-! ## The table -/

private def pad (w : Nat) (s : String) : String := s ++ "".pushn ' ' (w - min w s.length)
private def rpad (w : Nat) (s : String) : String := "".pushn ' ' (w - min w s.length) ++ s

private def msOpt : Option Ms → String
  | none   => "—"
  | some m => toString m ++ "ms"

def ScaleRow.line (r : ScaleRow) : String :=
  pad 10 r.shape ++ rpad 6 (toString r.n) ++ rpad 12 (toString r.points)
    ++ pad 3 "" ++ pad 10 (if r.carried then "rolled"
                           else if r.asked then "unrolled*" else "unrolled")
    ++ (if !r.taken then rpad 8 "—" ++ rpad 8 "—" ++ rpad 9 "—" ++ rpad 8 "—" ++ rpad 10 "—"
                         ++ "   over the ceiling"
        else rpad 8 (toString r.threads)
          ++ rpad 8 (toString r.readMs ++ "ms") ++ rpad 9 (toString r.checkMs ++ "ms")
          ++ rpad 8 (msOpt r.proveMs) ++ rpad 10 (msOpt r.elabMs)
          ++ "   " ++ (if !r.asAsked then "NOT THE ASKED REPRESENTATION"
                       else if !r.elabOK then "LEAN REJECTED THE MODULE"
                       else if r.proved then "proved" else "refused"))

def header : String :=
  pad 10 "shape" ++ rpad 6 "n" ++ rpad 12 "points" ++ pad 3 "" ++ pad 10 "carried"
    ++ rpad 8 "thr" ++ rpad 8 "read" ++ rpad 9 "verdict" ++ rpad 8 "write"
    ++ rpad 10 "elaborate" ++ "   result"

/-- Print a row the moment it lands, flushed, so a run in progress can be read. -/
def stream (r : ScaleRow) : IO Unit := do
  IO.println r.line
  (← IO.getStdout).flush

def preamble (lim : Limits) : String :=
  "ceilings       " ++ toString lim.ms ++ " ms per row, and "
    ++ toString lim.points ++ " points for the unrolled side\n"
    ++ "points         the nest's iteration space; the unrolled tree carries a node per point"

def legend : String :=
  "unrolled*      a rolled source under the "
    ++ toString Roll.maxUnroll ++ "-point threshold, so it lowered unrolled"

def report (lim : Limits) (rows : List ScaleRow) : String :=
  preamble lim ++ "\n" ++ legend ++ "\n\n" ++ header ++ "\n" ++ "\n".intercalate (rows.map ScaleRow.line)

def csvHeader : String :=
  "shape,n,points,asked,carried,taken,threads,as_asked,proved,read_ms,check_ms,prove_ms,elab_ms,elab_ok"

def ScaleRow.csv (r : ScaleRow) : String :=
  String.intercalate ","
    [ r.shape, toString r.n, toString r.points
    , if r.asked then "rolled" else "unrolled"
    , if r.carried then "rolled" else "unrolled"
    , if r.taken then "yes" else "over-ceiling"
    , toString r.threads, if r.asAsked then "yes" else "no"
    , if r.proved then "yes" else "no", toString r.readMs, toString r.checkMs
    , (r.proveMs.map toString).getD "", (r.elabMs.map toString).getD ""
    , if r.elabOK then "yes" else "no" ]

def csv (rows : List ScaleRow) : String :=
  csvHeader ++ "\n" ++ "\n".intercalate (rows.map ScaleRow.csv) ++ "\n"

end Paralever.Bench.Scale
