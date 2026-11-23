import Bench.Report
import Bench.Scale
import Bench.Threads
import Bench.Chaos

/-! # `paralever-bench` — the harness as a binary

An executable rather than an elaboration, for the reason `docs/bench.md` gives: a wall clock inside
`lake build` is not reproducible and a slow machine must not fail CI. So `lake build` never times
anything, and this is what produces a number.

```
paralever-bench                      the built-in .prl corpus, one job per core
paralever-bench --jobs 1             serial — the mode to quote a timing from
paralever-bench --csv out.csv        also write a row per kernel
paralever-bench --markdown           the table docs/bench.md quotes
paralever-bench FILE...              those files instead, labelled race-free
```

Exit code 1 when a row is a false acceptance, so the harness can gate a build. A false *refusal* is
imprecision and exits 0 with the number reported.
-/

namespace Paralever.Bench.Main
open Paralever.Bench

structure Opts where
  jobs     : Nat := 0
  csv      : Option String := none
  markdown : Bool := false
  /-- narrow the built-in corpus to one front end -/
  only     : Option String := none
  /-- also run the rolled-against-unrolled cost curve, which is minutes rather than milliseconds -/
  scale    : Bool := false
  /-- with `--scale`, also write and elaborate each `par_seq_eq` — the kernel's `decide`, which is
  the cost the compiled checks do not show -/
  prove    : Bool := false
  /-- where the cost curve stops; both are printed with the table -/
  limits   : Scale.Limits := {}
  /-- run the `runTask`-against-`runTaskSeq` curve instead of the corpus -/
  exec     : Bool := false
  /-- threads for `--exec`; the fork is one band of rows per thread -/
  execThreads : Nat := 16
  /-- sizes `--exec` walks, as matrix dimensions -/
  execSizes : List Nat := [4, 8, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128]
  /-- `--exec` stops once a row costs more than this -/
  execCeiling : Nat := 60000
  /-- runs per point; the median is kept -/
  reps     : Nat := 3
  /-- with `--exec`, also plan the program with `autoPar` and time what it proposes -/
  execPlan : Bool := true
  files    : List String := []
  deriving Repr, Inhabited

def usage : String :=
  "paralever-bench — the evaluation harness\n\n"
    ++ "  --jobs N        run N kernels at once (0 = one per core; 1 = serial, for timings)\n"
    ++ "  --csv PATH      write a row per kernel\n"
    ++ "  --markdown      print the table docs/bench.md quotes\n"
    ++ "  --prl           only the .prl entries of the built-in corpus\n"
    ++ "  --mlir          only the .mlir pilots\n"
    ++ "  --scale         also the rolled-against-unrolled cost curve (minutes, not ms)\n"
    ++ "  --prove         with --scale, also elaborate each proof (the kernel's decide)\n"
    ++ "  --ceiling-ms N  stop a curve after a row taking N ms (default 8000)\n"
    ++ "  --max-unrolled N  never start an unrolled program over N points (default 65536)\n"
    ++ "  FILE...         measure these files instead of the built-in corpus\n"
    ++ "\n  --exec          time execTask with its forks against the same run flattened\n"
    ++ "  --exec-threads N  threads for --exec (default 16)\n"
    ++ "  --exec-sizes a,b,c  matrix sizes to walk\n"
    ++ "  --exec-ceiling-ms N  stop the curve after a row this slow (default 60000)\n"
    ++ "  --reps N        runs per point, median kept (default 3)\n"
    ++ "  --exec-no-plan  skip the autoPar column, which is cubic in the atom count\n"

partial def parse (args : List String) (o : Opts) : Except String Opts :=
  match args with
  | []                  => .ok o
  | "--jobs" :: n :: rest =>
      match n.toNat? with
      | some k => parse rest { o with jobs := k }
      | none   => .error s!"--jobs wants a number, got '{n}'"
  | "--csv" :: p :: rest  => parse rest { o with csv := some p }
  | "--markdown" :: rest  => parse rest { o with markdown := true }
  | "--prl" :: rest       => parse rest { o with only := some "prl" }
  | "--mlir" :: rest      => parse rest { o with only := some "mlir" }
  | "--scale" :: rest     => parse rest { o with scale := true }
  | "--ceiling-ms" :: n :: rest =>
      match n.toNat? with
      | some k => parse rest { o with limits := { o.limits with ms := k } }
      | none   => .error s!"--ceiling-ms wants a number, got '{n}'"
  | "--max-unrolled" :: n :: rest =>
      match n.toNat? with
      | some k => parse rest { o with limits := { o.limits with points := k } }
      | none   => .error s!"--max-unrolled wants a number, got '{n}'"
  | "--prove" :: rest     => parse rest { o with scale := true, prove := true }
  | "--exec" :: rest      => parse rest { o with exec := true }
  | "--exec-no-plan" :: rest => parse rest { o with exec := true, execPlan := false }
  | "--exec-threads" :: n :: rest =>
      match n.toNat? with
      | some k => parse rest { o with exec := true, execThreads := max 1 k }
      | none   => .error s!"--exec-threads wants a number, got '{n}'"
  | "--exec-ceiling-ms" :: n :: rest =>
      match n.toNat? with
      | some k => parse rest { o with exec := true, execCeiling := k }
      | none   => .error s!"--exec-ceiling-ms wants a number, got '{n}'"
  | "--reps" :: n :: rest =>
      match n.toNat? with
      | some k => parse rest { o with reps := max 1 k }
      | none   => .error s!"--reps wants a number, got '{n}'"
  | "--exec-sizes" :: ns :: rest =>
      let parsed := (ns.splitOn ",").filterMap (fun t => t.trimAscii.toNat?)
      if parsed.isEmpty then .error s!"--exec-sizes wants numbers, got '{ns}'"
      else parse rest { o with exec := true, execSizes := parsed }
  | "--help" :: _         => .error usage
  | a :: rest             =>
      if a.startsWith "--" then .error s!"unknown option '{a}'\n\n{usage}"
      else parse rest { o with files := o.files ++ [a] }

/-- A file named on the command line carries no label, so it is taken as race-free and whatever the
checks say about it is reported rather than scored. -/
def adHoc (path : String) : Entry String :=
  let base := (path.splitOn "/").getLast!
  let stem := (base.splitOn ".").head!
  -- DataRaceBench's convention, which `Manifest.mlirCorpus` and `MLIR/Corpus.lean` both read: a
  -- filename is a label when it carries one, and only an unmarked name is taken as race-free
  { name := stem, item := path, racy := stem.endsWith "-yes"
  , why := if stem.endsWith "-yes" || stem.endsWith "-no"
           then "named on the command line; the label is the one the filename carries"
           else "named on the command line; no declared label, so taken as race-free" }

def main (args : List String) : IO UInt32 := do
  match parse args {} with
  | .error e => do IO.eprintln e; pure 2
  | .ok o    => do
      if o.files == ["spawn-probe"] then
        Threads.spawnProbe 16 20000000
        return 0
      if o.files == ["reg-vs-mem"] then
        Threads.regVsMem (if o.execSizes == [4, 8, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128] then [20000, 40000, 80000, 160000] else o.execSizes) o.reps
        return 0
      if o.files == ["chaos"] then
        Chaos.sweep (if o.execSizes == [4, 8, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128]
                     then [4, 6, 8, 12, 16, 24, 32, 48] else o.execSizes) o.reps o.execCeiling 8
        return 0
      if o.files == ["chaos-regions"] then do
        let n := o.execThreads
        Chaos.byRegion n (4 * n) (o.execSizes.headD 64) o.reps o.execCeiling
        return 0
      if o.files == ["chaos-depth"] then
        Chaos.sweepDepth o.execThreads
          (if o.execSizes == [4, 8, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128]
           then [8, 16, 32, 64, 128, 256, 512] else o.execSizes) o.reps o.execCeiling
        return 0
      if o.files == ["disjoint-probe"] then
        Threads.disjointProbe o.execThreads (o.execCeiling)
        return 0
      if o.files == ["fork-probe"] then
        Threads.forkProbe o.execSizes o.execThreads o.reps
        return 0
      if o.files == ["array-only"] then
        Threads.arrayOnly o.execSizes o.execThreads o.reps
        return 0
      if o.exec then
        IO.println s!"execTask on C := A x B. band = {o.execThreads} threads, one band of rows each."
        IO.println s!"auto = whatever autoPar proposes for the sequential program. median of {o.reps} runs."
        IO.println ("\n" ++ Threads.header)
        let rows ← Threads.curve o.execSizes o.execThreads o.reps o.execCeiling o.execPlan
        if rows.any (fun r => !r.agree) then
          IO.eprintln "a forked run disagreed with the flattened one: that contradicts runTask_eq_runTaskSeq"
          return 1
        return 0
      let builtIn := match o.only with
        | some "prl"  => Manifest.prlCorpus
        | some "mlir" => Manifest.mlirCorpus
        | _           => Manifest.corpus
      let corpus := if o.files.isEmpty then builtIn else o.files.map adHoc
      let jobs ← resolveJobs o.jobs
      let rows ← runCorpus jobs corpus
      IO.println (if o.markdown then markdown rows else report rows)
      match o.csv with
      | some p => do IO.FS.writeFile p (csv rows); IO.println s!"\nwrote {p}"
      | none   => pure ()
      if o.scale then do
        -- serial by construction: the two representations of one program are being compared, so a
        -- contended timing would compare the scheduler instead
        -- the generated modules and the `.prl` beside them go in one directory, which is left in
        -- place: a module that `lean` rejected is the thing a reader wants to open
        let proveIn ← if !o.prove then pure none else do
          let d : System.FilePath := "bench-proofs"
          IO.FS.createDirAll d
          IO.println s!"proof modules written to {d}/"
          pure (some d)
        IO.println ("\n" ++ Scale.preamble o.limits ++ "\n" ++ Scale.header)
        let srows ← Scale.run o.limits Scale.stream proveIn
        IO.println ("\n" ++ Scale.report o.limits srows)
        match o.csv with
        | some p => do
            IO.FS.writeFile (p ++ ".scale.csv") (Scale.csv srows)
            IO.println s!"\nwrote {p}.scale.csv"
        | none   => pure ()
      if runIsSound rows then pure 0
      else do
        IO.eprintln "a program labelled racy was accepted: this is a soundness bug, not a tuning matter"
        pure 1

end Paralever.Bench.Main

def main (args : List String) : IO UInt32 := Paralever.Bench.Main.main args
