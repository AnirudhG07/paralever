import Bench.Report
import Bench.Scale

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
