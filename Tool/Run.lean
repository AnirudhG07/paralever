import Tool.Proof

/-! # The `paralever` command line

One program per file, four things to do with it: check it, run it, parallelize it, prove it. The
two front ends are interchangeable here — a `.prl` file and a `.mlir` module both compile to a
`Layout` and a `ParProg`, and every command below takes whichever it is given.

Nothing in this module decides anything about a program. Every verdict is `Prl.Report`'s, every
proof is the generated file's, and the conversions are `Prl.Compile.Print` and `MLIR.Emit`.
-- ref: `docs/cli.md` -/

namespace Paralever.Tool
open Paralever Paralever.Prl

/-- What the command line asked for. -/
structure Opts where
  cmd     : String := ""
  file    : String := ""
  out     : Option String := none
  /-- `run`: one `Task` per thread of every fork, rather than the canonical order. -/
  threads : Bool := false
  /-- `to-prl`: ANSI colour, in the editor grammar's token classes. -/
  colour  : Bool := false
  /-- `prove`, `to-mlir`: the subject is the autoparallelized program. -/
  autopar : Bool := false
  /-- `prove`: typecheck the generated file with `lake env lean`. -/
  check   : Bool := false

def usage : String :=
  "paralever — parallel programs that agree with their sequential reading, and the proof of it

usage: paralever <command> FILE [options]

FILE is a `.prl` file or a `.mlir` module in generic form; both compile to the same program.

commands
  check     FILE               memory, footprint, thread count, rounds, and the verdict
  run       FILE               run it and print the heap it leaves, buffer by buffer
  race      FILE               the interleaving that reaches `wrong`, replayed step by step
  autopar   FILE               parallelize it, and print the result as `.prl`
  prove     FILE               write the Lean file that proves parallel = sequential
  to-prl    FILE               print it as `.prl`
  to-mlir   FILE               print it as MLIR generic form (memref globals, async.execute forks)
  to-lean   FILE               print it as Lean: a `Layout` and a `paralever { … }` block

options
  -o PATH                      write there instead of to standard output
  --threads                    `run`: one Task per thread, on real cores
  --autopar                    `prove`, `to-mlir`, `to-lean`: take the parallelized program
  --check                      `prove`: typecheck the generated file with `lake env lean`
  --colour                     `to-prl`: ANSI colour
  --help, --version

`check` exits 1 when the program has a race, so a build can gate on it.
"

/-- The command line, as options. Flags may come in any order; the first two bare words are the
command and the file. -/
def parseArgs (args : List String) : Except String Opts :=
  go args {}
where
  go : List String → Opts → Except String Opts
    | [],             o => .ok o
    | "-o" :: p :: as, o => go as { o with out := some p }
    | "-o" :: [],      _ => .error "-o needs a path"
    | "--threads" :: as, o => go as { o with threads := true }
    | "--autopar" :: as, o => go as { o with autopar := true }
    | "--check" :: as,   o => go as { o with check := true }
    | "--colour" :: as,  o => go as { o with colour := true }
    | "--color" :: as,   o => go as { o with colour := true }
    | a :: as,           o =>
        if a.startsWith "-" then .error s!"unknown option '{a}'"
        else if o.cmd.isEmpty then go as { o with cmd := a }
        else if o.file.isEmpty then go as { o with file := a }
        else .error s!"'{a}': one file at a time"

/-! ## Reading a program

Both front ends end in the same pair, so the commands are written once. What differs is what the
reader gave up on the way, which is printed as comments rather than dropped. -/

/-- A compiled program, the front end it came through, and the approximations the reader made. -/
def loadAny (path : String) : IO (Compiled × Kind × List String) := do
  if path.endsWith ".prl" then
    pure (← Paralever.Prl.load path, .prl, [])
  else if path.endsWith ".mlir" then
    match MLIR.lowerText (← IO.FS.readFile path) with
    | .error e => throw (IO.userError s!"{path}: {e}")
    | .ok r    =>
        let notes := r.notes ++
          (if r.exactValues then []
           else ["values are approximated in Int; MLIR/Eval.lean is the ℚ reference"])
        pure (⟨r.layout, r.prog, [], []⟩, .mlir, notes)
  else
    throw (IO.userError s!"{path}: not a .prl file or a .mlir module")

/-- `src` as a path from the directory the generated file goes in, since `prl_file` and `mlir_prog`
read relative to the file that names them. An absolute path when there is no shorter answer. -/
def pathFrom (out : Option String) (src : String) : IO String := do
  let srcAbs ← IO.FS.realPath src
  match out with
  | none   => pure srcAbs.toString
  | some o => do
      let dir := ((System.FilePath.mk o).parent).getD "."
      try
        let dirAbs ← IO.FS.realPath dir
        let ds := dirAbs.components
        let ss := srcAbs.components
        let common := ((ds.zip ss).takeWhile (fun p => p.1 == p.2)).length
        -- nothing but the root in common: `../../..` to the top and down again is no clearer
        -- than the absolute path, and more fragile.
        if common ≤ 1 then pure srcAbs.toString
        else pure ("/".intercalate (List.replicate (ds.length - common) ".." ++ ss.drop common))
      catch _ => pure srcAbs.toString

/-- Standard output, or the file `-o` named. -/
def put (o : Option String) (s : String) : IO Unit := do
  match o with
  | none   => IO.print s
  | some p => do
      IO.FS.writeFile p s
      IO.eprintln s!"written to {p}"

/-- The reader's approximations, as `.prl` comments. -/
def noteLines (notes : List String) : String :=
  if notes.isEmpty then "" else "\n".intercalate (notes.map (fun n => "-- " ++ n)) ++ "\n\n"

/-! ## The commands -/

/-- `prove`: the generated module, and optionally Lean's verdict on it. -/
def prove (o : Opts) (c : Compiled) (k : Kind) : IO UInt32 := do
  let name := (System.FilePath.mk o.file).fileName.getD o.file
  let s : Subject :=
    { kind := k, path := ← pathFrom o.out o.file, name := name, stem := identOf name, prog := c
    , autopar := o.autopar }
  put o.out (proofFile s)
  if o.check then
    match o.out with
    | none   => do
        IO.eprintln "--check needs -o: Lean typechecks a file, not standard output"
        pure 1
    | some p => do
        IO.eprintln s!"lake env lean {p}"
        let r ← IO.Process.output { cmd := "lake", args := #["env", "lean", p] }
        if !r.stdout.isEmpty then IO.eprint r.stdout
        if !r.stderr.isEmpty then IO.eprint r.stderr
        if r.exitCode == 0 then IO.eprintln s!"{p}: Lean accepts it"
        pure r.exitCode
  else pure 0

/-- `to-mlir`: generic form out, with the source it came from in the header. -/
def toMlir (o : Opts) (c : Compiled) : IO UInt32 := do
  let p := if o.autopar then AutoPar.rewrite c.prog else c.prog
  match MLIR.emitText c.layout p o.file with
  | .error e => do IO.eprintln s!"{o.file}: {e}"; pure 1
  | .ok src  => do put o.out src; pure 0

/-- Run one command on one file. -/
def run (o : Opts) : IO UInt32 := do
  let (c, k, notes) ← loadAny o.file
  match o.cmd with
  | "check"   => do
      IO.print (noteLines notes ++ checkReport o.file c)
      pure (if ParProg.wfB c.prog
              || (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty
            then 0 else 1)
  | "run"     => do
      -- a racy program has no single heap to print: what a run leaves is one schedule's answer
      let sites := raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state
      let warn :=
        if sites.isEmpty then ""
        else "-- this program has a race, so what follows is what one schedule left, not what\n"
               ++ "-- it computes: `paralever race` prints an interleaving that disagrees\n"
      put o.out (warn ++ runReport c o.threads)
      pure 0
  | "race"    => do IO.print (raceReport c); pure 0
  | "autopar" => do put o.out (noteLines notes ++ parReport c); pure 0
  | "prove"   => prove o c k
  | "to-prl"  => do
      let text := noteLines notes ++ print c
      put o.out (if o.colour then highlight text else text)
      pure 0
  | "to-mlir" => toMlir o c
  | "to-lean" => do
      let c' := if o.autopar then { c with prog := AutoPar.rewrite c.prog } else c
      put o.out (toLean c')
      pure 0
  | cmd       => do IO.eprintln s!"unknown command '{cmd}'\n\n{usage}"; pure 2

/-- **The entry point.** -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "--help" || args.contains "-h" || args.contains "help" then
    IO.println usage
    return 0
  if args.contains "--version" then
    IO.println "paralever 0.1.0"
    return 0
  match parseArgs args with
  | .error e => do IO.eprintln s!"{e}\n\n{usage}"; pure 2
  | .ok o    =>
      if o.file.isEmpty then do
        IO.eprintln s!"{o.cmd}: no file given\n\n{usage}"
        pure 2
      else
        try run o
        catch e => do IO.eprintln (toString e); pure 1

end Paralever.Tool
