import Tool.Proof

/-! # The `paralever` command line

One program per file, four things to do with it: check it, run it, parallelize it, prove it. The
two front ends are interchangeable here — a `.prl` file and a `.mlir` module both compile to a
`Layout` and a `ParProg`, and every command below takes whichever it is given.

Nothing in this module decides anything about a program. Every verdict is `Lang.Report`'s, every
proof is the generated file's, and the conversions are `Lang.Compile.Print` and `MLIR.Emit`.
-- ref: `docs/cli.md` -/

namespace Paralever.Tool
open Paralever Paralever.Lang

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
  /-- No command: write the proof module there as well as printing the verdict. -/
  proof   : Option String := none

def usage : String :=
  "paralever — parallel programs that agree with their sequential reading, and the proof of it

usage: paralever [command] FILE [options]

FILE is a `.prl` file or a `.mlir` module in generic form; both compile to the same program.
With no command, `paralever FILE` checks it and then shows the evidence: the theorem that holds,
or the interleaving that breaks it.

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
  --prove PATH                 no command: write the proof module there too, beside the verdict
  --colour                     `to-prl`: ANSI colour
  --help, --version

`check` and the no-command form exit 1 when the program has a race, so a build can gate on it.
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
    | "--prove" :: p :: as, o => go as { o with proof := some p }
    | "--prove" :: [],      _ => .error "--prove needs a path"

    | "--colour" :: as,  o => go as { o with colour := true }
    | "--color" :: as,   o => go as { o with colour := true }
    | a :: as,           o =>
        if a.startsWith "-" then .error s!"unknown option '{a}'"
        -- a bare word that names a file is the file, so `paralever FILE` needs no command
        else if o.file.isEmpty && (a.endsWith ".prl" || a.endsWith ".mlir") then
          go as { o with file := a }
        else if o.cmd.isEmpty then go as { o with cmd := a }
        else if o.file.isEmpty then go as { o with file := a }
        else .error s!"'{a}': one file at a time"

/-! ## Reading a program

Both front ends end in the same pair, so the commands are written once. What differs is what the
reader gave up on the way, which is printed as comments rather than dropped. -/

/-- A compiled program, the front end it came through, and the approximations the reader made. -/
def loadAny (path : String) : IO (Compiled × Kind × List String) := do
  if path.endsWith ".prl" then
    pure (← Paralever.Lang.load path, .prl, [])
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

/-- Standard output, or the file `-o` named. Always ends in a newline: a shell marks output that
does not (zsh prints a reverse-video `%`), which read as part of the report. -/
def put (o : Option String) (s : String) : IO Unit := do
  let s := if s.endsWith "\n" then s else s ++ "\n"
  match o with
  | none   => IO.print s
  | some p => do
      IO.FS.writeFile p s
      IO.eprintln s!"written to {p}"

/-- The reader's approximations, as `.prl` comments: for output that is source. -/
def noteLines (notes : List String) : String :=
  if notes.isEmpty then "" else "\n".intercalate (notes.map (fun n => "-- " ++ n)) ++ "\n\n"

/-- The same, for a report: a report is read, not elaborated, so it carries no comment markers. -/
def notePlain (notes : List String) : String :=
  if notes.isEmpty then "" else "\n".intercalate notes ++ "\n\n"

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
      put o.out (notePlain notes ++ checkReport o.file c)
      pure (if ParProg.wfB c.prog
              || (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty
            then 0 else 1)
  -- no command: the question a file arrives with. Check it, then show the evidence either way —
  -- the theorem that holds, or the interleaving that breaks it. -- ref: docs/cli.md
  | ""        => do
      let sites := raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state
      let how := match o.proof with
        | some p => s!"Lean module written to {p}; it re-reads this file as it elaborates.\n"
        | none   => s!"A Lean module stating and proving that: paralever prove {o.file} -o Proof.lean\n"
      let verdict :=
        if ParProg.wfB c.prog then
          "\nPROVED. Bernstein holds at every fork, so par_seq_eq applies: every schedule of this\n"
            ++ "program leaves the heap its sequential reading leaves.\n" ++ how
        else if sites.isEmpty then
          "\nNO RACE FOUND, BUT NOT PROVED. No schedule reaches wrong at the heap this file\n"
            ++ "declares, yet wfB says no: the syntactic footprint over-approximates a computed\n"
            ++ "address (docs/block-ir.md), so what holds is the equivalence at this heap alone.\n"
            ++ how
        else
          "\nRACY. The interleaving below reaches wrong, so no equivalence is available; what is\n"
            ++ "provable is the pair of refusals.\n" ++ how ++ "\n" ++ raceReport c ++ "\n"
      put o.out (notePlain notes ++ checkReport o.file c ++ verdict)
      -- a `--check` that Lean refused is the tool's answer too, so its code is passed on
      let rc ← if o.proof.isSome then prove { o with out := o.proof } c k else pure 0
      pure (if sites.isEmpty then rc else 1)
  | "run"     => do
      -- a racy program has no single heap to print: what a run leaves is one schedule's answer
      let sites := raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state
      let warn :=
        if sites.isEmpty then ""
        else "this program has a race, so what follows is what one schedule left, not what it\n"
               ++ "computes: paralever race prints an interleaving that disagrees\n\n"
      put o.out (warn ++ runReport c o.threads)
      pure 0
  | "race"    => do put o.out (raceReport c); pure 0
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
        let who := if o.cmd.isEmpty then "paralever" else o.cmd
        IO.eprintln s!"{who}: no file given\n\n{usage}"
        pure 2
      else
        try run o
        catch e => do IO.eprintln (toString e); pure 1

end Paralever.Tool
