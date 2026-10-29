import Tool.Proof
import Tool.Init
import Paralever.Version
import Lang.Smt.Report

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
  /-- The function to read, for an MLIR module that holds more than one. -/
  func    : Option String := none
  /-- `run`: print only this buffer, or only this cell of it — `C` or `C[1, 2]`. -/
  only    : Option String := none
  /-- `run`, no command: the headings and the heap, not only what `print` wrote. On by default;
  `--quiet` turns it off. -/
  verbose : Bool := true
  /-- `run`: every cell of every buffer, however many there are. -/
  allCells : Bool := false
  /-- `vc`: run a solver on what is left, rather than only printing the obligation. -/
  solve   : Bool := false
  /-- `vc`: hypotheses to assume about the loaded values — today only `nonneg`. -/
  assume  : List String := []
  /-- `vc`: the solver to use — a name or a path — instead of looking for one. -/
  solver  : Option String := none
  /-- `vc`: milliseconds a solver may spend per query; `0` is no limit. -/
  timeout : Nat := 10000

def usage : String :=
  "paralever — parallel programs that agree with their sequential reading, and the proof of it

usage: paralever [command] FILE [options]

FILE is a `.prl` file or a `.mlir` module in generic form; both compile to the same program.
With no command, `paralever FILE` says everything `run` says and adds the verdict: the theorem that
holds, or the interleaving that breaks it.

commands
  init      [DIR]              a Lake project with paralever as its dependency, and a program
  check     FILE               memory, footprint, thread count, rounds, and the verdict
  run       FILE               run it: what `print` wrote, then the heap it leaves, buffer by
                               buffer (`-n` for one)
  race      FILE               the interleaving that reaches `wrong`, replayed step by step
  autopar   FILE               parallelize it, and print the result as `.prl`
  funcs     FILE               what an MLIR module holds, function by function
  prove     FILE               write the Lean file that proves parallel = sequential
  vc        FILE               the independence obligation as SMT-LIB, for a solver to discharge
  to-prl    FILE               print it as `.prl`
  to-mlir   FILE               print it as MLIR generic form (memref globals, async.execute forks)
  to-lean   FILE               print it as Lean: a `Layout` and a `paralever { … }` block
  explain   CODE               what a diagnostic code means, and why the rule exists

options
  -o PATH                      write there instead of to standard output
  --threads                    `run`: one Task per thread, on real cores
  --autopar                    `prove`, `to-mlir`, `to-lean`: take the parallelized program
  --check                      `prove`: typecheck the generated file with `lake env lean`
  --solve                      `vc`: discharge what is left with the first solver found —
                               z3, then cvc5, or whatever PARALEVER_SMT names
  --solver NAME|PATH           `vc`: use that solver instead of looking for one (implies --solve)
  --timeout MS                 `vc`: milliseconds per query, default 10000; 0 for no limit
  --assume nonneg              `vc`: assume every value read from the heap is at or above zero
  --prove PATH                 no command: write the proof module there too, beside the verdict
  --func NAME                  the function to read, for an MLIR module that holds several
  -n NAME                      `run`: print only that buffer, or `-n 'C[1, 2]'` only that cell
  --quiet, -q                  `run`, no command: print only what the program's `print`
                               statements wrote — no headings, no heap
  --verbose, -v                verbosity on, which is the default (undoes an earlier `--quiet`)
  --all-cells                  `run`: every cell of every buffer, not the first 32 of each
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
    | "--solve" :: as,   o => go as { o with solve := true }
    | "--assume" :: a :: as, o =>
        if a == "nonneg" then go as { o with assume := o.assume ++ [a] }
        else .error s!"--assume: '{a}' is not a hypothesis paralever can state; try 'nonneg'"
    | "--assume" :: [],      _ => .error "--assume needs a hypothesis name, as `--assume nonneg`"
    | "--solver" :: v :: as, o => go as { o with solver := some v, solve := true }
    | "--solver" :: [],      _ =>
        .error "--solver needs a name or a path, as `--solver cvc5` or `--solver /opt/z3/bin/z3`"
    | "--timeout" :: v :: as, o =>
        match v.toNat? with
        | some n => go as { o with timeout := n }
        | none   => .error s!"--timeout: '{v}' is not a number of milliseconds"
    | "--timeout" :: [],      _ => .error "--timeout needs milliseconds, as `--timeout 60000`"
    | "--prove" :: p :: as, o => go as { o with proof := some p }
    | "--prove" :: [],      _ => .error "--prove needs a path"
    | "--func" :: f :: as,  o => go as { o with func := some f }
    | "--func" :: [],       _ => .error "--func needs a function name"
    | "-n" :: n :: as,      o => go as { o with only := some n }
    | "-n" :: [],           _ => .error "-n needs a buffer name, as `-n C` or `-n 'C[1, 2]'`"
    | "--verbose" :: as,    o => go as { o with verbose := true }
    | "-v" :: as,           o => go as { o with verbose := true }
    | "--quiet" :: as,      o => go as { o with verbose := false }
    | "-q" :: as,           o => go as { o with verbose := false }
    | "--all-cells" :: as,  o => go as { o with allCells := true }

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
def loadAny (path : String) (func : Option String := none) :
    IO (Compiled × Kind × List String) := do
  if path.endsWith ".prl" then
    pure (← Paralever.Lang.load path, .prl, [])
  else if path.endsWith ".mlir" then
    match MLIR.lowerTextAt func (← IO.FS.readFile path) with
    | .error e => throw (IO.userError s!"{path}: {e}")
    | .ok r    =>
        let notes := r.notes ++
          (if r.exactValues then []
           else ["values are approximated in Int; MLIR/Eval.lean is the ℚ reference"])
        pure (⟨r.layout, r.prog, [], [], none⟩, .mlir, notes)
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
does not (zsh prints a reverse-video `%`), which read as part of the report. Nothing to say stays
nothing — a `--quiet` run of a program with no `print` prints no blank line. -/
def put (o : Option String) (s : String) : IO Unit := do
  let s := if s.isEmpty || s.endsWith "\n" then s else s ++ "\n"
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

/-- A column of the given width, so the names line up. -/
def pad (w : Nat) (s : String) : String := s ++ "".pushn ' ' (w - min w s.length)

/-- `funcs`: the functions an MLIR module holds, and whether the reader takes each one. A real file
holds many, and one it cannot read is a fact about that function, not about the file.
-- ref: `docs/mlir-pretty.md` § One function out of twenty -/
def funcsReport (path src : String) : String :=
  let generic := MLIR.looksGeneric src
  let rows : List (String × Except String Nat) :=
    if generic then
      match MLIR.parse src with
      | .error e => [("<the module>", .error e)]
      | .ok ops  => (MLIR.funcsOf ops).map fun f =>
          ((f.symAttr? "sym_name").getD "?", .ok (MLIR.opCount [f]))
    else
      (MLIR.Pretty.parseFunctions src).map fun (nm, r) =>
        -- the ops of *that* function, since a module-wrapped file hands every row the whole module
        (nm, r.map fun ops =>
          match (MLIR.funcsOf ops).find? (fun f => f.symAttr? "sym_name" == some nm) with
          | some f => MLIR.opCount [f]
          | none   => MLIR.opCount ops)
  let w := rows.foldl (fun acc (nm, _) => max acc nm.length) 4
  let read := (rows.filter (fun r => r.2.toOption.isSome)).length
  let body := rows.map fun (nm, r) =>
    match r with
    | .ok n    => "  read     " ++ pad w nm ++ "  " ++ toString n ++ " ops"
    | .error e => "  refused  " ++ pad w nm ++ "  " ++ e
  path ++ " — " ++ toString rows.length
    ++ (if rows.length == 1 then " function, " else " functions, ")
    ++ (if generic then "generic form" else "custom (pretty) form") ++ "\n\n"
    ++ "\n".intercalate body ++ "\n\n"
    ++ toString read ++ " read, " ++ toString (rows.length - read) ++ " refused"
    ++ (if rows.length ≤ 1 then ".\n"
        else ". Check one of them with: paralever --func NAME " ++ path ++ "\n")

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

/-- **What a run says about the program.** The race caveat, what `print` wrote, and the heap — or,
under `--quiet`, the output alone. `run` and the no-command form print exactly this, so the two
commands say the same things and the bare form's only addition is the verdict.

`raceHint` is the one clause that differs: `run` points at `paralever race` for the interleaving,
and the bare form does not because it prints the interleaving itself.
-- ref: `docs/cli.md` § A file on its own -/
def runBody (o : Opts) (c : Compiled) (raceHint : Bool) : String :=
  if !o.verbose then quietReport c
  else
    -- a racy program has no single heap to print: what a run leaves is one schedule's answer.
    -- `wfB` accepting *is* the absence of a race, by `par_seq_eq`, so the scan — quadratic in the
    -- thread count — is only run when it refuses. -- ref: docs/scale.md § Where the time went
    let sites := if ParProg.wfB c.prog then []
                 else raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state
    let warn :=
      if sites.isEmpty then ""
      else "this program has a race, so what follows is what one schedule left, not what it\n"
             ++ "computes"
             ++ (if raceHint then ": paralever race prints an interleaving that disagrees" else "")
             ++ "\n\n"
    warn ++ runReport c o.threads o.allCells

/-- Run one command on one file. -/
def run (o : Opts) : IO UInt32 := do
  -- `explain` reads no file at all
  if o.cmd == "explain" then
    put o.out (Diag.explain o.file)
    return (if (Diag.find? o.file).isSome then 0 else 2)
  -- `funcs` reads the text and nothing else: a module whose entry will not lower still has
  -- nineteen other functions to report on.
  if o.cmd == "funcs" then
    if !o.file.endsWith ".mlir" then
      IO.eprintln s!"{o.file}: funcs reads an MLIR module; a .prl file is one program"
      return 2
    put o.out (funcsReport o.file (← IO.FS.readFile o.file))
    return 0
  -- `prove` writes a module that re-reads the file while Lean elaborates, and Lean has no pipe to
  -- offer it. Refused here, before the loader would block on a terminal waiting for input.
  if o.cmd == "prove" && o.file.endsWith ".prl" then
    if let .ok f := Paralever.Lang.parse (← IO.FS.readFile o.file) then
      if f.usesInput then
        IO.eprintln s!"{o.file}: {Paralever.Lang.inputRefusal "the Lean module 'prove' writes"}"
        return 1
  let (c, k, notes) ← loadAny o.file o.func
  match o.cmd with
  | "check"   => do
      put o.out (notePlain notes ++ checkReport o.file c)
      -- a claim that does not hold is a failure of the file, not a note on it
      pure (if (ParProg.wfB c.prog
                 || (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty)
               && claimHolds c
            then 0 else 1)
  -- no command: the question a file arrives with. Check it, then show the evidence either way —
  -- the theorem that holds, or the interleaving that breaks it. -- ref: docs/cli.md
  | ""        => do
      let sites := raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state
      -- the verdict is the one thing `run` does not say, so it is the one thing added. What follows
      -- it is `run`'s own body, and then only what neither already holds: where a proof module
      -- went, and the interleaving. -- ref: docs/cli.md § A file on its own
      let wrote := match o.proof with
        | some p => s!"\nLean module written to {p}\n"
        | none   => ""
      let head := if o.verbose then notePlain notes ++ verdictReport o.file c ++ "\n" else ""
      let tail := if o.verbose
                  then wrote ++ (if sites.isEmpty then "" else "\n" ++ raceReport c ++ "\n")
                  else ""
      put o.out (head ++ runBody o c (raceHint := false) ++ tail)
      -- a `--check` that Lean refused is the tool's answer too, so its code is passed on
      let rc ← if o.proof.isSome then prove { o with out := o.proof } c k else pure 0
      pure (if sites.isEmpty && claimHolds c then rc else 1)
  | "run"     => do
      match o.only with
      | none     => do put o.out (runBody o c (raceHint := true)); pure 0
      | some sel =>
          -- `-n` answers with one line, so the caveat goes to standard error rather than into it
          match runCell c o.threads sel with
          | .error e => do IO.eprintln s!"{o.file}: {e}"; pure 2
          | .ok line => do
              if ParProg.wfB c.prog
                 || (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty then
                pure ()
              else IO.eprint ("this program has a race, so what follows is what one schedule left,"
                ++ " not what it\ncomputes: paralever race prints an interleaving that"
                ++ " disagrees\n\n")
              -- what `print` wrote is the program's output, so `-n` keeps it and narrows the heap
              put o.out (if o.verbose then outReport c ++ line else quietReport c)
              pure 0
  | "race"    => do put o.out (raceReport c); pure 0
  | "autopar" => do put o.out (noteLines notes ++ parReport c); pure 0
  -- the obligation `wfB` refuses, handed to a solver instead. `wfB` runs first: what it accepts is
  -- decided by the kernel and needs no external program. -- ref: docs/smt-vc.md
  | "vc"      => do
      let vs0 := Smt.obligations c.prog
      let vs := if o.assume.contains "nonneg" then vs0.map Smt.assumeNonneg else vs0
      if let some path := o.out then
        IO.FS.writeFile path (Smt.smtFile c vs)
        IO.println s!"{vs.length} obligation(s) written to {path}"
        pure 0
      else if o.solve then do
        match ← Smt.choose o.solver with
        | .error e => do IO.eprintln s!"paralever vc: {e}"; pure 2
        | .ok (s, ver) => do
            let (text, ok) ← Smt.solveReport c { s with timeout := o.timeout } ver vs o.assume
            IO.print text
            pure (if ok then 0 else 1)
      else do
        put o.out (Smt.vcReport c vs o.assume)
        pure 0
  | "prove"   => prove o c k
  | "to-prl"  => do
      let text := noteLines notes ++ toPrl c
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
    IO.println Paralever.versionLine
    return 0
  match parseArgs args with
  | .error e => do IO.eprintln s!"{e}\n\n{usage}"; pure 2
  | .ok o    =>
      -- `init` writes files and reads none, so it is answered before the file is demanded
      if o.cmd == "init" then Init.write (if o.file.isEmpty then "." else o.file)
      else if o.file.isEmpty then do
        let who := if o.cmd.isEmpty then "paralever" else o.cmd
        IO.eprintln s!"{who}: no file given\n\n{usage}"
        pure 2
      else
        try run o
        catch e => do IO.eprintln (toString e); pure 1

end Paralever.Tool
