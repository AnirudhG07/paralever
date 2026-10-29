import Paralever.Version

/-! # `paralever init` — a Lake project with this one as a dependency

Five files and no build system of our own: Lake resolves `paralever`, `paralever` resolves Mathlib,
and `lake build` checks the generated module's theorem with the kernel. Nothing here runs `git` or
`curl` — the files are written and the two commands to run are printed.

What it writes and why: `docs/cli.md` § `init`. -/

namespace Paralever.Tool.Init

/-- A directory name as a Lake package name: lower case, with every run of other characters closed
up to a single `-`. `My Kernel/` ↦ `my-kernel`. -/
def packageOf (dir : String) : String :=
  let cs := (dir.splitOn "/").filter (fun s => !s.isEmpty && s != ".") |>.getLast? |>.getD dir
  let s := String.ofList (go cs.toList false)
  if s.isEmpty then "paralever-project" else s
where
  go : List Char → Bool → List Char
    | [],      _    => []
    | c :: cs, dash =>
        if c.isAlphanum then c.toLower :: go cs false
        else if dash then go cs true
        else '-' :: go cs true

/-- The same name as a Lean module: `my-kernel` ↦ `MyKernel`. -/
def moduleOf (pkg : String) : String :=
  let s := String.ofList (go pkg.toList true)
  if s.isEmpty then "Project" else s
where
  go : List Char → Bool → List Char
    | [],      _  => []
    | c :: cs, up =>
        if c.isAlphanum then (if up then c.toUpper else c) :: go cs false
        else go cs true

/-- The toolchain, from this project's own `lean-toolchain`: a generated project pins what the
dependency was built with, and the string is never written twice. -/
def toolchain : String := include_str "../lean-toolchain"

/-- Where the dependency is fetched from. A branch rather than a tag: there is no release yet, and
a pinned revision that does not exist is worse than one that moves. -/
def repo : String := "https://github.com/AnirudhG07/paralever"

private def lakefile (pkg mod : String) : String :=
  "\n".intercalate
    [ "name = \"" ++ pkg ++ "\""
    , "version = \"0.1.0\""
    , "defaultTargets = [\"" ++ mod ++ "\"]"
    , ""
    , "[[lean_lib]]"
    , "name = \"" ++ mod ++ "\""
    , ""
    , "# paralever carries its own dependency on Mathlib, so nothing here names one. `lake exe"
    , "# cache get` fetches Mathlib's prebuilt .olean files; without it the first build compiles"
    , "# Mathlib from source."
    , "[[require]]"
    , "name = \"paralever\""
    , "git = \"" ++ repo ++ "\""
    , "rev = \"main\""
    , "" ]

private def program : String :=
  "\n".intercalate
    [ "-- Two halves of one buffer, scaled by different factors at the same time."
    , "-- `paralever hello.prl` says whether this is correct under every schedule."
    , ""
    , "def scale(Out, In, k, n) {"
    , "  for i in n {"
    , "    %x := In[i]"
    , "    Out[i] := k * %x"
    , "  }"
    , "}"
    , ""
    , "buf A[8] = arange"
    , "buf B[8] = zeros"
    , "slice alo = A[0..4]"
    , "slice ahi = A[4..8]"
    , "slice blo = B[0..4]"
    , "slice bhi = B[4..8]"
    , ""
    , "parallel { scale(blo, alo, 2, 4) } | { scale(bhi, ahi, 3, 4) } :: \"scale\""
    , "print B"
    , "" ]

private def module (mod : String) : String :=
  "\n".intercalate
    [ "import Lang.Report"
    , ""
    , "/-! # " ++ mod
    , ""
    , "`hello.prl` is read and compiled *while this file elaborates*, so `src` below holds a"
    , "program literal and `by decide` sees the program rather than the reader."
    , ""
    , "`lake build` is the whole check: if the theorem at the bottom did not hold, this file would"
    , "not compile. -/"
    , ""
    , "namespace " ++ mod
    , "open Paralever Paralever.Lang"
    , ""
    , "-- `decide` reduces the program against a heap, which nests deeper than the default bound."
    , "set_option maxRecDepth 100000"
    , ""
    , "/-- The file, compiled: where its buffers are, and what its program is. -/"
    , "def src : Compiled := prl_file \"hello.prl\""
    , ""
    , "-- what `paralever check hello.prl` prints"
    , "#eval IO.println (checkReport \"hello.prl\" src)"
    , ""
    , "-- the heap the program leaves, run in the canonical order"
    , "#eval IO.println (runReport src (threads := false))"
    , ""
    , "/-- Bernstein's condition at every fork, decided on the syntax: no two threads write a"
    , "common cell, and neither reads a cell the other writes. -/"
    , "example : ParProg.wfB src.prog = true := by decide"
    , ""
    , "/-- **Parallel equals sequential.** For every register file, every heap and every schedule:"
    , "the parallel reading reaches an outcome exactly when the sequential one reaches that same"
    , "outcome. -/"
    , "theorem hello_par_seq_eq (ρ : Regs) (σ : State) :"
    , "    ParSeqEq (ParProg.execPar src.prog ρ) (ParProg.execSeq src.prog ρ) σ :="
    , "  ParProg.par_seq_eq (by decide) ρ σ"
    , ""
    , "end " ++ mod
    , "" ]

private def readme (pkg mod : String) : String :=
  "\n".intercalate
    [ "# " ++ pkg
    , ""
    , "A paralever project: a parallel program, and the proof that it agrees with its sequential"
    , "reading under every schedule."
    , ""
    , "```bash"
    , "lake exe cache get      # Mathlib's prebuilt oleans, once"
    , "lake build              # checks hello.prl's theorem with the kernel"
    , "```"
    , ""
    , "The program is `hello.prl` and the theorem about it is in `" ++ mod ++ ".lean`. The command"
    , "line comes with the dependency:"
    , ""
    , "```bash"
    , "lake exe paralever hello.prl            # the verdict, the output and the heap"
    , "lake exe paralever autopar hello.prl    # the same program, parallelized by the pass"
    , "lake exe paralever prove hello.prl -o Proof.lean"
    , "```"
    , ""
    , "Edit `hello.prl` and run `lake build` again. A program with a race fails the `by decide` in"
    , "`" ++ mod ++ ".lean`, and `lake exe paralever race hello.prl` prints the interleaving that"
    , "disagrees."
    , ""
    , "The language: `docs/prl.md` in the dependency. The command line: `docs/cli.md`."
    , "" ]

/-- The files, as paths relative to the project directory. -/
def files (dir : String) : List (String × String) :=
  let pkg := packageOf dir
  let mod := moduleOf pkg
  [ ("lakefile.toml",  lakefile pkg mod)
  , ("lean-toolchain", toolchain)
  , (mod ++ ".lean",   module mod)
  , ("hello.prl",      program)
  , ("README.md",      readme pkg mod)
  , (".gitignore",     "/.lake\n") ]

/-- **Write the project.** An existing file is never overwritten: the ones that are already there
are reported and left alone, so running this in a directory that has a `lakefile.toml` adds the
program and the module and nothing else. -/
def write (dir : String) : IO UInt32 := do
  let root := System.FilePath.mk dir
  IO.FS.createDirAll root
  let mut wrote : List String := []
  let mut kept  : List String := []
  for (name, contents) in files dir do
    let path := root / name
    if ← path.pathExists then kept := kept ++ [name]
    else do
      IO.FS.writeFile path contents
      wrote := wrote ++ [name]
  if wrote.isEmpty then
    IO.eprintln s!"{dir}: every file is already there — nothing written"
    return 1
  IO.println s!"{dir}: {", ".intercalate wrote}"
  if !kept.isEmpty then
    IO.println s!"left alone: {", ".intercalate kept}"
  IO.println ""
  IO.println "next:"
  if dir != "." then IO.println s!"  cd {dir}"
  IO.println "  lake exe cache get"
  IO.println "  lake build"
  return 0

end Paralever.Tool.Init
