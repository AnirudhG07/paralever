import Tool
import MLIR.Load

/-! # The command line and the two conversions, as build gates

What is gated here is the pair of claims the `paralever` executable makes about a file it writes.

*Out and back*: a program emitted as MLIR generic form and read again has the same memory, the
same footprint, the same verdict and leaves the same heap — `MLIR.emitRoundTrips`. It is not the
same *tree*: registers are assignable and SSA values are not, so a `%r := e` with no memory in it
is inlined into whatever reads it, and the registers that remain are renumbered.

*The right theorem*: `prove` has three routes and no choice about which it takes — `wfB` decides
one, the per-heap check the second, and a real race leaves neither. -- ref: `docs/cli.md` -/

namespace Test.Tool
open Paralever Paralever.Lang Paralever.Tool

/-! ## `.prl` out as MLIR, and back -/

def sum : Compiled      := prl_file "../Examples/Language/sum.prl"
def matmul : Compiled   := prl_file "../Examples/Language/matmul.prl"
def stencil : Compiled  := prl_file "../Examples/Language/stencil.prl"
def pipeline : Compiled := prl_file "../Examples/Language/pipeline.prl"
def chain : Compiled    := prl_file "../Examples/Language/chain.prl"
def race : Compiled     := prl_file "../Examples/Language/race.prl"
def scatter : Compiled  := prl_file "../Examples/Language/scatter.prl"
def control : Compiled  := prl_file "../Examples/Language/control.prl"
def arena : Compiled    := prl_file "../Examples/Language/arena.prl"
def equiv : Compiled    := prl_file "../Examples/Language/equiv.prl"

def emitted : List (String × Compiled) :=
  [ ("sum", sum), ("matmul", matmul), ("stencil", stencil), ("pipeline", pipeline)
  , ("chain", chain), ("race", race), ("scatter", scatter) ]

#guard emitted.all (fun e => MLIR.emitRoundTrips e.2.layout e.2.prog)

-- a computed subscript survives as one: the index is an operand, not an affine map
#guard (MLIR.emitText scatter.layout scatter.prog).toOption.any
  (fun s => (s.splitOn "arith.index_cast").length == 4)

-- a fork is a group of `async.execute` ops closed by the await that names their tokens, and the
-- name the `.prl` file gave it rides on that await
#guard (MLIR.emitText sum.layout sum.prog).toOption.any
  (fun s => (s.splitOn "\"async.execute\"").length == 4
              && (s.splitOn "paralever.label = \"chunked sum\"").length == 2)

/-! ### …and the two files with no generic form

Rejected rather than approximated, as the reader rejects: there is no conditional in the op set
the reader supports, and two MLIR globals cannot alias. -/

#guard (MLIR.emitText control.layout control.prog).toOption.isNone
#guard (MLIR.emitText arena.layout arena.prog).toOption.isNone

/-! ## MLIR in, `.prl` out

The other direction needs no new code: the lowering gives a `Layout` and a `ParProg`, which is
what `print` takes. What is gated is that the text it writes reads back as the same program. -/

def doall : Lang.ParProg      := mlir_prog "../Examples/Mlir/doall-no.mlir"
def doallL : Layout          := mlir_layout "../Examples/Mlir/doall-no.mlir"
def nested2d : Lang.ParProg   := mlir_prog "../Examples/Mlir/nested-2d-no.mlir"
def nested2dL : Layout       := mlir_layout "../Examples/Mlir/nested-2d-no.mlir"

#guard roundTrips (toPrl ⟨doallL, doall, [], [], none⟩)
#guard roundTrips (toPrl ⟨nested2dL, nested2d, [], [], none⟩)

-- and a lowered module emits as generic form again
#guard MLIR.emitRoundTrips doallL doall
#guard MLIR.emitRoundTrips nested2dL nested2d

/-! ## Which theorem `prove` writes

Three programs, three routes. The generated file is checked by Lean when it is checked at all
(`paralever prove -o FILE --check`), so what is gated here is only the choice. -/

private def subj (name : String) (c : Compiled) (autopar : Bool := false) : Subject :=
  { kind := .prl, path := name, name := name, stem := identOf name, prog := c, autopar }

private def has (s t : String) : Bool := (s.splitOn t).length > 1

-- independence at every heap: `par_seq_eq` itself, universally quantified over `ρ` and `σ`
#guard has (proofFile (subj "sum.prl" sum)) "theorem sum_par_seq_eq (ρ : Regs) (σ : State)"
#guard has (proofFile (subj "sum.prl" sum)) "ParProg.par_seq_eq (by decide) ρ σ"

-- a bound rather than a footprint: the per-heap route, at the heap the file declares
#guard has (proofFile (subj "scatter.prl" scatter)) "parSeqEq_of_runSeq_eq"
#guard has (proofFile (subj "scatter.prl" scatter)) "wellFormedB_iff"
#guard !has (proofFile (subj "scatter.prl" scatter)) "ParProg.par_seq_eq"

-- a real race: both checks refuse, and the file carries no theorem at all
#guard !has (proofFile (subj "race.prl" race)) "theorem"
#guard has (proofFile (subj "race.prl" race)) "= false := by decide"

-- a claim adds the two-program theorem to whichever of the three the left side carried
#guard has (proofFile (subj "equiv.prl" equiv)) "theorem equiv_agree"
#guard has (proofFile (subj "equiv.prl" equiv)) "ParProg.agreeOn_of_wfB"
#guard has (proofFile (subj "equiv.prl" equiv)) "ParProg.AgreeOn src.compared src.prog src.other"
-- and the left side keeps its own, so the file states both
#guard has (proofFile (subj "equiv.prl" equiv)) "theorem equiv_par_seq_eq"
-- a file with no claim says nothing about agreement
#guard !has (proofFile (subj "sum.prl" sum)) "AgreeOn"

-- `--autopar` adds the pass's own soundness, which has no hypothesis
#guard has (proofFile (subj "chain.prl" chain (autopar := true))) "AutoPar.rewrite_sound"

-- the namespace and the theorem are named after the file, whatever the path looked like
#guard identOf "doall-no.mlir" == "doallNo"
#guard identOf "sum.prl" == "sum"
#guard upperOf (identOf "nested-2d-no.mlir") == "Nested2dNo"

/-! ## The Lean form

`toLean` prints what `paralever { … }` parses, which holds only if the printer reaches for forms
that exist: a label is `:: "name"` and not a comment, initial contents are an `Init` and not a bare
`List Nat`, a computed access is `[A, e]`, and a layout whose buffers share a base is written with
its addresses because `Layout.of` would re-allocate them.
`Test/LeanForm.lean` is the other half — the same programs written by hand.
-- ref: `docs/prl.md` § The Lean form -/

#guard has (toLean sum) ":: \"chunked sum\""
#guard !has (toLean sum) "-- chunked sum"
#guard has (toLean sum) "(data [1, 2, 3, 4, 5, 6])"
#guard has (toLean scatter) "[(L.ref \"dst\"), %0] := 1"
#guard has (toLean arena) "base := 4"
#guard !has (toLean arena) "Layout.of"
#guard has (toLean matmul) "Layout.of"

/-! ## What `init` writes

Six files, the module named after the directory, and the toolchain a copy of this project's own, so
a generated project cannot pin a different one. -- ref: `docs/cli.md` § init -/

#guard (Init.files "my-kernel").map Prod.fst
  == ["lakefile.toml", "lean-toolchain", "MyKernel.lean", "hello.prl", "README.md", ".gitignore"]
#guard Init.moduleOf (Init.packageOf "/tmp/My Kernel/") == "MyKernel"
#guard Init.packageOf "demo" == "demo"
-- the dependency, and no second name for Mathlib: it arrives as paralever's own
#guard has ((Init.files "demo").lookup "lakefile.toml" |>.getD "") "name = \"paralever\""
#guard !has ((Init.files "demo").lookup "lakefile.toml" |>.getD "") "mathlib"
-- the generated module ends in the theorem, so `lake build` is the whole check
#guard has ((Init.files "demo").lookup "Demo.lean" |>.getD "") "ParProg.par_seq_eq (by decide)"
-- and the program it reads is one `wfB` accepts, with a `def` in it
#guard ((Init.files "demo").lookup "hello.prl" |>.getD "" |> Lang.ofString).toOption.all
  (fun c => ParProg.wfB c.prog)
#guard has ((Init.files "demo").lookup "hello.prl" |>.getD "") "def scale("

/-! ## The option grammar -/

private def opts (as : List String) : Option Opts := (parseArgs as).toOption

#guard (opts ["check", "a.prl"]).any (fun o => o.cmd == "check" && o.file == "a.prl")
-- `init` takes a directory, which is not a file name, and takes none at all
#guard (opts ["init", "my-kernel"]).any (fun o => o.cmd == "init" && o.file == "my-kernel")
#guard (opts ["init"]).any (fun o => o.cmd == "init" && o.file.isEmpty)
#guard (opts ["prove", "a.prl", "-o", "A.lean", "--check"]).any
  (fun o => o.out == some "A.lean" && o.check)
#guard (opts ["run", "--threads", "a.prl"]).any (fun o => o.threads && o.file == "a.prl")
#guard (opts ["to-mlir", "--autopar", "a.prl"]).any (fun o => o.autopar)
-- no command, and the proof asked for alongside the verdict
#guard (opts ["a.prl", "--prove", "A.lean"]).any
  (fun o => o.cmd.isEmpty && o.file == "a.prl" && o.proof == some "A.lean")
#guard (opts ["--func", "main", "a.mlir"]).any (fun o => o.func == some "main")
#guard (opts ["run", "a.prl", "-n", "C"]).any (fun o => o.only == some "C" && !o.allCells)
#guard (opts ["run", "a.prl", "--all-cells"]).any (fun o => o.allCells)
-- verbosity is on until something turns it off, and the last of the two wins
#guard (opts ["run", "a.prl"]).any (fun o => o.verbose)
#guard (opts ["run", "a.prl", "-q"]).any (fun o => !o.verbose)
#guard (opts ["run", "a.prl", "--quiet"]).any (fun o => !o.verbose)
#guard (opts ["run", "a.prl", "-q", "-v"]).any (fun o => o.verbose)
#guard (opts ["run", "a.prl", "-v", "--quiet"]).any (fun o => !o.verbose)
-- what is refused: an unknown flag, a missing `-o` path, a missing `--prove` path, a second file
#guard (opts ["check", "--wat", "a.prl"]).isNone
#guard (opts ["prove", "a.prl", "-o"]).isNone
#guard (opts ["a.prl", "--prove"]).isNone
#guard (opts ["a.mlir", "--func"]).isNone
#guard (opts ["run", "a.prl", "-n"]).isNone
#guard (opts ["check", "a.prl", "b.prl"]).isNone

/-! ## `-n`'s argument

A buffer, or one cell of a buffer. The subscript is the layout's, so `C[1, 2]` here is the same
subscript `Layout.at "C" [1, 2]` takes. -- ref: `docs/cli.md` § What `run` prints -/

#guard (splitIdx "C").toOption == some ("C", none)
#guard (splitIdx " C[1, 2] ").toOption == some ("C", some [1, 2])
#guard (splitIdx "C[3]").toOption == some ("C", some [3])
-- and what it refuses, each saying which part of the argument is wrong
#guard (splitIdx "C[1, 2").isOk == false
#guard (splitIdx "C[x]").isOk == false
#guard (splitIdx "C[1][2]").isOk == false

-- the two answers, on a program whose heap is known
#guard (runCell matmul false "C").toOption == some "C [2, 2] @8  [19, 22]\n             [43, 50]"
#guard (runCell matmul false "C[1, 1]").toOption == some "C[1, 1] @11  50"
#guard (runCell matmul false "Z").isOk == false
#guard (runCell matmul false "C[9, 0]").isOk == false

-- the default view elides a buffer past `runCells` cells and says how many it left out; a 2×2
-- buffer is under the limit, so the two agree there
#guard runReport matmul false == runReport matmul false (allCells := true)

/-! ## One body for `run` and for a bare file

`paralever FILE` says everything `paralever run FILE` says and adds the verdict, so both print
`runBody` and cannot drift. `--quiet` replaces that body with the program's output alone.
-- ref: `docs/cli.md` § A file on its own -/

def stripe : Compiled := prl_file "../Examples/Language/stripe.prl"

#guard runBody {} matmul (raceHint := false) == runReport matmul false
#guard runBody {} stripe (raceHint := true) == runReport stripe false
-- `--quiet` is what `print` wrote and nothing else, whichever command asked
#guard runBody { verbose := false } stripe (raceHint := false) == quietReport stripe
#guard quietReport stripe == "k = [0, 1]\n"
-- …and a program with no `print` then says nothing at all, not a blank line
#guard quietReport matmul == ""
-- the race caveat differs in one clause, because a bare file prints the interleaving itself
#guard runBody {} race (raceHint := false) != runBody {} race (raceHint := true)
#guard (runBody {} race (raceHint := true)).endsWith (runReport race false)

/-! ## The version

`Paralever/Version.lean` reads `lakefile.toml`, so these gates fail if the declaration is removed
or renamed rather than silently falling back to the default. -/

#guard Paralever.version == "1.34.0"
#guard Paralever.packageName == "paralever"
#guard Paralever.versionParts == (1, 34, 0)
-- the shape, not the toolchain: a patch bump of Lean must not fail a gate here, which is what
-- `Version.lean`'s `#guard` on the minor is for
#guard Paralever.versionLine == "paralever " ++ Paralever.version ++ " (" ++ Lean.toolchain ++ ")"

end Test.Tool
