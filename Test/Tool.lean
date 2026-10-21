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

#guard roundTrips (print ⟨doallL, doall, [], []⟩)
#guard roundTrips (print ⟨nested2dL, nested2d, [], []⟩)

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

-- `--autopar` adds the pass's own soundness, which has no hypothesis
#guard has (proofFile (subj "chain.prl" chain (autopar := true))) "AutoPar.rewrite_sound"

-- the namespace and the theorem are named after the file, whatever the path looked like
#guard identOf "doall-no.mlir" == "doallNo"
#guard identOf "sum.prl" == "sum"
#guard upperOf (identOf "nested-2d-no.mlir") == "Nested2dNo"

/-! ## The option grammar -/

private def opts (as : List String) : Option Opts := (parseArgs as).toOption

#guard (opts ["check", "a.prl"]).any (fun o => o.cmd == "check" && o.file == "a.prl")
#guard (opts ["prove", "a.prl", "-o", "A.lean", "--check"]).any
  (fun o => o.out == some "A.lean" && o.check)
#guard (opts ["run", "--threads", "a.prl"]).any (fun o => o.threads && o.file == "a.prl")
#guard (opts ["to-mlir", "--autopar", "a.prl"]).any (fun o => o.autopar)
-- no command, and the proof asked for alongside the verdict
#guard (opts ["a.prl", "--prove", "A.lean"]).any
  (fun o => o.cmd.isEmpty && o.file == "a.prl" && o.proof == some "A.lean")
-- what is refused: an unknown flag, a missing `-o` path, a missing `--prove` path, a second file
#guard (opts ["check", "--wat", "a.prl"]).isNone
#guard (opts ["prove", "a.prl", "-o"]).isNone
#guard (opts ["a.prl", "--prove"]).isNone
#guard (opts ["check", "a.prl", "b.prl"]).isNone

end Test.Tool
