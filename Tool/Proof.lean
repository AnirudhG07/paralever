import MLIR.Emit
import Lang.Report

/-! # The Lean file a program's correctness is carried by

`paralever prove FILE` writes a Lean module that reads `FILE` again while it elaborates and then
states what holds of it. Nothing is asserted here: the generated file is a file Lean checks, so a
claim it makes about the program is a claim the kernel accepts or the build fails.

Which theorem is available depends on the program, and there are exactly three cases — the three
`docs/block-ir.md` names. `wfB` decides independence on the syntax, at every heap, and that is the
hypothesis of `par_seq_eq`. When a footprint is a bound rather than the set of cells touched,
`wfB` refuses and the per-heap check `wellFormedB` can still accept, which gives the equivalence at
the heap the file declares. When there is a real race, both refuse, and no theorem of this shape
exists — the generated file says so and proves the refusals.
-- ref: `docs/cli.md` -/

namespace Paralever.Tool
open Paralever Paralever.Lang

/-- Which front end the program came through: the generated file reads the source the same way. -/
inductive Kind where
  | prl
  | mlir
  deriving BEq

/-- What `prove` was asked about: the compiled program, and how the generated file should name its
source again. -/
structure Subject where
  kind    : Kind
  /-- The source path as the generated file will spell it, which is resolved against the generated
  file's own directory. -/
  path    : String
  /-- The source's own file name, which is what the generated file's prose calls it. -/
  name    : String
  /-- An identifier made from the file name, for the namespace and the theorem. -/
  stem    : String
  prog    : Compiled
  /-- Prove the autoparallelized program instead, and carry `rewrite_sound` as well. -/
  autopar : Bool := false

/-- Characters of a name, with every run of punctuation closed up and the letter after it
capitalised. -/
private def camel : List Char → Bool → List Char
  | [],      _  => []
  | c :: cs, up =>
      if c.isAlphanum then (if up then c.toUpper else c) :: camel cs false
      else camel cs true

/-- A file name as a Lean identifier: `doall-no.mlir` ↦ `doallNo`. -/
def identOf (name : String) : String :=
  match camel ((name.splitOn ".").headD name).toList false with
  | []      => "prog"
  | c :: cs => String.ofList (c.toLower :: cs)

/-- An identifier capitalised, for a namespace. -/
def upperOf (s : String) : String :=
  match s.toList with
  | []      => "Prog"
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- The program the theorems are about: the file's own, or the pass's output. -/
def subjectProg (s : Subject) : ParProg :=
  if s.autopar then AutoPar.rewrite s.prog.prog else s.prog.prog

private def term (s : Subject) : String :=
  if s.autopar then "par" else
  match s.kind with
  | .prl  => "src.prog"
  | .mlir => "prog"

private def heap (s : Subject) : String :=
  match s.kind with
  | .prl  => "src.layout.state"
  | .mlir => "layout.state"

/-- The preamble: the imports, the namespace, and the source read back. -/
private def header (s : Subject) (title : String) (blurb : List String) : List String :=
  (match s.kind with
   | .prl  => ["import Lang.Report"]
   | .mlir => ["import MLIR.Load", "import Lang.Report"])
  ++ [ ""
     , "/-! # `" ++ s.name ++ "` — " ++ title
     , "" ]
  ++ blurb
  ++ [ ""
     , "Written by `paralever prove`. The source is read and compiled while this file elaborates,"
     , "so the declaration below holds a program literal and `by decide` never runs the reader."
     , "-- ref: `docs/cli.md` -/"
     , ""
     , "namespace Paralever.Proofs." ++ upperOf s.stem
     , "open Paralever Paralever.Lang"
     , ""
     , "-- `decide` reduces the program against a heap, which nests deeper than the default bound,"
     , "-- and reading a large file costs more than the default heartbeat budget allows. Both"
     , "-- terminate: the program is a finite literal by the time either runs."
     , "set_option maxRecDepth 100000"
     , "set_option maxHeartbeats 0"
     , "" ]
  ++ (match s.kind with
      | .prl  =>
          [ "/-- The file, compiled: where its buffers are and what its program is. -/"
          , "def src : Compiled := prl_file \"" ++ s.path ++ "\"" ]
      | .mlir =>
          [ "/-- The lowered program, and the memory the module declares. -/"
          , "def prog : ParProg := mlir_prog \"" ++ s.path ++ "\""
          , ""
          , "def layout : Layout := mlir_layout \"" ++ s.path ++ "\"" ])
  ++ [ ""
     , "/-- Registers start at zero, as every run of a compiled file does. -/"
     , "def ρ0 : Regs := fun _ => 0" ]
  ++ (if s.autopar then
        [ ""
        , "/-- What the pass emits. `rewrite` checks its own gate, so this is the program the"
        , "analysis proposed only when the gate passed, and the original otherwise. -/"
        , "def par : ParProg := AutoPar.rewrite " ++
            (match s.kind with | .prl => "src.prog" | .mlir => "prog") ]
      else [])

/-- `rewrite_sound`, which holds of every program with no hypothesis at all. -/
private def soundness (s : Subject) : List String :=
  let base := match s.kind with | .prl => "src.prog" | .mlir => "prog"
  [ ""
  , "/-- **The pass preserves the heap**, with no hypothesis: the independence check and the"
  , "register-flow check are inside `rewrite`, so a plan that fails either is never emitted."
  , "-- ref: `docs/autopar.md` -/"
  , "theorem " ++ s.stem ++ "_autopar_sound (ρ : Regs) (σ : State) :"
  , "    (runSeq (ParProg.execPar par ρ) σ).2 = (runSeq (ParProg.execSeq " ++ base ++ " ρ) σ).2 :="
  , "  AutoPar.rewrite_sound " ++ base ++ " ρ σ" ]

/-- A side's `WellFormed`, from whichever check decided it. -/
private def sideWF (t : String) (h : String) (wf : Bool) : String :=
  if wf then s!"(ParProg.wfB_wellFormed (by decide) ρ0 {h})"
  else   s!"((wellFormedB_iff (ParProg.execPar {t} ρ0) {h}).1 (by decide))"

/-- **The file's `assert`**, as a section appended to whichever theorem the left program carries.
The left side's own checks are above it already, so only the right side's are printed here. The
claim is about the file's own two programs and does not follow `--autopar` into the pass's output.
-- ref: `docs/equivalence.md` -/
private def claimPart (s : Subject) (cl : Lang.Claim) : List String :=
  let h := heap s
  -- `assertParSeq` states the stronger relation, so both the Boolean and the theorem change
  let ps := cl.strength == .parSeq
  let cells := if ps then "src.compared src.comparedRegs" else "src.compared"
  let agree := s!"ParProg.{if ps then "agreeParSeqB" else "agreeB"} {cells} src.prog src.other ρ0 {h}"
  let rel := if ps then "AgreeParSeq" else "AgreeOn"
  let lwf := ParProg.wfB s.prog.prog
  let rwf := ParProg.wfB cl.other
  let lok := Lang.sideSound s.prog.layout s.prog.prog
  let rok := Lang.sideSound s.prog.layout cl.other
  let σ := s.prog.layout.state
  let holds := if ps then ParProg.agreeParSeqB cl.cells cl.regs s.prog.prog cl.other (fun _ => 0) σ
               else ParProg.agreeB cl.cells s.prog.prog cl.other (fun _ => 0) σ
  let n := Lang.comparedWord cl
  let on := ", ".intercalate cl.bufs
  [ ""
  , "/-! ### The file's claim"
  , ""
  , "    " ++ (if ps then "assertParSeq " else "assert ") ++ cl.left ++ "(…) == " ++ cl.right
      ++ "(…) on " ++ on
  , ""
  , "Two programs, not one. The file was compiled twice, with each side's body written out where"
  , "the claim stands, so both start from the declarations above and from one heap. `src.prog` is"
  , "the left side, whose checks are above; `src.other` is the right."
  , "-- ref: `docs/equivalence.md` -/"
  , "" ]
  ++ (if !holds then
        [ "/-- **The claim does not hold.** The two sequential readings differ at some of the"
        , n ++ " compared, so there is nothing about schedules left to say. -/"
        , "example : " ++ agree ++ " = false := by decide" ]
      else if lok && rok then
        [ "/-- The right side's schedules agree with its own sequential reading. -/"
        , "example : ParProg.wfB src.other = " ++ (if rwf then "true" else "false")
            ++ " := by decide" ]
        ++ (if rwf then [] else
             [ ""
             , "/-- Its footprint is a bound rather than the cells touched — a computed address —"
             , "so the exact check decides it at this heap instead. -/"
             , "example : wellFormedB (ParProg.execPar src.other ρ0) " ++ h
                 ++ " = true := by decide" ])
        ++ [ ""
           , "/-- The two sequential readings leave the compared " ++ (if ps then
                 "cells and registers" else "cells") ++ " equal. This is the one"
           , "obligation parallelism has nothing to do with: neither reading has a fork in it."
           , "-- ref: `docs/equivalence.md` § How it is proved -/"
           , "example : " ++ agree ++ " = true := by decide"
           , ""
           , "/-- **The two programs agree.** Every outcome either one reaches, under every"
           , "schedule of either, holds the same values at " ++ on ++ " — " ++ n
               ++ " compared. -/"
           , "theorem " ++ s.stem ++ "_agree :"
           , "    ParProg." ++ rel ++ " " ++ cells ++ " src.prog src.other ρ0 " ++ h ++ " :=" ]
        ++ (if lwf && rwf then
              ["  ParProg." ++ (if ps then "agreeParSeq_of_wfB" else "agreeOn_of_wfB")
                 ++ " (by decide) (by decide) (by decide)"]
            else
              [ "  ParProg." ++ (if ps then "agreeParSeq_of_wellFormed" else
                                   "agreeOn_of_wellFormed")
              , "    " ++ sideWF "src.prog" h lwf
              , "    " ++ sideWF "src.other" h rwf ++ " (by decide)"
                  ++ (if ps then " (by decide)" else "") ])
      else
        let racy := if !lok then cl.left else cl.right
        let side := if !lok then "src.prog" else "src.other"
        [ "/-- The compared " ++ (if ps then "cells and registers" else "cells")
            ++ " agree on the canonical run, and **no claim follows**: '" ++ racy
            ++ "'"
        , "has a race, so it reaches outcomes its sequential reading does not and there is no"
        , "single answer to compare. -/"
        , "example : " ++ agree ++ " = true := by decide"
        , ""
        , "example : ParProg.wfB " ++ side ++ " = false := by decide"
        , ""
        , "example : wellFormedB (ParProg.execPar " ++ side ++ " ρ0) " ++ h
            ++ " = false := by decide" ])

/-- **The generated module.** -/
def proofFile (s : Subject) : String :=
  let p := subjectProg s
  let t := term s
  let body :=
    if ParProg.wfB p then
      header s "parallel equals sequential"
        [ "Independence holds at every `par` node of the program, so the equality of outcomes is"
        , "available at every heap and under every schedule." ]
        ++ (if s.autopar then soundness s else [])
        ++ [ ""
           , "/-- Bernstein's condition at every fork, decided on the syntax: no two threads write"
           , "a common cell, and neither reads a cell the other writes. -/"
           , "example : ParProg.wfB " ++ t ++ " = true := by decide"
           , ""
           , "/-- **Parallel equals sequential.** For every register file, every heap and every"
           , "schedule: the parallel reading reaches an outcome exactly when the sequential one"
           , "reaches that same outcome. -/"
           , "theorem " ++ s.stem ++ "_par_seq_eq (ρ : Regs) (σ : State) :"
           , "    ParSeqEq (ParProg.execPar " ++ t ++ " ρ) (ParProg.execSeq " ++ t ++ " ρ) σ :="
           , "  ParProg.par_seq_eq (by decide) ρ σ" ]
    else if wellFormedB (ParProg.execPar p (fun _ => 0)) s.prog.layout.state then
      header s "parallel equals sequential, at the heap the file declares"
        [ "A computed address makes the syntactic footprint a *bound* on the cells touched rather"
        , "than the set of them, so `wfB` refuses. The per-heap check measures the real accesses"
        , "along the canonical run and accepts, which gives the equivalence at this heap."
        , "-- ref: `docs/block-ir.md`" ]
        ++ (if s.autopar then soundness s else [])
        ++ [ ""
           , "/-- The bound is too coarse for the syntactic check. -/"
           , "example : ParProg.wfB " ++ t ++ " = false := by decide"
           , ""
           , "/-- The exact check accepts, at this heap. -/"
           , "example : wellFormedB (ParProg.execPar " ++ t ++ " ρ0) " ++ heap s ++ " = true :="
           , "  by decide"
           , ""
           , "/-- **Parallel equals sequential at this heap.** The two `WellFormed` hypotheses come"
           , "from the exact check; the canonical runs agree with no hypothesis at all. -/"
           , "theorem " ++ s.stem ++ "_par_seq_eq :"
           , "    ParSeqEq (ParProg.execPar " ++ t ++ " ρ0) (ParProg.execSeq " ++ t ++ " ρ0) "
               ++ heap s ++ " :="
           , "  parSeqEq_of_runSeq_eq _ _ _"
           , "    ((wellFormedB_iff _ _).1 (by decide))"
           , "    ((wellFormedB_iff _ _).1 (by decide))"
           , "    (ParProg.execPar_runSeq_all.1 " ++ t ++ " ρ0 " ++ heap s ++ ")" ]
    else
      header s "a race, so no equivalence"
        [ "Two threads touch a common cell and at least one writes it. `par_seq_eq`'s hypothesis is"
        , "false here, and so is its conclusion: the parallel reading reaches `wrong`, which is no"
        , "terminating outcome, while the sequential reading terminates. `paralever race` prints the"
        , "interleaving that does it, and `Examples/Races/Report.lean` carries the refutation in full."
        , "-- ref: `docs/semantics.md`" ]
        ++ [ ""
           , "/-- The syntactic check refuses. -/"
           , "example : ParProg.wfB " ++ t ++ " = false := by decide"
           , ""
           , "/-- And so does the exact one, at the heap the file declares: the conflict is real,"
           , "not an artefact of over-approximating a footprint. -/"
           , "example : wellFormedB (ParProg.execPar " ++ t ++ " ρ0) " ++ heap s ++ " = false :="
           , "  by decide" ]
  let body := body ++ (match s.prog.claim with
    | some cl => claimPart s cl
    | none    => [])
  "\n".intercalate (body ++ ["", "end Paralever.Proofs." ++ upperOf s.stem, ""])

end Paralever.Tool
