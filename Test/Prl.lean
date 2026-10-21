import Prl.Load
import Prl.Report

/-! # The `.prl` examples, as build gates

Every example reads, compiles, prints back as itself, and carries the verdict its header claims.
-- ref: `docs/prl.md` -/

namespace Test.Prl
open Paralever Paralever.Prl

/-- One example, with the verdict it is labelled with. -/
structure Entry where
  name  : String
  src   : String
  /-- Expected `wfB`. -/
  indep : Bool

def corpus : List Entry :=
  [ ⟨"sum",      include_str "../Examples/Language/sum.prl",      true⟩
  , ⟨"matmul",   include_str "../Examples/Language/matmul.prl",   true⟩
  , ⟨"stencil",  include_str "../Examples/Language/stencil.prl",  true⟩
  , ⟨"pipeline", include_str "../Examples/Language/pipeline.prl", true⟩
  , ⟨"control",  include_str "../Examples/Language/control.prl",  true⟩
  , ⟨"chain",    include_str "../Examples/Language/chain.prl",    true⟩
  , ⟨"race",     include_str "../Examples/Language/race.prl",     false⟩
  , ⟨"scatter",  include_str "../Examples/Language/scatter.prl",  false⟩
  , ⟨"arena",    include_str "../Examples/Language/arena.prl",    true⟩ ]

private def compiled (e : Entry) : Option Compiled := (ofString e.src).toOption

#guard corpus.all (fun e => (compiled e).isSome)
#guard corpus.all (fun e => roundTrips e.src)
#guard corpus.all (fun e => (compiled e).all (fun c => ParProg.wfB c.prog == e.indep))

-- the declaration is consistent, and the program stays inside the buffers it declared
#guard corpus.all (fun e => (compiled e).all
  (fun c => c.layout.wfB && c.layout.covers (ParProg.footprintOf c.prog)))

-- `race` is racy at the heap it declares; `scatter` is not, which is what the syntactic
-- footprint's over-approximation costs -- ref: docs/block-ir.md
#guard (corpus.find? (·.name == "race")).all (fun e => (compiled e).all
  (fun c => !(raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty))
#guard (corpus.find? (·.name == "scatter")).all (fun e => (compiled e).all
  (fun c => (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty))

/-! ## What they compute

Read through `prl_file`, so the program is a literal and `decide` never sees the reader. -/

def sum : Compiled      := prl_file "../Examples/Language/sum.prl"
def matmul : Compiled   := prl_file "../Examples/Language/matmul.prl"
def pipeline : Compiled := prl_file "../Examples/Language/pipeline.prl"
def control : Compiled  := prl_file "../Examples/Language/control.prl"
def stencil : Compiled  := prl_file "../Examples/Language/stencil.prl"
def chain : Compiled    := prl_file "../Examples/Language/chain.prl"
def arena : Compiled    := prl_file "../Examples/Language/arena.prl"
def race : Compiled     := prl_file "../Examples/Language/race.prl"
def scatter : Compiled  := prl_file "../Examples/Language/scatter.prl"

/-! ### The equivalence, once per accepted file

Each file compiles to a program the theorem applies to, with nothing further to supply: `wfB`
decides the obligation on the quoted program, and `par_seq_eq` turns it into the equality of
outcomes under every schedule. -/

theorem sum_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar sum.prog ρ) (ParProg.execSeq sum.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem matmul_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar matmul.prog ρ) (ParProg.execSeq matmul.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem stencil_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar stencil.prog ρ) (ParProg.execSeq stencil.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem pipeline_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar pipeline.prog ρ) (ParProg.execSeq pipeline.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem control_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar control.prog ρ) (ParProg.execSeq control.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem chain_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar chain.prog ρ) (ParProg.execSeq chain.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- `free` is erased, so a file that reuses a buffer's space proves the same way as one that
does not. -/
theorem arena_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar arena.prog ρ) (ParProg.execSeq arena.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ### …and the two files for which it is unavailable

`race.prl` has a real race and `scatter.prl` a computed address whose footprint is a bound, so
`wfB` refuses and no instance of `par_seq_eq` exists for either. For `race.prl` the conclusion
itself is false, refuted the way `Examples/Races/Caught.lean` and `Examples/Races/Report.lean` refute it; for
`scatter.prl` the conclusion holds at heaps where the indices miss, proved from the exact check in
`Examples/Language/Scatter.lean`. -/

example : ParProg.wfB race.prog = false := by decide
example : ParProg.wfB scatter.prog = false := by decide

private def after (c : Compiled) : State := (ParProg.runTaskSeq c.prog (fun _ => 0) c.layout.state).2

#guard (List.range 3).map (fun i => after sum (6 + i)) == [.int 3, .int 7, .int 11]
#guard (List.range 4).map (fun i => after matmul (8 + i)) == [.int 19, .int 22, .int 43, .int 50]
#guard (List.range 4).map (fun i => after stencil (5 + i)) == [.int 3, .int 5, .int 7, .int 9]
#guard after pipeline 4 == .int 25
#guard after control 1 == .int 6

-- on real threads, the same heap: `runTask_eq` says so for every program `wfB` accepts
#guard (ParProg.runTask matmul.prog (fun _ => 0) matmul.layout.state).2 8 == Val.int 19

/-! ## `buf` and `free` are erased

Neither emits a `ParProg` node, so no theorem about a program can depend on either: the same
program comes out of writing the addresses by hand. -/

private def progOf (src : String) : Option ParProg := (ofString src).toOption.map (fun c => c.prog)

#guard progOf "buf A[2]\nA[0] := 1\nfree A" == progOf "[0] := 1"
#guard progOf "buf A[2]\nA[0] := 1\nfree A\nbuf B[2]\nB[0] := 2" == progOf "[0] := 1\n[0] := 2"

-- freeing the most recent buffer returns its space; freeing an older one leaves the hole
private def bases (src : String) : Option (List Loc) :=
  (ofString src).toOption.map (fun c => c.layout.bufs.map (fun p => p.base))

#guard bases "buf A[2]\nfree A\nbuf B[2]\n[0] := 1" == some [0, 0]
#guard bases "buf A[2]\nbuf B[2]\nfree A\nbuf C[2]\n[0] := 1" == some [0, 2, 4]

-- a hand-placed buffer leaves a gap below it, and its initial values still arrive: the heap is
-- sized by the top address, not by the number of cells declared
#guard (ofString "buf A[4] = ones\nbuf S[4] at 100 = ones\nA[0] := 1").toOption.map
         (fun c => c.layout.state (c.layout.at "S" [0])) == some (Val.int 1)

/-! ## The same lifetimes, written in Lean

`Arena` is the `buf`/`free` rule as a library function, for a layout assembled in Lean rather than
read from a file. The placements agree with the ones above. -/

private def arenaBases (ds : List LDecl) : List Loc := (Arena.of ds).bufs.map (fun p => p.base)

#guard arenaBases [.buf (buf "A" [2]), .free "A", .buf (buf "B" [2])] == [0, 0]
#guard arenaBases [.buf (buf "A" [2]), .buf (buf "B" [2]), .free "A", .buf (buf "C" [2])]
         == [0, 2, 4]
-- a dead buffer keeps its address and loses its name
#guard (Arena.of [.buf (buf "A" [2]), .free "A", .buf (buf "B" [2])]).live.map (fun p => p.name)
         == ["B"]
-- freeing twice is a no-op, so the cursor cannot walk back over cells `B` now owns
#guard arenaBases [.buf (buf "A" [2]), .free "A", .buf (buf "B" [2]), .free "A", .buf (buf "C" [2])]
         == [0, 0, 2]

/-! ## What is rejected -/

private def rejected (src : String) : Bool := (ofString src).toOption.isNone

-- a register in a bare address: no array to confine it to
#guard rejected "[%0] := 1"
-- a subscript outside its buffer
#guard rejected "buf A[4]\nA[9] := 1"
-- two subscripts on a one-dimensional buffer
#guard rejected "buf A[4]\nA[1, 2] := 1"
-- a computed subscript beside a static one
#guard rejected "buf A[2, 2]\n%i := 0\nA[1, %i] := 1"
-- `at` placing one buffer on top of another
#guard rejected "buf A[4]\nbuf B[4] at 2\nA[0] := 1"
-- an undeclared buffer
#guard rejected "A[0] := 1"
-- a buffer used after its lifetime ended, and a `free` of something that is not a live buffer
#guard rejected "buf A[4]\nfree A\nA[0] := 1"
#guard rejected "buf A[4]\nfree A\nfree A"
#guard rejected "free A"
-- a declaration or a `free` inside a thread, where only part of the program would see it
#guard rejected "buf A[4]\nparallel { free A } | { A[0] := 1 }"
#guard rejected "parallel { buf A[4] } | { [0] := 1 }"
-- a name declared twice
#guard rejected "buf A[4]\nbuf A[2]\nA[0] := 1"
-- `%` as a value operator: `AExp` has no modulo
#guard rejected "%i := 7 % 2"
-- a load inside an expression
#guard rejected "buf A[4]\nreg x\n%x := A[0] + 1"
-- more initial values than cells
#guard rejected "buf A[2] = 1, 2, 3"

-- …and the accepted forms those rejections are the boundary of
-- a register needs no declaration: a name is registered where it is first used
#guard !rejected "[0] := %acc"
#guard progOf "%acc := 1\n[0] := %acc" == progOf "%0 := 1\n[0] := %0"
-- …and a name never collides with a number already in use
#guard progOf "%0 := 1\n%acc := 2\n[0] := %0 + %acc" == progOf "%0 := 1\n%1 := 2\n[0] := %0 + %1"
-- `reg acc = 3` pins an index when that matters
#guard progOf "reg acc = 3\n%acc := 1\n[0] := %acc" == progOf "%3 := 1\n[0] := %3"
#guard !rejected "buf A[4]\n%i := 0\nA[%i] := 1"
#guard !rejected "const n = 2\nbuf A[n, n]\nA[1, 1] := 1"
#guard !rejected "buf A[4]\nbuf B[4] at 100\nA[0] := 1"
#guard !rejected "[0] := 3; [1] := 4"
#guard !rejected "paralever {\n  [0] := 3;\n  parallel { [1] := 1 } | { [2] := 2 }\n}"

end Test.Prl
