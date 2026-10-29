import Lang.Load
import Lang.Report

/-! # The `.prl` examples, as build gates

Every example reads, compiles, prints back as itself, and carries the verdict its header claims.
-- ref: `docs/prl.md` -/

namespace Test.Lang
open Paralever Paralever.Lang

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
  , ⟨"arena",    include_str "../Examples/Language/arena.prl",    true⟩
  , ⟨"phases",   include_str "../Examples/Language/phases.prl",   true⟩
  , ⟨"branch",   include_str "../Examples/Language/branch.prl",   false⟩
  , ⟨"funcs",    include_str "../Examples/Language/funcs.prl",    true⟩
  , ⟨"sortnet",  include_str "../Examples/Language/sortnet.prl",  true⟩
  , ⟨"equiv",    include_str "../Examples/Language/equiv.prl",    true⟩
  , ⟨"twofold",  include_str "../Examples/Language/twofold.prl",  true⟩ ]

private def compiled (e : Entry) : Option Compiled := (ofString e.src).toOption

#guard corpus.all (fun e => (compiled e).isSome)
#guard corpus.all (fun e => roundTrips e.src)
#guard corpus.all (fun e => (compiled e).all (fun c => ParProg.wfB c.prog == e.indep))

-- the declaration is consistent, and the program stays inside the buffers it declared
#guard corpus.all (fun e => (compiled e).all
  (fun c => c.layout.wfB && c.layout.covers (ParProg.footprintOf c.prog)))

-- `race` is racy at the heap it declares; `scatter` and `branch` are not, which is what the
-- syntactic footprint's over-approximation costs -- ref: docs/block-ir.md
#guard (corpus.find? (·.name == "race")).all (fun e => (compiled e).all
  (fun c => !(raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty))
#guard ["scatter", "branch"].all (fun nm => (corpus.find? (·.name == nm)).all (fun e =>
  (compiled e).all
    (fun c => (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty)))

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

/-! ## Synchronization

A `synchronize` ends a phase: `autoPar` plans each phase on its own and keeps the barrier. The pair
below is why the construct exists — the two phases write disjoint buffers and only read `A`, so
Bernstein accepts one fork of eight, and the barrier is the only thing that splits it.
-- ref: `docs/autopar.md` § Synchronization -/

private def phasesSrc : String := include_str "../Examples/Language/phases.prl"
private def withoutSynchronize : String :=
  "buf X[2]\nbuf Y[2]\nX[0] := 1\nX[1] := 2\nY[0] := 3\nY[1] := 4\n"
private def withSynchronize : String :=
  "buf X[2]\nbuf Y[2]\nX[0] := 1\nX[1] := 2\nsynchronize\nY[0] := 3\nY[1] := 4\n"

private def forkSizes (src : String) : Option (List Nat) :=
  (ofString src).toOption.map (fun c =>
    (ParProg.flatten (ParProg.autoPar c.prog)).map fun s =>
      match s with | .par ts => ts.length | _ => 1)

-- one fork of four without the barrier, two of two with it
#guard forkSizes withoutSynchronize == some [4]
#guard forkSizes withSynchronize == some [2, 1, 2]
-- …and the proposal still passes the proved check
#guard (ofString withSynchronize).toOption.all (fun c => ParProg.wfB (ParProg.autoPar c.prog))

-- the two phases of `phases.prl`, eight statements each
#guard (ofString phasesSrc).toOption.map
         (fun c => (ParProg.phases (ParProg.flatten c.prog)).map List.length) == some [8, 8]
-- the barrier survives autoparallelization, and the printed result reads back as itself
#guard (ofString phasesSrc).toOption.all
         (fun c => !ParProg.synchronizeFree (ParProg.autoPar c.prog))
#guard (ofString phasesSrc).toOption.all
         (fun c => roundTrips (toPrl { c with prog := ParProg.autoPar c.prog }))
-- splitting into phases and joining them back is the identity on the chain, for every chain
example (us : List ParProg) : ParProg.joinPhases (ParProg.phases us) = us :=
  ParProg.joinPhases_phases us

/-! ### A print is the other barrier

`A[0] := 1` and the two stores after it are pairwise independent, so without the print `autoPar`
forks all three. The print groups with nothing, so the store it follows cannot be forked past the
point its value was observed. -- ref: `docs/print.md` § Erased, and a barrier -/

private def withoutPrint : String :=
  "buf A[4]
A[0] := 1
A[1] := 2
A[2] := 3
"
private def withPrint : String :=
  "buf A[4]
A[0] := 1
print A
A[1] := 2
A[2] := 3
"

#guard forkSizes withoutPrint == some [3]
#guard forkSizes withPrint == some [1, 1, 2]
-- the proved route declines it, so the print stays out of every thread and the text reads back
#guard (ofString withPrint).toOption.all (fun c => !AutoPar.rewriteOk c.prog)
#guard (ofString withPrint).toOption.all
         (fun c => ParProg.noBarrierInThread (ParProg.autoPar c.prog))
#guard (ofString withPrint).toOption.all
         (fun c => roundTrips (toPrl { c with prog := ParProg.autoPar c.prog }))

/-! ## `else if` is the nest

`ParProg` has one `ifElse`, so a chain is sugar for the nest and prints back as one.
-- ref: `docs/prl.md` § Conditions -/

#guard progOf "buf A[1]\n%k := A[0]\nif %k == 0 { [0] := 1 } else if %k == 1 { [0] := 2 }"
     == progOf "buf A[1]\n%k := A[0]\nif %k == 0 { [0] := 1 } else { if %k == 1 { [0] := 2 } }"

#guard roundTrips "buf A[1]\n%k := A[0]\nif %k == 0 { [0] := 1 } else if %k == 1 { [0] := 2 }"

/-! ## A call is its body, written out

A `def` reaches no `ParProg` node, so the program a file with calls compiles to is the program the
written-out file compiles to — register indices included. -- ref: `docs/prl.md` § Functions -/

private def sqDef : String :=
  "def square(A, i) {\n  %t := A[i]\n  A[i] := %t * %t\n}\nbuf A[4] = 1, 2, 3, 4\n"

#guard progOf (sqDef ++ "square(A, 0)")
     == progOf "buf A[4] = 1, 2, 3, 4\n%t := A[0]\nA[0] := %t * %t"

-- two calls, two registers: the body's own `%t` is renamed per call site, so neither call can
-- clobber what the other holds and the pass is free to put them in one fork
#guard progOf (sqDef ++ "square(A, 0)\nsquare(A, 1)")
     == progOf "buf A[4] = 1, 2, 3, 4\n%a := A[0]\nA[0] := %a * %a\n%b := A[1]\nA[1] := %b * %b"

-- a register parameter is the caller's register, and is not renamed
#guard progOf ("def load(%s, A, i) { %s := A[i] }\nbuf A[2] = 1, 2\nload(%out, A, 1)")
     == progOf "buf A[2] = 1, 2\n%out := A[1]"

-- a name parameter takes a slice as readily as a buffer: both name cells
#guard progOf ("def first(S) { S[0] := 7 }\nbuf A[4]\nslice h = A[2..4]\nfirst(h)")
     == progOf "buf A[4]\nA[2] := 7"

-- a call may precede the `def` it names, and a body may call another `def`
#guard progOf ("buf A[2]\ntwice(A)\ndef twice(B) { one(B)\n  one(B) }\ndef one(C) { C[0] := 1 }")
     == progOf "buf A[2]\nA[0] := 1\nA[0] := 1"

-- a loop variable shadows a parameter of the same name, as it would a `const`
#guard progOf ("def f(i) { for i in 2 { [i] := 1 } }\nf(9)")
     == progOf "[0] := 1\n[1] := 1"

-- the same call in both threads of a fork: `wfB` decides the expansion, and knows nothing of `def`
private def forkedCalls : String :=
  sqDef ++ "parallel { square(A, 0) } | { square(A, 1) }"

#guard (ofString forkedCalls).toOption.all (fun c => ParProg.wfB c.prog)
#guard roundTrips forkedCalls

-- and a fork whose threads touch one cell is refused, `def` or no `def`
#guard (ofString (sqDef ++ "parallel { square(A, 0) } | { square(A, 0) }")).toOption.all
  (fun c => !ParProg.wfB c.prog)

/-! ## Hygiene is what lets the pass fork two calls

`noRegFlow` refuses to split a chain whose statements share a register (`docs/autopar.md`), so three
calls that all wrote the body's `%v` would be sequential by construction. Each call's registers are
its own, so the pass puts the three in one fork. -- ref: `docs/prl.md` § Hygiene -/

private def threeCalls : String :=
  "def step(Out, In, i) { %v := In[i]\n  Out[i] := %v + 1 }\n" ++
  "buf A[3] = 1, 2, 3\nbuf B[3] = zeros\nstep(B, A, 0)\nstep(B, A, 1)\nstep(B, A, 2)"

#guard forkSizes threeCalls == some [3]
#guard (ofString threeCalls).toOption.all (fun c => ParProg.wfB (ParProg.autoPar c.prog))

/-! ## An `assert` is two programs

The claim compiles the file twice, with each side's body written out where the `assert` stands.
Everything else is shared, which is what gives the two programs one initial heap — the gate below
is that the declarations come out identical, not merely equivalent. -- ref: `docs/equivalence.md` -/

private def claimOf (src : String) : Option Claim := (ofString src).toOption.bind (·.claim)

private def twoSorts : String :=
  "def up(A) { %x := A[0]\n  %y := A[1]\n  if %x > %y { A[0] := %y\n  A[1] := %x } else { A[0] := %x\n  A[1] := %y } }\n" ++
  "def down(A) { %p := A[1]\n  %q := A[0]\n  if %p < %q { A[0] := %p\n  A[1] := %q } else { A[0] := %q\n  A[1] := %p } }\n" ++
  "buf A[2] = 2, 1\nassert up(A) == down(A) on A"

-- the two sides, named, and the cells they are compared on
#guard (claimOf twoSorts).map (fun c => (c.left, c.right, c.bufs, c.cells))
         == some ("up", "down", ["A"], [0, 1])
-- two orderings of one comparison: different programs, same answer
#guard (ofString twoSorts).toOption.all (fun c => c.prog != c.other)
#guard (ofString twoSorts).toOption.all (fun c =>
         ParProg.agreeB c.compared c.prog c.other (fun _ => 0) c.layout.state)

-- both compilations place memory identically, so `layout.state` is one heap and not two
#guard (ofString twoSorts).toOption.all (fun c => c.layout.bufs.map Placed.base == [0])

-- a file with no claim reads `other` as its own program, so every accessor is total
#guard (ofString "buf A[2]\nA[0] := 1").toOption.all (fun c => c.prog == c.other)
#guard (ofString "buf A[2]\nA[0] := 1").toOption.all (fun c => c.compared == [])

-- `on` omitted compares every live buffer, in declaration order
#guard (claimOf "def f(A, B) { A[0] := 1 }\nbuf A[2]\nbuf B[1]\nassert f(A, B) == f(A, B)").map
         (fun c => (c.bufs, c.cells)) == some (["A", "B"], [0, 1, 2])
-- and a freed buffer is not among them
#guard (claimOf "def f(A) { A[0] := 1 }\nbuf A[2]\nbuf B[1]\nfree B\nassert f(A) == f(A)").map
         (fun c => c.bufs) == some ["A"]

/-! ## `assertParSeq` — the same claim, with the register file in it

The keyword is the only difference in the surface, and the strength is the only difference in the
`Claim`. What it adds is `regs`: both sides' *written* registers, derived rather than named, and a
fork writes none the parent can see. -- ref: `docs/equivalence.md` § What `assertParSeq` adds -/

private def strongSrc : String :=
  "def up(A) { %x := A[0]\n  A[0] := %x }\ndef dn(A) { %x := A[0]\n  %z := %x + 1\n  A[0] := %x }\n" ++
  "buf A[1] = 5\nassertParSeq up(A) == dn(A) on A"

private def heapSrc : String :=
  "def up(A) { %x := A[0]\n  A[0] := %x }\ndef dn(A) { %x := A[0]\n  %z := %x + 1\n  A[0] := %x }\n" ++
  "buf A[1] = 5\nassert up(A) == dn(A) on A"

-- the keyword is recorded, and it is the only thing the two files differ in
#guard (claimOf strongSrc).map (fun c => c.strength) == some .parSeq
#guard (claimOf heapSrc).map (fun c => c.strength) == some .heap
#guard (claimOf strongSrc).map (fun c => (c.left, c.right, c.bufs, c.cells))
         == (claimOf heapSrc).map (fun c => (c.left, c.right, c.bufs, c.cells))

-- a `.heap` claim compares no register at all; a `.parSeq` claim compares both sides' writes
#guard (claimOf heapSrc).map (fun c => c.regs) == some []
#guard (claimOf strongSrc).map (fun c => c.regs.length) == some 2

-- the register the second side writes and the first does not is what separates the two keywords:
-- every compared cell agrees, so the heap claim holds and the stronger one does not
#guard (ofString strongSrc).toOption.all (fun c =>
         ParProg.agreeB c.compared c.prog c.other (fun _ => 0) c.layout.state)
#guard (ofString strongSrc).toOption.all (fun c =>
         !ParProg.agreeParSeqB c.compared c.comparedRegs c.prog c.other (fun _ => 0)
            c.layout.state)
#guard (ofString heapSrc).toOption.all claimHolds
#guard (ofString strongSrc).toOption.all (fun c => !claimHolds c)

-- a fork's registers are not compared: they are discarded at the join
#guard (claimOf ("def f(A) { parallel { %u := A[0]\n  A[0] := %u } | { A[1] := 1 } }\n" ++
                 "buf A[2]\nassertParSeq f(A) == f(A) on A")).map (fun c => c.regs) == some []

/-! ## A claim that does not hold

The two sides below differ in the cell they write, and `agreeB` says so. This is the anti-vacuity
gate on the claim: a check that accepted every pair of programs would decide nothing. -/

private def disagree : String :=
  "def one(A) { A[0] := 1 }\ndef two(A) { A[0] := 2 }\nbuf A[1]\nassert one(A) == two(A) on A"

#guard (ofString disagree).toOption.all (fun c =>
         !ParProg.agreeB c.compared c.prog c.other (fun _ => 0) c.layout.state)
#guard (ofString disagree).toOption.all (fun c =>
         ParProg.disagreeOn c.compared c.prog c.other (fun _ => 0) c.layout.state == [0])
-- the file compiles: a false claim is a verdict about the program, not a compile error
#guard (ofString disagree).toOption.isSome

/-! ## What is rejected -/

private def rejected (src : String) : Bool := (ofString src).toOption.isNone

-- a register in a bare address: no array to confine it to
#guard rejected "[%0] := 1"
-- a `def` that calls itself, directly or through a chain
#guard rejected "def f(x) { f(x) }\nf(0)"
#guard rejected "def a(x) { b(x) }\ndef b(x) { a(x) }\na(0)"
-- the wrong number of arguments, and the wrong kind
#guard rejected "def f(A, i) { A[i] := 1 }\nbuf A[2]\nf(A)"
#guard rejected "def f(%s, A) { %s := A[0] }\nbuf A[2]\nf(1, A)"
#guard rejected "def f(A, i) { A[i] := 1 }\nbuf A[2]\nf(%r, 0)"
-- a value where the body names cells with it
#guard rejected "def f(A, i) { A[i] := 1 }\nbuf A[2]\nf(3, 0)"
-- a call to a name no `def` gives, in a body as at the top level
#guard rejected "buf A[2]\ng(A, 0)"
#guard rejected "def f(A) { g(A) }\nbuf A[2]\nf(A)"
-- a declaration, a `free`, an `input` or a nested `def` in a body
#guard rejected "def f(n) { buf B[n] = zeros }\nf(2)"
#guard rejected "def f(n) { const k = n }\nf(2)"
#guard rejected "def f(A) { free A }\nbuf A[2]\nf(A)"
#guard rejected "def f(A) { %v := input\n A[0] := %v }\nbuf A[2]\nf(A)"
#guard rejected "def f(A) { def g(B) { B[0] := 1 } }\nbuf A[2]\nf(A)"
#guard rejected "buf A[2]\nfor i in 2 { def g(B) { B[0] := 1 } }"
-- two `def`s of one name, and a slice in a body with a parameter's name
#guard rejected "def f(A) { A[0] := 1 }\ndef f(A) { A[1] := 1 }\nbuf A[2]\nf(A)"
#guard rejected "def f(A) { slice A = A[0..1] }\nbuf A[2]\nf(A)"
-- more than one `assert`, or one anywhere but the top level
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nassert f(A) == f(A)\nassert f(A) == f(A)"
#guard rejected "def f(A) { A[0] := 1 }\ndef g(A) { assert f(A) == f(A) }\nbuf A[2]\ng(A)"
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nfor i in 2 { assert f(A) == f(A) }"
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nparallel { assert f(A) == f(A) } | { A[1] := 1 }"
-- `assertParSeq` is a reserved word, and the two keywords do not shadow each other
#guard rejected "buf assertParSeq[2]\nassertParSeq[0] := 1"
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nassertParSeq f(A) f(A) on A"
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nassertParSeq f(A) == f(A)\nassert f(A) == f(A)"
-- an `assert` side that is not a call, and one missing its `==`
#guard rejected "buf A[2]\nassert A[0] == A[1] on A"
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nassert f(A) f(A) on A"
-- an `on` naming something that is not a live buffer
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nassert f(A) == f(A) on T"
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nconst k = 1\nassert f(A) == f(A) on k"
-- an `assert` side the usual call checks refuse
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nassert f(A) == g(A) on A"
#guard rejected "def f(A) { A[0] := 1 }\nbuf A[2]\nassert f(A, 1) == f(A) on A"
-- `assert` and `on` are reserved words, so neither is a buffer name
#guard rejected "buf assert[2]"
#guard rejected "buf on[2]"
-- `def` is a reserved word, so it is not a buffer name
#guard rejected "buf def[2]"
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
-- a `synchronize` inside a thread: threads of one fork have no barrier between them
#guard rejected "buf A[4]\nparallel { synchronize } | { A[0] := 1 }"
#guard rejected "buf A[4]\nparfor i in 2 { synchronize }"
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
-- a synchronize in a `for`, `if` or `while` body is fine: those are spliced into the chain
#guard !rejected "buf A[4]\nfor i in 2 { A[i] := 1\nsynchronize }"
#guard !rejected "buf A[4]\nif 1 { A[0] := 1\nsynchronize } else { A[1] := 2 }"
#guard !rejected "paralever {\n  [0] := 3;\n  parallel { [1] := 1 } | { [2] := 2 }\n}"

/-! ## `let` is `buf` with the shape read off the initializer

-- ref: `docs/prl.md` § Variables -/

private def printOf (src : String) : Option String := (ofString src).toOption.map toPrl

/-- `printOf` with a line of standard input, for the one declaration that reads it. -/
private def printOf' (src stdin : String) : Option String :=
  (ofString src stdin).toOption.map toPrl

-- a single value is a scalar, so the name alone is the address
#guard printOf "let a = 1\n%t := a\na := %t + 1" == printOf "buf a = 1\n%t := a\na := %t + 1"
-- a string takes one cell per UTF-8 byte, with no `str` keyword needed
#guard printOf "let m = \"hi\"" == printOf "buf m[2] = str \"hi\""
#guard printOf "let m = \"hé\"" == printOf "buf m[3] = str \"hé\""
-- a list takes one cell per value
#guard printOf "let xs = [3, 1, 4]" == printOf "buf xs[3] = 3, 1, 4"
-- a bare string literal is a `str` initializer under `buf` too, as `Coe String Init` makes it in Lean
#guard printOf "buf m[2] = \"hi\"" == printOf "buf m[2] = str \"hi\""

-- the initializers that fit any size and fix none
#guard rejected "let a = zeros"
#guard rejected "let a = ones"
#guard rejected "let a = eye"
#guard rejected "let a = arange"
#guard rejected "let a = full 3"
#guard rejected "let a = input str"
-- `input` is one value, so it is a scalar — read with the stream supplied, as `prl_file` cannot
#guard printOf' "let a = input" "7" == printOf "buf a = 7"
-- reserved, like every other keyword
#guard rejected "let let = 1"
#guard rejected "buf let[2]"
-- and placed like any declaration
#guard rejected "buf o[2] = zeros\nparfor i in 2 { let a = 1\no[i] := 1 }"

/-! ## Slices, `#`, and `copy`

A slice is a *view*: the cells are the buffer's and nothing is copied, so the bound a computed
subscript gets is the slice's cells rather than the whole buffer's. That is what turns a
per-thread computed index from an over-approximation into an independence proof.

-- ref: `docs/prl.md` § Slices; `Paralever/Lib/ArrRef.lean` -/

/-- `wfB` on a compiled source, or `none` when it does not compile. -/
private def wfOf (src : String) : Option Bool :=
  (ofString src).toOption.map (fun c => ParProg.wfB c.prog)

private def quarters : String :=
  "buf s[16] = arange\nparfor t in 4 {\n  slice mine = s[t*4 .. t*4+4]\n  %p := t + 1\n\
   %c := mine[%p]\n  mine[%p] := %c + 100\n} :: \"quarters\""

/-- The same program with the index into the whole buffer. Each thread's footprint is then all 16
cells, so `wfB` refuses a program that is in fact independent. -/
private def whole : String :=
  "buf s[16] = arange\nparfor t in 4 {\n  %p := t * 4 + t + 1\n\
   %c := s[%p]\n  s[%p] := %c + 100\n} :: \"whole\""

-- the headline: a slice is what makes a computed per-thread index provable
#guard wfOf quarters == some true
#guard wfOf whole == some false

-- a computed subscript through a slice is bounded by the slice, and prints back as the range
#guard ((ofString quarters).toOption.map toPrl).any (fun t => (t.splitOn "s[4..8][%0]").length > 1)
#guard roundTrips quarters

-- `#A` is the cell count, folded to a literal: legal in both an address and a value
#guard printOf "buf A[6]\nbuf o = 0\no := #A" == printOf "buf A[6]\nbuf o = 0\no := 6"
#guard printOf "buf A[2, 3]\n%t := #A" == printOf "buf A[2, 3]\n%t := 6"
#guard printOf "buf A[8]\nslice h = A[2..5]\n%t := #h" == printOf "buf A[8]\n%t := 3"
-- a sigil, not a word, so `len`, `size` and `cells` stay available as names
#guard (ofString "const len = 2\nbuf A[2]\nA[0] := len").isOk
#guard (ofString "buf size[2]\nsize[0] := 1").isOk
#guard (ofString "buf cells[2]\ncells[0] := 1").isOk

-- `copy` is sugar: it becomes a `for`, so it prints as the stores it performed
#guard printOf "let m = [7, 8]\nbuf d[2]\ncopy d from m"
         == printOf "let m = [7, 8]\nbuf d[2]\nfor i in 2 { %t := m[i]\nd[i] := %t }"
-- a range on either side, and `A` alone is all of A
#guard printOf "buf a[4] = arange\nbuf b[4]\ncopy b[1..3] from a[2..4]"
         == printOf "buf a[4] = arange\nbuf b[4]\nfor i in 2 { %t := a[2..4][i]\nb[1..3][i] := %t }"
-- the register and loop variable `copy` uses begin with a digit, so no program can collide with one
#guard (ofString "buf a[2]\nbuf b[2]\n%0t := 1").toOption.isNone

-- a slice is refused where it is not inside its buffer, and where it is not indexed
#guard rejected "buf s[8]\n%t := s[4..2][0]"
#guard rejected "buf s[8]\n%t := s[0..9][0]"
#guard rejected "buf s[8]\n%t := s[3..3][0]"
#guard rejected "buf s[8]\n%t := s[0..4][5]"
#guard rejected "buf s[8]\ns[0..4] := 1"
#guard rejected "buf s[8]\nslice h = s[0..4]\nslice h = s[4..8]\n%t := h[0]"
#guard rejected "buf s[8]\nslice h = s[0..4]\n%t := h[1, 1]"
#guard rejected "buf s[8]\nbuf d[8]\ncopy d s"
#guard rejected "buf s[8]\ncopy s from s[0]"
-- `hi` left off is the buffer's end, and a slice of a slice keeps the root
#guard printOf "buf s[8]\nslice h = s[6..]\n%t := h[1]" == printOf "buf s[8]\n%t := s[7]"
#guard printOf "buf s[8]\nslice h = s[2..6]\nslice g = h[1..3]\n%t := g[0]"
         == printOf "buf s[8]\n%t := s[3]"
-- a view of a freed buffer leaves scope with it
#guard rejected "buf s[8]\nslice h = s[0..4]\nfree s\n%t := h[0]"
-- and a `slice` is the one declaration a thread may make, because it places no cells
#guard (ofString "buf o[2]\nparfor i in 2 { slice h = o[i..i+1]\nh[0] := 1 }").isOk
#guard rejected "buf o[2]\nparfor i in 2 { const k = 1\no[i] := 1 }"

/-! ## A bare name before an operator is an expression, not a load

`%r := n + 1` read `n` as an address and then could not continue, so a `const` or a loop variable
could not be computed with at all. The rule the reader enforces is about *loads*
(`docs/block-ir.md`), and a `const` is not one — only the environment knows which a bare name is. -/

-- the `const` folds to its value, and the expression around it is the one that was written
#guard printOf "const n = 4\nbuf A[1]\n%p := n + 1\nA[0] := %p"
         == printOf "buf A[1]\n%p := 4 + 1\nA[0] := %p"
#guard printOf "const n = 4\nbuf A[1]\n%p := n\nA[0] := %p"
         == printOf "buf A[1]\n%p := 4\nA[0] := %p"
#guard printOf "const n = 4\nbuf A[1]\n%p := n - 1\nA[0] := %p"
         == printOf "buf A[1]\n%p := 4 - 1\nA[0] := %p"
#guard printOf "buf A[2]\nfor i in 2 { %p := i * 2\nA[i] := %p }"
         == printOf "buf A[2]\n%p := 0 * 2\nA[0] := %p\n%p := 1 * 2\nA[1] := %p"
-- and the values are right, not merely the spelling
#guard (ofString "const n = 4\nbuf A[1]\n%p := n + 1\nA[0] := %p").toOption.map
         (fun c => heapAfter c false (c.layout.at "A" [0])) == some (Paralever.Val.int 5)
-- a subscripted load in an expression is still refused, which is the rule that matters
#guard rejected "buf A[1]\n%p := A[0] + 1"
#guard rejected "buf A[1]\n%p := [0] + 1"
-- and a scalar buffer with nothing after it is still a load
#guard printOf "buf a = 7\n%p := a" == printOf "buf a = 7\n%p := a"

/-! ## The editor grammar carries every keyword

`web/js/site.js` highlights `.prl` on the published site from a list written by hand, and
`Lang.keywords` is the one the reader uses. A word in the reader's list and not the site's would be
printed as a name. -/

private def siteJs : String := include_str "../web/js/site.js"

/-- Whether the site grammar lists `w` as a whole word. The lists are space-separated inside
string literals, so a word sits at the start, the middle or the end of one. -/
private def listed (w : String) : Bool :=
  (siteJs.splitOn ("\"" ++ w ++ " ")).length > 1 ||
  (siteJs.splitOn (" " ++ w ++ " ")).length > 1 ||
  (siteJs.splitOn (" " ++ w ++ "\"")).length > 1

#guard keywords.all listed

end Test.Lang
