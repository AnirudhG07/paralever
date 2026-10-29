import Lang.Load
import Lang.Report
import MLIR.Emit
import MLIR.Parse
import Lang.Core.Cost

/-! # The front ends carry a nest

`Test/Loop.lean` gates the constructor on nests written by hand. This gates the two routes that
*produce* them: a `.prl` `for`/`parfor` above the unrolling threshold, and MLIR's `affine.for` and
`affine.parallel`.

Three things are gated, because each is a separate claim.

* **The threshold from both sides.** Below it nothing changes, which is what keeps every pinned
  term in `Examples/` and `Test/` the shape it has.
* **What the recognizer refuses.** A fallback is not an error — the unrolled route still accepts
  the program — so a refusal is only visible as "not rolled", and a gate is the only way to know
  the recognizer refused for the reason claimed rather than by accident.
* **The nest the front end built is the nest the theory decides.** `rolled.prl`'s program is read
  through `prl_file`, so `decide` sees a `LoopNest` literal and never the reader.

Rationale: `docs/loops.md` § Rolling. -/

namespace Paralever.Test.Roll
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-! ## Whether a program is one nest -/

-- `ParProg.block [s] = s`, so a file holding one nest *is* the nest
private def isNest : ParProg → Bool
  | .loop _            => true
  | .label _ (.loop _) => true
  | _                  => false

private def nestOf? : ParProg → Option LoopNest
  | .loop n            => some n
  | .label _ (.loop n) => some n
  | _                  => none

private def rolls (src : String) : Bool :=
  match ofString src with
  | .error _ => false
  | .ok c    => isNest c.prog

private def accepts (src : String) : Bool :=
  match ofString src with
  | .error _ => false
  | .ok c    => c.prog.wfB

private def threads (src : String) : Nat :=
  match ofString src with
  | .error _ => 0
  | .ok c    => c.prog.threadCount

/-! ## The threshold, from both sides

`Roll.maxUnroll` is a strict lower bound: a nest of exactly that many points still unrolls. Both
sides are gated on the same text with one number changed, so the boundary is measured rather than
asserted. -/

#guard Roll.maxUnroll == 128

private def elemwise (n : String) : String :=
  "buf A[" ++ n ++ "]\nbuf C[" ++ n ++ "]\nparfor i in " ++ n ++
    " {\n  %x := A[i]\n  C[i] := %x\n}\n"

#guard !rolls (elemwise "128")        -- 128 points: unrolled, as every existing program is
#guard rolls (elemwise "129")         -- 129: rolled
#guard accepts (elemwise "128") && accepts (elemwise "129")
#guard threads (elemwise "129") == 129

/-! ## A nest the front end built, and what the certificate says about it

`parfor i { for j { C[i,j] := A[i,j] + B[i,j] } }` at 12 x 12. The write mentions the sequential
coordinate and is still accepted, which is the scaled reading of `outerInjective`. -/

private def src (ls : List String) : String := String.intercalate "\n" ls ++ "\n"

private def two : String := src
  [ "buf A[200, 200]", "buf B[200, 200]", "buf C[200, 200]"
  , "parfor i in 200 {", "  for j in 200 {"
  , "    %a := A[i, j]", "    %b := B[i, j]", "    C[i, j] := %a + %b", "  }", "}" ]

#guard rolls two
#guard accepts two
-- 40 000 points, and the term is the size it would be at 2 x 2: four statements and six numbers
#guard (nestOf? (match ofString two with | .ok c => c.prog | .error _ => .synchronize)).map
          (fun n => (n.sizes, n.parDepth, n.body.length))
        == some ([200, 200], 1, 3)
#guard threads two == 200

/-! ### gemm, rolled and accepted at two forked depths

The same text with `parfor`/`for` swapped at the second level. Both are accepted, and the pair is
the reason the certificate's forked-injectivity clause is scaled rather than absolute. -/

private def gemm (second : String) : String := src
  [ "buf A[200, 200]", "buf B[200, 200]", "buf C[200, 200]"
  , "parfor i in 200 { " ++ second ++ " j in 200 { for k in 200 {"
  , "  %a := A[i, k]", "  %b := B[k, j]", "  %c := C[i, j]"
  , "  C[i, j] := %c + %a * %b", "} } }" ]

#guard rolls (gemm "parfor") && accepts (gemm "parfor")
#guard rolls (gemm "for")    && accepts (gemm "for")
#guard threads (gemm "parfor") == 40000
#guard threads (gemm "for") == 200

/-! ## The paired negative

`A[i+1] := A[i] + 1` is the loop-carried dependence, and it is rolled either way — the recognizer's
job is to build the nest, not to judge it. Forked it is refused; sequential it is accepted with one
thread, which is what `parDepth = 0` means. -/

private def carried (kw : String) : String := src
  [ "buf A[400]", kw ++ " i in 399 {", "  %x := A[i]", "  A[i + 1] := %x + 1", "}" ]

#guard rolls (carried "parfor") && !accepts (carried "parfor")
#guard rolls (carried "for")    && accepts (carried "for")
#guard threads (carried "for") == 1

-- a transposed write is refused, and that is this route's false refusal: `B[j,i]` is injective
-- over the box, so the unrestricted statement is true. Gated so the count is measured.
private def transposed : String := src
  [ "buf A[200, 200]", "buf B[200, 200]"
  , "parfor i in 200 { for j in 200 {", "  %x := A[i, j]", "  B[j, i] := %x", "} }" ]

#guard rolls transposed
#guard !accepts transposed

/-! ## What the recognizer refuses, and falls back on

Each of these is a program the unrolled route still compiles — a fallback costs precision, never
correctness. The point of gating them is that "not rolled" has a stated cause. -/

-- a computed subscript: `A[%r]` is heap-dependent, which is `scatter.prl`'s shape
#guard !rolls (src ["buf A[200]", "buf I[200]", "%r := I[0]",
                    "parfor i in 200 {", "  A[%r] := 1", "}"])
-- a `parfor` *under* a `for`: `parDepth` is a prefix, so this is not one nest
#guard !rolls (src ["buf A[200, 200]", "for i in 200 { parfor j in 200 {",
                    "  A[i, j] := 1", "} }"])
-- an `if` in the body: `NestStmt` has no branch for an access to hide behind
#guard !rolls (src ["buf A[200]", "parfor i in 200 {", "  if 1 {", "    A[i] := 1", "  }", "}"])
-- a non-rectangular nest: the sizes are folded before the loop variables are bound
#guard !rolls (src ["buf A[200, 200]", "parfor i in 200 { for j in i {",
                    "  A[i, j] := 1", "} }"])
-- a nest whose body forks: a nest's body is straight-line
#guard !rolls (src ["buf A[200]", "parfor i in 200 {", "  parallel {", "    A[i] := 1",
                    "  } | {", "  }", "}"])

/-! ## `par_seq_eq`, on the nest the front end built

`prl_file` quotes the compiled program, so `decide` sees the `LoopNest` and `nestIndepB` decides
three subscript maps — not 144 threads. -/

def rolledFile : Compiled := prl_file "../Examples/Language/rolled.prl"

#guard isNest rolledFile.prog
#guard rolledFile.prog.wfB
#guard rolledFile.prog.threadCount == 12

/-- **The equivalence, through the front end.** -/
example (ρ : Regs) (σ : State) :
    ParSeqEq (execPar rolledFile.prog ρ) (execSeq rolledFile.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- …and the cost ordering, from the same `Bool`. -/
example (ρ : Regs) (σ : State) :
    time (execPar rolledFile.prog ρ) σ ≤ time (execSeq rolledFile.prog ρ) σ :=
  time_le (by decide) ρ σ

/-! ## MLIR: `affine.for` is sequential, `affine.parallel` forks

The one bit the two ops differ in is `parDepth`, and a rolled nest keeps it instead of discarding
the loop and emitting its iterations. -/

open Paralever.MLIR

private def mlirNest (outer : List String) : String := src
  ([ "module {"
   , "  memref.global \"private\" @A : memref<20x20xi64> = dense<3>"
   , "  memref.global \"private\" @C : memref<20x20xi64> = dense<0>"
   , "  func.func @main() {"
   , "    %A = memref.get_global @A : memref<20x20xi64>"
   , "    %C = memref.get_global @C : memref<20x20xi64>" ] ++ outer ++
   [ "      %0 = affine.load %A[%i, %j] : memref<20x20xi64>"
   , "      affine.store %0, %C[%i, %j] : memref<20x20xi64>"
   , "      }", "    }", "    return", "  }", "}" ])

private def seqNest : String :=
  mlirNest ["    affine.for %i = 0 to 20 {", "      affine.for %j = 0 to 20 {"]
private def parNest : String :=
  mlirNest ["    affine.parallel (%i) = (0) to (20) {", "      affine.for %j = 0 to 20 {"]

private def mlirRolls (src : String) : Bool :=
  match lowerText src with
  | .error _ => false
  | .ok lw   => isNest lw.prog

private def mlirDepth (src : String) : Option Nat :=
  match lowerText src with
  | .error _ => none
  | .ok lw   => (nestOf? lw.prog).map (fun n => n.parDepth)

#guard mlirRolls seqNest && mlirRolls parNest
#guard mlirDepth seqNest == some 0        -- affine.for: one thread, Bernstein has nothing to say
#guard mlirDepth parNest == some 1        -- affine.parallel: the outer level forks
#guard (match lowerText parNest with | .ok lw => lw.prog.wfB | .error _ => false)
#guard (match lowerText parNest with | .ok lw => lw.prog.threadCount == 20 | .error _ => false)

-- the sizes and the body survive the read, and the body is three ops shorter than its MLIR
#guard (match lowerText parNest with
        | .ok lw => (nestOf? lw.prog).map (fun n => (n.sizes, n.body.length))
        | .error _ => none) == some ([20, 20], 2)

/-! ### Out again

A nest emits as `affine.parallel` over its forked prefix wrapping one `affine.for` per sequential
level, and `emitRoundTrips` compares memory, footprint, verdict and heap — not the tree, because
registers are not SSA values. -/

#guard (match lowerText parNest with
        | .ok lw => emitRoundTrips lw.layout lw.prog
        | .error _ => false)
#guard (match lowerText seqNest with
        | .ok lw => emitRoundTrips lw.layout lw.prog
        | .error _ => false)

-- and the emitted text says `affine.parallel`, so the fork is not lost on the way out
#guard (match lowerText parNest with
        | .ok lw =>
            match emitText lw.layout lw.prog with
            | .ok txt => (txt.splitOn "affine.parallel").length == 2
            | _       => false
        | .error _ => false)

end Paralever.Test.Roll
