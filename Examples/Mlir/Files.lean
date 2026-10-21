import MLIR.Corpus
import Lang.Report

namespace Paralever.Examples.Mlir
open Paralever Paralever.MLIR

/-! ## 1 · An MLIR file, lowered while this file elaborates

`mlir_prog` parses MLIR generic form and lowers it to a `ParProg` at elaboration time, exactly as
`prl_file` does for `.prl`. No command line, and `by decide` below sees a program literal.

`doall-no.mlir` is an `affine.parallel` over `C[i] := A[i] + B[i]`. An `affine.map` already *is* a
footprint function, which is why the lowering is a translation rather than an analysis. -/

-- ANCHOR: site-mlir-doall
def doall : Lang.Compiled := ⟨mlir_layout "doall-no.mlir", mlir_prog "doall-no.mlir", [], []⟩
-- ANCHOR_END: site-mlir-doall

-- the eight iterations become eight threads of one fork, printed back in the surface language
/--
info: buf A[8] = 1, 2, 3, 4, 5, 6, 7, 8
buf B[8] = 10, 20, 30, 40, 50, 60, 70, 80
buf C[8]

parallel {
  %0 := A[0]
  %1 := B[0]
  C[0] := (%0 + %1)
} | {
  %0 := A[1]
  %1 := B[1]
  C[1] := (%0 + %1)
} | {
  %0 := A[2]
  %1 := B[2]
  C[2] := (%0 + %1)
} | {
  %0 := A[3]
  %1 := B[3]
  C[3] := (%0 + %1)
} | {
  %0 := A[4]
  %1 := B[4]
  C[4] := (%0 + %1)
} | {
  %0 := A[5]
  %1 := B[5]
  C[5] := (%0 + %1)
} | {
  %0 := A[6]
  %1 := B[6]
  C[6] := (%0 + %1)
} | {
  %0 := A[7]
  %1 := B[7]
  C[7] := (%0 + %1)
}
-/
#guard_msgs in
#eval IO.println (Lang.print doall)

/--
info: doall-no.mlir
  memory    A[8] @0, B[8] @8, C[8] @16  (24 cells)
  reads     {A[0], B[0], A[1], B[1], A[2], B[2], A[3], B[3], A[4], B[4], … +6 more}
  writes    {C[0], C[1], C[2], C[3], C[4], C[5], C[6], C[7]}
  threads   8
  rounds    3 parallel, 24 sequential
  verdict   independent — par = seq under every schedule (wfB = true)
-/
#guard_msgs in
#eval IO.println (Lang.checkReport "doall-no.mlir" doall)

/--
info: heap after the run — a .prl program has no print statement, so this is its output
24 cells in 3 buffers, addressed 0 to 23
NAME [dims] @base — the buffer's first cell in that flat heap; cells row-major from there

A [8] @0  [1, 2, 3, 4, 5, 6, 7, 8]
B [8] @8  [10, 20, 30, 40, 50, 60, 70, 80]
C [8] @16  [11, 22, 33, 44, 55, 66, 77, 88]
-/
#guard_msgs in
#eval IO.println (Lang.runReport doall false)

-- ANCHOR: site-mlir-theorem
theorem doall_ok (ρ : Regs) (σ : State) :
    ParSeqEq (Lang.ParProg.execPar doall.prog ρ) (Lang.ParProg.execSeq doall.prog ρ) σ :=
  Lang.ParProg.par_seq_eq (by decide) ρ σ
-- ANCHOR_END: site-mlir-theorem

/-! ## 2 · A file that is refused

`reduction-yes.mlir` is the missing-reduction-clause bug: every iteration accumulates into the same
cell. `wfB` refuses it, so no instance of the theorem exists — and the refusal is not merely a
verdict, because the two readings really do compute different numbers. The ℚ reference interpreter
takes the canonical schedule and gets 36; the threaded run of the lowered program does not. -/

#guard Corpus.refOf "reduction-yes" "sum" == some [.int 36]
#guard Corpus.refOf "reduction-yes" "sum" != Corpus.progOf "reduction-yes" "sum"

example : Lang.ParProg.wfB (mlir_prog "reduction-yes.mlir") = false := by decide

/-! ## 3 · All seven pilots

Seven hand-written files in this directory, each named with the verdict it is expected to get, in
DataRaceBench's `-yes`/`-no` convention. `Corpus.summary` is the whole gate in one string; every
number in it is also a `#guard` in `MLIR/Corpus.lean`, so a regression fails the build. -/

/--
info: expressible    7/7
unsupported    []
confusion      tp=3 fp=0 fn=0 tn=4
precision gap  []
over-approx    [indirect-yes]
round trip     true

doall-no  label=race-free  wfB=true  exact=true  sites=0  fp=exact  values=Int  agrees=(some true)
antidep-yes  label=racy      wfB=false  exact=false  sites=6  fp=exact  values=Int  agrees=(some true)
reduction-yes  label=racy      wfB=false  exact=false  sites=7  fp=exact  values=Int  agrees=(some false)
reduction-split-no  label=race-free  wfB=true  exact=true  sites=0  fp=exact  values=Int  agrees=(some true)
stencil-f64-no  label=race-free  wfB=true  exact=true  sites=0  fp=exact  values=ℚ only  agrees=(some false)
nested-2d-no  label=race-free  wfB=true  exact=true  sites=0  fp=exact  values=Int  agrees=(some true)
indirect-yes  label=racy      wfB=false  exact=false  sites=3  fp=bound  values=Int  agrees=(some false)
-/
#guard_msgs in
#eval IO.println Corpus.summary

end Paralever.Examples.Mlir
