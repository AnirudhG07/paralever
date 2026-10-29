import Lang.Core.Exec
import Lang.Core.Cost
import Lang.Report

/-! # The rolled nest, gated

`Paralever/Theory/Nest.lean` decides the certificate; `Test/Nest.lean` gates that decision. This
file gates the *constructor*: that a nest runs, that `wfB` accepts and refuses the right nests at
PolyBench sizes, that `par_seq_eq` instantiates at a rolled nest, and that the loop-carried case
is refused with its conflict exhibited.

Rationale: `docs/loops.md`. -/

namespace Paralever.Test.Loop
open Paralever Paralever.Box Paralever.Nest Paralever.Lang Paralever.Lang.ParProg

/-! ## A nest that runs

`C[i,j] := A[i,j] + B[i,j]` over a 4×4 box, both levels forked: 16 threads, one point each. Small
enough that the heap can be checked cell by cell. -/

private def N : Nat := 4
private def cells : Nat := N * N

private def Aij : AffAccess := { base := 0,         size := cells, coeffs := [N, 1], off := 0 }
private def Bij : AffAccess := { base := cells,     size := cells, coeffs := [N, 1], off := 0 }
private def Cij : AffAccess := { base := 2 * cells, size := cells, coeffs := [N, 1], off := 0 }

private def addNest : LoopNest :=
  { ivs := [0, 1], sizes := [N, N], lo := [0, 0], step := [1, 1], parDepth := 2,
    body := [ .rd 10 Aij, .rd 11 Bij, .wr Cij (.add (.reg 10) (.reg 11)) ] }

-- the accesses are **computed** from the body, not declared beside it
#guard addNest.reads  == [Aij, Bij]
#guard addNest.writes == [Cij]
#guard addNest.bodyOps == 3
#guard addNest.threadCount == 16
#guard addNest.threadOps == 3          -- one point per thread, three memory operations
#guard addNest.innerBox == [[]]        -- nothing left to iterate inside a thread
#guard addNest.outerBox.length == 16

#guard wfB (.loop addNest)
#guard stepBound (.loop addNest) == 16 * 3 + 16
#guard threadCount (.loop addNest) == 16
-- a nest forks, so a program containing one is not `parFree`
#guard hasPar (.loop addNest)
-- …and its footprint is the buffer bound, never exact
#guard !footprintExact (.loop addNest)

/-- Cell `l` starts out holding `l`, so `A[i,j] = 4i+j` and `B[i,j] = 16+4i+j`. -/
private def σ0 : State := fun l => .int (l : Int)

-- C[0,0]=0+16, C[0,1]=1+17, C[1,0]=4+20, C[3,3]=15+31
#guard evalTaskSeq (.loop addNest) σ0 [32, 33, 36, 47]
        == [.int 16, .int 18, .int 24, .int 46]
-- and the threaded run agrees, which `runTask_eq_runTaskSeq` proves in general
#guard evalTask (.loop addNest) σ0 [32, 33, 36, 47]
        == evalTaskSeq (.loop addNest) σ0 [32, 33, 36, 47]

/-- **The equivalence, for a rolled nest.** One `decide` on the certificate, no enumeration of the
box. -/
example (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (.loop addNest) ρ) (execSeq (.loop addNest) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- …and the cost comparison from the same `Bool`. -/
example (ρ : Regs) (σ : State) :
    time (execPar (.loop addNest) ρ) σ ≤ time (execSeq (.loop addNest) ρ) σ :=
  time_le (by decide) ρ σ

/-! ## The induction registers carry `lo + step * c`

`Out[i] := %i` over three iterations from `5` by `2`. Nothing in the certificate reads `lo` or
`step`; this is what they are for. -/

private def Out : AffAccess := { base := 0, size := 3, coeffs := [1], off := 0 }

private def strided : LoopNest :=
  { ivs := [0], sizes := [3], lo := [5], step := [2], parDepth := 1,
    body := [ .wr Out (.reg 0) ] }

#guard ivVal 5 2 0 == 5
#guard ivVal 5 2 2 == 9
#guard wfB (.loop strided)
#guard evalTaskSeq (.loop strided) σ0 [0, 1, 2] == [.int 5, .int 7, .int 9]

/-! ## gemm at N = 1000, accepted at `d = 2` and refused at `d = 3`

The same nest, the same declarations; the forked depth is the only difference. The box has 10⁹
points and is never enumerated. -/

private def M : Nat := 1000
private def mcells : Nat := M * M

private def gC : AffAccess := { base := 0,          size := mcells, coeffs := [M, 1, 0], off := 0 }
private def gA : AffAccess := { base := mcells,     size := mcells, coeffs := [M, 0, 1], off := 0 }
private def gB : AffAccess := { base := 2 * mcells, size := mcells, coeffs := [0, 1, M], off := 0 }

private def gemm (d : Nat) : LoopNest :=
  { ivs := [0, 1, 2], sizes := [M, M, M], lo := [0, 0, 0], step := [1, 1, 1], parDepth := d,
    body := [ .rd 10 gC, .rd 11 gA, .rd 12 gB,
              .wr gC (.add (.reg 10) (.mul (.reg 11) (.reg 12))) ] }

#guard (gemm 2).threadCount == 1000000
#guard (gemm 2).threadOps == 4000          -- 1000 values of k, four memory operations each
#guard wfB (.loop (gemm 2))
#guard !wfB (.loop (gemm 3))               -- forking `k` makes `C[i,j]` a shared write

/-- **gemm's equivalence, rolled.** The term is the same size it would be at `N = 4`. -/
example (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (.loop (gemm 2)) ρ) (execSeq (.loop (gemm 2)) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ## The paired negative: a loop-carried dependence

`A[i+1] := A[i] + 1`, the project's standing anti-vacuity case
(`CLAUDE.md` § Anti-vacuity discipline). Refused at every forked depth above one thread, and the
refusal is exhibited rather than asserted: iteration 0's write **is** iteration 1's read. -/

private def Aw : AffAccess := { base := 0, size := N + 1, coeffs := [1], off := 1 }
private def Ar : AffAccess := { base := 0, size := N + 1, coeffs := [1], off := 0 }

private def carried (d : Nat) : LoopNest :=
  { ivs := [0], sizes := [N], lo := [0], step := [1], parDepth := d,
    body := [ .rd 10 Ar, .wr Aw (.add (.reg 10) (.lit 1)) ] }

#guard !wfB (.loop (carried 1))
-- the conflict itself, so the refusal is measured rather than claimed
#guard Aw.addr [0] == Ar.addr [1]
#guard (carried 1).reads == [Ar]
#guard (carried 1).writes == [Aw]

/-! ### …and the same nest run sequentially is accepted

`parDepth = 0` forks one thread, so Bernstein has nothing to say. Without this a sequential
`affine.for` — most of PolyBench — would be refused for carrying a dependence it is allowed to
carry. -/

#guard (carried 0).threadCount == 1
#guard wfB (.loop (carried 0))
#guard evalTaskSeq (.loop (carried 0)) (fun _ => .int 0) [0, 1, 2, 3, 4]
        == [.int 0, .int 1, .int 2, .int 3, .int 4]

example (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (.loop (carried 0)) ρ) (execSeq (.loop (carried 0)) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ## A write that is not row-major in the forked levels

`A[j]` while forking `(i, j)`: every value of `i` writes the same cell, so this is a genuine race
and is refused. Gated so the module's refusals are known to be the ones intended. -/

private def collide : AffAccess := { base := 0, size := cells, coeffs := [0, 1], off := 0 }

private def colliding : LoopNest :=
  { ivs := [0, 1], sizes := [N, N], lo := [0, 0], step := [1, 1], parDepth := 2,
    body := [ .wr collide (.reg 0) ] }

#guard !wfB (.loop colliding)
#guard collide.addr [0, 1] == collide.addr [1, 1]      -- two threads, one cell

end Paralever.Test.Loop
