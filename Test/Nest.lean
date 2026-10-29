import Paralever.Theory.Nest

/-! # The nest certificate, both directions

What `nestIndepB` accepts and what it refuses, at sizes the unrolled route cannot reach: every
`#guard` here is over a box of 10⁶ points and none of them enumerates it.

The refusals are of three kinds and are kept apart on purpose — a loop-carried dependence, a write
that is not injective, and a write that *is* injective but not row-major. Only the first two are
races; the third is imprecision, and it is gated so the number is visible rather than assumed away.

Rationale: `docs/loops.md`. -/

namespace Paralever.Test.Nest
open Paralever Paralever.Box Paralever.Nest

/-! ## The strides of a box -/

#guard strides [1000, 1000] == [1000, 1]
#guard strides [4, 4, 4] == [16, 4, 1]
#guard strides ([] : List Nat) == []
#guard strides [7] == [1]

-- `dotN (strides ns)` is `linBox ns`, which is what `linBox_inj` makes it injective
#guard dotN (strides [6, 7]) [3, 4] == linBox [6, 7] [3, 4]
#guard dotN (strides [4, 4, 4]) [1, 2, 3] == linBox [4, 4, 4] [1, 2, 3]

/-! ## Three buffers of a million cells each

`N = 1000` is PolyBench's standard size, and the box has 10⁶ points. The unrolled route reaches
**one hundred** threads in 19 s (`Examples/Programs/MatMul.lean:267`). -/

private def N : Nat := 1000
private def cells : Nat := N * N
private def rm : List Nat := strides [N, N]

private def A : AffAccess := { base := 0,         size := cells, coeffs := rm, off := 0 }
private def B : AffAccess := { base := cells,     size := cells, coeffs := rm, off := 0 }
private def C : AffAccess := { base := 2 * cells, size := cells, coeffs := rm, off := 0 }

#guard rm == [1000, 1]
#guard A.inBounds [N, N] && B.inBounds [N, N] && C.inBounds [N, N]

-- `C[i,j] := A[i,j] + B[i,j]` — accepted, over a million iterations
#guard nestIndepB [N, N] 2 [A, B] [C]

-- `A[i,j] := A[i,j] + 1` — the read-modify-write of one cell by its own iteration. Bernstein
-- permits it, and it is `mapsDisjoint A A` reducing to `outerInjective`.
#guard nestIndepB [N, N] 2 [A] [A]
#guard mapsDisjoint [N, N] 2 A A

/-! ### Shared reads, which is the clause that lets gemm through

`Arow` reads the same cell from a whole row of iterations. There is no read-versus-read clause, so
total overlap between two reads is accepted — without it a matmul would be refused. -/

private def Arow : AffAccess := { base := 0, size := cells, coeffs := [N, 0], off := 0 }

#guard nestIndepB [N, N] 2 [Arow, Arow] [C]

/-! ## Refused: a loop-carried dependence

`A[i+1] := A[i] + 1`, the case four other modules already encode. Same buffer, same coefficients,
*different* offsets — and that is precisely the clause an earlier draft accepted. The buffer is
`N+1` cells so that `boundsOK` holds and the refusal is about the dependence rather than the
bounds. -/

private def Aw : AffAccess := { base := 0, size := N + 1, coeffs := strides [N], off := 1 }
private def Ar : AffAccess := { base := 0, size := N + 1, coeffs := strides [N], off := 0 }

#guard Aw.inBounds [N] && Ar.inBounds [N]
#guard !nestIndepB [N] 1 [Ar] [Aw]
#guard !mapsDisjoint [N] 1 Aw Ar

/-! ## Refused: a write that collides with itself

`collide` ignores `i`, so `(0,0)` and `(1,0)` both address `base`. This is the **self-pair**: two
distinct iterations performing the same write. An earlier draft wrote `w == w' || …` and skipped
exactly this pair. -/

private def collide : AffAccess := { base := 0, size := 16, coeffs := [0, 1], off := 0 }
private def good    : AffAccess := { base := 0, size := 16, coeffs := strides [4, 4], off := 0 }

#guard collide.inBounds [4, 4]
#guard !mapsDisjoint [4, 4] 2 collide collide
#guard !nestIndepB [4, 4] 2 [] [collide]
-- and the row-major write of the same box is accepted, so the refusal is not about the box
#guard mapsDisjoint [4, 4] 2 good good
#guard nestIndepB [4, 4] 2 [] [good]

/-! ## gemm, accepted at `d = 2` and refused at `d = 3`

The same nest, the same declarations, and the forked depth is the only thing that changes. `C[i,j]`
over the box `(i,j,k)` is written by a thousand iterations of `k`: fork `(i,j)` and those thousand
belong to one thread, so the nest is independent; fork `k` as well and they are a thousand threads
writing one cell, so it is not. The certificate says both.

This pair is what `outerInjective` exists for. A whole-box formulation would not do: `C[i,j]`'s
coefficients are not the stride vector of `(i,j,k)` and never will be. -/

-- `C[i,j] := C[i,j] + A[i,k] * B[k,j]`
private def Cij : AffAccess := { base := 2 * cells, size := cells, coeffs := [N, 1, 0], off := 0 }
private def Aik : AffAccess := { base := 0,         size := cells, coeffs := [N, 0, 1], off := 0 }
private def Bkj : AffAccess := { base := cells,     size := cells, coeffs := [0, 1, N], off := 0 }

#guard Cij.inBounds [N, N, N] && Aik.inBounds [N, N, N] && Bkj.inBounds [N, N, N]
-- `C[i,j]` does not mention `k`, so the sequential level adds nothing and the forked levels are
-- row-major unscaled
#guard innerSpan [N, N, N] 2 Cij == 1
#guard outerInjective [N, N, N] 2 Cij

-- forked over `(i,j)`: accepted. `C` is read and written by the same access, which is the
-- accumulation, and `A` and `B` are read from other buffers.
#guard nestIndepB [N, N, N] 2 [Cij, Aik, Bkj] [Cij]

-- forked over `(i,j,k)` as well: refused, and rightly — `k` is a reduction, and MLIR's
-- `isLoopParallel` declines it too
#guard !nestIndepB [N, N, N] 3 [Cij, Aik, Bkj] [Cij]
#guard !outerInjective [N, N, N] 3 Cij

-- and a write that *does* depend on the sequential level is refused even at `d = 2`: two threads
-- differing only in `j` would both write `A[i,k]`
#guard !nestIndepB [N, N, N] 2 [] [Aik]

/-! ### …and accepted at `d = 1`, where the write does mention a sequential level

`C[i,j]` at `d = 1` is not blind to the sequential coordinates — `j` is one of them — so the
`innerSpan = 1` reading has nothing to say. It is still injective across threads, because thread
`i` owns the `N` consecutive cells `C[i, 0 .. N)` and thread `i+1` owns the next `N`. That is the
scaled reading: the forked level's coefficient is `strides [N] = [1]` times the span `N` the
sequential levels can reach. One clause decides both, which is what makes
`parfor i { for j { … } }` — the shape most of PolyBench is written in — expressible. -/

#guard innerSpan [N, N, N] 1 Cij == N
#guard outerInjective [N, N, N] 1 Cij
#guard nestIndepB [N, N, N] 1 [Cij, Aik, Bkj] [Cij]

-- the two-level elementwise kernel, forking its outer level only: the same shape without the
-- reduction
#guard innerSpan [N, N] 1 C == N
#guard nestIndepB [N, N] 1 [A, B] [C]

-- the scaling is load-bearing, not decoration: drop it and `C[i,j]` at `d = 1` reads as a write
-- whose forked coefficient is `1`, which two threads `N` apart would share
#guard !outerInjective [N, N, N] 1 { Cij with coeffs := [1, 1, 0] }

/-! ## Refused, and imprecisely: a column-major write

`B[j,i] := …` is injective over the box, so the unrestricted statement is **true** and the
certificate still refuses it. This is a false refusal, it is this module's only one, and it is
gated so that the count is measured rather than claimed. -- ref: `docs/loops.md` -/

private def colMajor : AffAccess := { base := 0, size := 16, coeffs := [1, 4], off := 0 }

#guard colMajor.inBounds [4, 4]
#guard !nestIndepB [4, 4] 2 [] [colMajor]

/-! ## Refused: an access that escapes its buffer

A declared footprint the body overruns would make the certificate vacuous, so `boundsOK` is
checked rather than assumed. -/

private def escapes : AffAccess := { base := 0, size := 8, coeffs := strides [4, 4], off := 0 }

#guard !escapes.inBounds [4, 4]
#guard !nestIndepB [4, 4] 2 [] [escapes]
#guard !nestIndepB [4, 4] 2 [escapes] [good]

/-! ## The soundness theorems, instantiated

`#guard` says the `Bool` is `true`; these say what that buys — the disjointness
`parAll_par_seq_eq_of_indexed_rw` consumes as `hww` and `hwr`, at a million points. -/

example : ∀ w ∈ [good], ∀ w' ∈ [good], ∀ u v p q,
    InBox ([4, 4].take 2) u → InBox ([4, 4].take 2) v → u ≠ v →
    InBox [4, 4] (u ++ p) → InBox [4, 4] (v ++ q) → w.addr (u ++ p) ≠ w'.addr (v ++ q) :=
  nestIndepB_ww (reads := []) (by decide)

example : ∀ w ∈ [C], ∀ r ∈ [A, B], ∀ u v p q,
    InBox ([N, N].take 2) u → InBox ([N, N].take 2) v → u ≠ v →
    InBox [N, N] (u ++ p) → InBox [N, N] (v ++ q) → w.addr (u ++ p) ≠ r.addr (v ++ q) :=
  nestIndepB_wr (by decide)

-- the in-place doall: distinct threads of `A[i,j] := A[i,j] + 1` never collide
example : ∀ w ∈ [A], ∀ r ∈ [A], ∀ u v p q,
    InBox ([N, N].take 2) u → InBox ([N, N].take 2) v → u ≠ v →
    InBox [N, N] (u ++ p) → InBox [N, N] (v ++ q) → w.addr (u ++ p) ≠ r.addr (v ++ q) :=
  nestIndepB_wr (by decide)

-- **gemm's accumulation, as the two halves the equivalence theorem consumes.** `C[i,j]` is both
-- the write and a read, over a box of 10⁹ points forked two levels deep.
example : ∀ w ∈ [Cij], ∀ r ∈ [Cij, Aik, Bkj], ∀ u v p q,
    InBox ([N, N, N].take 2) u → InBox ([N, N, N].take 2) v → u ≠ v →
    InBox [N, N, N] (u ++ p) → InBox [N, N, N] (v ++ q) →
    w.addr (u ++ p) ≠ r.addr (v ++ q) :=
  nestIndepB_wr (by decide)

end Paralever.Test.Nest
