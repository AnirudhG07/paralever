import Lang.Load
import Lang.Verdict

/-! # The general-heap search

`wfB` answers for every heap and `raceSites` for one. This gates what sits between them: the
bounded search of `Lang/Core/Heaps.lean`, and the two-part verdict built on it.

A hit is decisive and is gated as such — the heap it names is re-run here and `wellFormedB` is
`false` at it, so the search's answer is checked rather than trusted. A miss is bounded, so the
guards below record the size of the search that came back empty and never read it as a proof.

Rationale: `docs/general-heap.md`. -/

namespace Test.Heaps
open Paralever Paralever.Lang

private def ok (src : String) : Compiled :=
  match ofString src with
  | .ok c    => c
  | .error _ => ⟨⟨[]⟩, .synchronize, [], [], none⟩

/-! ## What is probed

The cells a `load` names, and the values that make `ArrRef.addr` alias: `-1` for the `Int.toNat`
clamp, and `n - 1`, `n`, `n + 1` of each buffer for the `% max len 1` wrap. -/

private def stripe : Compiled := ok
  "buf A[8]\nbuf k[2] = 0, 1\n\nparallel {\n  %p := k[0]\n  A[2 * %p] := 1\n} | {\n  \
%q := k[1]\n  A[2 * %q + 1] := 2\n}"

#guard ParProg.probeCells stripe.prog == [8, 9]
#guard probeValues stripe.layout == [-1, 0, 1, 7, 8, 9, 2, 3]

-- a computed address contributes nothing to the probe set: its own cell is unknown too
#guard ParProg.probeCells
  (ok "buf idx[2] = arange\nbuf A[2]\n\n%i := idx[0]\n%p := A[%i]").prog == [0]

/-! ## Stripe: the unrestricted statement is false

`A[2 * %p]` against `A[2 * %q + 1]` writes two different cells for every *in-range* pair of
indices, and `paralever vc`'s solver was asked to say so. It cannot, because the claim is false:
`ArrRef.addr` clamps with `Int.toNat`, so at `k[1] = -1` the odd address `2 * (-1) + 1` folds onto
`A[0]` — which is where `2 * 0` already is. -/

private def stripeRace : Option Heap :=
  match ParProg.verdictAnywhere stripe.layout stripe.prog with
  | .race h _ => some h
  | _         => none

#guard stripeRace == some ⟨[(9, -1)]⟩

-- and the heap the search named really does race, checked against `raceSites` here
#guard match stripeRace with
  | some h => !wellFormedB (ParProg.execPar stripe.prog (fun _ => 0)) (h.apply stripe.layout.state)
  | none   => false

-- the declared heap is race-free, which is the other half of the verdict
#guard wellFormedB (ParProg.execPar stripe.prog (fun _ => 0)) stripe.layout.state

/-! ## Scatter: a permutation that stops being one

`idx = 2, 0, 1` sends three threads to three cells. One negative index clamps onto `dst[0]`, which
another thread already owns. -/

private def scatter : Compiled := ok
  "buf idx[3] = 2, 0, 1\nbuf dst[3]\n\nparfor t in 3 {\n  %i := idx[t]\n  dst[%i] := 1\n}"

#guard match ParProg.verdictAnywhere scatter.layout scatter.prog with
  | .race h st => h == ⟨[(0, -1)]⟩ && st.conflicts == [3]
  | _          => false

/-! ## A branch: the search finds nothing, and that is all it says

Both threads write a cell the other does not, whichever arm runs, so `par = seq` at every heap. The
footprint of an `ifElse` is the union of its arms, so `wfB` refuses; the search probes every value
of the one cell the condition is read from and finds no race. `Inconclusive`, with the reason. -/

private def branch : Compiled := ok
  "buf A[2]\nbuf c[1] = 1\n\n%g := c[0]\n\nparallel {\n  if %g { A[0] := 1 } else { A[1] := 1 }\n\
} | {\n  if %g { A[1] := 2 } else { A[0] := 2 }\n}"

#guard !ParProg.wfB branch.prog
#guard ParProg.probeCells branch.prog == [2]
#guard match ParProg.verdictAnywhere branch.layout branch.prog with
  | .unknown n => n == 11
  | _          => false

-- and what the report says about it: a branch widened the footprint, not a computed address
#guard ParProg.widenedBy branch.prog
  == ["a branch contributes both arms although only one runs"]
#guard ParProg.widenedBy stripe.prog
  == ["a computed address contributes every cell of its buffer"]
#guard (refusedAt branch.prog).map RaceSite.conflicts == some [0, 1]

/-! ## The two parts, and when they collapse to one

`wfB` accepting answers both halves at once; a race at the declared heap is a race at a heap, so
there is nothing left to say about the others. The verdict is two lines only in between. -/

private def disjoint : Compiled := ok
  "buf A[2]\n\nparallel {\n  A[0] := 1\n} | {\n  A[1] := 2\n}"
private def racy : Compiled := ok
  "buf A[1]\n\nparallel {\n  A[0] := 1\n} | {\n  A[0] := 2\n}"

#guard (verdictParts disjoint).map Prod.fst == ["every heap"]
#guard (verdictParts racy).map Prod.fst == ["every heap"]
#guard (verdictParts stripe).map Prod.fst == ["this heap", "any heap"]
#guard (verdictParts branch).map Prod.fst == ["this heap", "any heap"]

-- the first line of each, so a change to the wording is a change to a gate
#guard ((verdictParts disjoint).head?.map Prod.snd).any (·.startsWith "Proved: Yes — wfB accepts")
#guard ((verdictParts racy).head?.map Prod.snd).any (·.startsWith "RACE found")
#guard ((verdictParts stripe).getLast?.map Prod.snd).any (·.startsWith "RACE found — with k[1] = -1")
#guard ((verdictParts branch).getLast?.map Prod.snd).any (·.startsWith "Inconclusive — wfB refuses")

/-! ## The search is bounded, and says so

`probeHeaps` starts at the declared heap, so the general search can never miss a race the per-heap
check finds, and it stops at `budget` however many the shape would generate. -/

#guard (probeHeaps 512 [1, 2] [0, 1]).head? == some Heap.declared
#guard (probeHeaps 512 [1, 2] [0, 1]).length == 1 + 4 + 2 + 4
#guard (probeHeaps 3 [1, 2] [0, 1]).length == 3
#guard (probeHeaps 512 [] [0, 1]).length == 1 + 0 + 2 + 0

end Test.Heaps
