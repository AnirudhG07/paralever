import Lang.Load
import Lang.Report

/-! # The same three programs, written in Lean instead of in a file

A `.prl` file and a `paralever { … }` block are two surfaces over one `ParProg`, so anything a file
says can be said in Lean. What is gated here is that claim on the three files that exercise the
parts of the language a block could not reach until the surface was completed: a label
(`:: "name"`), a computed access (`[A, e]`), and an arena whose buffers are not placed
consecutively. Each program is written out by hand, the way a user would, and compared with the
compilation of the file — the layout by its addresses and its initial cells, the program up to
`;`-associativity. -- ref: docs/prl.md § The Lean form -/

namespace Test.LeanForm
open Paralever Paralever.Lang

/-- Addresses and initial contents: what a program is compiled against. Two layouts that agree on
both are the same memory, whichever surface declared it. -/
private def sameMemory (a b : Layout) : Bool :=
  a.bufs.map Placed.base == b.bufs.map Placed.base && a.data == b.data

/-! ## A label — `sum.prl`

The registers are the ones the file's compiler assigned, since the two programs are compared as
terms and a register is its index. -/

abbrev acc : Reg := 0
abbrev v   : Reg := 1

def sumL : Layout := Layout.of
  [ buf "A" [6] (data [1, 2, 3, 4, 5, 6])
  , buf "out" [3] ]

def sumProg : ParProg := paralever {
  parfor c in 3 {
    %acc := 0;
    for k in 2 { %v := [sumL.at "A" [c * 2 + k]]; %acc := (%acc + %v) };
    [sumL.at "out" [c]] := %acc
  } :: "chunked sum"
}

def sumFile : Compiled := prl_file "../Examples/Language/sum.prl"

#guard sameMemory sumL sumFile.layout
#guard norm sumProg == norm sumFile.prog

/-! ## A computed access — `scatter.prl`

`[A, e]` is `loadAt`/`storeAt`: the cell of the range `A` at index `e`. The range is `L.ref "dst"`,
which is the same `ArrRef` the file's `dst[%i]` compiles to. -/

abbrev ix : Reg := 0

def scatterL : Layout := Layout.of
  [ buf "idx" [3] (data [2, 0, 1])
  , buf "dst" [3] ]

def scatterProg : ParProg := paralever {
  parfor t in 3 { %ix := [scatterL.at "idx" [t]]; [scatterL.ref "dst", %ix] := 1 }
}

def scatterFile : Compiled := prl_file "../Examples/Language/scatter.prl"

#guard sameMemory scatterL scatterFile.layout
#guard norm scatterProg == norm scatterFile.prog

/-! ## An arena — `arena.prl`

`out` is placed on `tmp`'s freed cells, so the two share a base and `Layout.of` — which allocates
consecutively — cannot express this layout. The bases are written out instead, which is what
`toLean` prints for the same reason. -/

abbrev dbl : Reg := 0
abbrev inc : Reg := 1

def arenaL : Layout := { bufs :=
  [ { name := "src", shape := [4], init := [1, 2, 3, 4], base := 0 }
  , { name := "tmp", shape := [4], init := [], base := 4 }
  , { name := "out", shape := [4], init := [], base := 4 } ] }

def arenaProg : ParProg := paralever {
  parfor i in 4 { %dbl := [arenaL.at "src" [i]]; [arenaL.at "tmp" [i]] := (%dbl * 2) } :: "double";
  parfor i in 4 { %inc := [arenaL.at "out" [i]]; [arenaL.at "out" [i]] := (%inc + 1) }
    :: "increment in place"
}

def arenaFile : Compiled := prl_file "../Examples/Language/arena.prl"

#guard sameMemory arenaL arenaFile.layout
#guard norm arenaProg == norm arenaFile.prog

/-! ## And the heap each pair leaves

Equal programs over equal memory leave equal heaps, so this gate is redundant by construction —
kept because it is the property a reader actually cares about, and because it fails loudly if
`sameMemory` is ever weakened. -/

private def heap (L : Layout) (p : ParProg) : List Val :=
  (List.range L.size).map (ParProg.runTaskSeq p (fun _ => 0) L.state).2

#guard heap sumL sumProg == heap sumFile.layout sumFile.prog
#guard heap scatterL scatterProg == heap scatterFile.layout scatterFile.prog
#guard heap arenaL arenaProg == heap arenaFile.layout arenaFile.prog

end Test.LeanForm
