import Lang.Load
import Lang.Report

/-! # The language under stress

Programs here are *generated as text*, so one gate covers the whole path: the reader, the
lowering, the footprint, the independence check and the interpreter. Each shape comes with the
answer computed independently of the interpreter — a closed form, not a second run — so a gate
fails when the language disagrees with arithmetic rather than when two runs disagree.

Sizes are the largest that keep this file's elaboration under a few seconds; the measured
behaviour at the sizes that hurt is in `docs/scale.md`, which is written from the command line
rather than from here. -- ref: docs/scale.md -/

namespace Test.Stress
open Paralever Paralever.Lang

private def lines (xs : List String) : String := String.intercalate "\n" xs

/-- `{` and `}` would be read as interpolation inside `s!`, so the two lines that open and close a
block are built here instead of inline. -/
private def parforOpen (v : String) (n : Nat) : String :=
  "parfor " ++ v ++ " in " ++ toString n ++ " {"

private def closeAs (nm : String) : String := "} :: \"" ++ nm ++ "\""

/-! ## Shapes

Each generator takes a size and returns `.prl` text. They are deliberately written the way a user
would write them — `parfor` over a `const`, buffers declared by shape — so the gates exercise the
surface and not an internal constructor. -/

/-- `n` sequential stores to distinct cells, and no fork: the reader and the lowering, `n` lines. -/
def chainSrc (n : Nat) : String :=
  lines (s!"buf A[{n}]" :: "" :: (List.range n).map (fun i => s!"A[{i}] := {i}"))

/-- One thread per cell, each writing its own cell: `n` threads, pairwise-disjoint writes. -/
def forkSrc (n : Nat) : String :=
  lines [s!"buf A[{n}]", "", parforOpen "i" n, "  A[i] := i", closeAs "disjoint"]

/-- One thread per cell, every thread reading the same cell: Bernstein and not disjointness, which
is the case naive `∗`-style separation rejects. -/
def sharedReadSrc (n : Nat) : String :=
  lines [ "buf S[1] = 5", s!"buf A[{n}]", "", parforOpen "i" n,
          "  %x := S[0]", "  A[i] := %x + i", closeAs "shared reads"]

/-- `chunks` threads, each summing `len` cells of `A` into its own cell of `out`. -/
def reduceSrc (chunks len : Nat) : String :=
  lines [ s!"const len = {len}", s!"buf A[{chunks * len}] = arange", s!"buf out[{chunks}]", "",
          parforOpen "c" chunks, "  %acc := 0", "  for k in len {",
          "    %v := A[c * len + k]", "    %acc := %acc + %v", "  }", "  out[c] := %acc",
          closeAs "chunked sum"]

/-- `n`×`n` matmul: disjoint writes to `C`, overlapping reads of `A` and `B`. -/
def matmulSrc (n : Nat) : String :=
  lines [ s!"const n = {n}", s!"buf A[{n}, {n}] = arange", s!"buf B[{n}, {n}] = arange",
          s!"buf C[{n}, {n}]", "", "parfor i in n {", "  for j in n {", "    %acc := 0",
          "    for k in n {", "      %x := A[i, k]", "      %y := B[k, j]",
          "      %acc := %acc + %x * %y", "    }", "    C[i, j] := %acc", "  }",
          closeAs s!"matmul {n}x{n}"]

/-- Forks nested `d` deep, two ways at each level: `2^d` leaves, each writing one cell. -/
def nestSrc (d : Nat) : String :=
  let rec body (k : Nat) (stride : Nat) (off : String) : List String :=
    match k with
    | 0     => [s!"A[{off}] := {off}"]
    | k + 1 =>
        [parforOpen s!"i{k}" 2]
          ++ (body k (stride / 2) s!"{off} + i{k} * {stride / 2}").map (fun l => "  " ++ l)
          ++ ["}"]
  lines ([s!"buf A[{2 ^ d}]", ""] ++ body d (2 ^ d) "0")

/-- Phases separated by barriers: every phase reads what the one before it wrote, so the heap is a
chain and a parallelizer that crossed a barrier would be caught by the value, not by a verdict. -/
def barrierSrc (phases width : Nat) : String :=
  lines ([s!"buf A[{width}] = ones", ""] ++
    (List.range phases).flatMap (fun p =>
      [parforOpen "i" width, "  %v := A[i]", "  A[i] := %v + 1", closeAs s!"phase {p}"]
        ++ (if p + 1 == phases then [] else ["", "synchronize", ""])))

/-- `buf`/`free` alternating, so every buffer after the first lands on the previous one's cells and
the heap has one live range however many were declared. -/
def arenaSrc (rounds width : Nat) : String :=
  lines ((List.range rounds).flatMap (fun r =>
    [ s!"buf b{r}[{width}]", "", parforOpen "i" width, s!"  b{r}[i] := {r + 1}", "}", ""]
      ++ (if r + 1 == rounds then [] else [s!"free b{r}", ""])))

/-- A race: two threads writing one cell, with different values, so a schedule disagrees. -/
def racySrc : String :=
  lines ["buf A[1]", "", "parallel {", "  A[0] := 1", "} | {", "  A[0] := 2", "}"]

/-- A computed address: the index comes from memory, so the footprint is the whole range and `wfB`
refuses although the three threads write three distinct cells. -/
def scatterSrc (n : Nat) : String :=
  lines [ s!"buf idx[{n}] = arange", s!"buf dst[{n}]", "", parforOpen "t" n,
          "  %i := idx[t]", "  dst[%i] := 1", "}"]

/-! ## The gates

Every shape is compiled from its text, run, and compared with the answer written out as
arithmetic. A disagreement is a bug in the language, not in a second interpreter — which is why
none of these compare two runs. -/

/-- The declared cells after a run, in address order. Programs here produce `.int` only. -/
private def runCells (src : String) : Option (List Int) :=
  (ofString src).toOption.map fun c =>
    let σ := (ParProg.runTaskSeq c.prog (fun _ => 0) c.layout.state).2
    (List.range c.layout.size).map fun l =>
      match σ l with
      | .int k  => k
      | .bool b => if b then 1 else 0
      | .unit   => 0

/-- `wfB`, for a shape that must be accepted or refused. -/
private def accepted (src : String) : Option Bool :=
  (ofString src).toOption.map (fun c => ParProg.wfB c.prog)

/-- How many schedules reach `wrong` — the exact per-heap check, not the syntactic one. -/
private def races (src : String) : Option Nat :=
  (ofString src).toOption.map fun c =>
    (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).length

private def upto (n : Nat) : List Int := (List.range n).map Int.ofNat

private def sum (xs : List Int) : Int := xs.foldl (· + ·) 0

/-! ### Independent shapes: accepted, and arithmetic says what they leave -/

#guard accepted (chainSrc 128) == some true
#guard runCells (chainSrc 128) == some (upto 128)
#guard roundTrips (chainSrc 128)

#guard accepted (forkSrc 24) == some true
#guard runCells (forkSrc 24) == some (upto 24)
#guard roundTrips (forkSrc 24)

-- the shared-read case: 24 threads all read `S[0]`, which no `∗`-style disjointness allows
#guard accepted (sharedReadSrc 24) == some true
#guard runCells (sharedReadSrc 24) == some (5 :: (upto 24).map (5 + ·))

#guard accepted (reduceSrc 8 8) == some true
#guard runCells (reduceSrc 8 8) ==
  some (upto 64 ++ (List.range 8).map (fun c => sum ((List.range 8).map (fun k => Int.ofNat (c * 8 + k)))))

#guard accepted (matmulSrc 5) == some true
#guard runCells (matmulSrc 5) ==
  some (upto 25 ++ upto 25 ++ (List.range 5).flatMap (fun i => (List.range 5).map (fun j =>
    sum ((List.range 5).map (fun k => Int.ofNat (i * 5 + k) * Int.ofNat (k * 5 + j))))))

-- forks nested five deep: 32 leaves, each writing the cell its index names
#guard accepted (nestSrc 5) == some true
#guard runCells (nestSrc 5) == some (upto 32)

-- four phases of eight threads, each phase reading what the one before it wrote
#guard accepted (barrierSrc 4 8) == some true
#guard runCells (barrierSrc 4 8) == some (List.replicate 8 5)

-- four rounds of `buf`/`free`: every buffer after the first lands on the previous one's cells
#guard accepted (arenaSrc 4 4) == some true
#guard runCells (arenaSrc 4 4) == some (List.replicate 4 4 ++ List.replicate 12 0)

/-! ### And the shapes that must be refused

The first is a real race, so both checks refuse it. The second is the price of a footprint read off
the syntax: `wfB` refuses although no schedule disagrees *at the declared heap*, which is the verdict
the reports split into `this heap` and `any heap`. -- ref: docs/block-ir.md, docs/general-heap.md -/

#guard accepted racySrc == some false
#guard races racySrc == some 1

#guard accepted (scatterSrc 3) == some false
#guard races (scatterSrc 3) == some 0

-- a write one thread reads and another writes: the hypothesis is load-bearing, not decoration
private def conflictSrc : String :=
  lines ["buf A[2]", "", "parallel {", "  A[0] := 1", "} | {", "  %0 := A[0]", "  A[1] := %0", "}"]

#guard accepted conflictSrc == some false
#guard races conflictSrc == some 1

-- the loop-carried dependence `A[i + 1] := A[i] + 1`, which must stay unprovable
private def carriedSrc : String :=
  lines ["buf A[4] = arange", "", parforOpen "i" 3, "  %v := A[i]", "  A[i + 1] := %v + 1", "}"]

#guard accepted carriedSrc == some false
#guard races carriedSrc == some 2

/-! ### Crazy inputs

What the reader accepts, what it refuses, and what it computes where another language would have
undefined behaviour. Each refusal names the object it is about; `State` is total, so division by
zero and an unwritten cell are values rather than faults. -/

#guard runCells "" == some []
#guard runCells "-- nothing at all" == some []
#guard runCells "buf A[0]" == some []
#guard runCells "buf x\n\nx := 1" == some [1]
#guard runCells "buf A[2]\n\nA[0] := 1; A[1] := 2" == some [1, 2]
#guard runCells "buf A[2]\r\n\r\nA[0] := 1\r\nA[1] := 2" == some [1, 2]
#guard runCells "buf A[1]\n\nA[0] := 123456789012345678" == some [123456789012345678]
#guard runCells "buf A[1]\n\n%0 := 0\nA[0] := 5 / %0" == some [0]
#guard runCells "buf A[2] = -1, -2" == some [-1, -2]
#guard runCells "buf A[1]\n\n%0 := 3\nwhile %0 in 5 {\n  %0 := %0 - 1\n  A[0] := %0\n}" == some [0]
#guard runCells "buf A[1]\n\nparfor i in 0 {\n  A[0] := 1\n}" == some [0]
-- `b` is placed on `a`'s cells, so the layout declares four and the heap has two addresses
#guard runCells "buf a[2]\nfree a\nbuf b[2]\n\nb[0] := 7" == some [7, 0, 0, 0]

-- and the refusals, each naming what is wrong
private def refused (src : String) : Bool := (ofString src).toOption.isNone

#guard refused "buf A[4]\n\nA[9] := 1"
#guard refused "buf A[4]\nbuf A[4]"
#guard refused "buf A[4]\n\nB[0] := 1"
#guard refused "buf A[4]\nfree A\n\nA[0] := 1"
#guard refused "buf A[4]\nfree A\nfree A"
#guard refused "buf A[4]\n\n%0 := 1\n[%0] := 1"
#guard refused "buf A[4] at 0\nbuf B[4] at 2"
#guard refused "buf A[4]\n\n%0 := 7\nA[0] := %0 % 2"
#guard refused "buf A[0]\n\nA[0] := 1"

end Test.Stress
