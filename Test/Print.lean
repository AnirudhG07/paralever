import Lang.Load
import Lang.Report

/-! # `print` — the surface, the erasure, and the output

Three separate claims, gated separately.

*The surface*: `print` reads, prints back and reads again as itself, for each of the four things it
can name. *The erasure*: it contributes nothing to a footprint, nothing to `wfB`, and nothing to
either interpreter — `dropPrints` is the program the theorems are about, and
`ParProg.execPar_dropPrints` proves the two run the same. *The output*: the lines are produced by
the walk in `Lang/Report.lean`, which runs everything that is not a print through `execSeq`, and the
heap it leaves is gated here against the heap `runTaskSeq` leaves.

Rationale: `docs/print.md`. -/

namespace Test.Print
open Paralever Paralever.Lang

private def ok (src : String) : Option Compiled := (ofString src).toOption

private def codeOf (src : String) : Option String :=
  match ofString src with
  | .error d => d.code.map Diag.Code.id
  | .ok _    => none

/-! ## The surface

A bare name is the whole buffer — the one place in the language where a name without a subscript is
not a cell. Everything else is told apart the way `%r := …` tells a load from an assignment. -/

private def src : String :=
  "buf A[2, 3] = arange\nbuf n = 7\nconst k = 4\nreg p\n\n%p := 1\n"
    ++ "print A\nprint n\nprint A[1, 2]\nprint %p\nprint k\nprint 2 * %p + 1\n"
    ++ "print \"label\", A[0, 0]\nprint A[%p]\n"

#guard (ok src).isSome
#guard roundTrips src

-- each form, resolved: a buffer, a scalar buffer, a cell, a register, a `const`, an expression,
-- a labelled cell, and a computed cell
#guard (ok src).map (fun c => (ParProg.dropPrints c.prog == c.prog)) == some false

private def items (c : Compiled) : List (List PrintItem) :=
  (ParProg.flatten c.prog).filterMap fun
    | .print is => some is
    | _         => none

#guard (ok src).map items == some
  [ [.buf "A" [2, 3] 0], [.buf "n" [] 6], [.cell "A" [1, 2] 5], [.exp (.reg 0)]
  , [.exp (.lit 4)], [.exp (.add (.mul (.lit 2) (.reg 0)) (.lit 1))]
  , [.text "label", .cell "A" [0, 0] 0], [.at "A" ⟨0, 6⟩ (.reg 0)] ]

-- a `slice` name is refused: a slice is erased once the file compiles, so `to-prl` could not write
-- it back and the printed program would not read as itself
#guard codeOf "buf A[4] = arange\nslice h = A[1..3]\n\nprint h" == some "P111"
#guard codeOf "buf A[4] = arange\nslice h = A[1..3]\n\nprint h[0]" == some "P111"
#guard codeOf "buf A[4] = arange\n\nprint A[1..3][0]" == some "P111"

-- and the `.prl` text comes back out, so a file with prints is still a file
#guard roundTrips "buf A[4]\nreg p\n\n%p := 2\nprint \"p =\", %p, A[%p]"

/-! ## Where a print may go, which is anywhere

A print is erased from both interpreters and carries an empty footprint, so no theorem can see one
wherever it sits. In a `for`, an `if` or a `while` — chains spliced into the one that encloses them
— it reads the heap that reaches it, and that is the whole story.

In a `parallel` thread the lines come off the canonical order, the threads as written, and the two
kinds of print differ. A register print is schedule-independent: each thread starts from the
register file the fork copied in and none of its writes escape, so what it shows is what every
schedule shows. A memory print is not. `print` adds no read to a footprint, so `wfB` accepting says
nothing about what another thread wrote to the cell it names — the first guard below reads `[0]`
only because thread one runs first. -- ref: `docs/print.md` § In a thread -/

#guard (ok "buf A[2]\n\nfor i in 2 {\n  print A[i]\n}").isSome
#guard (ok "buf A[1]\nreg p\n\n%p := 1\nif %p { print A } else { print A }").isSome

-- a memory print inside a thread: accepted, and what it shows is one order's answer
#guard (ok "buf A[1]\n\nparallel {\n  print A\n} | {\n  A[0] := 1\n}").map outputOf
  == some ["A = [0]"]

-- registers are copied in at the fork and discarded at the join, so each thread sees its own and
-- the program keeps the file it had before: 2 in the first thread, 4 in the second, 2 after
#guard (ok "%0 := 2\n\nparallel {\n  %a := %0\n  print %0, %a\n} | {\n  %0 := 4\n  print %0\n}\n\nprint %0").map
  outputOf == some ["2 2", "4", "2"]

-- and the text comes back out with the print still inside the thread
#guard roundTrips "buf A[1]\n\nparallel {\n  print A\n} | {\n  A[0] := 1\n}"

-- a print in a `parfor` body is legal too; it blocks rolling, as an `if` or a `while` there does
#guard (ok "buf A[2]\n\nparfor i in 2 {\n  print A\n}").map outputOf
  == some ["A = [0, 0]", "A = [0, 0]"]

/-! ## Erased

Nothing a print names reaches a footprint, an independence check, or an interpreter. The two
programs below differ only by their prints and agree on every one of those. -/

private def withP : String := "buf A[2]\n\nparallel {\n  A[0] := 1\n} | {\n  A[1] := 2\n}\nprint A"
private def noP   : String := "buf A[2]\n\nparallel {\n  A[0] := 1\n} | {\n  A[1] := 2\n}"

private def fp (c : Compiled) : List Loc × List Loc :=
  let f := ParProg.footprintOf c.prog; (f.reads, f.writes)

#guard ((ok withP).map fp) == ((ok noP).map fp)
#guard (ok withP).map (fun c => ParProg.wfB c.prog) == some true
#guard (ok withP).map (fun c => ParProg.footprintExact c.prog)
     == (ok noP).map (fun c => ParProg.footprintExact c.prog)
#guard ((ok withP).map (fun c => norm (ParProg.dropPrints c.prog)))
     == ((ok noP).map (fun c => norm c.prog))
-- a program that is nothing but prints erases to the other statement both interpreters ignore
#guard (ok "buf A[1]\n\nprint A").map (fun c => ParProg.dropPrints c.prog)
     == some ParProg.synchronize

-- the verdict is the same with the prints and without them, which is the point
#guard ((ok withP).map (fun c => verdictParts c)) == ((ok noP).map (fun c => verdictParts c))

/-! ## A print is a barrier for the parallelizer, and not a phase boundary

Three claims from `docs/print.md`, each on the predicate that carries it. A print's footprint is
empty, so without them nothing would stop a scheduler forking a statement past one and changing
what the program says. -/

-- `canParSeg` refuses to group a print with anything, so a print is always its own group
#guard !ParProg.canParSeg (.print []) (.store 0 (.lit 1))
#guard !ParProg.canParSeg (.store 0 (.lit 1)) (.print [])
#guard ParProg.canParSeg (.store 0 (.lit 1)) (.store 1 (.lit 1))

-- the *proved* rewrite route declines a print for the same reason it declines a `synchronize`
#guard !ParProg.barrierFree (.print [])
#guard !ParProg.barrierFree ParProg.synchronize
#guard !ParProg.barrierFree (.seq (.store 0 (.lit 1)) (.print []))
#guard ParProg.barrierFree (.store 0 (.lit 1))

-- but a print is **not** a phase boundary: `phases` splits on `synchronize` alone, because
-- `joinPhases` puts a `synchronize` back between phases and could not put a print back
#guard !ParProg.isSynchronize (.print [])
#guard ParProg.isBarrier (.print [])
#guard (ParProg.phases [.store 0 (.lit 1), .print [],
                        .store 1 (.lit 1)]).length == 1
#guard (ParProg.phases [.store 0 (.lit 1), ParProg.synchronize,
                        .store 1 (.lit 1)]).length == 2

/-! ## The output, and the heap it was read off

The walk that produces the lines threads the heap itself, so it could drift from `execSeq`. It does
not: for each program here the cell it leaves and the cell `runTaskSeq` leaves are equal, at every
declared address. -/

private def agrees (src : String) : Bool :=
  match ok src with
  | none   => false
  | some c =>
      let σ := heapAfterOut c
      let τ := (ParProg.runTaskSeq c.prog (fun _ => 0) c.layout.state).2
      (List.range c.layout.size).all (fun l => σ l == τ l)

#guard agrees src
#guard agrees withP
#guard agrees "buf A[4] = arange\nreg s\n\n%s := 0\nfor i in 4 {\n  print A[i]\n  A[i] := i + 1\n}\nprint A"
#guard agrees "buf A[2]\nreg p\n\n%p := 0\nwhile %p in 3 {\n  print \"round\", %p\n  %p := %p + 1\n}"
#guard agrees "buf A[1] = 5\nreg p\n\n%p := A[0]\nif %p { print \"yes\" } else { print \"no\" }"
-- the walk descends into a fork now, so it has to thread the heap through the threads exactly as
-- `execSeq`'s `seqAll` does: same pre-fork registers into each, heap in turn, registers back out
#guard agrees "buf A[2]\n\nparallel {\n  print A\n  A[0] := 1\n} | {\n  A[1] := 2\n  print A\n}\nprint A"
#guard agrees "buf A[2]\n\nparfor i in 2 {\n  print A[i]\n  A[i] := i + 1\n}\nprint A"

/-! ### And what it writes

A cell and a buffer print as `name = value`, so a line says what it is with no label. A matrix is
one line here, unlike `run`'s view of the whole heap, because a print sits in a sequence of them. -/

#guard (ok src).map outputOf == some
  [ "A = [[0, 1, 2], [3, 4, 5]]", "n = 7", "A[1, 2] = 5", "1", "4", "3"
  , "label A[0, 0] = 0", "A[1] = 1" ]

#guard (ok "buf A[4] = arange\nfor i in 4 { print A[i] }").map outputOf
  == some ["A[0] = 0", "A[1] = 1", "A[2] = 2", "A[3] = 3"]

-- only the arm that runs writes anything
#guard (ok "buf c = 0\nreg g\n\n%g := c\nif %g { print \"then\" } else { print \"else\" }").map
  outputOf == some ["else"]

-- a program with no print has no output section at all
#guard (ok noP).map outReport == some ""

end Test.Print
