import Lang.Core.Heaps
import Lang.Core.Agree
import Lang.Compile.Lower
import Paralever.Search.Explain

/-! # The verdict, in two parts

Its own module because both reports print it — `check`'s and `vc`'s — and neither should be able to
say something the other does not. -/

namespace Paralever.Lang
open Paralever

/-! ## The verdict, in two parts

A program with a computed address has two different answers, and reporting one of them is what made
the old single line misleading. **This heap** is the one the file's `buf` initializers describe, and
`raceSites` decides it exactly. **Any heap** is the universally quantified question, which `wfB`
decides when it accepts and the bounded search of `Lang/Core/Heaps.lean` attacks when it does not.
The two are printed as one line when they agree and as two when they differ.
-- ref: `docs/general-heap.md` § The two parts -/

/-- How a cell is contended: the three Bernstein clauses, in words. -/
def conflictWord (st : RaceSite) (l : Loc) : String :=
  if st.left.writes.contains l && st.right.writes.contains l then "written by both threads"
  else if st.left.writes.contains l then "written by one thread, read by the other"
  else "read by one thread, written by the other"

/-- `A[0] written by both threads`, naming at most two cells. -/
def raceText (c : Compiled) (st : RaceSite) : String :=
  match st.conflicts with
  | []     => "two threads are not independent"
  | l :: _ => c.locName l ++ " " ++ conflictWord st l
                ++ (if st.conflicts.length == 1 then ""
                    else " (and " ++ toString (st.conflicts.length - 1) ++ " more cell(s))")

/-- `k[1] = -1` — the cells a counterexample heap changes, in the program's own names. -/
def editText (c : Compiled) (h : Heap) : String :=
  if h.edits.isEmpty then "the heap this file declares"
  else ", ".intercalate (h.edits.map (fun (l, v) => c.locName l ++ " = " ++ toString v))

/-- Why the general question is still open: what `wfB` refused over, and how far the search looked.
-- ref: `docs/general-heap.md` § What `inconclusive` means -/
def openText (c : Compiled) (probed : Nat) : String :=
  let site := match refusedAt c.prog with
    | some st => " over " ++ clipNames c.locName 6 st.conflicts
    | none    => ""
  let why := "; ".intercalate (ParProg.widenedBy c.prog)
  "Inconclusive — wfB refuses" ++ site ++ (if why.isEmpty then "" else ": " ++ why)
    ++ "\n            no race found in " ++ toString probed ++ " heap(s) probed over "
    ++ clipNames c.locName 6 (ParProg.probeCells c.prog)

/-- The verdict's halves: a label and what holds under it. One pair when both halves agree.

**`wfB` accepting settles both halves without a run.** `wfB_wellFormed` holds at every heap, and the
declared heap is one of them, so `raceSites` would return `[]` by theorem — asking it is the only
step here whose cost is the program's own, and a rolled nest is exactly the program whose iteration
space nothing else walks. -- ref: `docs/loops.md` § What rolling does not make cheap -/
def verdictParts (c : Compiled) : List (String × String) :=
  if ParProg.wfB c.prog then
    [("every heap", "Proved: Yes — wfB accepts: the threads' footprints are pairwise independent")]
  else
  let here := ParProg.verdictHere c.layout c.prog
  let any  := ParProg.verdictAnywhere c.layout c.prog
  match here, any with
  | .proved, .proved =>
      [("every heap", "Proved: Yes — wfB accepts: the threads' footprints are pairwise independent")]
  | .race _ st, _ =>
      -- the declared heap is one of the heaps, so there is nothing left to say about the rest
      [("every heap", "RACE found — " ++ raceText c st)]
  | .proved, .race h st =>
      [ ("this heap", "Proved: Yes — no two threads touch one cell here")
      , ("any heap",  "RACE found — with " ++ editText c h ++ ": " ++ raceText c st) ]
  | .proved, .unknown n =>
      [ ("this heap", "Proved: Yes — no two threads touch one cell here")
      , ("any heap",  openText c n) ]
  | .unknown _, _ => [("this heap", "Inconclusive")]

/-! ## An `assert`'s verdict

A claim is a second question about the same file, so it is reported as a second block rather than
folded into the first: the `verdict` lines are about the left program alone, exactly as they are
for a file with no claim. -- ref: `docs/equivalence.md` -/

/-- Whether a side's parallel reading is known well formed, which is what makes the claim's theorem
available: `wfB` decides it at every heap, and the exact check decides it at this one. -/
def sideSound (L : Layout) (p : ParProg) : Bool :=
  ParProg.wfB p || wellFormedB (ParProg.execPar p (fun _ => 0)) L.state

/-- What a claim compares, in words: the cells always, and the registers when the keyword was
`assertParSeq`. -/
def comparedWord (cl : Claim) : String :=
  match cl.strength with
  | .heap   => toString cl.cells.length ++ " cell(s)"
  | .parSeq => toString cl.cells.length ++ " cell(s) and "
                 ++ toString cl.regs.length ++ " register(s)"

/-- What the claim says, and whether it holds: the two sides compared on the heap the file
declares, plus whether that comparison extends to every schedule of both. An `assertParSeq`
compares the final register file as well, so its two halves are reported separately — a register
disagreement is a different fault from a cell disagreement and names different things.
-- ref: `docs/equivalence.md` § What `assertParSeq` adds -/
def claimParts (c : Compiled) (cl : Claim) : String × String :=
  let ρ : Regs := fun _ => 0
  let σ := c.layout.state
  let bad  := ParProg.disagreeOn cl.cells c.prog cl.other ρ σ
  let badR := ParProg.disagreeRegs cl.regs c.prog cl.other ρ σ
  let stated := cl.left ++ " == " ++ cl.right ++ " on " ++ ", ".intercalate cl.bufs
                  ++ (match cl.strength with
                      | .heap   => ""
                      | .parSeq => ", and " ++ clipNames c.regName 6 cl.regs)
  let held :=
    if !bad.isEmpty then
      "DISAGREE — " ++ clipNames c.locName 6 bad ++ " ("
        ++ toString bad.length ++ " of " ++ toString cl.cells.length ++ " cell(s) compared)"
    else if !badR.isEmpty then
      "DISAGREE — " ++ clipNames c.regName 6 badR ++ " ("
        ++ toString badR.length ++ " of " ++ toString cl.regs.length
        ++ " register(s) compared; every compared cell agrees)"
    else if ParProg.wfB c.prog && ParProg.wfB cl.other then
      "Agree: Yes — the same " ++ comparedWord cl
        ++ ", under every schedule of either side"
    else if sideSound c.layout c.prog && sideSound c.layout cl.other then
      "Agree: Yes — the same " ++ comparedWord cl
        ++ ", under every schedule of either side at this heap"
    else
      let racy := if !sideSound c.layout c.prog then cl.left else cl.right
      "Agree: Yes on the canonical run — but '" ++ racy
        ++ "' has a race, so nothing holds under every schedule"
  (stated, held)

/-- Whether the file's claim holds, so the command line can answer with it: the compared cells
agree and both sides are sound, or the file states no claim. A disagreement is a failure of the
file and not a caveat on it. -/
def claimHolds (c : Compiled) : Bool :=
  match c.claim with
  | none    => true
  | some cl =>
      (ParProg.disagreeOn cl.cells c.prog cl.other (fun _ => 0) c.layout.state).isEmpty
        && (ParProg.disagreeRegs cl.regs c.prog cl.other (fun _ => 0) c.layout.state).isEmpty
        && sideSound c.layout c.prog && sideSound c.layout cl.other

/-- The claim's two lines, the second indented to the first's column. -/
def claimBlock (c : Compiled) (cl : Claim) (gutter : String) : String :=
  let (stated, held) := claimParts c cl
  stated ++ "\n" ++ gutter ++ held

/-- The two halves, each label in its own column, indented under one `verdict` heading. -/
def verdictBlock (c : Compiled) (gutter : String) : String :=
  "\n".intercalate ((verdictParts c).zipIdx.map fun ((lbl, txt), i) =>
    (if i == 0 then "" else gutter)
      ++ lbl ++ String.ofList (List.replicate (12 - min 12 lbl.length) ' ') ++ txt)


end Paralever.Lang
