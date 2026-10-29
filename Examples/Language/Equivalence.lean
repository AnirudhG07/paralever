import Lang.Load
import Lang.Report
import Lang.Core.Agree

/-! # `equiv.prl` and `twofold.prl` — two programs, and the theorem that they agree

`par_seq_eq` is about one program: does reading its `parallel` blocks in parallel reach the
outcomes reading them in order does? A reader with a sequential sort and a parallel one is asking
something else — do *these two programs* compute the same thing? `assert` states that question and
`ParProg.AgreeOn` is what it means. Rationale: `docs/equivalence.md`.

The files here are the shapes the question comes in. `equiv.prl` compares a program with no
`parallel` block at all against one built out of forks and barriers. `twofold.prl` compares two
*different* parallel programs, neither of them the sequential one. `strength.prl` and `tally.prl`
are stated with `assertParSeq`, which compares the final register file as well — the pair
`ParSeqEq` quantifies rather than the heap half alone. -/

namespace Paralever.Examples.Equivalence
open Paralever Paralever.Lang

set_option maxRecDepth 100000

/-! ## A sequential sort against a parallel one

Bubble sort and odd-even transposition sort, built from one comparator `def` so that the two sides
differ in their schedule and in nothing else. Bubble sort reads the comparator 56 times in order;
the network runs eight phases of up to four at once, with a barrier between them. -/

def file : Compiled := prl_file "equiv.prl"

/--
info: equiv.prl
  memory    A[8] @0  (8 cells)
  reads     {A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7]}
  writes    {A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7]}
  threads   1
  rounds    224 parallel, 224 sequential
  verdict   every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
  claim     bubble == oddeven on A
            Agree: Yes — the same 8 cell(s), under every schedule of either side
-/
#guard_msgs in
#eval IO.println (checkReport "equiv.prl" file)

/-! ### The two programs

`prog` is the left side and `other` the right: the same file twice over, with each side's body
written out where the `assert` stands. The declarations are shared, which is what gives both one
initial heap — and the claim is not a comparison of a program with itself, which the differing
statement counts show. -/

-- 56 comparator steps written out against 8 phases of forks: the same comparator, read twice
#guard (ParProg.flatten file.prog).length == 169
#guard (ParProg.flatten file.other).length == 17
#guard file.compared.length == 8
#guard file.claim.map (fun c => (c.left, c.right, c.bufs)) == some ("bubble", "oddeven", ["A"])

-- and two registers for all 56 of them: a call inside unrolled loops is one call site, so the
-- comparator's `%x` and `%y` are renamed once -- ref: `docs/prl.md` § Hygiene
#guard file.regs.map Prod.fst == ["x'1", "y'2"]

/-! ### What holds of them

Three decidable checks. The first two are `par_seq_eq`'s hypothesis on each side, and they are what
makes the third enough: once each program's schedules agree with its own sequential reading, two
sequential readings are all that is left to compare, and neither has a fork in it. -/

example : ParProg.wfB file.prog = true := by decide
example : ParProg.wfB file.other = true := by decide

example :
    ParProg.agreeB file.compared file.prog file.other (fun _ => 0) file.layout.state = true := by
  decide

/-- **The two sorts agree.** Every outcome either program reaches from the declared heap, under
every schedule of either, holds the same eight values in `A`. -/
theorem equiv_agree :
    ParProg.AgreeOn file.compared file.prog file.other (fun _ => 0) file.layout.state :=
  ParProg.agreeOn_of_wfB (by decide) (by decide) (by decide)

/-- And each side on its own is the theorem this project started with. -/
theorem equiv_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar file.prog ρ) (ParProg.execSeq file.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem oddeven_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar file.other ρ) (ParProg.execSeq file.other ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ### What they agree *on*

Both sides sort, so they agree at every cell of `A` — and the heap they leave is sorted, which the
claim alone does not say. `AgreeOn` compares two programs to each other and not to a
specification; that `A` ends up in order is a separate fact about one of them. -/

private def after : State := (ParProg.runTaskSeq file.prog (fun _ => 0) file.layout.state).2

#guard (List.range 8).map after == [1, 2, 3, 4, 5, 6, 7, 8]

/-! ## Two parallel programs, neither of them sequential

`twofold.prl` sums eight numbers twice: four threads over two cells each followed by a serial fold
of the partials, against a halving tree of three forks separated by barriers. Both are parallel,
both leave the answer in `S`, and both use `P` as scratch — which they leave holding different
things. That is why the claim names `S`: comparing all of memory would reject the pair over cells
neither program was asked about. -/

def two : Compiled := prl_file "twofold.prl"

/--
info: twofold.prl
  memory    X[8] @0, P[8] @8, S[1] @16  (17 cells)
  reads     {X[0], X[1], X[2], X[3], X[4], X[5], X[6], X[7], P[0], P[1], … +2 more}
  writes    {P[0], P[1], P[2], P[3], S[0]}
  threads   4
  rounds    8 parallel, 17 sequential
  verdict   every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
  claim     chunked == tree on S
            Agree: Yes — the same 1 cell(s), under every schedule of either side
-/
#guard_msgs in
#eval IO.println (checkReport "twofold.prl" two)

#guard two.compared == [16]
#guard two.claim.map (fun c => c.bufs) == some ["S"]

example : ParProg.wfB two.prog = true := by decide
example : ParProg.wfB two.other = true := by decide

/-- **The two reductions agree** on the cell the file names, under every schedule of either. -/
theorem twofold_agree :
    ParProg.AgreeOn two.compared two.prog two.other (fun _ => 0) two.layout.state :=
  ParProg.agreeOn_of_wfB (by decide) (by decide) (by decide)

/-- **And the claim is not vacuous.** Compared over every buffer instead of over `S`, the two
programs disagree: the scratch cells hold a chunked program's four partials on one side and a
tree's running sums on the other. What `on` selects is load-bearing. -/
example :
    ParProg.agreeB (List.range 17) two.prog two.other (fun _ => 0) two.layout.state = false := by
  decide

-- both leave 1 + ⋯ + 8 in `S`
#guard (ParProg.runTaskSeq two.prog (fun _ => 0) two.layout.state).2 16 == 36
#guard (ParProg.runTaskSeq two.other (fun _ => 0) two.layout.state).2 16 == 36

/-! ## The register file too: `assertParSeq`

`assert` compares the named cells of the final heap and nothing else, because two programs need not
name the same registers. When they do, dropping the register file hides a difference: a side can
carry extra work that lands in a register and still agree at every cell. `assertParSeq` compares
both halves of the outcome `ParSeqEq` quantifies, and `ParProg.AgreeParSeq` is what it means.

The registers compared are not named in the file. `Lang.claimRegs` derives them as both sides'
*written* registers, and a fork writes none the parent can see — threads get a copy and it is
discarded — so what is compared is the registers either side leaves outside a `parallel` block.
-- ref: `docs/equivalence.md` § What `assertParSeq` adds -/

def strong : Compiled := prl_file "strength.prl"

/--
info: strength.prl
  memory    X[4] @0, P[2] @4, S[1] @6, D[1] @7  (8 cells)
  reads     {X[0], X[1], X[2], X[3], P[0], P[1]}
  writes    {P[0], P[1], S[0], D[0]}
  threads   2
  rounds    7 parallel, 10 sequential
  verdict   every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
  claim     logged == quiet on S, and {%x'3, %y'4}
            Agree: Yes — the same 1 cell(s) and 2 register(s), under every schedule of either side
-/
#guard_msgs in
#eval IO.println (checkReport "strength.prl" strong)

-- the two post-barrier registers, and not the two inside the fork
#guard strong.comparedRegs == [2, 3]
#guard strong.comparedRegs.map strong.regName == ["%x'3", "%y'4"]
#guard strong.claim.map (fun c => c.strength) == some .parSeq

/-- **The two programs agree in memory and in registers.** Every outcome either one reaches, under
every schedule of either, holds the same value at `S[0]` *and* the same values in `%x` and `%y`. -/
theorem strength_agree :
    ParProg.AgreeParSeq strong.compared strong.comparedRegs strong.prog strong.other (fun _ => 0)
      strong.layout.state :=
  ParProg.agreeParSeq_of_wfB (by decide) (by decide) (by decide)

/-- The stronger claim implies the weaker one, so the heap half is available without reproving. -/
theorem strength_agree_heap :
    ParProg.AgreeOn strong.compared strong.prog strong.other (fun _ => 0) strong.layout.state :=
  strength_agree.toAgreeOn

/-- And `on` is still load-bearing: compared over every cell the two differ at `D[0]`, which only
`logged` writes. Naming the registers does not widen the cells. -/
example :
    ParProg.disagreeOn (List.range 8) strong.prog strong.other (fun _ => 0) strong.layout.state
      == [7] := by decide

/-! ### Why the stronger relation is strictly stronger

`tally.prl` is the witness. Both sides sum `X` through the same fork and keep a tally of the
partials they folded; the second peels the last iteration out of the loop and forgets to count it.
The heap is identical at every cell — an `assert` holds — and `%cnt` is 2 on one side and 1 on the
other, so the `assertParSeq` fails. This is the difference the heap comparison cannot see, and the
reason the two keywords are not the same claim. -/

def tally : Compiled := prl_file "tally.prl"

/--
info: tally.prl
  memory    X[4] @0, P[2] @4, S[1] @6  (7 cells)
  reads     {X[0], X[1], X[2], X[3], P[0], P[1]}
  writes    {P[0], P[1], S[0]}
  threads   2
  rounds    6 parallel, 9 sequential
  verdict   every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
  claim     counted == miscounted on S, and {%acc'3, %cnt'4, %p'5}
            DISAGREE — {%cnt'4} (1 of 3 register(s) compared; every compared cell agrees)
-/
#guard_msgs in
#eval IO.println (checkReport "tally.prl" tally)

-- every cell agrees, including the ones the claim does not name
example :
    ParProg.disagreeOn (List.range 7) tally.prog tally.other (fun _ => 0) tally.layout.state
      == [] := by decide

-- so the weaker claim holds …
theorem tally_agree_heap :
    ParProg.AgreeOn tally.compared tally.prog tally.other (fun _ => 0) tally.layout.state :=
  ParProg.agreeOn_of_wfB (by decide) (by decide) (by decide)

-- … and the stronger one does not, at exactly one register
example :
    ParProg.disagreeRegs tally.comparedRegs tally.prog tally.other (fun _ => 0)
      tally.layout.state == [3] := by decide

example :
    ParProg.agreeParSeqB tally.compared tally.comparedRegs tally.prog tally.other (fun _ => 0)
      tally.layout.state = false := by decide

#guard !claimHolds tally
#guard claimHolds strong

end Paralever.Examples.Equivalence
