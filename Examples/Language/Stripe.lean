import Lang.Load
import Lang.Report
import Paralever.Search.Explain

namespace Paralever.Examples.Stripe
open Paralever Paralever.Lang

abbrev p : Reg := 0
abbrev q : Reg := 1

abbrev A : ArrRef := ⟨0, 8⟩
abbrev kb : ArrRef := ⟨8, 2⟩

def t1 : ParProg := .seq (.load p 8) (.storeAt A (2 * %p) 1)
def t2 : ParProg := .seq (.load q 9) (.storeAt A (2 * %q + 1) 2)
def prog : ParProg := .par [t1, t2]

def file : Compiled := prl_file "stripe.prl"

#guard file.layout.bufs.map Placed.base == [A.base, kb.base]
-- the file ends in `print k`, which both interpreters erase, so the program this module is about is
-- the one `dropPrints` leaves — `parSeqEq_dropPrints_iff` says that is the same theorem
#guard norm prog == norm (ParProg.dropPrints file.prog)

def ρ0 : Regs := fun _ => 0

/-- The value cell `l` holds, read as an `Int` — what the index expression sees. -/
def ix (σ : State) (l : Loc) : Int := (Storable.decode (σ l)).getD (0 : Int)

theorem acc_t1 (σ : State) :
    accesses (ParProg.execPar t1 ρ0) σ = ⟨[8], [A.addr (2 * ix σ 8)]⟩ := by
  simp [t1, ParProg.execPar.eq_4, ParProg.execPar.eq_1, ParProg.execPar.eq_8,
    accesses_bind, readAs_accesses, writeAs_accesses, Footprint.empty, ix, Regs.set]

theorem acc_t2 (σ : State) :
    accesses (ParProg.execPar t2 ρ0) σ = ⟨[9], [A.addr (2 * ix σ 9 + 1)]⟩ := by
  simp [t2, ParProg.execPar.eq_4, ParProg.execPar.eq_1, ParProg.execPar.eq_8,
    accesses_bind, readAs_accesses, writeAs_accesses, Footprint.empty, ix, Regs.set]

theorem run_t1 (σ : State) :
    (runSeq (ParProg.execPar t1 ρ0) σ).2 = σ.update (A.addr (2 * ix σ 8)) (.int 1) := by
  simp [t1, ParProg.execPar.eq_4, ParProg.execPar.eq_1, ParProg.execPar.eq_8,
    readAs, writeAs, runSeq, Storable.encode, ix, Regs.set]

theorem wf_t1 (σ : State) : WellFormed (ParProg.execPar t1 ρ0) σ := by
  simp [t1, ParProg.execPar.eq_4, ParProg.execPar.eq_1, ParProg.execPar.eq_8,
    readAs, writeAs, Regs.set]

theorem wf_t2 (σ : State) : WellFormed (ParProg.execPar t2 ρ0) σ := by
  simp [t2, ParProg.execPar.eq_4, ParProg.execPar.eq_1, ParProg.execPar.eq_8,
    readAs, writeAs, Regs.set]

/-! ## Independence -/

/-- Reading one cell depends on that cell alone, so a store elsewhere leaves an index unchanged. -/
theorem ix_congr {σ τ : State} (l : Loc) (h : σ l = τ l) : ix σ l = ix τ l := by
  unfold ix; rw [h]

/-- Every address of `A` is a cell of `A`, so neither store can reach `k`. -/
theorem addr_lt (i : Int) : A.addr i < 8 := (ArrRef.addr_inRange A (by decide) i).2

/-- **The independence obligation, discharged.** Both stores land in `A`, and `2a ≠ 2b + 1` keeps
them apart — which is `ArrRef.addr_ne`, hence `grind`, with no solver. -/
theorem indep (σ : State) (ha : 0 ≤ ix σ 8) (ha' : ix σ 8 < 4)
    (hb : 0 ≤ ix σ 9) (hb' : ix σ 9 < 4) :
    Indep (accesses (ParProg.execPar t1 ρ0) σ)
          (accesses (ParProg.execPar t2 ρ0) (runSeq (ParProg.execPar t1 ρ0) σ).2) := by
  have hlen : ((A.len : Int)) = 8 := rfl
  have hne : A.addr (2 * ix σ 8) ≠ A.addr (2 * ix σ 9 + 1) :=
    ArrRef.addr_ne A (by omega) (by rw [hlen]; omega) (by omega) (by rw [hlen]; omega) (by omega)
  have h1 : A.addr (2 * ix σ 8) < 8 := addr_lt _
  have h2 : A.addr (2 * ix σ 9 + 1) < 8 := addr_lt _
  have hne9 : (9 : Loc) ≠ A.addr (2 * ix σ 8) := by
    intro h; rw [← h] at h1; exact absurd h1 (by decide)
  rw [run_t1, acc_t1, acc_t2, ix_congr 9 (State.update_other σ (Val.int 1) hne9)]
  refine ⟨?_, ?_, ?_⟩ <;> intro l hl hr <;> simp at hl hr <;> grind

/-! ## Well-formedness, and the equivalence -/

private abbrev u1 : ParM Regs := ParProg.execPar t1 ρ0
private abbrev u2 : ParM Regs := ParProg.execPar t2 ρ0

theorem wf_parAll (σ : State) (ha : 0 ≤ ix σ 8) (ha' : ix σ 8 < 4)
    (hb : 0 ≤ ix σ 9) (hb' : ix σ 9 < 4) : WellFormed (ParM.parAll [u1, u2]) σ := by
  refine WellFormed_parAll_cons _ _ _ (wf_t1 σ) ?_ ?_
  · have := indep σ ha ha' hb hb'
    simpa [accesses_parAll_cons, accesses_parAll_nil, Footprint.union, Footprint.empty] using this
  · exact WellFormed_parAll_cons _ _ _ (wf_t2 _) (by simp [Footprint.empty]) (WellFormed_parAll_nil _)

/-- **Parallel equals sequential, at every heap whose two indices are cells of `A`'s halves.** The
declared heap is one such; the hypotheses are what `wfB` cannot see and what a solver was being
asked for. -/
theorem par_seq_eq_of_inRange (σ : State) (ha : 0 ≤ ix σ 8) (ha' : ix σ 8 < 4)
    (hb : 0 ≤ ix σ 9) (hb' : ix σ 9 < 4) :
    ParSeqEq (ParProg.execPar prog ρ0) (ParProg.execSeq prog ρ0) σ := by
  have hp : ParProg.execPar prog ρ0
      = ParM.bind (ParM.parAll [u1, u2]) (fun _ => ParM.pure ρ0) := rfl
  have hs : ParProg.execSeq prog ρ0
      = ParM.bind (ParM.seqAll [u1, u2]) (fun _ => ParM.pure ρ0) := rfl
  have hall := wf_parAll σ ha ha' hb hb'
  refine parSeqEq_of_runSeq_eq _ _ σ ?_ ?_ (ParProg.execPar_runSeq_all.1 prog ρ0 σ)
  · rw [hp, WellFormed_bind]; exact ⟨hall, trivial⟩
  · rw [hs, WellFormed_bind]; exact ⟨wellFormed_of_seqAll _ σ hall, trivial⟩

/-- The heap the file declares is one of them, so `par = seq` there needs no hypothesis of its own.
-/
theorem par_seq_eq_declared :
    ParSeqEq (ParProg.execPar prog ρ0) (ParProg.execSeq prog ρ0) file.layout.state :=
  par_seq_eq_of_inRange _ (by decide) (by decide) (by decide) (by decide)

/-! ## The range hypothesis is load-bearing

`A[2 * %q + 1]` is an odd cell only while `%q` is non-negative: `ArrRef.addr` clamps with
`Int.toNat`, so a negative index addresses `A[0]` — and so does `A[2 * %p]` at `%p = -1`. At that
heap the two threads write one cell. `par_seq_eq` quantified over *every* heap is therefore not
merely unproved for this program; it is false, which is why no tactic discharges it.

`ParProg.verdictAnywhere` finds this without being told where to look, at the smaller witness
`k[1] = -1`, and the report prints it as the `any heap` half of the verdict — so the hypothesis of
`par_seq_eq_of_inRange` is not an admission but the whole content of the theorem.
-- ref: `docs/general-heap.md`, `docs/smt-vc.md` § The wrap is semantics, not an artifact -/

def σneg : State := fun l => if l == 8 || l == 9 then .int (-1) else .int 0

#guard wellFormedB (ParProg.execPar prog ρ0) σneg == false
#guard (raceSites (ParProg.execPar prog ρ0) σneg).map RaceSite.conflicts == [[0]]

-- and the search finds a heap of its own, one cell away from the declared one
#guard match ParProg.verdictAnywhere file.layout file.prog with
  | .race h _ => h.edits == [(9, -1)]
  | _         => false

end Paralever.Examples.Stripe
