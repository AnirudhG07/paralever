import Lang.Core.Prog

/-! # Two programs, one heap: when do they agree?

`par_seq_eq` answers a question about *one* program — does reading its `parallel` blocks in
parallel reach the outcomes reading them in order does? A reader who has written both a sequential
sort and a parallel one wants a different question answered: do *these two programs* compute the
same thing?

They are not the same question and the second does not reduce to the first. What it reduces to is
the first, twice, plus an equality between the two programs' **sequential** readings — and that
last part has nothing to do with parallelism. Rationale, and the boundary of what is decided:
`docs/equivalence.md`. -/

namespace Paralever.Lang
open Paralever

namespace ParProg

/-- **Two programs agree on `cells`.** Every outcome `p` reaches from `σ` and every outcome `q`
reaches from `σ` hold the same values at those cells — so there is no schedule of `p` and no
schedule of `q` that disagree, and a reader comparing them need not be told which ran.

Registers are not compared: two programs need not even name the same registers, and a register is
private to its run. Nor is termination: `ParM` is inductive, so every program here terminates.

The quantifier ranges over the outcomes each program *reaches*, so a program all of whose schedules
race satisfies this vacuously — which is why both sides' well-formedness is a hypothesis of the
theorem below and not a remark on it.
-- ref: `docs/equivalence.md` § What the statement says -/
def AgreeOn (cells : List Loc) (p q : ParProg) (ρ : Regs) (σ : State) : Prop :=
  ∀ r₁ σ₁ r₂ σ₂,
    Reaches (.run (execPar p ρ) σ) (.run (.pure r₁) σ₁) →
    Reaches (.run (execPar q ρ) σ) (.run (.pure r₂) σ₂) →
    ∀ l ∈ cells, σ₁ l = σ₂ l

/-- **The canonical outcome is the only one.** A program whose parallel reading is well formed at
`σ` reaches `(r, σ')` exactly when the reference run computes it — and the reference run may be
taken on the *sequential* reading, which has no fork to schedule. `par_seq_eq` with its right-hand
side spelled out as a function rather than as a second program. -/
theorem reaches_iff_runSeq {s : ParProg} {ρ : Regs} {σ : State}
    (h : WellFormed (execPar s ρ) σ) (r : Regs) (σ' : State) :
    Reaches (.run (execPar s ρ) σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq (execSeq s ρ) σ := by
  rw [wellFormed_canonical _ σ r σ' h, execPar_runSeq_all.1 s ρ σ]

/-- The agreement, as one `Bool` on the two reference runs: what `decide` is asked and what the
command line evaluates. -/
def agreeB (cells : List Loc) (p q : ParProg) (ρ : Regs) (σ : State) : Bool :=
  let σ₁ := (runSeq (execSeq p ρ) σ).2
  let σ₂ := (runSeq (execSeq q ρ) σ).2
  cells.all (fun l => σ₁ l == σ₂ l)

/-- The cells the two programs leave differing — empty exactly when `agreeB` is true. What a report
names when the claim fails. -/
def disagreeOn (cells : List Loc) (p q : ParProg) (ρ : Regs) (σ : State) : List Loc :=
  let σ₁ := (runSeq (execSeq p ρ) σ).2
  let σ₂ := (runSeq (execSeq q ρ) σ).2
  cells.filter (fun l => σ₁ l != σ₂ l)

/-- **The two-program theorem.** Each side's parallel reading is well formed, and the two
sequential readings leave `cells` equal: then every schedule of either program leaves `cells`
equal. The parallel half of the question is discharged for both sides by the canonical-outcomes
theorem; the half that is left compares two programs with no fork in them. -/
theorem agreeOn_of_wellFormed {p q : ParProg} {cells : List Loc} {ρ : Regs} {σ : State}
    (hp : WellFormed (execPar p ρ) σ) (hq : WellFormed (execPar q ρ) σ)
    (h : agreeB cells p q ρ σ = true) : AgreeOn cells p q ρ σ := by
  intro r₁ σ₁ r₂ σ₂ k₁ k₂ l hl
  have e₁ : σ₁ = (runSeq (execSeq p ρ) σ).2 :=
    congrArg Prod.snd ((reaches_iff_runSeq hp r₁ σ₁).1 k₁)
  have e₂ : σ₂ = (runSeq (execSeq q ρ) σ).2 :=
    congrArg Prod.snd ((reaches_iff_runSeq hq r₂ σ₂).1 k₂)
  rw [e₁, e₂]
  exact beq_iff_eq.1 (List.all_eq_true.1 h l hl)

/-- **Write two programs, check two Booleans, get the theorem.** `wfB` on each side and the
agreement of the two sequential runs: three `decide`s and the equivalence holds under every
schedule of both. -/
theorem agreeOn_of_wfB {p q : ParProg} {cells : List Loc} {ρ : Regs} {σ : State}
    (hp : wfB p = true) (hq : wfB q = true) (h : agreeB cells p q ρ σ = true) :
    AgreeOn cells p q ρ σ :=
  agreeOn_of_wellFormed (wfB_wellFormed hp ρ σ) (wfB_wellFormed hq ρ σ) h

/-- **Reflexivity is not free.** A program agrees with *itself* only once its parallel reading is
well formed: a fork can race and still reach two different heaps, so the relation fails at `p = q`
without the hypothesis. This is the anti-vacuity check on `AgreeOn` — a relation every pair
satisfied would say nothing. -- ref: `docs/equivalence.md` § What the statement says -/
theorem AgreeOn.refl_of_wellFormed {cells : List Loc} {p : ParProg} {ρ : Regs} {σ : State}
    (hp : WellFormed (execPar p ρ) σ) : AgreeOn cells p p ρ σ :=
  agreeOn_of_wellFormed hp hp (by simp [agreeB])

/-- Which side is called the left one does not matter. Transitivity is **not** here for the same
reason reflexivity carries a hypothesis: chaining two claims needs the middle program to have an
outcome at all, which is `wellFormed_canonical`'s forward direction and so its hypothesis too. -/
theorem AgreeOn.symm {cells : List Loc} {p q : ParProg} {ρ : Regs} {σ : State}
    (h : AgreeOn cells p q ρ σ) : AgreeOn cells q p ρ σ :=
  fun r₁ σ₁ r₂ σ₂ k₁ k₂ l hl => (h r₂ σ₂ r₁ σ₁ k₂ k₁ l hl).symm

/-- Fewer cells compared is a weaker claim. -/
theorem AgreeOn.mono {cells sub : List Loc} {p q : ParProg} {ρ : Regs} {σ : State}
    (hs : ∀ l ∈ sub, l ∈ cells) (h : AgreeOn cells p q ρ σ) : AgreeOn sub p q ρ σ :=
  fun r₁ σ₁ r₂ σ₂ k₁ k₂ l hl => h r₁ σ₁ r₂ σ₂ k₁ k₂ l (hs l hl)

/-! ## The stronger claim: the register file too

`AgreeOn` drops the register file because two programs need not name the same registers. When they
do, dropping it hides a difference — a side can carry an extra `%r := …` and still agree at every
cell. `AgreeParSeq` compares the pair `ParSeqEq` quantifies, so an `assert` can be stated at the
metatheorem's own strength. -- ref: `docs/equivalence.md` § What `assertParSeq` adds -/

/-- **Two programs agree on `cells` and at `regs`.** `AgreeOn`'s conclusion together with the final
register file compared at the named registers: the outcome `ParSeqEq` quantifies is the pair
`(r, σ')`, and this is both of its components rather than the heap alone.

The registers are a *list* for the same reason the cells are: `Regs` is a function, so equality on
all of it is not decidable, and a program's register file is only as observable as the registers
named. `Lang/Compile/Lower.lean`'s `claimRegs` derives the list as both sides' written registers, so
a file cannot name the wrong set. -- ref: `docs/equivalence.md` § What `assertParSeq` adds -/
def AgreeParSeq (cells : List Loc) (regs : List Reg) (p q : ParProg) (ρ : Regs) (σ : State) : Prop :=
  ∀ r₁ σ₁ r₂ σ₂,
    Reaches (.run (execPar p ρ) σ) (.run (.pure r₁) σ₁) →
    Reaches (.run (execPar q ρ) σ) (.run (.pure r₂) σ₂) →
    (∀ l ∈ cells, σ₁ l = σ₂ l) ∧ (∀ k ∈ regs, r₁ k = r₂ k)

/-- The register half, as one `Bool` on the two reference runs. `agreeB`'s counterpart. -/
def agreeRegsB (regs : List Reg) (p q : ParProg) (ρ : Regs) (σ : State) : Bool :=
  let r₁ := (runSeq (execSeq p ρ) σ).1
  let r₂ := (runSeq (execSeq q ρ) σ).1
  regs.all (fun k => r₁ k == r₂ k)

/-- The registers the two programs leave differing — what a report names when the register half of
a claim fails. `disagreeOn`'s counterpart. -/
def disagreeRegs (regs : List Reg) (p q : ParProg) (ρ : Regs) (σ : State) : List Reg :=
  let r₁ := (runSeq (execSeq p ρ) σ).1
  let r₂ := (runSeq (execSeq q ρ) σ).1
  regs.filter (fun k => r₁ k != r₂ k)

/-- Both halves at once: what the command line evaluates for an `assertParSeq`. -/
def agreeParSeqB (cells : List Loc) (regs : List Reg) (p q : ParProg) (ρ : Regs) (σ : State) : Bool :=
  agreeB cells p q ρ σ && agreeRegsB regs p q ρ σ

/-- **The two-program theorem, at the metatheorem's strength.** The same two hypotheses as
`agreeOn_of_wellFormed` and one more Boolean: `reaches_iff_runSeq` pins the whole outcome `(r, σ')`,
so the register half costs the other projection of an equation already in hand. -/
theorem agreeParSeq_of_wellFormed {p q : ParProg} {cells : List Loc} {regs : List Reg}
    {ρ : Regs} {σ : State}
    (hp : WellFormed (execPar p ρ) σ) (hq : WellFormed (execPar q ρ) σ)
    (hc : agreeB cells p q ρ σ = true) (hr : agreeRegsB regs p q ρ σ = true) :
    AgreeParSeq cells regs p q ρ σ := by
  intro r₁ σ₁ r₂ σ₂ k₁ k₂
  have e₁ := (reaches_iff_runSeq hp r₁ σ₁).1 k₁
  have e₂ := (reaches_iff_runSeq hq r₂ σ₂).1 k₂
  have s₁ : σ₁ = (runSeq (execSeq p ρ) σ).2 := congrArg Prod.snd e₁
  have s₂ : σ₂ = (runSeq (execSeq q ρ) σ).2 := congrArg Prod.snd e₂
  have t₁ : r₁ = (runSeq (execSeq p ρ) σ).1 := congrArg Prod.fst e₁
  have t₂ : r₂ = (runSeq (execSeq q ρ) σ).1 := congrArg Prod.fst e₂
  refine ⟨fun l hl => ?_, fun k hk => ?_⟩
  · rw [s₁, s₂]
    exact beq_iff_eq.1 (List.all_eq_true.1 hc l hl)
  · rw [t₁, t₂]
    exact beq_iff_eq.1 (List.all_eq_true.1 hr k hk)

/-- **Write two programs, check three Booleans, get the stronger theorem.** `agreeOn_of_wfB`'s
counterpart; `agreeParSeqB` is the `&&` of the last two, which is what a report evaluates. -/
theorem agreeParSeq_of_wfB {p q : ParProg} {cells : List Loc} {regs : List Reg}
    {ρ : Regs} {σ : State}
    (hp : wfB p = true) (hq : wfB q = true) (h : agreeParSeqB cells regs p q ρ σ = true) :
    AgreeParSeq cells regs p q ρ σ := by
  have hs : agreeB cells p q ρ σ = true ∧ agreeRegsB regs p q ρ σ = true := by
    simpa [agreeParSeqB] using h
  exact agreeParSeq_of_wellFormed (wfB_wellFormed hp ρ σ) (wfB_wellFormed hq ρ σ) hs.1 hs.2

/-- The stronger claim implies the weaker one, for any register list: the heap half is `AgreeOn`
verbatim. So `assertParSeq` never states less than `assert` on the same cells. -/
theorem AgreeParSeq.toAgreeOn {cells : List Loc} {regs : List Reg} {p q : ParProg}
    {ρ : Regs} {σ : State} (h : AgreeParSeq cells regs p q ρ σ) : AgreeOn cells p q ρ σ :=
  fun r₁ σ₁ r₂ σ₂ k₁ k₂ => (h r₁ σ₁ r₂ σ₂ k₁ k₂).1

/-- Reflexivity carries the same hypothesis and for the same reason as `AgreeOn.refl_of_wellFormed`:
a racy fork reaches two different outcomes, and now two different register files as well. -/
theorem AgreeParSeq.refl_of_wellFormed {cells : List Loc} {regs : List Reg} {p : ParProg}
    {ρ : Regs} {σ : State} (hp : WellFormed (execPar p ρ) σ) : AgreeParSeq cells regs p p ρ σ :=
  agreeParSeq_of_wellFormed hp hp (by simp [agreeB]) (by simp [agreeRegsB])

/-- Which side is called the left one does not matter, as for `AgreeOn.symm`. -/
theorem AgreeParSeq.symm {cells : List Loc} {regs : List Reg} {p q : ParProg} {ρ : Regs} {σ : State}
    (h : AgreeParSeq cells regs p q ρ σ) : AgreeParSeq cells regs q p ρ σ :=
  fun r₁ σ₁ r₂ σ₂ k₁ k₂ =>
    let ⟨hc, hr⟩ := h r₂ σ₂ r₁ σ₁ k₂ k₁
    ⟨fun l hl => (hc l hl).symm, fun k hk => (hr k hk).symm⟩

/-- Fewer cells and fewer registers compared is a weaker claim. -/
theorem AgreeParSeq.mono {cells sub : List Loc} {regs rsub : List Reg} {p q : ParProg}
    {ρ : Regs} {σ : State} (hs : ∀ l ∈ sub, l ∈ cells) (hk : ∀ k ∈ rsub, k ∈ regs)
    (h : AgreeParSeq cells regs p q ρ σ) : AgreeParSeq sub rsub p q ρ σ :=
  fun r₁ σ₁ r₂ σ₂ k₁ k₂ =>
    let ⟨hc, hr⟩ := h r₁ σ₁ r₂ σ₂ k₁ k₂
    ⟨fun l hl => hc l (hs l hl), fun k h' => hr k (hk k h')⟩

end ParProg

end Paralever.Lang
