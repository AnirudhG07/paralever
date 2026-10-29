import Lang.Core.Analysis

/-! # The proposal preserves the program

`autoPar` rewrites a `;`-chain into forks. This file proves that the rewrite is *meaning*-preserving
— the proposal's canonical run leaves the heap the original program leaves.

`wfB` cannot supply this. It rules out memory races, and the way a rewrite goes wrong here is not a
race: a `par` node resets the register file, so a register written on one side of a fork boundary
and read on the other reads a stale value, in **both** readings. -- ref: docs/autopar.md -/

namespace Paralever.Lang
open Paralever

namespace ParProg

/-! ### Registers an expression reads -/

theorem eval_congr : ∀ {e : AExp} {ρ ρ' : Regs},
    (∀ r ∈ regsOf e, ρ r = ρ' r) → e.eval ρ = e.eval ρ' := by
  intro e
  induction e with
  | lit n => intro _ _ _; rfl
  | reg r => intro _ _ h; exact h r (by simp [regsOf])
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb
  | min a b iha ihb | max a b iha ihb | div a b iha ihb
  | lt a b iha ihb | eq a b iha ihb =>
      intro ρ ρ' h
      have ha := iha (fun r hr => h r (by simp [regsOf, hr]))
      have hb := ihb (fun r hr => h r (by simp [regsOf, hr]))
      simp [AExp.eval, ha, hb]
  | not a iha =>
      intro ρ ρ' h
      simp [AExp.eval, iha (fun r hr => h r (by simpa [regsOf] using hr))]

/-! ### A statement changes only the registers its register footprint names

The frame property for the register file. It is what lets the proof say "the file the next segment
sees differs from the pre-fork one only on registers written so far". -/

theorem regs_frame_all :
    (∀ (s : ParProg) (ρ : Regs) (σ : State) (r : Reg),
        r ∉ (regFootprint s).writes → (runSeq (execSeq s ρ) σ).1 r = ρ r)
    ∧ (∀ _ : List ParProg, True) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r' l ρ σ r hr
    simp only [regFootprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [execSeq, readAs, runSeq, Regs.set, hr]
  · intro l e ρ σ r _; simp [execSeq, writeAs, runSeq]
  · intro r' e ρ σ r hr
    simp only [regFootprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [execSeq, runSeq, Regs.set, hr]
  · intro a b iha ihb ρ σ r hr
    simp only [regFootprint, Footprint.union, List.mem_append, not_or] at hr
    rw [execSeq, runSeq_bind, ihb _ _ _ hr.2, iha _ _ _ hr.1]
  · intro ss _ ρ σ r _; simp [execSeq, runSeq_bind]
  · intro nm s ih ρ σ r hr; exact ih ρ σ r hr
  · intro r' a e ρ σ r hr
    simp only [regFootprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [execSeq, readAs, runSeq, Regs.set, hr]
  · intro a e v ρ σ r _; simp [execSeq, writeAs, runSeq]
  · intro c t e iht ihe ρ σ r hr
    simp only [regFootprint, Footprint.union, List.nil_append,
      List.mem_append, not_or] at hr
    rw [execSeq]
    split
    · exact iht _ _ _ hr.1
    · exact ihe _ _ _ hr.2
  · intro ρ σ r _; simp [execSeq, runSeq]
  · trivial
  · intro _ _ _ _; trivial
  · intro _ ρ σ r _; rfl
  -- the nest: a fork hands back the file it was given, so nothing moved
  · intro n ρ σ r _; simp [execSeq, runSeq_bind]

/-- `regs_frame_all`, for one statement. -/
theorem regs_frame (s : ParProg) (ρ : Regs) (σ : State) {r : Reg}
    (h : r ∉ (regFootprint s).writes) : (runSeq (execSeq s ρ) σ).1 r = ρ r :=
  regs_frame_all.1 s ρ σ r h

/-! ### Agreement on a register set is preserved by a run

If two register files agree on a set `R` that covers everything the statement reads, the statement
leaves the same heap under both and the files still agree on `R` afterwards. Stated with `R` as a
parameter rather than with the statement's own read set, because that is what carries through a `;`
— and because a conditional's write set names registers only one branch assigns, so "the files
agree on the writes" is simply false for `ifElse`. -/

/-! ### A nest leaves the same heap under agreeing register files

The nest case of `agree_run_all` below. A nest has no sub-statement, so the induction cannot be
delegated: it runs over the body, then over the inner points, then over the threads. The invariant
is the same one at all three levels — equal heaps, and files agreeing on `R`. A register written
*inside* the body may lie outside `R`, which is harmless, because anything the body goes on to read
is in `regsOfNest` and so in `R`. -- ref: `docs/loops.md` -/

private theorem agree_setIvs (R : List Reg) : ∀ (rs : List Reg) (los sts : List Int)
    (cs : List Nat) (ρ ρ' : Regs), (∀ r ∈ R, ρ r = ρ' r) →
      ∀ r ∈ R, setIvs rs los sts cs ρ r = setIvs rs los sts cs ρ' r := by
  intro rs
  induction rs with
  | nil => intro los sts cs ρ ρ' hR; exact hR
  | cons r0 rs ih =>
      intro los sts cs ρ ρ' hR
      cases los with
      | nil => exact hR
      | cons l los =>
        cases sts with
        | nil => exact hR
        | cons st sts =>
          cases cs with
          | nil => exact hR
          | cons c cs =>
            refine ih los sts cs _ _ ?_
            intro r hr
            simp only [Regs.set]
            split
            · rfl
            · exact hR r hr

private theorem agree_runStmts (R : List Reg) (q : List Nat) :
    ∀ (body : List NestStmt), (∀ r ∈ regsOfNest body, r ∈ R) →
    ∀ (ρ ρ' : Regs) (σ : State), (∀ r ∈ R, ρ r = ρ' r) →
      (runSeq (runStmts body q ρ) σ).2 = (runSeq (runStmts body q ρ') σ).2
      ∧ ∀ r ∈ R, (runSeq (runStmts body q ρ) σ).1 r = (runSeq (runStmts body q ρ') σ).1 r := by
  intro body
  induction body with
  | nil => intro _ ρ ρ' σ hR; exact ⟨rfl, hR⟩
  | cons s ss ih =>
      intro hsub ρ ρ' σ hR
      cases s with
      | rd r a =>
          simp only [runStmts, runSeq_bind, runSeq_exec_rd]
          refine ih (fun r' hr' => hsub r' (by simp only [regsOfNest]; exact hr')) _ _ σ ?_
          intro r' hr'
          simp only [Regs.set]
          split
          · rfl
          · exact hR r' hr'
      | wr a e =>
          have he : e.eval ρ = e.eval ρ' :=
            eval_congr (fun r' hr' => hR r' (hsub r'
              (by simp only [regsOfNest]; exact List.mem_append.2 (Or.inl hr'))))
          simp only [runStmts, runSeq_bind, runSeq_exec_wr, he]
          exact ih (fun r' hr' => hsub r'
            (by simp only [regsOfNest]; exact List.mem_append.2 (Or.inr hr'))) _ _ _ hR
      | st r e =>
          have he : e.eval ρ = e.eval ρ' :=
            eval_congr (fun r' hr' => hR r' (hsub r'
              (by simp only [regsOfNest]; exact List.mem_append.2 (Or.inl hr'))))
          simp only [runStmts, runSeq_bind, runSeq_exec_st, he]
          refine ih (fun r' hr' => hsub r'
            (by simp only [regsOfNest]; exact List.mem_append.2 (Or.inr hr'))) _ _ σ ?_
          intro r' hr'
          simp only [Regs.set]
          split
          · rfl
          · exact hR r' hr'

private theorem agree_inner (n : LoopNest) (R : List Reg)
    (hsub : ∀ r ∈ regsOfNest n.body, r ∈ R) (u : List Nat) :
    ∀ (ps : List (List Nat)) (ρ ρ' : Regs) (σ : State), (∀ r ∈ R, ρ r = ρ' r) →
      (runSeq (n.inner u ps ρ) σ).2 = (runSeq (n.inner u ps ρ') σ).2
      ∧ ∀ r ∈ R, (runSeq (n.inner u ps ρ) σ).1 r = (runSeq (n.inner u ps ρ') σ).1 r := by
  intro ps
  induction ps with
  | nil => intro ρ ρ' σ hR; exact ⟨rfl, hR⟩
  | cons p ps ih =>
      intro ρ ρ' σ hR
      obtain ⟨h1, h2⟩ := agree_runStmts R (u ++ p) n.body hsub
        (setIvs n.ivs n.lo n.step (u ++ p) ρ) (setIvs n.ivs n.lo n.step (u ++ p) ρ') σ
        (agree_setIvs R n.ivs n.lo n.step (u ++ p) ρ ρ' hR)
      simp only [LoopNest.inner, LoopNest.atPoint, runSeq_bind]
      rw [h1]
      exact ih _ _ _ h2

private theorem agree_threads (n : LoopNest) (R : List Reg)
    (hsub : ∀ r ∈ regsOfNest n.body, r ∈ R) :
    ∀ (us : List (List Nat)) (ρ ρ' : Regs) (σ : State), (∀ r ∈ R, ρ r = ρ' r) →
      (runSeq (ParM.seqAll (us.map (n.thread ρ))) σ).2
        = (runSeq (ParM.seqAll (us.map (n.thread ρ'))) σ).2 := by
  intro us
  induction us with
  | nil => intro ρ ρ' σ _; rfl
  | cons u us ih =>
      intro ρ ρ' σ hR
      simp only [List.map_cons, runSeq_seqAll_cons', LoopNest.thread]
      rw [(agree_inner n R hsub u n.innerBox ρ ρ' σ hR).1]
      exact ih ρ ρ' _ hR

theorem agree_run_all :
    (∀ (s : ParProg) (R : List Reg) (ρ ρ' : Regs) (σ : State),
        (∀ r ∈ (regFootprint s).reads, r ∈ R) → (∀ r ∈ R, ρ r = ρ' r) →
          (runSeq (execSeq s ρ) σ).2 = (runSeq (execSeq s ρ') σ).2
          ∧ ∀ r ∈ R, (runSeq (execSeq s ρ) σ).1 r = (runSeq (execSeq s ρ') σ).1 r)
    ∧ (∀ (ss : List ParProg) (R : List Reg) (ρ ρ' : Regs) (σ : State),
        (∀ r ∈ (regFootprintsOf ss).reads, r ∈ R) → (∀ r ∈ R, ρ r = ρ' r) →
          (runSeq (ParM.seqAll (execSeqAll ss ρ)) σ).2
            = (runSeq (ParM.seqAll (execSeqAll ss ρ')) σ).2) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- load: the address is a literal, so both sides read the same cell
  · intro r' l R ρ ρ' σ _ hR
    refine ⟨by simp [execSeq, readAs, runSeq], ?_⟩
    intro r hr
    simp only [execSeq, readAs, runSeq_bind, runSeq, Regs.set]
    split
    · rfl
    · exact hR r hr
  -- store
  · intro l e R ρ ρ' σ hsub hR
    have he : e.eval ρ = e.eval ρ' :=
      eval_congr (fun r hr => hR r (hsub r (by simpa [regFootprint] using hr)))
    exact ⟨by simp [execSeq, writeAs, runSeq, he], by intro r hr; simpa [execSeq, runSeq] using hR r hr⟩
  -- set
  · intro r' e R ρ ρ' σ hsub hR
    have he : e.eval ρ = e.eval ρ' :=
      eval_congr (fun r hr => hR r (hsub r (by simpa [regFootprint] using hr)))
    refine ⟨by simp [execSeq, runSeq], ?_⟩
    intro r hr
    simp only [execSeq, runSeq, Regs.set]
    split
    · exact he
    · exact hR r hr
  -- seq: `R` is carried through unchanged, which is the point of parameterising by it
  · intro a b iha ihb R ρ ρ' σ hsub hR
    simp only [regFootprint, Footprint.union, List.mem_append] at hsub
    obtain ⟨hA, hAw⟩ := iha R ρ ρ' σ (fun r hr => hsub r (Or.inl hr)) hR
    obtain ⟨hB, hBw⟩ := ihb R _ _ (runSeq (execSeq a ρ) σ).2
      (fun r hr => hsub r (Or.inr hr)) hAw
    simp only [execSeq, runSeq_bind]
    rw [← hA]
    exact ⟨hB, hBw⟩
  -- par: the threads see the file as it was, so only the heap is at stake
  · intro ss ih R ρ ρ' σ hsub hR
    refine ⟨?_, ?_⟩
    · simp only [execSeq, runSeq_bind, runSeq]
      exact ih R ρ ρ' σ (fun r hr => hsub r (by simpa [regFootprint] using hr)) hR
    · intro r hr; simpa [execSeq, runSeq_bind, runSeq] using hR r hr
  -- label
  · intro nm s ih R ρ ρ' σ hsub hR; exact ih R ρ ρ' σ hsub hR
  -- loadAt: the address is computed, so it needs the expression congruence
  · intro r' a e R ρ ρ' σ hsub hR
    have he : e.eval ρ = e.eval ρ' :=
      eval_congr (fun r hr => hR r (hsub r (by simpa [regFootprint] using hr)))
    refine ⟨by simp [execSeq, readAs, runSeq], ?_⟩
    intro r hr
    simp only [execSeq, readAs, runSeq_bind, runSeq, Regs.set, he]
    split
    · rfl
    · exact hR r hr
  -- storeAt
  · intro a e v R ρ ρ' σ hsub hR
    simp only [regFootprint] at hsub
    have he : e.eval ρ = e.eval ρ' :=
      eval_congr (fun r hr => hR r (hsub r (List.mem_append.2 (Or.inl hr))))
    have hv : v.eval ρ = v.eval ρ' :=
      eval_congr (fun r hr => hR r (hsub r (List.mem_append.2 (Or.inr hr))))
    exact ⟨by simp [execSeq, writeAs, runSeq, he, hv],
           by intro r hr; simpa [execSeq, runSeq] using hR r hr⟩
  -- ifElse: the same branch is taken, because the condition's registers are in `R`
  · intro c t e iht ihe R ρ ρ' σ hsub hR
    simp only [regFootprint, Footprint.union, List.nil_append, List.mem_append] at hsub
    have hc : c.eval ρ = c.eval ρ' := eval_congr (fun r hr => hR r (hsub r (Or.inl hr)))
    simp only [execSeq, hc]
    split
    · exact iht R ρ ρ' σ (fun r hr => hsub r (Or.inr (Or.inl hr))) hR
    · exact ihe R ρ ρ' σ (fun r hr => hsub r (Or.inr (Or.inr hr))) hR
  -- nil
  · intro R ρ ρ' σ _ hR
    exact ⟨by simp [execSeq, runSeq], by intro r hr; simpa [execSeq, runSeq] using hR r hr⟩
  · intro R ρ ρ' σ _ _; rfl
  -- cons
  · intro s ss ih1 ih2 R ρ ρ' σ hsub hR
    simp only [regFootprintsOf, Footprint.union, List.mem_append] at hsub
    obtain ⟨hhd, _⟩ := ih1 R ρ ρ' σ (fun r hr => hsub r (Or.inl hr)) hR
    show (runSeq (ParM.bind (ParM.seqPair _ _) _) σ).2
        = (runSeq (ParM.bind (ParM.seqPair _ _) _) σ).2
    simp only [ParM.seqPair, runSeq_bind, runSeq]
    rw [hhd]
    exact ih2 R ρ ρ' _ (fun r hr => hsub r (Or.inr hr)) hR
  · intro _ R ρ ρ' σ _ hR; exact ⟨rfl, fun r hr => hR r hr⟩
  -- the nest: no sub-statement, so the three inductions above do the work
  · intro n R ρ ρ' σ hsub hR
    refine ⟨?_, fun r hr => by simpa [execSeq, runSeq_bind, runSeq] using hR r hr⟩
    simp only [execSeq, LoopNest.threads, runSeq_bind, runSeq]
    exact agree_threads n R (fun r hr => hsub r (by simpa [regFootprint] using hr))
      n.outerBox ρ ρ' σ hR

/-- `agree_run_all`, for one statement: agreement on what it reads gives the same heap. -/
theorem agree_heap (s : ParProg) (R : List Reg) (ρ ρ' : Regs) (σ : State)
    (hsub : ∀ r ∈ (regFootprint s).reads, r ∈ R) (hR : ∀ r ∈ R, ρ r = ρ' r) :
    (runSeq (execSeq s ρ) σ).2 = (runSeq (execSeq s ρ') σ).2 :=
  (agree_run_all.1 s R ρ ρ' σ hsub hR).1

/-! ### Forking a chain

The construction's core. A `par` node hands every thread the *pre-fork* register file, where the
`;`-chain it replaces threads the file from one statement to the next. The two therefore leave the
same heap exactly when no statement reads a register an earlier one wrote — which is the condition
`atoms` establishes by placing fork boundaries only at legal cuts. -/

/-- No register written by one segment is read by a later one. -/
def noRegFlow : List ParProg → Bool
  | []      => true
  | s :: ss => ss.all (fun t => disjointB (regFootprint s).writes (regFootprint t).reads)
               && noRegFlow ss

/-- **Forking a chain preserves its heap.** `wr` tracks the registers already written by statements
*before* this chain, so the lemma can be applied part-way along one; at the top it is empty. -/
theorem fork_heap : ∀ (g : List ParProg) (wr : List Reg) (ρ ρ₀ : Regs) (σ : State),
    (∀ r, r ∉ wr → ρ r = ρ₀ r) →
    (∀ s ∈ g, ∀ r ∈ (regFootprint s).reads, r ∉ wr) →
    noRegFlow g = true →
    (runSeq (ParM.seqAll (execSeqAll g ρ₀)) σ).2 = (runSeq (execSeq (block g) ρ) σ).2 := by
  intro g
  induction g with
  | nil => intro wr ρ ρ₀ σ _ _ _; simp [execSeqAll, ParM.seqAll, block, execSeq, runSeq]
  | cons s rest ih =>
      intro wr ρ ρ₀ σ hwr hrd hflow
      -- the head sees the same registers either way
      have hhead : (runSeq (execSeq s ρ₀) σ).2 = (runSeq (execSeq s ρ) σ).2 := by
        refine agree_heap s (regFootprint s).reads ρ₀ ρ σ (fun _ h => h) ?_
        intro r hr
        exact (hwr r (hrd s (by simp) r hr)).symm
      simp only [noRegFlow, Bool.and_eq_true, List.all_eq_true] at hflow
      match rest, ih with
      | [], _ =>
          show (runSeq (ParM.bind (ParM.seqPair _ _) _) σ).2 = _
          simp only [ParM.seqPair, runSeq_bind, runSeq, execSeqAll, ParM.seqAll, block]
          exact hhead
      | t :: rest', ih =>
          show (runSeq (ParM.bind (ParM.seqPair _ _) _) σ).2 = _
          simp only [ParM.seqPair, runSeq_bind, runSeq, execSeqAll, block, execSeq]
          rw [hhead]
          refine ih (wr ++ (regFootprint s).writes) (runSeq (execSeq s ρ) σ).1 ρ₀ _ ?_ ?_ ?_
          · intro r hr
            simp only [List.mem_append, not_or] at hr
            rw [regs_frame s ρ σ hr.2]; exact hwr r hr.1
          · intro u hu r hr
            simp only [List.mem_append, not_or]
            refine ⟨hrd u (by simp [hu]) r hr, ?_⟩
            have := (disjointB_iff _ _).1 (hflow.1 u hu)
            exact fun hc => this r hc hr
          · exact hflow.2

/-- **A `par` node and the `;`-chain it replaces leave the same heap**, when no register flows
between the threads. -/
theorem par_block_heap (g : List ParProg) (h : noRegFlow g = true) (ρ : Regs) (σ : State) :
    (runSeq (execPar (.par g) ρ) σ).2 = (runSeq (execSeq (block g) ρ) σ).2 := by
  rw [execPar_runSeq_all.1 (.par g) ρ σ]
  show (runSeq (ParM.bind (ParM.seqAll (execSeqAll g ρ)) _) σ).2 = _
  rw [runSeq_bind]
  simp only [runSeq]
  exact fork_heap g [] ρ ρ σ (fun _ _ => rfl) (fun _ _ _ _ => by simp) h

end ParProg
end Paralever.Lang
