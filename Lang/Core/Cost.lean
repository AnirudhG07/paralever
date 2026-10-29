import Lang.Core.Prog
import Paralever.Lib.Cost

/-! # Cost: the parallel reading is never slower

`par_seq_eq` says the two readings compute the same thing; this says what parallelising buys. The
spans are ordered for every program the check accepts, from the same `Bool`. -/

namespace Paralever.Lang
open Paralever

namespace ParProg

/-! ## Cost: the parallel reading is never slower

The spans are ordered for every program the check accepts. The induction mirrors `par_seq_eq`'s:
`time_parAll_le_seqAll` at a fork, the children-level motive carrying the comparison between the two
different lists the interpreters produce, states aligned by `execPar_runSeq_all`. -/

theorem time_execPar_le_all :
    (∀ s ρ σ, wfB s = true → time (execPar s ρ) σ ≤ time (execSeq s ρ) σ) ∧
    (∀ ss ρ σ, wfAllB ss = true →
      time (ParM.seqAll (execParAll ss ρ)) σ ≤ time (ParM.seqAll (execSeqAll ss ρ)) σ) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l ρ σ _; exact Nat.le_refl _
  · intro l e ρ σ _; exact Nat.le_refl _
  · intro r e ρ σ _; exact Nat.le_refl _
  · intro a b ia ib ρ σ h
    rw [wfB, Bool.and_eq_true] at h
    have hwfa : WellFormed (execPar a ρ) σ := wfB_wellFormed h.1 ρ σ
    have hwfb : WellFormed (execPar b (runSeq (execPar a ρ) σ).1) (runSeq (execPar a ρ) σ).2 :=
      wfB_wellFormed h.2 _ _
    have hsa : WellFormed (execSeq a ρ) σ := wfB_wellFormedSeq_all.1 a h.1 ρ σ
    have hsb : WellFormed (execSeq b (runSeq (execSeq a ρ) σ).1) (runSeq (execSeq a ρ) σ).2 :=
      wfB_wellFormedSeq_all.1 b h.2 _ _
    have hp : WellFormed (ParM.bind (execPar a ρ) (fun ρ' => execPar b ρ')) σ := by
      rw [WellFormed_bind]; exact ⟨hwfa, hwfb⟩
    have hs : WellFormed (ParM.bind (execSeq a ρ) (fun ρ' => execSeq b ρ')) σ := by
      rw [WellFormed_bind]; exact ⟨hsa, hsb⟩
    show time (ParM.bind (execPar a ρ) _) σ ≤ time (ParM.bind (execSeq a ρ) _) σ
    rw [time_bind_add _ _ σ hp, time_bind_add _ _ σ hs, execPar_runSeq_all.1 a ρ σ]
    exact Nat.add_le_add (ia ρ σ h.1) (ib _ _ h.2)
  · intro ss ih ρ σ h
    rw [wfB, Bool.and_eq_true] at h
    have hwfPar : WellFormed (ParM.parAll (execParAll ss ρ)) σ := by
      have := wfB_wellFormed (s := .par ss) (by rw [wfB, Bool.and_eq_true]; exact h) ρ σ
      exact ((WellFormed_bind _ _ σ).mp this).1
    show time (ParM.bind (ParM.parAll (execParAll ss ρ)) _) σ
       ≤ time (ParM.bind (ParM.seqAll (execSeqAll ss ρ)) _) σ
    have hsq : WellFormed (ParM.seqAll (execSeqAll ss ρ)) σ :=
      wfB_wellFormedSeq_all.2 ss h.2 ρ σ
    rw [time_bind_add _ _ σ (by rw [WellFormed_bind]; exact ⟨hwfPar, trivial⟩),
        time_bind_add _ _ σ (by rw [WellFormed_bind]; exact ⟨hsq, trivial⟩)]
    have h1 : time (ParM.parAll (execParAll ss ρ)) σ
            ≤ time (ParM.seqAll (execParAll ss ρ)) σ :=
      time_parAll_le_seqAll _ σ hwfPar
    have h2 := ih ρ σ h.2
    have hz : ∀ (τ : State) (r : Regs), time (ParM.pure r) τ = 0 := fun _ _ => rfl
    rw [hz, hz]
    omega
  · intro nm s ih ρ σ h; exact ih ρ σ h
  · intro r a e ρ σ _; exact Nat.le_refl _
  · intro a e v ρ σ _; exact Nat.le_refl _
  · intro c t e it ie ρ σ h
    rw [wfB, Bool.and_eq_true] at h
    show time (if c.eval ρ != 0 then execPar t ρ else execPar e ρ) σ
       ≤ time (if c.eval ρ != 0 then execSeq t ρ else execSeq e ρ) σ
    by_cases hc : c.eval ρ != 0
    · rw [ite_eq_left hc, ite_eq_left hc]; exact it ρ σ h.1
    · rw [ite_eq_right hc, ite_eq_right hc]; exact ie ρ σ h.2
  · intro ρ σ _; exact Nat.le_refl _
  · intro ρ σ _; exact Nat.le_refl _
  · intro s ss i1 i2 ρ σ h
    rw [wfAllB, Bool.and_eq_true] at h
    have hwp : WellFormed (ParM.seqAll (execParAll (s :: ss) ρ)) σ :=
      wellFormed_seqAll_of_childs _ σ
        (wfB_wellFormed_all.2 (s :: ss) (by rw [wfAllB, Bool.and_eq_true]; exact h) ρ σ)
    have hws : WellFormed (ParM.seqAll (execSeqAll (s :: ss) ρ)) σ :=
      wfB_wellFormedSeq_all.2 (s :: ss) (by rw [wfAllB, Bool.and_eq_true]; exact h) ρ σ
    show time (ParM.seqAll (execPar s ρ :: execParAll ss ρ)) σ
       ≤ time (ParM.seqAll (execSeq s ρ :: execSeqAll ss ρ)) σ
    rw [time_seqAll_cons _ _ σ hwp, time_seqAll_cons _ _ σ hws,
        execPar_runSeq_all.1 s ρ σ]
    exact Nat.add_le_add (i1 ρ σ h.1) (i2 _ _ h.2)
  · intro _ ρ σ _; exact Nat.le_refl _
  · -- the nest: the same children both ways, so `time_parAll_le_seqAll` is the whole step
    intro n ρ σ h
    simp only [wfB] at h
    have hwfPar : WellFormed (ParM.parAll (n.threads ρ)) σ := LoopNest.wellFormed_threads h ρ σ
    have hsq : WellFormed (ParM.seqAll (n.threads ρ)) σ := n.wellFormed_seqAll ρ σ
    show time (ParM.bind (ParM.parAll (n.threads ρ)) _) σ
       ≤ time (ParM.bind (ParM.seqAll (n.threads ρ)) _) σ
    rw [time_bind_add _ _ σ (by rw [WellFormed_bind]; exact ⟨hwfPar, trivial⟩),
        time_bind_add _ _ σ (by rw [WellFormed_bind]; exact ⟨hsq, trivial⟩)]
    have h1 : time (ParM.parAll (n.threads ρ)) σ ≤ time (ParM.seqAll (n.threads ρ)) σ :=
      time_parAll_le_seqAll _ σ hwfPar
    have hz : ∀ (τ : State) (r : Regs), time (ParM.pure r) τ = 0 := fun _ _ => rfl
    rw [hz, hz]
    omega

/-- **Par ≤ Seq, in rounds.** For every program the check accepts, the parallel reading needs no
more rounds than the sequential one — the cost counterpart of `par_seq_eq`, from the same `Bool`. -/
theorem time_le {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    time (execPar s ρ) σ ≤ time (execSeq s ρ) σ := time_execPar_le_all.1 s ρ σ h
end ParProg

end Paralever.Lang
