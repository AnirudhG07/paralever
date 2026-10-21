import Paralever.AutoPar.Plan
import Prl.Lang.AutoParSound

/-! # The rewrite preserves the outcome

`execSeq` of a `par` node hands every thread the pre-fork register file and restores it at the join,
so **every thread of the whole plan runs at the initial registers** — which is exactly the situation
`fork_heap` (`Prl/Lang/AutoParSound.lean`) is about, one level up. The proof is that observation plus
the regrouping lemmas. -- ref: docs/autopar-algorithm.md § The theorem -/

namespace Paralever.AutoPar
open Paralever Paralever.Prl Paralever.Prl.ParProg

/-! ## Running a list of threads in order -/

/-- One thread peeled off a sequenced list. -/
theorem runSeq_seqAll_cons (s : ParProg) (ss : List ParProg) (ρ : Regs) (σ : State) :
    (runSeq (ParM.seqAll (execSeqAll (s :: ss) ρ)) σ).2
      = (runSeq (ParM.seqAll (execSeqAll ss ρ)) (runSeq (execSeq s ρ) σ).2).2 := by
  show (runSeq (ParM.bind (ParM.seqPair _ _) _) σ).2 = _
  simp only [ParM.seqPair, runSeq_bind, runSeq]

/-- A sequenced list of threads splits at any concatenation. Every thread sees the *same* `ρ`, so
the registers never move and only the heap is threaded. -/
theorem runSeq_seqAll_append : ∀ (A B : List ParProg) (ρ : Regs) (σ : State),
    (runSeq (ParM.seqAll (execSeqAll (A ++ B) ρ)) σ).2
      = (runSeq (ParM.seqAll (execSeqAll B ρ)) (runSeq (ParM.seqAll (execSeqAll A ρ)) σ).2).2 := by
  intro A
  induction A with
  | nil => intro B ρ σ; simp [execSeqAll, ParM.seqAll, runSeq]
  | cons a rest ih =>
      intro B ρ σ
      rw [List.cons_append, runSeq_seqAll_cons, ih, runSeq_seqAll_cons]

/-! ## The plan's stages -/

/-- A plan's threads, head stage first. -/
theorem threads_cons (st : List (List ParProg)) (rest : Plan) :
    threads (st :: rest) = st.map block ++ threads rest := by
  simp [threads, List.flatten_cons, List.map_append]

/-- **A chain of `parallel` blocks runs every thread at the initial registers.** The stage
boundaries move the heap along and leave the register file where it started. -/
theorem stages_seqAll : ∀ (pl : Plan) (ρ : Regs) (σ : State),
    (runSeq (execSeq (emit pl) ρ) σ).2 = (runSeq (ParM.seqAll (execSeqAll (threads pl) ρ)) σ).2 := by
  intro pl
  induction pl with
  | nil =>
      intro ρ σ
      rw [show emit [] = block [] from rfl, runSeq_block_nil]
      simp [threads, execSeqAll, ParM.seqAll, runSeq]
  | cons st rest ih =>
      intro ρ σ
      rw [show emit (st :: rest)
            = block (.par (st.map block) :: (rest.map fun s => .par (s.map block))) from rfl,
        runSeq_block_cons]
      have hreg : (runSeq (execSeq (.par (st.map block)) ρ) σ).1 = ρ := by
        show (runSeq (ParM.bind (ParM.seqAll (execSeqAll (st.map block) ρ)) _) σ).1 = ρ
        simp only [runSeq_bind, runSeq]
      have hheap : (runSeq (execSeq (.par (st.map block)) ρ) σ).2
          = (runSeq (ParM.seqAll (execSeqAll (st.map block) ρ)) σ).2 := by
        show (runSeq (ParM.bind (ParM.seqAll (execSeqAll (st.map block) ρ)) _) σ).2 = _
        simp only [runSeq_bind, runSeq]
      rw [hreg, hheap, show block (rest.map fun s => .par (s.map block)) = emit rest from rfl,
        ih, threads_cons, runSeq_seqAll_append]

/-! ## The theorem -/

/-- **The rewrite preserves the heap.** The emitted program, read in parallel, leaves the same heap
as the unit chain it was built from — whenever no register flows between threads.

Both hypotheses are discharged downstream: `plan_units` makes the chain *equal* to the original by
construction, and `noRegFlow` is a `Bool` the rewrite checks before committing. -/
theorem emit_heap (pl : Plan) (h : noRegFlow (threads pl) = true) (ρ : Regs) (σ : State) :
    (runSeq (execPar (emit pl) ρ) σ).2 = (runSeq (execSeq (block (planUnits pl)) ρ) σ).2 := by
  rw [execPar_runSeq_all.1 (emit pl) ρ σ, stages_seqAll pl ρ σ]
  rw [fork_heap (threads pl) [] ρ ρ σ (fun _ _ => rfl) (fun _ _ _ _ => by simp) h]
  show (runSeq (execSeq (block (pl.flatten.map block)) ρ) σ).2 = _
  rw [runSeq_block_map]
  rfl

/-- **The rewrite preserves the outcome of a program.** Everything in one statement: the plan's
units are the program's statements, so the parallel reading of the rewrite leaves exactly the heap
the original sequential program does. -/
theorem rewrite_heap (p : ParProg) (us : List ParProg) (hus : planUnits (plan us) = us)
    (hblk : ∀ (ρ : Regs) (σ : State),
      runSeq (execSeq (block us) ρ) σ = runSeq (execSeq p ρ) σ)
    (h : noRegFlow (threads (plan us)) = true) (ρ : Regs) (σ : State) :
    (runSeq (execPar (emit (plan us)) ρ) σ).2 = (runSeq (execSeq p ρ) σ).2 := by
  rw [emit_heap (plan us) h ρ σ, hus, hblk ρ σ]

end Paralever.AutoPar
