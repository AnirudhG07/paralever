import Lang.Core.Analysis

/-! # Regrouping a `;`-chain

The rewrite moves statements between nesting levels and never changes their order: a chain becomes
segments, segments become threads, threads become stages. Each step is one regrouping, so one lemma
(`runSeq_block_map`) covers all of them. -- ref: docs/autopar-algorithm.md § Why regrouping -/

namespace Paralever.AutoPar
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-- `block []` is `%r := R r`, so it is a no-op only up to function extensionality. -/
theorem Regs.set_self (ρ : Regs) (r : Reg) : ρ.set r (ρ r) = ρ := by
  funext r'; unfold Paralever.Regs.set; split
  · subst_vars; rfl
  · rfl

/-- The empty chain leaves both the registers and the heap alone. -/
theorem runSeq_block_nil (ρ : Regs) (σ : State) :
    runSeq (execSeq (block []) ρ) σ = (ρ, σ) := by
  show runSeq (execSeq (.set 0 (.reg 0)) ρ) σ = _
  simp only [execSeq, runSeq, AExp.eval]
  rw [Regs.set_self]

/-- One statement peeled off the front of a chain. -/
theorem runSeq_block_cons (s : ParProg) (ss : List ParProg) (ρ : Regs) (σ : State) :
    runSeq (execSeq (block (s :: ss)) ρ) σ
      = runSeq (execSeq (block ss) (runSeq (execSeq s ρ) σ).1) (runSeq (execSeq s ρ) σ).2 := by
  match ss with
  | []      => rw [runSeq_block_nil]; rfl
  | t :: ts =>
      show runSeq (execSeq (.seq s (block (t :: ts))) ρ) σ = _
      simp only [execSeq, runSeq_bind]

/-- **A chain splits at any concatenation.** -/
theorem runSeq_block_append : ∀ (xs ys : List ParProg) (ρ : Regs) (σ : State),
    runSeq (execSeq (block (xs ++ ys)) ρ) σ
      = runSeq (execSeq (block ys) (runSeq (execSeq (block xs) ρ) σ).1)
          (runSeq (execSeq (block xs) ρ) σ).2 := by
  intro xs
  induction xs with
  | nil => intro ys ρ σ; rw [runSeq_block_nil]; rfl
  | cons x rest ih =>
      intro ys ρ σ
      rw [List.cons_append, runSeq_block_cons, ih, runSeq_block_cons]

/-- **Regrouping is invisible.** A chain of blocks runs exactly like the flat chain — the lemma the
whole rewrite is built from, applied once per nesting level. -/
theorem runSeq_block_map : ∀ (xss : List (List ParProg)) (ρ : Regs) (σ : State),
    runSeq (execSeq (block (xss.map block)) ρ) σ
      = runSeq (execSeq (block xss.flatten) ρ) σ := by
  intro xss
  induction xss with
  | nil => intro ρ σ; simp
  | cons xs rest ih =>
      intro ρ σ
      rw [List.map_cons, runSeq_block_cons, List.flatten_cons, runSeq_block_append, ih]

/-- **`flatten` is faithful.** The statement list of a chain runs like the chain. Only `seq` does
any work: every other constructor is its own singleton list. -/
theorem runSeq_flatten_all :
    (∀ (p : ParProg) (ρ : Regs) (σ : State),
        runSeq (execSeq (block (flatten p)) ρ) σ = runSeq (execSeq p ρ) σ)
    ∧ (∀ (_ : List ParProg), True) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l ρ σ; rfl
  · intro l e ρ σ; rfl
  · intro r e ρ σ; rfl
  · intro a b ia ib ρ σ
    show runSeq (execSeq (block (flatten a ++ flatten b)) ρ) σ = _
    rw [runSeq_block_append, ia, ib]
    simp only [execSeq, runSeq_bind]
  · intro ss _ ρ σ; rfl
  · intro nm s _ ρ σ; rfl
  · intro r a e ρ σ; rfl
  · intro a e v ρ σ; rfl
  · intro c t e _ _ ρ σ; rfl
  · intro ρ σ; rfl
  · trivial
  · intro _ _ _ _; trivial

/-- `runSeq_flatten_all`, for one program. -/
theorem runSeq_flatten (p : ParProg) (ρ : Regs) (σ : State) :
    runSeq (execSeq (block (flatten p)) ρ) σ = runSeq (execSeq p ρ) σ :=
  runSeq_flatten_all.1 p ρ σ

/-! ### Segments concatenate back

`atoms` only inserts boundaries, so the segments it produces reassemble the chain it was given.
-- ref: docs/autopar-algorithm.md § Units -/

/-- `atomsGo`'s pieces concatenate to the accumulator plus what is left. -/
theorem atomsGo_flatten : ∀ (ss pre acc : List ParProg),
    (atomsGo pre acc ss).flatten = acc.reverse ++ ss := by
  intro ss
  induction ss with
  | nil =>
      intro pre acc
      by_cases h : acc.isEmpty = true
      · simp only [atomsGo, h, ite_true]
        rw [List.isEmpty_iff.mp h]; rfl
      · simp only [atomsGo, h, ite_false, Bool.false_eq_true, List.flatten_cons,
          List.flatten_nil, List.append_nil]
  | cons s rest ih =>
      intro pre acc
      by_cases h : cutOK (pre ++ [s]) rest = true
      · simp only [atomsGo, h, ite_true, List.flatten_cons, ih, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append]
      · simp only [atomsGo, h, ite_false, Bool.false_eq_true, ih, List.reverse_cons,
          List.append_assoc, List.singleton_append]

/-- **The segments of a chain concatenate back to it.** -/
theorem atoms_flatten (ss : List ParProg) : (atoms ss).flatten = ss := by
  rw [atoms, atomsGo_flatten]; rfl

end Paralever.AutoPar
