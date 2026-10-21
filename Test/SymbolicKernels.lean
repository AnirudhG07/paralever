import Lang.Core.Imp

/-! # The symbolic route is usable

Every kernel's obligation is proved at symbolic size; these discharge the hypotheses at a
disjoint-block layout, at every size. Two patterns recur: bound a nonlinear cell index with
`lin_lt` first, and use `grind` rather than `omega`, which cannot see through `abbrev Loc := Nat`.
-- ref: `docs/block-ir.md` -/

namespace Paralever.Test.SymbolicKernels
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-- Output block past the input, at every `n` and window `w`. -/
theorem stencil_ok (n w inp out : Nat) (h : inp + n + w ≤ out) :
    wfB (stencilK n w inp out (fun _ => .lit 1)) = true :=
  wfB_stencilK n w inp out _ (fun i j _ hj k hk => by grind)

/-- Four disjoint blocks. Threads share all of `xs`; only writes need separating. -/
theorem dense_ok (rows cols wgt xs bias out : Nat)
    (h1 : wgt + rows * cols ≤ xs) (h2 : xs + cols ≤ bias) (h3 : bias + rows ≤ out) :
    wfB (denseK rows cols wgt xs bias out) = true := by
  refine wfB_denseK rows cols wgt xs bias out (fun i j hi hj k hk => ⟨?_, ?_⟩)
    (fun i j hi hj => by grind)
  · have : j * cols + k < rows * cols := by
      rw [show j * cols + k = lin cols j k from rfl]; exact lin_lt hj hk
    grind
  · grind

/-- Injectivity is `lin_ne_of_ne` after one associativity step: `lin` associates the other way. -/
theorem biasAdd_ok (rows cols inp bias out : Nat)
    (h1 : inp + rows * cols ≤ bias) (h2 : bias + cols ≤ out) :
    wfB (biasAddK rows cols inp bias out) = true := by
  refine wfB_biasAddK rows cols inp bias out (fun i j i' j' _ hj _ hj' hne => ?_)
    (fun i j i' j' hi hj hi' hj' => ⟨?_, ?_⟩)
  · rw [Nat.add_assoc, Nat.add_assoc]
    exact lin_ne_of_ne hj hj' hne
  · have : i * cols + j < rows * cols := by
      rw [show i * cols + j = lin cols i j from rfl]; exact lin_lt hi hj
    have : i' * cols + j' < rows * cols := by
      rw [show i' * cols + j' = lin cols i' j' from rfl]; exact lin_lt hi' hj'
    grind
  · have : i * cols + j < rows * cols := by
      rw [show i * cols + j = lin cols i j from rfl]; exact lin_lt hi hj
    grind

end Paralever.Test.SymbolicKernels
